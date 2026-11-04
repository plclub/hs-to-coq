#!/usr/bin/env bash
# Exercise deriving through the real CLI, then compile dictionary consumers.
set -euo pipefail

version=8.20
retained_only=false
while [[ $# -gt 0 ]]; do
    case "$1" in
        --target-version)
            if [[ $# -lt 2 ]]; then exit 2; fi
            if [[ "$2" != 8.20 && "$2" != 9.0 ]]; then exit 2; fi
            version=$2
            shift 2
            ;;
        --retained-only) retained_only=true; shift ;;
        *)
            printf 'Usage: bash %s [--target-version 8.20|9.0] [--retained-only]\n' "${0##*/}" >&2
            exit 2
            ;;
    esac
done

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
workspace=$(cd "$script_dir/.." && pwd)
export STACK_YAML="$workspace/stack.yaml"
fixtures="$script_dir/deriving-fixtures"
translator=(stack --allow-different-user exec hs-to-rocq --)
if [[ "$version" == 8.20 ]]; then
    read -r -a compiler <<< "${COQC:-coqc}"
else
    read -r -a compiler <<< "${COQC:-rocq c -w +deprecated-dirpath-Coq}"
fi
tmp=$(mktemp -d "${TMPDIR:-/tmp}/hs-to-rocq-deriving.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

fail() {
    printf 'not ok - %s/%s: %s\n' "$version" "$case_name" "$*" >&2
    local file line
    for file in "$tmp"/*.log "$tmp/out"/*.v "$tmp/out"/Data/*.v "$tmp/out"/GHC/*.v; do
        [[ -f "$file" ]] || continue
        printf '%s:\n' "$file" >&2
        while IFS= read -r line || [[ -n "$line" ]]; do printf '%s\n' "$line" >&2; done < "$file"
    done
    exit 1
}

check_recovery() {
    local edits=$1 module=$2 consumer=$3 source=${4:-DerivingRecovery} policy=${5:---strict} suffix
    mkdir "$tmp/out"
    (
        cd "$tmp"
        "${translator[@]}" --target-version "$version" "$policy" -N -i "$fixtures" \
            -e "$workspace/examples/tests/renamings" -e "$fixtures/$edits.edits" \
            -o "$tmp/out" "$fixtures/$source.hs"
    ) > "$tmp/translator.log" 2>&1 || fail 'translation failed'
    for suffix in v h2ci; do
        [[ -s "$tmp/out/$module.$suffix" ]] || fail "missing $module.$suffix"
    done
    "${compiler[@]}" -Q "$tmp/out" '' "$tmp/out/$module.v" > "$tmp/compiler.log" 2>&1 \
        || fail 'generated module did not compile'
    cp "$fixtures/$consumer.v" "$tmp/Consumer.v"
    "${compiler[@]}" -Q "$tmp/out" '' "$tmp/Consumer.v" >> "$tmp/compiler.log" 2>&1 \
        || fail 'dictionary inference or computation failed'
    printf 'ok - %s/%s\n' "$version" "$case_name"
    rm -rf "$tmp/out"
}

require_text() {
    local file=$1 text=$2 line
    while IFS= read -r line || [[ -n "$line" ]]; do
        [[ "$line" != *"$text"* ]] || return 0
    done < "$file"
    fail "missing '$text' in ${file##*/}"
}

require_occurrences() {
    local file=$1 text=$2 expected=$3 line count=0
    while IFS= read -r line || [[ -n "$line" ]]; do
        if [[ "$line" == *"$text"* ]]; then count=$((count + 1)); fi
    done < "$file"
    [[ $count -eq $expected ]] || fail "expected $expected occurrences of '$text', got $count"
}

if [[ "$version" == 8.20 ]]; then
    base=${DERIVING_BASE:-$workspace/base}
else
    base=${DERIVING_BASE:-$workspace/examples/rocq9.0/base}
fi

check_retained() {
    local source=$1 consumer=$2 edits=$3 reports=$4 suffix head
    shift 4
    mkdir "$tmp/out"
    (
        cd "$tmp"
        "${translator[@]}" --target-version "$version" --strict -N \
            -e "$workspace/examples/base-src/edits" -e "$fixtures/$edits.edits" --iface-dir "$base" \
            --ghc -this-unit-id --ghc ghc-internal-local \
            -o "$tmp/out" "$fixtures/$source.hs"
    ) > "$tmp/translator.log" 2>&1 || fail 'retained deriving translation failed'
    for suffix in v h2ci; do
        [[ -s "$tmp/out/$source.$suffix" ]] || fail "missing $source.$suffix"
    done
    for head in "$@"; do require_occurrences "$tmp/out/$source.v" "Program Instance $head" 1; done
    "${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/out/$source.v" \
        > "$tmp/compiler.log" 2>&1 || fail 'retained deriving output did not compile'
    cp "$fixtures/$consumer.v" "$tmp/Consumer.v"
    "${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/Consumer.v" \
        >> "$tmp/compiler.log" 2>&1 || fail 'retained deriving inference or computation failed'
    require_occurrences "$tmp/compiler.log" 'Closed under the global context' "$reports"
    printf 'ok - %s/%s\n' "$version" "$case_name"
    rm -rf "$tmp/out"
}

case_name=retained-standalone-functor
check_retained DerivingKleisli KleisliConsumer kleisli 1 Functor__Kleisli
case_name=retained-inline-kinds
check_retained DerivingInlineKinds InlineKindsConsumer inline-kinds 2 Semigroup__Phantom Functor__Wrap
if [[ "$retained_only" == true ]]; then exit 0; fi

case_name=method-redefine-unused-helpers
mkdir "$tmp/out" "$tmp/ifaces"
# The manual Enum has no h2ci metadata. Generate just its interface from a
# compatible source class, without the production edits that skip Enum entirely.
(
    cd "$tmp"
    "${translator[@]}" --target-version "$version" --strict -N \
        -e "$workspace/examples/tests/renamings" -e "$fixtures/enum-aux.edits" \
        --iface-dir "$base" -o "$tmp/ifaces" "$fixtures/DerivingEnumClass.hs"
) > "$tmp/bootstrap.log" 2>&1 || fail 'Enum class interface bootstrap failed'
[[ -s "$tmp/ifaces/GHC/Enum.h2ci" ]] || fail 'missing bootstrap GHC/Enum.h2ci'
(
    cd "$tmp"
    "${translator[@]}" --target-version "$version" --strict -N \
        -e "$workspace/examples/tests/renamings" -e "$fixtures/enum-aux.edits" \
        -e "$fixtures/method-aux.edits" --iface-dir "$tmp/ifaces" --iface-dir "$base" \
        -o "$tmp/out" "$fixtures/DerivingMethodAux.hs"
) > "$tmp/translator.log" 2>&1 || fail 'method redefine translation failed'
for suffix in v h2ci; do
    [[ -s "$tmp/out/MethodAux.$suffix" ]] || fail "missing MethodAux.$suffix"
done
require_occurrences "$tmp/out/MethodAux.v" 'Program Instance Enum__E' 1
require_occurrences "$tmp/out/MethodAux.v" 'tag2con' 0
require_occurrences "$tmp/out/MethodAux.v" 'maxtag' 0
"${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/out/MethodAux.v" \
    > "$tmp/compiler.log" 2>&1 || fail 'method redefine output did not compile'
cp "$fixtures/MethodAuxConsumer.v" "$tmp/Consumer.v"
"${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/Consumer.v" \
    >> "$tmp/compiler.log" 2>&1 || fail 'method dictionary inference or computation failed'
printf 'ok - %s/%s\n' "$version" "$case_name"
rm -rf "$tmp/out" "$tmp/ifaces"

check_method_helpers() {
    local consumer=$1 helpers=$2 bootstrap_edits=$3 target=$4 suffix module
    shift 4
    mkdir "$tmp/out"
    (
        cd "$tmp"
        "${translator[@]}" --target-version "$version" --strict -N -i "$fixtures" \
            -e "$workspace/examples/tests/renamings" -e "$fixtures/retained-aux.edits" \
            ${bootstrap_edits:+-e "$fixtures/$bootstrap_edits.edits"} \
            --iface-dir "$tmp/out" -o "$tmp/out" "$fixtures/EnumAuxRuntime.hs" \
            "$fixtures/DerivingEnumClass.hs"
    ) > "$tmp/bootstrap.log" 2>&1 || fail 'helper runtime/interface bootstrap failed'
    if [[ "$bootstrap_edits" == skipped-method-aux ]]; then
        require_occurrences "$tmp/out/GHC/Enum.v" 'enumerate :' 0
    else
        require_occurrences "$tmp/out/GHC/Enum.v" 'enumerate :' 1
    fi
    # Extra edits, GHC flags, and selected providers apply only to the consumer run.
    (
        cd "$tmp"
        "${translator[@]}" --target-version "$version" --strict -N -i "$fixtures" \
            -e "$workspace/examples/tests/renamings" -e "$fixtures/retained-aux.edits" "$@" \
            --iface-dir "$tmp/out" -o "$tmp/out" "$fixtures/DerivingRetainedAux.hs"
    ) > "$tmp/translator.log" 2>&1 || fail 'method helper translation failed'
    for module in EnumAuxRuntime GHC/Enum "$target"; do
        for suffix in v h2ci; do
            [[ -s "$tmp/out/$module.$suffix" ]] || fail "missing $module.$suffix"
        done
        "${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/out/$module.v" \
            >> "$tmp/compiler.log" 2>&1 || fail "$module did not compile"
    done
    require_occurrences "$tmp/out/$target.v" 'Program Instance Enum__E' 1
    sed "s/^Require Import DerivingRetainedAux /Require Import $target /" \
        "$fixtures/$consumer.v" > "$tmp/Consumer.v"
    "${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/Consumer.v" \
        > "$tmp/consumer.log" 2>&1 || fail 'original method inference or computation failed'
    require_occurrences "$tmp/consumer.log" 'Closed under the global context' 1
    require_occurrences "$tmp/out/$target.v" 'Definition lop_zdtag2con' "$helpers"
    require_occurrences "$tmp/out/$target.v" 'Definition lop_zdmaxtag' "$helpers"
    printf 'ok - %s/%s\n' "$version" "$case_name"
    rm -rf "$tmp/out"
}

case_name=retained-original-method-helpers
check_method_helpers RetainedAuxConsumer 1 '' DerivingRetainedAux
case_name=renamed-method-skip-unused-helpers
check_method_helpers SkippedMethodAuxConsumer 0 skipped-method-aux DerivingRetainedAux \
    -e "$fixtures/skipped-method-aux.edits"
case_name=renamed-method-redefine-unused-helpers
check_method_helpers RenamedMethodAuxConsumer 0 renamed-method-aux DerivingRetainedAux \
    -e "$fixtures/renamed-method-aux.edits"
case_name=provider-only-method-skip-unused-helpers
check_method_helpers SkippedMethodAuxConsumer 0 skipped-method-aux DerivingRetainedAux
case_name=unselected-source-dependency-method-skip-unused-helpers
check_method_helpers SkippedMethodAuxConsumer 0 skipped-method-aux DerivingRetainedAux \
    --ghc -DDERIVING_SOURCE_DEPENDENCY
# convertModules sorts target names: GHC.Enum precedes ZDerivingRetainedAux.
case_name=selected-provider-retains-original-method-helpers
check_method_helpers RetainedAuxConsumer 1 skipped-method-aux ZDerivingRetainedAux \
    -e "$fixtures/selected-provider-aux.edits" --ghc -DDERIVING_SOURCE_DEPENDENCY \
    "$fixtures/DerivingEnumClass.hs"
case_name=selected-provider-skips-unused-method-helpers
check_method_helpers SkippedMethodAuxConsumer 0 '' ZDerivingRetainedAux \
    -e "$fixtures/selected-provider-aux.edits" -e "$fixtures/skipped-method-aux.edits" \
    --ghc -DDERIVING_SOURCE_DEPENDENCY "$fixtures/DerivingEnumClass.hs"

case_name=multi-module-forward-interface
mkdir "$tmp/out" "$tmp/ifaces" "$tmp/control"
# Neither module derives instances; the client sorts before its provider.
(
    cd "$tmp"
    "${translator[@]}" --target-version "$version" --strict -N -i "$fixtures" \
        -e "$workspace/examples/tests/renamings" \
        -o "$tmp/ifaces" "$fixtures/DerivingZClass.hs"
) > "$tmp/bootstrap.log" 2>&1 || fail 'provider interface bootstrap failed'
for suffix in v h2ci; do
    [[ -s "$tmp/ifaces/DerivingZClass.$suffix" ]] || fail "missing bootstrap DerivingZClass.$suffix"
done
"${compiler[@]}" -Q "$tmp/ifaces" '' "$tmp/ifaces/DerivingZClass.v" \
    > "$tmp/compiler.log" 2>&1 || fail 'bootstrap provider did not compile'
(
    cd "$tmp"
    "${translator[@]}" --target-version "$version" --strict -N -i "$fixtures" \
        -e "$workspace/examples/tests/renamings" --iface-dir "$tmp/ifaces" \
        -o "$tmp/control" "$fixtures/DerivingAClient.hs"
) > "$tmp/control.log" 2>&1 || fail 'single-client control translation failed'
for suffix in v h2ci; do
    [[ -s "$tmp/control/DerivingAClient.$suffix" ]] || fail "missing control DerivingAClient.$suffix"
done
"${compiler[@]}" -Q "$tmp/ifaces" '' -Q "$tmp/control" '' "$tmp/control/DerivingAClient.v" \
    >> "$tmp/compiler.log" 2>&1 || fail 'single-client control did not compile'
cp "$fixtures/ForwardInterfaceConsumer.v" "$tmp/Consumer.v"
"${compiler[@]}" -Q "$tmp/ifaces" '' -Q "$tmp/control" '' "$tmp/Consumer.v" \
    >> "$tmp/compiler.log" 2>&1 || fail 'single-client dictionary inference or computation failed'
(
    cd "$tmp"
    "${translator[@]}" --target-version "$version" --strict -N -i "$fixtures" \
        -e "$workspace/examples/tests/renamings" --iface-dir "$tmp/ifaces" \
        -o "$tmp/out" "$fixtures/DerivingAClient.hs" "$fixtures/DerivingZClass.hs"
) > "$tmp/translator.log" 2>&1 || fail 'multi-module forward-interface translation failed'
for module in DerivingZClass DerivingAClient; do
    for suffix in v h2ci; do
        [[ -s "$tmp/out/$module.$suffix" ]] || fail "missing $module.$suffix"
    done
    "${compiler[@]}" -Q "$tmp/out" '' "$tmp/out/$module.v" \
        >> "$tmp/compiler.log" 2>&1 || fail "$module did not compile"
done
"${compiler[@]}" -Q "$tmp/out" '' "$tmp/Consumer.v" \
    >> "$tmp/compiler.log" 2>&1 || fail 'multi-module dictionary inference or computation failed'
printf 'ok - %s/%s\n' "$version" "$case_name"
rm -rf "$tmp/out" "$tmp/ifaces" "$tmp/control"

case_name=recovery
check_recovery recovery DerivingRecovery RecoveryConsumer
case_name=renamed-instance-skip
check_recovery renamed Recovered RenamedConsumer
case_name=renamed-class-skip
check_recovery renamed-class Recovered RenamedConsumer
case_name=renamed-module-skip
check_recovery module-skip DerivingModuleSkip ModuleConsumer DerivingModuleSkip
case_name=inline-recovery
check_recovery inline DerivingInline InlineConsumer DerivingInline
case_name=skipped-auxiliary-bindings
check_recovery aux DerivingAux AuxConsumer DerivingAux

case_name=whole-instance-redefine-unused-helpers
mkdir "$tmp/out"
(
    cd "$tmp"
    "${translator[@]}" --target-version "$version" --strict -N \
        -e "$workspace/examples/tests/renamings" -e "$fixtures/redefined-aux.edits" \
        --iface-dir "$base" -o "$tmp/out" "$fixtures/DerivingRedefinedAux.hs"
) > "$tmp/translator.log" 2>&1 || fail 'whole-instance redefine translation failed'
for suffix in v h2ci; do
    [[ -s "$tmp/out/DerivingRedefinedAux.$suffix" ]] || fail "missing DerivingRedefinedAux.$suffix"
done
"${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/out/DerivingRedefinedAux.v" \
    > "$tmp/compiler.log" 2>&1 || fail 'whole-instance redefine output did not compile'
cp "$fixtures/RedefinedAuxConsumer.v" "$tmp/Consumer.v"
"${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/Consumer.v" \
    >> "$tmp/compiler.log" 2>&1 || fail 'redefined dictionary inference or computation failed'
printf 'ok - %s/%s\n' "$version" "$case_name"
rm -rf "$tmp/out"

case_name=inline-standalone-explicit-method-skips
check_recovery methods DerivingMethods MethodsConsumer DerivingMethods

for policy in default strict; do
    case_name="$policy-failure"
    option=
    if [[ "$policy" == strict ]]; then option=--strict; fi
    mkdir "$tmp/out"
    if (
        cd "$tmp"
        "${translator[@]}" --target-version "$version" ${option:+"$option"} -N \
            -e "$workspace/examples/tests/renamings" -e "$fixtures/unskipped.edits" \
            -o "$tmp/out" "$fixtures/DerivingRecovery.hs"
    ) > "$tmp/translator.log" 2>&1; then
        fail 'unskipped derivation failure exited zero'
    fi
    require_text "$tmp/translator.log" 'deriving Rejected Wrapped failed'
    require_text "$tmp/translator.log" 'DerivingRecovery.hs:17:1'
    require_text "$tmp/translator.log" 'not a stock derivable class'
    [[ ! -e "$tmp/out/DerivingRecovery.v" ]] || fail 'strict failure produced Gallina'
    printf 'ok - %s/%s\n' "$version" "$case_name"
    rm -rf "$tmp/out"
done

case_name=permissive-partial-success
check_recovery unskipped DerivingRecovery RecoveryConsumer DerivingRecovery --permissive
require_text "$tmp/translator.log" 'hs-to-rocq: warning:'
require_text "$tmp/translator.log" 'deriving Rejected Wrapped failed'

case_name=permissive-inline-failure
check_recovery inline-failure DerivingInlineFailure InlineFailureConsumer DerivingInlineFailure --permissive
require_text "$tmp/translator.log" 'hs-to-rocq: warning:'
require_text "$tmp/translator.log" 'Missing Bool'
require_text "$tmp/translator.log" 'deriving Missing Failed failed'

case_name=inline-instance-skip
check_recovery inline-instance-skip DerivingInlineFailure InlineFailureConsumer DerivingInlineFailure

case_name=imported-stock-traversable
mkdir "$tmp/out"
(
    cd "$tmp"
    "${translator[@]}" --target-version "$version" --strict -N \
        -e "$workspace/examples/base-src/edits" -e "$fixtures/stock.edits" \
        --iface-dir "$base" --iface-dir "$tmp/out" -i "$fixtures" \
        -o "$tmp/out" "$fixtures/DerivingForeign.hs" "$fixtures/DerivingStock.hs"
) > "$tmp/translator.log" 2>&1 || fail 'stock traversal translation failed'
for module in DerivingForeign DerivingStock; do
    for suffix in v h2ci; do
        [[ -s "$tmp/out/$module.$suffix" ]] || fail "missing $module.$suffix"
    done
    "${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/out/$module.v" \
        >> "$tmp/compiler.log" 2>&1 || fail "$module did not compile"
done
cp "$fixtures/StockConsumer.v" "$tmp/Consumer.v"
"${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/Consumer.v" \
    >> "$tmp/compiler.log" 2>&1 || fail 'stock dictionary inference or computation failed'
printf 'ok - %s/%s\n' "$version" "$case_name"

bridge_translate() {
    local policy=$1
    shift
    rm -rf "$tmp/out"
    (
        cd "$tmp"
        "${translator[@]}" --target-version "$version" "$policy" -N \
            -e "$workspace/examples/base-src/edits" -e "$fixtures/$bridge_edits.edits" \
            --iface-dir "$base" --iface-dir "$workspace/examples/base-src/manual" \
            --ghc -this-unit-id --ghc ghc-internal-local \
            -o "$tmp/out" "$@" "$fixtures/$bridge_source.hs"
    ) > "$tmp/translator.log" 2>&1
}

bridge_compile() {
    local suffix
    for suffix in v h2ci; do
        [[ -s "$tmp/out/Data/$bridge_class.$suffix" ]] || fail "missing Data/$bridge_class.$suffix"
    done
    require_occurrences "$tmp/out/Data/$bridge_class.v" "Program Instance ${bridge_class}__$bridge_head" 1
    require_occurrences "$tmp/out/Data/$bridge_class.v" "Program Instance ${bridge_class}__Wrap" 1
    "${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/out/Data/$bridge_class.v" \
        > "$tmp/compiler.log" 2>&1 || fail 'source-class output did not compile'
    cp "$fixtures/$bridge_consumer.v" "$tmp/Consumer.v"
    "${compiler[@]}" -Q "$base" '' -Q "$tmp/out" '' "$tmp/Consumer.v" \
        >> "$tmp/compiler.log" 2>&1 || fail 'source-class dictionary inference or computation failed'
    require_occurrences "$tmp/compiler.log" 'Closed under the global context' 1
}

case_name=source-class-stock-bridge
bridge_source=BridgeTraversable
bridge_class=Traversable
bridge_head=Identity
bridge_consumer=BridgeConsumer
bridge_edits=bridge
bridge_translate --strict || fail 'source-class stock deriving failed'
bridge_compile
printf 'ok - %s/%s\n' "$version" "$case_name"

case_name=source-class-explicit-stock-bridge
bridge_translate --strict --ghc -DBRIDGE_EXPLICIT_STOCK || fail 'explicit stock source-class deriving failed'
bridge_compile
printf 'ok - %s/%s\n' "$version" "$case_name"

for variant in EXTRA_METHOD METHOD_TYPE MISSING_DEFAULT USER_CLASS BAD_FIELD HIDDEN_CONSTRUCTOR MISSING_SUPERCLASS; do
    case_name="bridge-reject-$variant"
    if bridge_translate --strict --ghc "-DBRIDGE_$variant"; then
        fail 'unsupported source-class derivation exited zero'
    fi
    [[ ! -e "$tmp/out/Data/Traversable.v" ]] || fail 'failed source-class derivation produced Gallina'
    require_text "$tmp/translator.log" 'deriving Traversable'
    require_text "$tmp/translator.log" 'BridgeTraversable.hs:'
    case "$variant" in
        EXTRA_METHOD|METHOD_TYPE|MISSING_DEFAULT) require_text "$tmp/translator.log" 'incompatible with' ;;
        USER_CLASS) require_text "$tmp/translator.log" 'not a stock derivable class' ;;
        BAD_FIELD) require_text "$tmp/translator.log" 'must not contain function types' ;;
        HIDDEN_CONSTRUCTOR) require_text "$tmp/translator.log" 'data constructors' ;;
        MISSING_SUPERCLASS) require_text "$tmp/translator.log" 'Functor Bare' ;;
    esac
    printf 'ok - %s/%s\n' "$version" "$case_name"
done

case_name=bridge-permissive-synthesized-instance-removal
bridge_translate --permissive --ghc -DBRIDGE_MISSING_SUPERCLASS || fail 'permissive source-class recovery failed'
require_text "$tmp/translator.log" 'hs-to-rocq: warning:'
require_text "$tmp/translator.log" 'deriving Traversable Bare failed'
require_text "$tmp/translator.log" 'Functor Bare'
require_occurrences "$tmp/out/Data/Traversable.v" 'Program Instance Traversable__Bare' 0
bridge_compile
printf 'ok - %s/%s\n' "$version" "$case_name"

case_name=source-foldable-stock-bridge
bridge_source=BridgeFoldable
bridge_class=Foldable
bridge_head=Down
bridge_consumer=BridgeFoldableConsumer
bridge_edits=bridge-foldable
bridge_translate --strict || fail 'source Foldable stock deriving failed'
require_occurrences "$tmp/out/Data/Foldable.v" 'Program Instance Foldable__Solo' 1
bridge_compile
printf 'ok - %s/%s\n' "$version" "$case_name"
