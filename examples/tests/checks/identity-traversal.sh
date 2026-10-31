#!/usr/bin/env bash
# Compile the same public-base regression in an isolated, fresh output directory.
# Usage: bash identity-traversal.sh --target-version 8.20|9.0 [--base PATH]
#          [-- COMPILER ARG ...]
# Use the matching compiler environment, as with the other compiler checks.
set -euo pipefail

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
target=8.20
base=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --target-version|--base)
      if [ "$#" -lt 2 ]; then
        printf 'Missing value for %s\n' "$1" >&2; exit 2
      fi
      case "$1" in
        --target-version) target=$2 ;;
        --base) base=$2 ;;
      esac
      shift 2 ;;
    --) shift; break ;;
    *) printf 'Unknown option: %s\n' "$1" >&2; exit 2 ;;
  esac
done
case "$target" in
  8.20)
    base=${base:-$root/base}
    read -r -a compiler <<< "${COQC:-coqc}" ;;
  9.0)
    base=${base:-$root/examples/rocq9.0/base}
    read -r -a compiler <<< "${COQC:-rocq c -w +deprecated-dirpath-Coq}" ;;
  *) printf 'Unsupported target version: %s\n' "$target" >&2; exit 2 ;;
esac
if [ "$#" -gt 0 ]; then compiler=("$@"); fi

base=$(cd "$base" && pwd)
out=$(mktemp -d "${TMPDIR:-/tmp}/identity-traversal-$target.XXXXXX")
trap 'rm -rf "$out"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
cp "$root/examples/base-tests/IdentityTraversal.v" "$out/IdentityTraversal.v"
status=0
"${compiler[@]}" -Q "$base" '' "$out/IdentityTraversal.v" > "$out/compiler.log" 2>&1 || status=$?
reports=0
axioms=0
while IFS= read -r line || [[ -n "$line" ]]; do
  printf '%s\n' "$line"
  case "$line" in
    *'Closed under the global context'*) reports=$((reports + 1)) ;;
    *'Axioms:'*) axioms=1 ;;
  esac
done < "$out/compiler.log"
[[ $status -eq 0 ]] || exit "$status"
if [[ $reports -ne 14 || $axioms -ne 0 ]]; then
  printf 'IdentityTraversal: expected fourteen closed assumption reports\n' >&2
  exit 1
fi
printf 'IdentityTraversal (%s): PASS (fourteen closed assumption reports)\n' "$target"
