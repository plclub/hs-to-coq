# Makefile for generating Rocq 9.0 base library from Haskell sources.
# Reuses edits, module-edits, and manual files from examples/base-src/,
# with --target-version 9.0 for automatic Coq.* → Stdlib.* rewriting.

include ../../../common.mk

# Base-src directory with all the source material
BASE_SRC=../../base-src

# Output directory (checked-in convenience copies)
OUT=../base

# Handwritten modules (same as base-src)
HANDMOD = \
  HsToRocq/Wf \
  HsToRocq/Skip \
  HsToRocq/DeferredFix \
  HsToRocq/DeferredFixImpl \
  HsToRocq/Unpeel \
  GHC/Num \
  GHC/Char \
  GHC/Real \
  GHC/Enum \
  Data/Bits \
  Data/Functor/Classes \
  GHC/Prim \
  GHC/Types \
  GHC/Tuple \
  Data/Type/Equality \
  HsToRocq/Err \
  GHC/Err \
  HsToRocq/Nat \
  GHC/Unicode \
  Prelude

EARLY_GHC_INTERNAL_MODULES = \
  Data/Functor/Identity \
  Data/Traversable

EARLY_BASE_MODULES =

GHC_INTERNAL_MODULES = \
  Data/Maybe \
  Data/List \
  Data/OldList \
  Data/Bool \
  Data/Tuple \
  Data/Void \
  Data/Function \
  Data/Ord \
  Data/Functor \
  Data/Either \
  Data/Proxy \
  Control/Monad \
  Data/Monoid \
  Data/Functor/Utils \
  Control/Monad/Fail \
  Data/Foldable \
  Data/Functor/Const \
  Control/Category \
  Control/Arrow

GHC_INTERNAL_GHC_MODULES = \
  GHC/List

BASE_MODULES = \
  Control/Applicative \
  Data/Bifunctor \
  Data/List/NonEmpty \
  Data/Semigroup \
  Data/Functor/Compose \
  Data/Functor/Product \
  Data/Functor/Sum \
  Data/Bifoldable \
  Data/Bitraversable \
  Control/Monad/Zip

MODULES = $(GHC_INTERNAL_MODULES) $(GHC_INTERNAL_GHC_MODULES) $(BASE_MODULES)
EARLY_MODULES = $(EARLY_GHC_INTERNAL_MODULES) $(EARLY_BASE_MODULES)
ALL_MODULES = $(EARLY_MODULES) $(MODULES)

RENAMED = \
  Data/SemigroupInternal

DROPIN =

SPECIAL_MODULES = \
  GHC/Base

VFILES_GHC_INTERNAL     = $(addprefix $(OUT)/,$(addsuffix .v,$(GHC_INTERNAL_MODULES)))
VFILES_GHC_INTERNAL_GHC = $(addprefix $(OUT)/,$(addsuffix .v,$(GHC_INTERNAL_GHC_MODULES)))
VFILES_BASE_GEN  = $(addprefix $(OUT)/,$(addsuffix .v,$(BASE_MODULES)))
VFILES_EARLY_GHC_INTERNAL = $(addprefix $(OUT)/,$(addsuffix .v,$(EARLY_GHC_INTERNAL_MODULES)))
VFILES_EARLY_BASE = $(addprefix $(OUT)/,$(addsuffix .v,$(EARLY_BASE_MODULES)))
VFILES_GEN       = $(VFILES_GHC_INTERNAL) $(VFILES_GHC_INTERNAL_GHC) $(VFILES_BASE_GEN) $(VFILES_EARLY_GHC_INTERNAL) $(VFILES_EARLY_BASE)
VFILES_RENAMED   = $(addprefix $(OUT)/,$(addsuffix .v,$(RENAMED)))
VFILES_MAN       = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL   = $(addprefix $(OUT)/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN    = $(addprefix $(OUT)/,$(addsuffix .v,$(DROPIN)))

VFILES   = $(VFILES_MAN) $(VFILES_GEN) $(VFILES_SPECIAL) $(VFILES_DROPIN) $(VFILES_RENAMED)

# Extra flag for Rocq 9.0 target
TARGET_VERSION = --target-version 9.0

all: vfiles

vfiles: deps $(OUT)/_CoqProject $(VFILES)

deps:
	mkdir -p deps

$(OUT)/_CoqProject : Makefile
	mkdir -p $(OUT)
	> $@
	echo '-Q . ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) $(addsuffix .v,$(EARLY_MODULES)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(RENAMED)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@
	echo $(addsuffix .v,$(DROPIN)) >> $@

# All generated modules depend on GHC/Base and manual modules.
# Additional inter-module deps for fresh builds (before deps/*.mk exists).
$(VFILES_GEN) $(VFILES_RENAMED): | $(OUT)/GHC/Base.v $(VFILES_MAN)
$(OUT)/Data/Monoid.v: | $(OUT)/Control/Monad/Fail.v
$(OUT)/Data/Foldable.v: | $(OUT)/Data/Functor/Utils.v $(OUT)/Data/Monoid.v
$(OUT)/Data/Functor/Identity.v: | $(OUT)/Data/Foldable.v
$(OUT)/Data/Traversable.v: | $(OUT)/Data/Functor/Identity.v $(OUT)/Data/Foldable.v
$(OUT)/Control/Applicative.v: | $(OUT)/Data/Traversable.v $(OUT)/Data/Functor/Const.v
$(OUT)/Data/List/NonEmpty.v: | $(OUT)/Data/Foldable.v $(OUT)/Data/Traversable.v
$(OUT)/Data/Semigroup.v: | $(OUT)/Data/List/NonEmpty.v
$(OUT)/Data/Functor/Compose.v: | $(OUT)/Data/Foldable.v $(OUT)/Data/Traversable.v
$(OUT)/Data/Functor/Product.v: | $(OUT)/Data/Foldable.v $(OUT)/Data/Traversable.v
$(OUT)/Data/Functor/Sum.v: | $(OUT)/Data/Foldable.v $(OUT)/Data/Traversable.v
$(OUT)/Data/Bifoldable.v: | $(OUT)/Data/Foldable.v
$(OUT)/Data/Bitraversable.v: | $(OUT)/Data/Bifoldable.v $(OUT)/Data/Traversable.v
$(OUT)/Data/Bifunctor.v: | $(OUT)/Data/Bifoldable.v $(OUT)/Data/Bitraversable.v
$(OUT)/Control/Monad/Zip.v: | $(OUT)/Control/Monad.v
$(OUT)/Control/Arrow.v: | $(OUT)/Control/Category.v
$(OUT)/Data/Functor/Product.v: | $(OUT)/Control/Monad/Zip.v
$(OUT)/Data/OldList.v: | $(OUT)/Data/Foldable.v
$(OUT)/Data/List.v: | $(OUT)/Data/OldList.v
$(OUT)/Data/SemigroupInternal.v: | $(OUT)/Data/Foldable.v

# Common options shared by all translation rules
HS_TO_ROCQ_OPTS_COMMON := \
    $(TARGET_VERSION) \
    -e $(BASE_SRC)/edits \
    -N \
    -I $(BASE_SRC)/gen-files \
    -I $(BASE_SRC)/ghc-internal/include \
    --iface-dir $(OUT) \
    --dependency-dir deps \
    -o $(OUT)

HS_TO_ROCQ_OPTS_INTERNAL := \
    $(HS_TO_ROCQ_OPTS_COMMON) \
    --ghc -this-unit-id --ghc ghc-internal-local

HS_TO_ROCQ_OPTS_GHC_BASE := \
    $(HS_TO_ROCQ_OPTS_COMMON) \
    -i $(BASE_SRC)/gen-files \
    -i $(BASE_SRC)/ghc-internal/src \
    --ghc -this-unit-id --ghc ghc-internal

HS_TO_ROCQ_OPTS_BASE := \
    $(HS_TO_ROCQ_OPTS_COMMON) \
    -i $(BASE_SRC)/base/src \
    --ghc -this-unit-id --ghc base


-include deps/*.mk

.SECONDEXPANSION:

# Rule for Data/* and Control/* modules from ghc-internal
$(VFILES_GHC_INTERNAL) $(VFILES_EARLY_GHC_INTERNAL): $(OUT)/%.v : $$(wildcard $(BASE_SRC)/module-edits/$$*/preamble.v) $$(wildcard $(BASE_SRC)/module-edits/$$*/midamble.v) $$(wildcard $(BASE_SRC)/module-edits/$$*/edits) $(BASE_SRC)/edits
	$(HS_TO_ROCQ) $(addprefix -e , $(wildcard $(BASE_SRC)/module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard $(BASE_SRC)/module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard $(BASE_SRC)/module-edits/$*/midamble.v)) \
		     $(HS_TO_ROCQ_OPTS_INTERNAL) \
		     $(BASE_SRC)/ghc-internal/src/GHC/Internal/$*.hs
	test -e $@

# Rule for GHC/* modules from ghc-internal
$(VFILES_GHC_INTERNAL_GHC): $(OUT)/GHC/%.v : $$(wildcard $(BASE_SRC)/module-edits/GHC/$$*/preamble.v) $$(wildcard $(BASE_SRC)/module-edits/GHC/$$*/midamble.v) $$(wildcard $(BASE_SRC)/module-edits/GHC/$$*/edits) $(BASE_SRC)/edits
	$(HS_TO_ROCQ) $(addprefix -e , $(wildcard $(BASE_SRC)/module-edits/GHC/$*/edits)) \
	             $(addprefix -p , $(wildcard $(BASE_SRC)/module-edits/GHC/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard $(BASE_SRC)/module-edits/GHC/$*/midamble.v)) \
		     $(HS_TO_ROCQ_OPTS_INTERNAL) \
		     $(BASE_SRC)/ghc-internal/src/GHC/Internal/$*.hs
	test -e $@

# Rule for modules still in base/src
$(VFILES_BASE_GEN) $(VFILES_EARLY_BASE): $(OUT)/%.v : $$(wildcard $(BASE_SRC)/module-edits/$$*/preamble.v) $$(wildcard $(BASE_SRC)/module-edits/$$*/midamble.v) $$(wildcard $(BASE_SRC)/module-edits/$$*/edits) $(BASE_SRC)/edits
	$(HS_TO_ROCQ) $(addprefix -e , $(wildcard $(BASE_SRC)/module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard $(BASE_SRC)/module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard $(BASE_SRC)/module-edits/$*/midamble.v)) \
		     $(HS_TO_ROCQ_OPTS_BASE) \
		     $(BASE_SRC)/base/src/$*.hs
	test -e $@

# Renamed module: Data/Semigroup/Internal → Data/SemigroupInternal
$(OUT)/Data/SemigroupInternal.v : $(wildcard $(BASE_SRC)/module-edits/Data/Semigroup/Internal/preamble.v) $(wildcard $(BASE_SRC)/module-edits/Data/Semigroup/Internal/midamble.v) $(wildcard $(BASE_SRC)/module-edits/Data/Semigroup/Internal/edits) $(BASE_SRC)/edits
	$(HS_TO_ROCQ) $(addprefix -e , $(wildcard $(BASE_SRC)/module-edits/Data/Semigroup/Internal/edits)) \
	             $(addprefix -p , $(wildcard $(BASE_SRC)/module-edits/Data/Semigroup/Internal/preamble.v)) \
	             $(addprefix --midamble , $(wildcard $(BASE_SRC)/module-edits/Data/Semigroup/Internal/midamble.v)) \
		     $(HS_TO_ROCQ_OPTS_INTERNAL) \
		     $(BASE_SRC)/ghc-internal/src/GHC/Internal/Data/Semigroup/Internal.hs
	test -e $(OUT)/Data/SemigroupInternal.v

# GHC/Base: merged from multiple source files
GHC_BASE_PRE = $(wildcard $(BASE_SRC)/module-edits/GHC/Base/preamble.v $(BASE_SRC)/module-edits/GHC/Maybe/preamble.v)
GHC_BASE_MID = $(wildcard $(BASE_SRC)/module-edits/GHC/Base/midamble.v $(BASE_SRC)/module-edits/GHC/Maybe/midamble.v)
GHC_BASE_EDITS = $(wildcard $(BASE_SRC)/module-edits/GHC/Base/edits $(BASE_SRC)/module-edits/GHC/Maybe/edits)

$(OUT)/GHC/Base.v: $(GHC_BASE_PRE) $(GHC_BASE_MID) $(GHC_BASE_EDITS) $(BASE_SRC)/edits
	cat /dev/null $(GHC_BASE_PRE) > Base_preamble.v
	cat /dev/null $(GHC_BASE_MID) > Base_midamble.v
	$(HS_TO_ROCQ) -p Base_preamble.v \
	             --midamble Base_midamble.v \
	             $(addprefix -e , $(GHC_BASE_EDITS)) \
	             $(HS_TO_ROCQ_OPTS_GHC_BASE) \
	             $(BASE_SRC)/ghc-internal/src/GHC/Internal/Stack/Types.hs \
	             $(BASE_SRC)/gen-files/GHC/Internal/Exception/Context.hs \
	             $(BASE_SRC)/ghc-internal/src/GHC/Internal/Base.hs $(BASE_SRC)/ghc-internal/src/GHC/Internal/Maybe.hs
	test -e $(OUT)/GHC/Base.v
	rm -f Base_preamble.v Base_midamble.v

# Handwritten modules: copy from base-src/manual/ rewriting Coq.* paths to
# their Rocq-9 equivalents. Order matters:
#   1. Rocq 9 moved WfExtensionality out of Program/Wf.v into a sibling file,
#      so rewrite Coq.Program.Wf.WfExtensionality → Stdlib.Program.WfExtensionality.WfExtensionality
#      (the inner module still exists in the new file) and inject an extra
#      `Require Import Stdlib.Program.WfExtensionality.` whenever we import
#      Coq.Program.Wf.
#   2. Coq.Init.* modules are Corelib re-exports; fully-qualified references
#      must use Corelib, not Stdlib.
#   3. Everything else: Coq. → Stdlib.
# Also copy .h2ci files if they exist (needed for cross-module type info).
$(VFILES_MAN): $(OUT)/%.v : $(BASE_SRC)/manual/%.v
	mkdir -p $(dir $@)
	sed \
	    -e 's#Coq\.Program\.Wf\.WfExtensionality#Stdlib.Program.WfExtensionality.WfExtensionality#g' \
	    -e 's#^Require Import Coq\.Program\.Wf\.$$#Require Import Coq.Program.Wf. Require Import Stdlib.Program.WfExtensionality.#' \
	    -e 's#Coq\.Init\.#Corelib.Init.#g' \
	    -e 's#Coq\.#Stdlib.#g' \
	    $< > $@
	@if [ -e $(BASE_SRC)/manual/$*.h2ci ]; then cp $(BASE_SRC)/manual/$*.h2ci $(OUT)/$*.h2ci; fi

%.h2ci: %.v
	@true

clean:
	rm -rf $(OUT) deps

.PHONY: all vfiles clean
