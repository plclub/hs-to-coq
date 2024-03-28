HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run -v0 exe:hs-to-coq --
endif
SHELL = bash

SRC=build-systems-ala-carte/src

OUT=out

RENAMED=renamed

HS_SPEC=hs-spec

# not all of these need to be handwritten. eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \



# Generated modules
#
# Build/Multi \ # Gives below error
# COQC Build/Multi.v
# File "./Build/Multi.v", line 35, characters 22-42:
# Error:
# In environment
# k : Type
# v : Type
# H : Base.Eq_ k
# The term "Base.Applicative" has type
#  "forall f : Type -> Type, Base.Functor f -> Type"
# while it is expected to have type "(Type -> Type) -> Type"
# (universe inconsistency).# generated directly from GHC/libraries/$(SRC)
#
# Build/Utilities,
# abandoned due to requiring algebraic-graphs dependency, which would add 2 more other deps
# Also, hoping that the utils are mostly for the tests of correctness in tests/, and letting us still
# translate the rest of the library's structures.
#
# Build/SelfTracking # Gives below error, primary issue is functions are partial here.
# File "./Build/SelfTracking.v", line 40, characters 0-353:
# Error: Unable to satisfy the following constraints:
# UNDEFINED EVARS:
#  ?X23==[f k v t H fetch key arg_0__ y |- Err.Default v] (parameter H of
#          @Err.error) {?H}
#  ?X28==[f k v t H fetch key
#          (extract:=fun arg_0__ : Value v t =>
#                    match arg_0__ with
#                    | Mk_Value v => v
#                    | ValueTask y =>
#                        Err.error (Base.hs_string__ "Inconsistent fetch")
#                    end) |- Base.Functor f] (parameter H of
#          @Functor.op_zlzdzg__) {?H0}
# TYPECLASSES:?X23 ?X28
#
# Build/SelfTracking/Typed # Has following extensions
# {-# LANGUAGE ConstraintKinds, GADTs, RankNTypes, ScopedTypeVariables #-}
# also then gives the following error in the Coq generated code for key:
# Error: Cannot infer the type of a in environment:
# Inductive Key k v s a : Type :=
#   | Script : k -> Key k v s s
#   | Value : k -> Key k v s v.
MODULES = \
   Build/Task \
   Build/Store \
   Build/Trace \
   Build/Task/Monad \



# Generated modules
# generated directly from GHC/libraries/$(SRC)/tests
TEST_MODULES = \

# generated from drop-in/
DROPIN =

# also generated from drop-in/
SPECIAL_MODULES =


VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_GEN_TEST = $(addprefix $(OUT)/,$(addsuffix .v,$(TEST_MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL = $(addprefix $(OUT)/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN = $(addprefix $(OUT)/,$(addsuffix .v,$(DROPIN)))

VFILES = $(VFILES_GEN_TEST) $(VFILES_GEN) $(VFILES_MAN) $(VFILES_SPECIAL) $(VFILES_DROPIN)

all: vfiles coq

vfiles: $(OUT)/edits  $(OUT)/README.md $(OUT)/_CoqProject $(VFILES)

$(OUT)/_CoqProject : Makefile
	mkdir -p $(OUT)
	> $@
	echo '-Q . ""' >> $@
	echo '-Q ../../../base ""' >> $@
	echo '-Q ../../transformers/lib ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@
	echo $(addsuffix .v,$(DROPIN)) >> $@

$(OUT)/Makefile: $(OUT)/_CoqProject $(VFILES)
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

$(OUT)/edits: $(OUT)/README.md
	ln -fs ../edits $(OUT)/edits

$(OUT)/README.md:
	mkdir -p $(OUT)
	> $@
	echo 'This directory contains a Coq’ified version of the Haskell $(SRC) library' >> $@
	echo 'Do not edit files here! Instead, look in `examples/$(SRC)`.' >> $@


coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)

  # --dependency-dir deps/ \
  #
  #
HS_TO_COQ_OPTS := \
  -e ../../base/edits \
  -e edits \
  --iface-dir ../../base \
  -e ../transformers/edits  --iface-dir ../transformers/lib   \
  --iface-dir $(OUT) \
  -N \
  -i $(SRC) \
  -i $(SRC)/tests \
  -i $(SRC)/dist-install/build \
  -I $(SRC)/include \
  -o $(OUT) \


.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) $(wildcard module-edits/$$*/flags) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_OPTS) \
	             $(addprefix `cat , $(addsuffix ` , $(wildcard module-edits/$*/flags))) \
	             $(wildcard $(SRC)/$*.hs) $(wildcard $(SRC)/tests/$*.hs)
	test -e $@

$(VFILES_DROPIN): $(OUT)/%.v : module-edits/%/edits edits module-edits/%/preamble.v drop-in/%.hs
	$(HS_TO_COQ) -e module-edits/$*/edits \
	             $(HS_TO_COQ_OPTS) \
	             drop-in/$*.hs

.SECONDEXPANSION:
$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/

%.h2ci: %.v
	test -e $@

clean:
	rm -rf $(OUT) $(RENAMED) $(HS_SPEC)
	rm -f counts.pdf *.aux *.log

todo:
	grep -a Axiom $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	grep -a Admitted $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	grep -a errorWithout $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	grep -a Parameter $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v

counts.pdf: counts.fig
	pdflatex counts

counts.fig: Makefile $(VFILES)
	(echo "\\begin{tabular}{lllll}"; \
    echo "Module & Defs & Class & Insts & Skipped\\\\"; \
    echo "\\multicolumn{4}{l}{\emph{Generated modules}}\\\\"; \
	 for i in  $(MODULES) $(DROPIN) ; \
       do (echo $$i; echo "&"; grep -a "Definition" $(OUT)/$$i.v | wc -l ; echo "&"; \
           grep -a "Class" $(OUT)/$$i.v | wc -l;  echo "&"; \
           grep -a "Instance" $(OUT)/$$i.v | wc -l;  echo "&"; \
           grep -a "skip" module-edits/$$i/edits | wc -l;  echo "\\\\" ) done; \
    echo "\\\\"; \
    echo "\\multicolumn{4}{l}{\emph{Manually adapted modules}}\\\\"; \
	 for i in  $(HANDMOD) ; \
       do (echo $$i; echo "&"; grep -a "Definition" $(OUT)/$$i.v | wc -l ;  echo "&"; \
           grep -a "Class" $(OUT)/$$i.v | wc -l ;  echo "&"; \
           grep -a "Instance" $(OUT)/$$i.v| wc -l; echo "\\\\" ) done; \
	 echo "\\end{tabular}") > counts.fig
