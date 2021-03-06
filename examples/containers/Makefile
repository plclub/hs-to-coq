include ../../common.mk

ifeq (,$(wildcard containers))
$(error Please run git submodule update --init --recursive)
endif

OUT=lib

HS_SPEC=hs-spec

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \
  Utils/Containers/Internal/PtrEquality \
  CTZ \
  BitTerminationProofs \
  Test/QuickCheck/Property \
  Test/QuickCheck/Arbitrary \
  Test/QuickCheck/Gen \
  IntWord \

#  Data/SequenceManual \

# Generated modules
# generated directly from GHC/libraries/containers
MODULES = \
  Data/Set/Internal \
  Utils/Containers/Internal/BitUtil \
  Data/IntSet/Internal \
  Data/IntSet/InternalWord \
  Data/IntMap/Internal \
  Data/Map/Internal \
  IntSetValidity \

HS_SPEC_MODULES = \
  IntSetProperties

# Non-standard file names
SRC_FILE_IntSetProperties = containers/tests/intset-properties.hs
SRC_FILE_Data/IntSet/InternalWord = containers/Data/IntSet/Internal.hs

# Generated modules
# generated directly from GHC/libraries/containers/tests
TEST_MODULES = \

# generated from drop-in/
DROPIN =

# also generated from drop-in/
SPECIAL_MODULES =


VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_HS_SPEC_GEN = $(addprefix $(HS_SPEC)/,$(addsuffix .v,$(HS_SPEC_MODULES)))
VFILES_GEN_TEST = $(addprefix $(OUT)/,$(addsuffix .v,$(TEST_MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL = $(addprefix $(OUT)/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN = $(addprefix $(OUT)/,$(addsuffix .v,$(DROPIN)))

VFILES = $(VFILES_GEN_TEST) $(VFILES_GEN) $(VFILES_HS_SPEC_GEN) $(VFILES_MAN) $(VFILES_SPECIAL) $(VFILES_DROPIN)

all: vfiles coq

vfiles: $(OUT)/edits  $(HS_SPEC)/README.md $(OUT)/README.md $(OUT)/_CoqProject $(VFILES)

$(OUT)/_CoqProject : Makefile $(OUT)/README.md
	> $@
	echo '-Q . ""' >> $@
	echo '-Q ../../../base ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@
	echo $(addsuffix .v,$(DROPIN)) >> $@

$(OUT)/Makefile: $(OUT)/_CoqProject $(VFILES) $(OUT)/README.md
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

$(OUT)/edits: $(OUT)/README.md
	ln -fs ../edits $(OUT)/edits

$(OUT)/README.md:
	mkdir -p $(OUT)
	> $@
	echo 'This directory contains a Coq’ified version of the Haskell containers library' >> $@
	echo 'Do not edit files here! Instead, look in `examples/containers`.' >> $@

$(HS_SPEC)/README.md:
	mkdir -p $(HS_SPEC)
	> $@
	echo 'This directory contains a Coq’ified version of the Haskell containers library specification' >> $@
	echo 'Do not edit files here! Instead, look in `examples/containers`.' >> $@

coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)

HS_TO_COQ_OPTS := \
  -e ../../base/edits \
  -e edits \
  --iface-dir ../../base/ \
  --iface-dir $(OUT) \
  -N \
  -i containers \
  -i containers/tests \
  -i containers/dist-install/build \
  -I containers/include \


# KEEP THIS IN SYNC WITH THE NEXT RULE (there ought to be a better way)
.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) $(wildcard module-edits/$$*/flags) edits $(OUT)/README.md
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
	             $(addprefix `cat , $(addsuffix ` , $(wildcard module-edits/$*/flags))) \
		     $(HS_TO_COQ_OPTS) \
	             -o $(OUT) \
	             $(wildcard containers/$*.hs) \
		     $(wildcard containers/tests/$*.hs) \
		     $(SRC_FILE_$*)
	test -e $@

# KEEP THIS IN SYNC WITH THE PREVIOUS RULE (there ought to be a better way)
.SECONDEXPANSION:
$(VFILES_HS_SPEC_GEN): $(HS_SPEC)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) $$(wildcard module-edits/$$*/flags) edits $(HS_SPEC)/README.md
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_OPTS) \
	             $(addprefix `cat , $(addsuffix ` , $(wildcard module-edits/$*/flags))) \
	             -o $(HS_SPEC) \
	             $(wildcard containers/$*.hs) \
		     $(wildcard containers/tests/$*.hs) \
		     $(SRC_FILE_$*)
	test -e $@

$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/


$(VFILES_DROPIN): $(OUT)/%.v : module-edits/%/edits edits module-edits/%/preamble.v drop-in/%.hs $(OUT)/README.md
	$(HS_TO_COQ) -e module-edits/$*/edits \
	             -e edits \
	       -o $(OUT) \
	       -N \
	       -p module-edits/$*/preamble.v \
	       --ghc -icontainers \
	       --ghc -icontainers/dist-install/build \
	       -Icontainers/include \
	       drop-in/$*.hs

clean:
	rm -rf $(OUT) $(HS_SPEC)
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
