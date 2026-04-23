# Makefile for Rocq 9.0 unit tests.
# Reuses test .hs files from examples/tests/ with --target-version 9.0.

include ../../../common.mk

# Source tests directory
TESTS_SRC=../../tests

# Extra flag for Rocq 9.0 target
TARGET_VERSION = --target-version 9.0

# tests that should pass
PASS = \
  Simple \
  Self \
  Poly \
  Irrefutable \
  LocalTopoSort \
  InstCtx \
  ExhaustGuard \
  PartialAppliedPolyDataCon \
  NonStructuralRec \
  DotName \
  MapAccumR \
  Sub \
  FTP \
  AddAndReplace \
  FTPDefault \
  PolyInstance2 \
  PolyInstance3 \
  Bits \
  BitsRewrite \
  PatternGuard \
  Guard2 \
  Notations \
  Renamed \
  RenameModule \
  Mutrec \
  GADT \
  Underscore_Module \
  LetPattern \
  AxiomatizeModule \
  RedefineAddAxiom \
  AddTheorem \
  Existential \
  SkipConstructor \
  SkipMatches \
  Promote \
  Promote2 \
  ExceptIn \
  ParserTests \
  StrictPair \
  InstVar \
  PolyKind \
  PolyKindClass \
  ClassKinds \
  UniversePolymorphic \
  Equations \

# tests that *should* pass but currently fail
TODO_PASS = \
  TypeAnnotations \
  MutrecInst \
  TopBind \
  ExceptInDataDefinition \

# tests that *should* pass but currently don't even translate
TODO_TRANSLATE = \


MODULES = $(PASS) $(TODO_PASS) $(TODO_TRANSLATE)

VFILES    = $(addsuffix .v,$(MODULES)) Renamed.v
VOFILES   = $(patsubst %.v,%.vo,$(VFILES))
COQFLAGS  = ""

# typecheck *quietly*
TYPECHECK=coqc 1>/dev/null

main:
	# Call ourselves with -k, so that we see all test outputs,
	# even if some fail
	$(MAKE) -k all

all:  $(VFILES) pass todo_pass todo_translate

pass: $(addsuffix .pass,$(PASS))
	@echo
	@echo -------- END PASS ------------
	@echo

todo_pass: $(foreach f,$(TODO_PASS),$(f).fail)
	@echo
	@echo "Any names printed without errors should be moved from TODO_PASS to PASS"
	@echo -------- END FAIL ------------
	@echo
	@echo "(Errors are expected from now on)"
	@echo

todo_translate: $(foreach f, $(TODO_TRANSLATE), $(f).fail_translate)
	@echo
	@echo "Any names that fail should be moved from TODO_TRANSLATE to TODO_PASS"
	@echo "Any names that pass should be moved from TODO_TRANSLATE to PASS"
	@echo -------- END UNTRANSLATABLE ------------

%.pass : %.v
	@/usr/bin/env echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m (should pass)"; exit 1;\
	 elif ! $(TYPECHECK) $< >&/dev/null;\
	 then echo -e "\033[1;31mfailed\033[0m (should pass)"; exit 1;  \
	 else echo -e "\033[1;32mpassed\033[0m"; \
	 fi

%.fail : %.v
	@/usr/bin/env echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m"; \
	 elif ! $(TYPECHECK) $< >&/dev/null; \
	 then echo -e "\033[1;31mfailed\033[0m"; \
	 else echo -e "\033[1;32mpassed\033[0m (unexpected)"; exit 1; \
	 fi

%.fail_translate : %.v
	@/usr/bin/env echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m"; \
	 elif ! $(TYPECHECK) $< >&/dev/null; \
	 then echo -e "\033[1;33mfailed\033[0m (unexpected)"; exit 1;\
	 else echo -e "\033[1;32mpassed\033[0m (unexpected)"; exit 1; \
	 fi

%.vo : %.v
	@coqc -Q . "" $*.v

.SECONDEXPANSION:
# Generate .v from .hs using source tests directory
# Look for edits/preamble/midamble in the source tests directory
%.v : FORCE $$(wildcard $(TESTS_SRC)/$$*/edits) $$(wildcard $(TESTS_SRC)/$$*/preamble.v) $(TESTS_SRC)/%.hs
	@rm -f $*.v
	@if [ -e $(TESTS_SRC)/$*/preamble.v ]; then P_ARG="--preamble $(TESTS_SRC)/$*/preamble.v"; else P_ARG=; fi;\
	 if [ -e $(TESTS_SRC)/$*/midamble.v ]; then M_ARG="--midamble $(TESTS_SRC)/$*/midamble.v"; else M_ARG=; fi;\
	 if [ -e $(TESTS_SRC)/$*/edits ];      then E_ARG="--edits    $(TESTS_SRC)/$*/edits";      else E_ARG=; fi;\
	 $(HS_TO_ROCQ) $(TARGET_VERSION) $${E_ARG} -N -e $(TESTS_SRC)/renamings -o . $${P_ARG} $${M_ARG} $(TESTS_SRC)/$*.hs 1>/dev/null || true

Renamed.v: $(TESTS_SRC)/RenameMe.hs $(TESTS_SRC)/RenameMe.hs-boot $(TESTS_SRC)/RenameMeToo.hs $(TESTS_SRC)/RenameMe/edits
	@rm -f Renamed.v
	$(HS_TO_ROCQ) $(TARGET_VERSION) -N -e $(TESTS_SRC)/RenameMe/edits -e $(TESTS_SRC)/renamings -o . $(TESTS_SRC)/RenameMe.hs $(TESTS_SRC)/RenameMeToo.hs 1>/dev/null

RenameModule.v:: Renamed.vo

# We always want to re-build the .v files, to test the current build of hs-to-rocq
FORCE:

clean:
	rm -rf */*.vo */*.glob */*.v.d *.vo *.v.d *.glob *.hi *.o *.hi-boot *.o-boot $(VFILES) _CoqProject Makefile.coq *~

.SECONDARY: $(VFILES)
