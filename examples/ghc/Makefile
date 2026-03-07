include ../../common.mk

OUT=lib

CORE_EDITS=axiomatize-types.edits

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \
  FastString \
  AxiomatizedTypes \
  NestedRecursionHelpers \
  IntMap \
  State \
  # Used by CSE
  # TysWiredIn \


# generated from drop-in/
DROPIN = \

# These are core dependencies that we do not need to translate
#
EXTRA_CORE = Json \
  FastFunctions \
  Encoding \
  ErrUtils \
  Annotations \
  GhcPrelude \
  Packages \
  Foreign \
  IfaceType \
  PrelNames \
  TysWiredIn \
  CoAxiom


UTILS = \
  Util \
  SrcLoc \
  Unique \
  UniqSupply \
  HsSyn \
  BasicTypes \
  DynFlags \
  Panic \
  OccName \
  Module \

DATASTRUCTS = \
  Bag \
  EnumSet \
  BooleanFormula \
  UniqFM \
  UniqSet \
  OrdList \
  FiniteMap \
  ListSetOps \
  Pair \
  Maybes \
  MonadUtils \

# Generated modules
# These are general purpose utility modules
MODULES = \
  $(UTILS) \
  $(DATASTRUCTS) \

## Not actually used??
#  CmmType \


##
CORESYN = \
   IdInfo Class TyCon DataCon PatSyn Var VarSet VarEnv CoreSyn Demand Type TyCoRep Coercion  \

##
CONSTRUCTORS = \

# These are modules that we translate but do not do anything about
EXTRAS = \
  TrieMap \
  CSE \
  CoreStats \
  UnVarGraph \
  CoreArity \
  CoreTidy \
  CallArity \
  CoAxiom \
  TysWiredIn \
  MkCore \
  Digraph \
  SetLevels \
  CoreMonad \
  OccurAnal \
  FloatIn \
  FloatOut \

## These are the modules most directly related to the core language
CORE_MODULES = \
  FastStringEnv \
  Constants \
  Id \
  CoreSubst \
  PrelNames \
  CoreUtils \
  Name \
  NameEnv \
  NameSet \
  FV \
  Literal \
  FieldLabel \
  ConLike \
  CoreFVs \
  Exitify \




NOTRANSLATE = \
  Constructors \
  CoreType \
  IdInfo2 \

CORETYPE = \
  TyCoRep \
  Coercion \

# These modules translate, but do not compile, at the moment and
# should not be processed by coq
BROKEN_MODULES = \
  IntMap \


####################################################
# GHC 9.10 source path mappings
# Maps old module names to GHC 9.10 compiler paths
####################################################

SRCPATH = ghc/compiler

# UTILS
SRC_Util        = $(SRCPATH)/GHC/Utils/Misc.hs
SRC_SrcLoc      = $(SRCPATH)/GHC/Types/SrcLoc.hs
SRC_Unique      = $(SRCPATH)/GHC/Types/Unique.hs
SRC_UniqSupply  = $(SRCPATH)/GHC/Types/Unique/Supply.hs
SRC_HsSyn       = $(SRCPATH)/Language/Haskell/Syntax/Basic.hs
SRC_BasicTypes  = $(SRCPATH)/GHC/Types/Basic.hs
SRC_DynFlags    = $(SRCPATH)/GHC/Driver/DynFlags.hs
SRC_Panic       = $(SRCPATH)/GHC/Utils/Panic.hs
SRC_OccName     = $(SRCPATH)/GHC/Types/Name/Occurrence.hs
SRC_Module      = $(SRCPATH)/GHC/Unit/Module.hs

# DATASTRUCTS
SRC_Bag         = $(SRCPATH)/GHC/Data/Bag.hs
SRC_EnumSet     = $(SRCPATH)/GHC/Data/EnumSet.hs
SRC_BooleanFormula = $(SRCPATH)/GHC/Data/BooleanFormula.hs
SRC_UniqFM      = $(SRCPATH)/GHC/Types/Unique/FM.hs
SRC_UniqSet     = $(SRCPATH)/GHC/Types/Unique/Set.hs
SRC_OrdList     = ghc-head/OrdList.hs
SRC_FiniteMap   = $(SRCPATH)/GHC/Data/FiniteMap.hs
SRC_ListSetOps  = $(SRCPATH)/GHC/Data/List/SetOps.hs
SRC_Pair        = $(SRCPATH)/GHC/Data/Pair.hs
SRC_Maybes      = $(SRCPATH)/GHC/Data/Maybe.hs
SRC_MonadUtils  = $(SRCPATH)/GHC/Utils/Monad.hs

# CORESYN (mutually dependent modules -> Core.v)
SRC_IdInfo      = $(SRCPATH)/GHC/Types/Id/Info.hs
SRC_Class       = $(SRCPATH)/GHC/Core/Class.hs
SRC_TyCon       = $(SRCPATH)/GHC/Core/TyCon.hs
SRC_DataCon     = $(SRCPATH)/GHC/Core/DataCon.hs
SRC_PatSyn      = $(SRCPATH)/GHC/Core/PatSyn.hs
SRC_Var         = $(SRCPATH)/GHC/Types/Var.hs
SRC_VarSet      = $(SRCPATH)/GHC/Types/Var/Set.hs
SRC_VarEnv      = $(SRCPATH)/GHC/Types/Var/Env.hs
SRC_CoreSyn     = $(SRCPATH)/GHC/Core.hs
SRC_Demand      = $(SRCPATH)/GHC/Types/Demand.hs
SRC_Type        = $(SRCPATH)/GHC/Core/Type.hs
SRC_TyCoRep     = $(SRCPATH)/GHC/Core/TyCo/Rep.hs
SRC_Coercion    = $(SRCPATH)/GHC/Core/Coercion.hs

# CORE_MODULES
SRC_FastStringEnv = $(SRCPATH)/GHC/Data/FastString/Env.hs
SRC_Constants   = $(SRCPATH)/GHC/Settings/Constants.hs
SRC_Id          = $(SRCPATH)/GHC/Types/Id.hs
SRC_CoreSubst   = $(SRCPATH)/GHC/Core/Subst.hs
SRC_PrelNames   = $(SRCPATH)/GHC/Builtin/Names.hs
SRC_CoreUtils   = $(SRCPATH)/GHC/Core/Utils.hs
SRC_Name        = $(SRCPATH)/GHC/Types/Name.hs
SRC_NameEnv     = $(SRCPATH)/GHC/Types/Name/Env.hs
SRC_NameSet     = $(SRCPATH)/GHC/Types/Name/Set.hs
SRC_FV          = $(SRCPATH)/GHC/Utils/FV.hs
SRC_Literal     = $(SRCPATH)/GHC/Types/Literal.hs
SRC_FieldLabel  = $(SRCPATH)/GHC/Types/FieldLabel.hs
SRC_ConLike     = $(SRCPATH)/GHC/Core/ConLike.hs
SRC_CoreFVs     = $(SRCPATH)/GHC/Core/FVs.hs
SRC_Exitify     = $(SRCPATH)/GHC/Core/Opt/Exitify.hs

# EXTRAS
SRC_TrieMap     = $(SRCPATH)/GHC/Data/TrieMap.hs
SRC_CSE         = $(SRCPATH)/GHC/Core/Opt/CSE.hs
SRC_CoreStats   = $(SRCPATH)/GHC/Core/Stats.hs
SRC_UnVarGraph  = $(SRCPATH)/GHC/Data/Graph/UnVar.hs
SRC_CoreArity   = $(SRCPATH)/GHC/Core/Opt/Arity.hs
SRC_CoreTidy    = $(SRCPATH)/GHC/Core/Tidy.hs
SRC_CallArity   = $(SRCPATH)/GHC/Core/Opt/CallArity.hs
SRC_CoAxiom     = $(SRCPATH)/GHC/Core/Coercion/Axiom.hs
SRC_TysWiredIn  = $(SRCPATH)/GHC/Builtin/Types.hs
SRC_MkCore      = $(SRCPATH)/GHC/Core/Make.hs
SRC_Digraph     = $(SRCPATH)/GHC/Data/Graph/Directed.hs
SRC_SetLevels   = $(SRCPATH)/GHC/Core/Opt/SetLevels.hs
SRC_CoreMonad   = $(SRCPATH)/GHC/Core/Opt/Monad.hs
SRC_OccurAnal   = $(SRCPATH)/GHC/Core/Opt/OccurAnal.hs
SRC_FloatIn     = $(SRCPATH)/GHC/Core/Opt/FloatIn.hs
SRC_FloatOut    = $(SRCPATH)/GHC/Core/Opt/FloatOut.hs

# Helper function: get source path for a module name
# Usage: $(call ghc_src,ModuleName)
ghc_src = $(SRC_$(1))

####################################################

VFILES_GEN       = $(addsuffix .v,$(MODULES))
VFILES_MAN       = $(addsuffix .v,$(HANDMOD))
VFILES_DROPIN    = $(addsuffix .v,$(DROPIN))
VFILES_CORE      = $(addsuffix .v,$(CORE_MODULES) $(EXTRAS))
VFILES_CONSTR    = Constructors.v
VFILES_CORESYN   = Core.v
VFILES_TYPE      = Type_.v

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_DROPIN) $(VFILES_CORE) $(VFILES_CORESYN)

OUTFILES_GEN       = $(addprefix $(OUT)/,$(VFILES_GEN))
OUTFILES_MAN       = $(addprefix $(OUT)/,$(VFILES_MAN))
OUTFILES_CORE      = $(addprefix $(OUT)/,$(VFILES_CORE))
OUTFILES_DROPIN    = $(addprefix $(OUT)/,$(VFILES_DROPIN))
OUTFILES_CORETYPE  = $(addprefix $(OUT)/,$(VFILES_CORETYPE))
OUTFILES_CONSTR    = $(addprefix $(OUT)/,$(VFILES_CONSTR))
OUTFILES_CORESYN   = $(addprefix $(OUT)/,$(VFILES_CORESYN))
OUTFILES_TYPE      = $(addprefix $(OUT)/,$(VFILES_TYPE))

OUTFILES   = $(OUTFILES_GEN) $(OUTFILES_MAN) $(OUTFILES_DROPIN) $(OUTFILES_CORE) $(OUTFILES_CORESYN)

# Build list of source .hs files using path mappings
HSFILES     = $(foreach m,$(MODULES) $(CORESYN) $(CORE_MODULES),$(SRC_$(m)))

EDITPATHS = $(addprefix module-edits/,$(MODULES) $(CORESYN) $(CORE_MODULES))
EDITFILES = edits $(CORE_EDITS) $(addsuffix /edits,$(EDITPATHS)) $(addsuffix /*.v, $(EDITPATHS))

all: vfiles coq

vfiles: $(OUT)/edits  $(OUT)/README.md $(OUT)/_CoqProject $(OUTFILES)

core: $(OUT)/README.md coq


filelist:
	@for f in $(HSFILES); do echo $$f; done


editlist:
	@ls -1 $(EDITFILES) 2>/dev/null | xargs cloc --by-file-by-lang --lang-no-ext=zsh --force-lang=zsh,edits --force-lang=Coq,v --skip-uniqueness

edittable:
	@echo "skip"
	@cat $(EDITFILES) 2>/dev/null | grep "skip" | grep -v "#" | grep -v "constructor" | grep -v "module" | wc -l
	@echo "skip constructor"
	@cat $(EDITFILES) 2>/dev/null | grep "skip constructor" | grep -v "#" | wc -l
	@echo "skip module"
	@cat $(EDITFILES) 2>/dev/null | grep "skip module" | grep -v "#" | wc -l
	@echo "axiomatize"
	@cat $(EDITFILES) 2>/dev/null | grep "axiomatize" | grep -v "#" | grep -v "module" | wc -l
	@echo "redefine Axiom"
	@cat $(EDITFILES) 2>/dev/null | grep "redefine Axiom" | grep -v "#" | wc -l
	@echo "axiomatize module"
	@cat $(EDITFILES) 2>/dev/null | grep "axiomatize" | grep "module" | grep -v "#" | wc -l
	@echo "order"
	@cat $(EDITFILES) 2>/dev/null | grep "order" | grep -v "#" | wc -l
	@echo "termination"
	@cat $(EDITFILES) 2>/dev/null | grep "termination" | grep -v "#" | wc -l
	@echo "rewrite"
	@cat $(EDITFILES) 2>/dev/null | grep "rewrite" | grep -v "#" | wc -l
	@echo "redefine"
	@cat $(EDITFILES) 2>/dev/null | grep "redefine" | grep -v "#" | grep -v "Axiom"
	@echo "rename type"
	@cat $(EDITFILES) 2>/dev/null | grep "rename type" | grep -v "#" | wc -l
	@echo "rename value"
	@cat $(EDITFILES) 2>/dev/null | grep "rename value" | grep -v "#" | wc -l
	@echo "set type"
	@cat $(EDITFILES) 2>/dev/null | grep "set type" | grep -v "#" | wc -l
	@echo "inline mutual"
	@cat $(EDITFILES) 2>/dev/null | grep "inline mutual" | grep -v "#" | wc -l
	@echo "rename module"
	@cat $(EDITFILES) 2>/dev/null | grep "rename module" | grep -v "#" | wc -l
	@echo "TOTAL"
	@cat $(EDITFILES) 2>/dev/null | grep -v "#" --include "*edits" | wc -l


# This target is also used as a dependecy to ensure that $(OUT) exists.
$(OUT)/README.md:
	mkdir -p $(OUT)
	mkdir -p deps
	> $@
	echo 'This directory contains a Coq'\''ified version of parts of GHC' >> $@
	echo 'Do not edit files here! Instead, look in `examples/ghc`.' >> $@

$(OUT)/edits:
	mkdir -p $(OUT)
	ln -fs ../edits $(OUT)/edits

$(OUT)/_CoqProject: $(OUT)/README.md Makefile
	> $@
	echo '-Q . ""' >> $@
	echo '-Q ../../../base ""' >> $@
	echo '-Q ../../../base-thy  Proofs' >> $@
	echo '-Q ../../containers/lib   ""' >> $@
	echo '-Q ../../containers/theories  ""' >> $@
	echo '-Q ../../transformers/lib  ""' >> $@
	echo $(filter-out $(addsuffix .v,$(BROKEN_MODULES)), $(VFILES)) >> $@

$(OUT)/Makefile: $(OUT)/README.md $(OUT)/_CoqProject $(OUTFILES) Makefile
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

coq: $(OUT)/Makefile $(OUTFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)


HS_TO_COQ_GHC_OPTS=\
     --ghc-tree ghc \
     -i gen-files \
     -I gen-files \
     -I ghc/rts/include \
     -I ghc/rts/include/stg \
     -I ghc/rts/include/rts/storage \
     -I ghc/compiler \
     --ghc -DSTAGE=2 \
     --ghc -package=ghc-boot-th \
     --ghc -package=ghc \
     --ghc -XNoImplicitPrelude \
     -e ../../base/edits \
     -e ../containers/edits \
     -e ../transformers/edits \
     --iface-dir ../../base \
     --iface-dir ../containers/lib \
     --iface-dir ../transformers/lib \
     --iface-dir $(OUT) \
     --dependency-dir deps \
     -e edits \
     -N \


-include deps/*.mk

%.h2ci: %.v
	test -e $@

.SECONDEXPANSION:
$(OUTFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -o $(OUT) \
		     $(SRC_$*)
	test -e $@

$(OUTFILES_CORE): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits $(CORE_EDITS)
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -e $(CORE_EDITS) \
                     -o $(OUT) \
		     $(SRC_$*)
	test -e $@

CORESYN_PRE = $(wildcard $(addprefix module-edits/, $(addsuffix /preamble.v, $(CORESYN))))
CORESYN_MID = $(wildcard $(addprefix module-edits/, $(addsuffix /midamble.v, $(CORESYN))))

$(OUTFILES_CORESYN) : edits $(CORE_EDITS) $(CORESYN_PRE) $(CORESYN_MID) $(wildcard $(addprefix module-edits/, $(addsuffix /edits, $(CORESYN))))
	cat $(CORESYN_PRE) > CoreSyn_preamble.v
	cat $(CORESYN_MID) > CoreSyn_midamble.v
	$(HS_TO_COQ) $(HS_TO_COQ_GHC_OPTS) \
                -p CoreSyn_preamble.v \
                --midamble CoreSyn_midamble.v \
	             $(addprefix -e , $(wildcard $(addprefix module-edits/, $(addsuffix /edits, $(CORESYN))))) \
                -e $(CORE_EDITS) \
                -o $(OUT) \
		     $(foreach m,$(CORESYN),$(SRC_$(m)))
	test -e $@
	rm -f CoreSyn_preamble.v CoreSyn_midamble.v

$(OUTFILES_TYPE) : edits $(CORE_EDITS) $$(wildcard module-edits/Type/preamble.v) $$(wildcard module-edits/Type/midamble.v)  $$(wildcard module-edits/Type/edits)
		$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/Type/edits)) \
	             $(addprefix -p , $(wildcard module-edits/Type/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/Type/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
            -o Type_.v \
		     $(SRC_Type)
	test -e $@

$(OUTFILES_CONSTR) : edits $(CORE_EDITS) module-edits/Constructors/preamble.v  module-edits/Constructors/midamble.v module-edits/Constructors/edits
	$(HS_TO_COQ) -e module-edits/Constructors/edits \
	                  -p module-edits/Constructors/preamble.v \
	                  --midamble module-edits/Constructors/midamble.v \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -e $(CORE_EDITS) \
                     -o $(OUT) \
		     $(foreach m,$(CONSTRUCTORS),$(SRC_$(m)))
	test -e $@


$(OUTFILES_CORETYPE) : edits core-edits module-edits/CoreType/preamble.v  module-edits/CoreType/midamble.v module-edits/CoreType/edits
	$(HS_TO_COQ) -e module-edits/CoreType/edits \
	                  -p module-edits/CoreType/preamble.v \
	                  --midamble module-edits/CoreType/midamble.v \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -e core-edits \
                     -o $(OUT) \
		     $(foreach m,$(CORETYPE),$(SRC_$(m)))
	test -e $@

$(OUTFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/

clean:
	rm -rf $(OUT)
	rm -f *.aux *.log

cleancore:
	rm -rf $(OUTFILES_CORE)
