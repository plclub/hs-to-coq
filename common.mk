HAVE_STACK := $(shell command -v stack 2> /dev/null)

ifdef HAVE_STACK
ifdef FOREIGN_HS_TO_ROCQ
ifndef HS_TO_ROCQ_DIR
$(error "Using `hs-to-rocq/common.mk' outside the hs-to-rocq directory requires setting `HS_TO_ROCQ_DIR'")
endif
HS_TO_ROCQ = $(shell cd $(HS_TO_ROCQ_DIR) && stack exec env | perl -ne 'print "$$1/hs-to-rocq\n" if /^PATH=([^:]+)/')
else
HS_TO_ROCQ = stack --allow-different-user exec hs-to-rocq --
endif
else
ifndef FOREIGN_HS_TO_ROCQ
$(error "Using `hs-to-rocq/common.mk' outside the hs-to-rocq directory requires `stack'")
endif
ifeq ($(HS_TO_ROCQ_COVERAGE),True)
	CABAL_OPTS = --enable-coverage
endif
TOP := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
HS_TO_ROCQ = cabal new-run --project-file=$(TOP)/cabal.project  -v0 $(CABAL_OPTS) exe:hs-to-rocq --
endif

SHELL = bash

# GHC 9.10: generated .v files contain Unicode (e.g. ∘).
# Ensure hs-to-rocq can encode output correctly.
export LANG := C.utf8
