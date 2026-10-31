all: base tests

BASE_CHECKS ?= base-checks

base: base/Makefile
	$(MAKE) -C base
	$(if $(strip $(BASE_CHECKS)),$(MAKE) $(BASE_CHECKS),:)

base-checks:
	bash ../tests/checks/deriving.sh --target-version 9.0
	bash ../tests/checks/identity-traversal.sh --target-version 9.0

base/Makefile: base/_CoqProject
	cd base && coq_makefile -f _CoqProject -o Makefile

# clean removes the convenience copy. Finish regenerating every source before
# coq_makefile or the compiler reads the rebuilt tree. Remove the trigger on
# failure so the next build retries generation, keeping successful sources.
base/_CoqProject:
	$(MAKE) -C base-src vfiles || { status=$$?; rm -f "$@"; exit $$status; }

vfiles:
	$(MAKE) -C base-src vfiles

tests:
	$(MAKE) -C tests

clean:
	$(MAKE) -C base-src clean
	$(MAKE) -C tests clean

.PHONY: all base base-checks vfiles tests clean
