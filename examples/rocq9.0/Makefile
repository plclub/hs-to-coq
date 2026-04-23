all: base tests

base: base/Makefile
	$(MAKE) -C base

base/Makefile: base/_CoqProject
	cd base && coq_makefile -f _CoqProject -o Makefile

vfiles:
	$(MAKE) -C base-src vfiles

tests:
	$(MAKE) -C tests

clean:
	$(MAKE) -C base-src clean
	$(MAKE) -C tests clean

.PHONY: all base vfiles tests clean
