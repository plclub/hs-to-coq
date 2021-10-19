all:
	cd base && coq_makefile -f _CoqProject -o Makefile
	cd base-thy && coq_makefile -f _CoqProject -o Makefile
	cd examples/containers/lib && coq_makefile -f _CoqProject -o Makefile
	make -C base
	make -C base-thy
	make -C examples/containers/lib

clean:
	make -C base clean
	make -C base-thy clean
	make -C examples/containers/lib clean
