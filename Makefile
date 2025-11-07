all: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq all

install: all
	$(MAKE) -f Makefile.rocq install

clean: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq cleanall
	rm -f Makefile.rocq

Makefile.rocq: _RocqProject
	$(COQBIN)coq_makefile -f _RocqProject -o Makefile.rocq
