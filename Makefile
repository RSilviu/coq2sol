# Makefile originally taken from coq-club and adapted

%: CoqMakefile phony
	+make -f CoqMakefile $@

all: CoqMakefile
	+make -f CoqMakefile all

clean: CoqMakefile
	+make -f CoqMakefile clean
	rm -f CoqMakefile

CoqMakefile: _CoqProject Makefile
	coq_makefile -f _CoqProject -o CoqMakefile

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony