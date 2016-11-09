# Makefile originally taken from coq-club

%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	rm -f Makefile.coq

uninstall:
	+@make -f Makefile.uninstall uninstall

install: Makefile.coq uninstall
	+@make -f Makefile.coq install

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean install uninstall phony
