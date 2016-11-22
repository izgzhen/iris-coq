# Determine Coq version
COQ_VERSION=$(shell coqc --version | egrep -o 'version 8.[0-9]' | egrep -o '8.[0-9]')
COQ_MAKEFILE_FLAGS ?=

ifeq ($(COQ_VERSION), 8.6)
	COQ_MAKEFILE_FLAGS += -arg -w -arg -notation-overridden,-redundant-canonical-projection
endif

%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find \( -name "*.v.d" -o -name "*.vo" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile $(COQ_MAKEFILE_FLAGS) -f _CoqProject -o Makefile.coq.tmp
	sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' < Makefile.coq.tmp \
	  | awk '/^install:$$/{print;print "\tif [ -d \"$$(DSTROOT)\"$$(COQLIBINSTALL)/iris/ ]; then find \"$$(DSTROOT)\"$$(COQLIBINSTALL)/iris/ -name \"*.vo\" -print -delete; fi";next}1' > Makefile.coq
	rm Makefile.coq.tmp

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony
