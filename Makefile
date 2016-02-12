# Makefile taken from coq-club, Christian Doczkal <doczkal@ps.uni-saarland.de>,
# who adapted it from "somewhere".
all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all clean
