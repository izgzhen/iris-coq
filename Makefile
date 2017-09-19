# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find theories \( -name "*.v.d" -o -name "*.vo" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete
	rm -f Makefile.coq

# Create Coq Makefile. POSIX awk can't do in-place editing, but coq_makefile wants the real
# filename, so we do some file gymnastics.
Makefile.coq: _CoqProject Makefile awk.Makefile
	coq_makefile -f _CoqProject -o Makefile.coq
	mv Makefile.coq Makefile.coq.tmp && awk -f awk.Makefile Makefile.coq.tmp > Makefile.coq && rm Makefile.coq.tmp

# Install build-dependencies
build-dep: phony
	@# We want opam to not just instal the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything.
	mkdir -p build-dep
	@echo "build-dep package is $$BUILD_DEP_PACKAGE"
	sed <opam 's/^\(build\|install\|remove\):.*/\1: []/; s/^name: *"\(.*\)" */name: "\1-builddep"/' > build-dep/opam
	@fgrep builddep build-dep/opam >/dev/null || (echo "sed failed to fix the package name" && exit 1) # sanity check
	@# Compute the package name, add the pin and install it
	opam pin add "$$(egrep "^name:" build-dep/opam | sed 's/^name: *"\(.*\)" */\1/')" "$$(pwd)/build-dep" -k path $(OPAMFLAGS)

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
awk.Makefile: ;

# Phony targets (i.e. targets that should be run no matter the timestamps of the involved files)
phony: ;
.PHONY: all clean phony
