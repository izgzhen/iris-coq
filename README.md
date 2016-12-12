# IRIS COQ DEVELOPMENT

This is the Coq development of the [Iris Project](http://iris-project.org).

## Prerequisites

This version is known to compile with:

 - Coq 8.5pl3
 - Ssreflect 1.6
 - A development version of [Iris](https://gitlab.mpi-sws.org/FP/iris-coq/)

The easiest way to install the correct versions of the dependencies is through
opam.  Once you got opam set up, just run `make build-dep` to install the right
versions of the dependencies.  When the dependencies change, just run `make
build-dep` again.

For development, better make sure you have a version of Ssreflect that includes
commit ad273277 (no such version has been released so far, you will have to
fetch the development branch yourself).  Iris compiles fine even without this
patch, but proof bullets will only be in 'strict' (enforcing) mode with the
fixed version of Ssreflect.  If you are using opam, you can easily get a fixed
version by running

    opam pin add coq-mathcomp-ssreflect https://github.com/math-comp/math-comp.git#ad273277ab38bfe458e9332dea5f3a79e3885567
 
## Building Instructions

Run `make` to build the full development.

## Structure

* The folder [prelude](prelude) contains an extended "Standard Library" by
  [Robbert Krebbers](http://robbertkrebbers.nl/thesis.html).
* The folder [algebra](algebra) contains the COFE and CMRA constructions as well
  as the solver for recursive domain equations.
* The folder [base_logic](base_logic) defines the Iris base logic and the
  primitive connectives.  It also contains derived constructions that are
  entirely independent of the choice of resources.
  * The subfolder [lib](base_logic/lib) contains some generally useful
    derived constructions.  Most importantly, it defines composeable
    dynamic resources and ownership of them; the other constructions depend
    on this setup.
* The folder [program_logic](program_logic) specializes the base logic to build
  Iris, the program logic.   This includes weakest preconditions that are
  defined for any language satisfying some generic axioms, and some derived
  constructions that work for any such language.
* The folder [proofmode](proofmode) contains the Iris proof mode, which extends
  Coq with contexts for persistent and spatial Iris assertions. It also contains
  tactics for interactive proofs in Iris. Documentation can be found in
  [ProofMode.md](ProofMode.md).
* The folder [heap_lang](heap_lang) defines the ML-like concurrent heap language
  * The subfolder [lib](heap_lang/lib) contains a few derived constructions
    within this language, e.g., parallel composition.
    Most notable here is [lib/barrier](heap_lang/lib/barrier), the implementation
    and proof of a barrier as described in <http://doi.acm.org/10.1145/2818638>.
* The folder [tests](tests) contains modules we use to test our infrastructure.
  Users of the Iris Coq library should *not* depend on these modules; they may
  change or disappear without any notice.

## Documentation

A LaTeX version of the core logic definitions and some derived forms is
available in [docs/iris.tex](docs/iris.tex).  A compiled PDF version of this
document is [available online](http://plv.mpi-sws.org/iris/appendix-3.0.pdf).
