# IRIS COQ DEVELOPMENT

This is the Coq development of the [Iris Project](http://plv.mpi-sws.org/iris/).

## Prerequisites

This version is known to compile with:

 - Coq 8.5pl2
 - Ssreflect 1.6

For development, better make sure you have a version of Ssreflect that includes
commit be724937 (no such version has been released so far, you will have to
fetch the development branch yourself). Iris compiles fine even without this
patch, but proof bullets will only be in 'strict' (enforcing) mode with the
fixed version of Ssreflect.
 
## Building Instructions

Run the following command to build the full development:

    make

The development can then be installed as the Coq user contribution `iris` by
running:

    make install

## Structure

* The folder `prelude` contains an extended "Standard Library" by Robbert
  Krebbers <http://robbertkrebbers.nl/thesis.html>.
* The folder `algebra` contains the COFE and CMRA constructions as well as
  the solver for recursive domain equations.
* The folder `program_logic` builds the semantic domain of Iris, defines and
  verifies primitive view shifts and weakest preconditions, and builds some
  language-independent derived constructions (e.g., STSs).
* The folder `heap_lang` defines the ML-like concurrent heap language
  * The subfolder `lib` contains a few derived constructions within this
    language, e.g., parallel composition.
    Most notable here s `lib/barrier`, the implementation and proof of a barrier
    as described in <http://doi.acm.org/10.1145/2818638>.
* The folder `proofmode` contains the Iris proof mode, which extends Coq with
  contexts for persistent and spatial Iris assertions. It also contains tactics
  for interactive proofs in Iris. Documentation can be found in `ProofMode.md`.
* The folder `tests` contains modules we use to test our infrastructure.
  Users of the Iris Coq library should *not* depend on these modules; they may
  change or disappear without any notice.

## Documentation

A LaTeX version of the core logic definitions and some derived forms is
available in `docs/iris.tex`.
