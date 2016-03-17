# IRIS COQ DEVELOPMENT

This is the Coq development of the [Iris Project](http://plv.mpi-sws.org/iris/).

## Prerequisites

This version is known to compile with:

 - Coq 8.5
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
* The folder `heap_lang` defines the ML-like concurrent heap language, and a
  few derived constructions (e.g., parallel composition).
* The folder `barrier` contains the implementation and proof of the barrier
  <http://doi.acm.org/10.1145/2818638>.

## Documentation

A LaTeX version of the core logic definitions and some derived forms is
available in `docs/iris.tex`.
