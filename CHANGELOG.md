In this changelog, we document "large-ish" changes to Iris that affect even the
way the logic is used on paper.  We also mention some significant changes in the
Coq development, but not every API-breaking change is listed.  Changes marked
`[#]` still need to be ported to the Iris Documentation LaTeX file(s).

## Iris 3.1.0 (unfinished)

Changes in and extensions of the theory:

* [#] CMRA morphisms have to be homomorphisms, not just monotone functions.
* [#] Show that f has a fixed point if f^k is contractive.
* Provide least and greatest fixed point (defined in the logic of Iris).
* Prove the inverse of wp_bind.

Changes in Coq:

* Some things got renamed and notation changed:
  - The unit of a CMRA: empty -> unit, ∅ -> ε
  - IntoOp -> IsOp
* Fix a bunch of consistency issues in the proof mode, and make it overall more
  usable.  In particular:
  - All proof mode tactics start the proof mode if necessary; iStartProof is no
    longer needed.
  - Change in the grammar of specialization patterns: >[...] -> [> ...]
  - ? More stuff ?
* Redefine bigops to get more definitional equalities.
* Improve solve_ndisj.
* Improve handling of pure (non-state-dependent) reductions in heap_lang.
* Use Hint Mode to prevent Coq from making arbitrary guesses in the presence of
  evars.  There are a few places where type annotations are now needed.
* The prelude folder has been moved to its own project: std++

## Iris 3.0.0 (released 2017-01-11)

* There now is a deprecation process.  The modules `*.deprecated` contain
  deprecated notations and definitions that are provided for backwards
  compatibility and will be removed in a future version of Iris.
* View shifts are radically simplified to just internalize frame-preserving
  updates.  Weakestpre is defined inside the logic, and invariants and view
  shifts with masks are also coded up inside Iris.  Adequacy of weakestpre is
  proven in the logic. The old ownership of the entire physical state is
  replaced by a user-selected predicate over physical state that is maintained
  by weakestpre.
* Use OFEs instead of COFEs everywhere.  COFEs are only used for solving the
  recursive domain equation.  As a consequence, CMRAs no longer need a proof of
  completeness.  (The old `cofeT` is provided by `algebra.deprecated`.)
* Implement a new agreement construction.  Unlike the old one, this one
  preserves discreteness.  dec_agree is thus no longer needed and has been moved
  to algebra.deprecated.
* Renaming and moving things around: uPred and the rest of the base logic are in
  `base_logic`, while `program_logic` is for everything involving the general
  Iris notion of a language.
* Renaming in prelude.list: Rename `prefix_of` -> `prefix` and `suffix_of` ->
  `suffix` in lemma names, but keep notation ``l1 `prefix_of` l2`` and ``l1
  `suffix_of` l2``.  `` l1 `sublist` l2`` becomes ``l1 `sublist_of` l2``. Rename
  `contains` -> `submseteq` and change `` l1 `contains` l2`` to ``l1 ⊆+ l2``.
* Slightly weaker notion of atomicity: an expression is atomic if it reduces in
  one step to something that does not reduce further.
* Changed notation for embedding Coq assertions into Iris.  The new notation is
  ⌜φ⌝.  Also removed `=` and `⊥` from the Iris scope.  (The old notations are
  provided in `base_logic.deprecated`.)
* Up-closure of namespaces is now a notation (↑) instead of a coercion.
* With invariants and the physical state being handled in the logic, there is no
  longer any reason to demand the CMRA unit to be discrete.
* The language can now fork off multiple threads at once.
* Local Updates (for the authoritative monoid) are now a 4-way relation with
  syntax-directed lemmas proving them.

## Iris 2.0

* [heap_lang] No longer use dependent types for expressions.  Instead, values
  carry a proof of closedness.  Substitution, closedness and value-ness proofs
  are performed by computation after reflecting into a term langauge that knows
  about values and closed expressions.
* [program_logic/language] The language does not define its own "atomic"
  predicate.  Instead, atomicity is defined as reducing in one step to a value.
* [program_logic] Due to a lack of maintenance and usefulness, lifting lemmas
  for Hoare triples are removed.

## Iris 2.0-rc2

This version matches the final ICFP 2016 paper.

* [algebra] Make the core of an RA or CMRA a partial function.
* [program_logic/lifting] Lifting lemmas no longer round-trip through a
  user-chosen predicate to define the configurations we can reduce to; they
  directly relate to the operational semantics.  This is equivalent and
  much simpler to read.

## Iris 2.0-rc1

This is the Coq development and Iris Documentation as submitted to ICFP 2016.
