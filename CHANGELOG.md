In this changelog, we document "large-ish" changes to Iris that affect even the
way the logic is used on paper.  We also mention some significant changes in the
Coq development, but not every API-breaking change is listed.  Changes marked
`[#]` still need to be ported to the Iris Documentation LaTeX file(s).

## Iris 3.1.0 (unfinished)

Changes in and extensions of the theory:

* [#] Add new modality: ■ ("plainly").
* Camera morphisms have to be homomorphisms, not just monotone functions.
* Add a proof that `f` has a fixed point if `f^k` is contractive.
* Constructions for least and greatest fixed points over monotone predicates
  (defined in the logic of Iris using impredicative quantification).
* Add a proof of the inverse of `wp_bind`.

Changes in Coq:

* Rename some things and change notation:
  - The unit of a camera: `empty` -> `unit`, `∅` -> `ε`
  - Disjointness: `⊥` -> `##`
  - A proof mode type class `IntoOp` -> `IsOp`
  - OFEs with all elements being discrete: `Discrete` -> `OfeDiscrete`
  - OFE elements whose equality is discrete: `Timeless` -> `Discrete`
  - Timeless propositions: `TimelessP` -> `Timeless`
  - Camera elements such that `core x = x`: `Persistent` -> `CoreId`
  - Persistent propositions: `PersistentP` -> `Persistent`
  - The persistent modality: `always` -> `persistently`
  - Consistently SnakeCase identifiers:
    + `CMRAMixin` -> `CmraMixin`
    + `CMRAT` -> `CmraT`
    + `CMRATotal` -> `CmraTotal`
    + `CMRAMorphism` -> `CmraMorphism`
    + `CMRADiscrete` -> `CmraDiscrete`
    + `UCMRAMixin` -> `UcmraMixin`
    + `UCMRAT` -> `UcmraT`
    + `DRAMixin` -> `DraMixin`
    + `DRAT` -> `DraT`
    + `STS` -> `Sts`
  - Many lemmas also changed their name.  `always_*` became `persistently_*`,
    and furthermore: (the following list is not complete)
    + `impl_wand` -> `impl_wand_1` (it only involves one direction of the
      equivalent)
    + `always_impl_wand` -> `impl_wand`
    + `always_and_sep_l` -> `and_sep_l`
    + `always_and_sep_r` -> `and_sep_r`
    + `always_sep_dup` -> `sep_dup`
    + `wand_impl_always` -> `impl_wand_persistently` (additionally,
      the direction of this equivalence got swapped for consistency's sake)
    + `always_wand_impl` -> `persistently_impl_wand` (additionally, the
      direction of this equivalence got swapped for consistency's sake)
  The following `sed` snippet should get you most of the way:
```
sed 's/\bPersistentP\b/Persistent/g; s/\bTimelessP\b/Timeless/g; s/\bCMRADiscrete\b/CmraDiscrete/g; s/\bCMRAT\b/CmraT/g; s/\bCMRAMixin\b/CmraMixin/g; s/\bUCMRAT\b/UcmraT/g; s/\bUCMRAMixin\b/UcmraMixin/g; s/\bSTS\b/Sts/g' -i $(find -name "*.v")
```
* Fix a bunch of consistency issues in the proof mode, and make it overall more
  usable.  In particular:
  - All proof mode tactics start the proof mode if necessary; `iStartProof` is
    no longer needed and should only be used for building custom proof mode
    tactics.
  - Change in the grammar of specialization patterns: `>[...]` -> `[> ...]`
  - Various new specification patterns for `done` and framing.
  - There is common machinery for symbolic execution of pure reductions. This
    is provided by the type classes `PureExec` and `IntoVal`.
  - There is a new connective `tc_opaque`, which can be used to make definitions
    opaque for type classes, and thus opaque for most tactics of the proof
    mode.
  - Define Many missing type class instances for distributing connectives.
  - Implement the tactics `iIntros (?)` and `iIntros "!#"` (i.e. `iAlways`)
    using type classes. This makes them more generic, e.g., `iIntros (?)` also
    works when the universal quantifier is below a modality, and `iAlways` also
    works for the plainness modality.  A breaking change, however, is that these
    tactics now no longer work when the universal quantifier or modality is
    behind a type class opaque definition.  Furthermore, this can change the
    name of anonymous identifiers introduced with the "%" pattern.
* Define the generic `fill` operation of the `ectxi_language` construct in terms
  of a left fold instead of a right fold. This gives rise to more definitional
  equalities.
* Improved big operators:
  + They are no longer tied to cameras, but work on any monoid
  + The version of big operations over lists was redefined so that it enjoys
    more definitional equalities.
* Various improvements to `solve_ndisj`.
* Improve handling of pure (non-state-dependent) reductions in heap_lang.
* Use `Hint Mode` to prevent Coq from making arbitrary guesses in the presence
  of evars, which often led to divergence. There are a few places where type
  annotations are now needed.
* Move the `prelude` folder to its own project: std++
* The rules `internal_eq_rewrite` and `internal_eq_rewrite_contractive` are now
  stated in the logic, i.e. they are `iApply` friendly.

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
