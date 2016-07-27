In this changelog, we document "large-ish" changes to Iris that affect even the
way the logic is used on paper.  We also mention some significant changes in the
Coq development, but not every API-breaking change is listed.  Changes marked
[#] still need to be ported to the Iris Documentation LaTeX file.

## Iris 2.0

This version accompanies the final ICFP paper.

* [algebra] Make the core of an RA or CMRA a partial function.
* [heap_lang] No longer use dependent types for expressions.  Instead, values
  carry a proof of closedness.  Substitution, closedness and value-ness proofs
  are performed by computation after reflecting into a term langauge that knows
  about values and closed expressions.
* [program_logic/language] The language does not define its own "atomic"
  predicate.  Instead, atomicity is defined as reducing in one step to a value.
* [# program_logic/lifting] Lifting lemmas no longer round-trip through a
  user-chosen predicate to define the configurations we can reduce to; they
  directly relate to the operational semantics.  This is equivalent and
  much simpler to read.
  Due to a lack of maintenance and usefulness, lifting lemmas for Hoare triples
  are removed.

## Iris 2.0-rc1

This is the Coq development and Iris Documentation as submitted to ICFP.
