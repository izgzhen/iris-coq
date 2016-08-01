Tactic overview
===============

Many of the tactics below apply to more goals than described in this document
since the behavior of these tactics can be tuned via instances of the type
classes in the file `proofmode/classes`. Most notable, many of the tactics can
be applied when the to be introduced or to be eliminated connective appears
under a later, a primitive view shift, or in the conclusion of a weakest
precondition connective.

Applying hypotheses and lemmas
------------------------------

- `iExact "H"`  : finish the goal if the conclusion matches the hypothesis `H`
- `iAssumption` : finish the goal if the conclusion matches any hypothesis
- `iApply pm_trm` : match the conclusion of the current goal against the
   conclusion of `pm_trm` and generates goals for the premises of `pm_trm`. See
   proof mode terms below.

Context management
------------------

- `iIntros (x1 ... xn) "ipat1 ... ipatn"` : introduce universal quantifiers
  using Coq introduction patterns `x1 ... xn` and implications/wands using proof
  mode introduction patterns `ipat1 ... ipatn`.
- `iClear "H1 ... Hn"` : clear the hypothesis `H1 ... Hn`. The symbol `★` can
  be used to clear entire spatial context.
- `iRevert (x1 ... xn) "H1 ... Hn"` : revert the proof mode hypotheses
  `H1 ... Hn` into wands, as well as the Coq level hypotheses/variables
  `x1 ... xn` into universal quantifiers. The symbol `★` can be used to revert
  the entire spatial context.
- `iRename "H1" into "H2"` : rename the hypothesis `H1` into `H2`.
- `iSpecialize pm_trm` : instantiate universal quantifiers and eliminate
  implications/wands of a hypothesis `pm_trm`. See proof mode terms below.
- `iPoseProof pm_trm as "H"` : put `pm_trm` into the context as a new hypothesis
  `H`.
- `iAssert P with "spat" as "ipat"` : create a new goal with conclusion `P` and
  put `P` in the context of the original goal. The specialization pattern
  `spat` specifies which hypotheses will be consumed by proving `P` and the
  introduction pattern `ipat` specifies how to eliminate `P`.

Introduction of logical connectives
-----------------------------------

- `iPureIntro` : turn a pure goal into a Coq goal. This tactic works for goals
  of the shape `■ φ`, `a ≡ b` on discrete COFEs, and `✓ a` on discrete CMRAs.

- `iLeft` : left introduction of disjunction.
- `iRight` : right introduction of disjunction.

- `iSplit` : introduction of a conjunction, or separating conjunction provided
  one of the operands is persistent.
- `iSplitL "H1 ... Hn"` : introduction of a separating conjunction. The
  hypotheses `H1 ... Hn` are used for the left conjunct, and the remaining ones
  for the right conjunct.
- `iSplitR "H0 ... Hn"` : symmetric version of the above.
- `iExist t1, .., tn` : introduction of an existential quantifier.

Elimination of logical connectives
----------------------------------

- `iExFalso` : Ex falso sequitur quod libet.
- `iDestruct pm_trm as (x1 ... xn) "spat1 ... spatn"` : elimination of
  existential quantifiers using Coq introduction patterns `x1 ... xn` and
  elimination of object level connectives using the proof mode introduction
  patterns `ipat1 ... ipatn`.
- `iDestruct pm_trm as %cpat` : elimination of a pure hypothesis using the Coq
  introduction pattern `cpat`.

Separating logic specific tactics
---------------------------------

- `iFrame "H0 ... Hn"` : cancel the hypotheses `H0 ... Hn` in the goal. 
- `iCombine "H1" "H2" as "H"` : turns `H1 : P1` and `H2 : P2` into
  `H : P1 ★ P2`.

The later modality
------------------
- `iNext` : introduce a later by stripping laters from all hypotheses.
- `iLöb (x1 ... xn) as "IH"` : perform Löb induction by generalizing over the
  Coq level variables `x1 ... xn` and the entire spatial context.

Rewriting
---------

- `iRewrite pm_trm` : rewrite an equality in the conclusion.
- `iRewrite pm_trm in "H"` : rewrite an equality in the hypothesis `H`.

Iris
----

- `iPvsIntro` : introduction of a primitive view shift. Generates a goal if
  the masks are not syntactically equal.
- `iPvs pm_trm as (x1 ... xn) "ipat"` : runs a primitive view shift `pm_trm`.
- `iInv N as (x1 ... xn) "ipat"` : open the invariant `N`.
- `iInv> N as (x1 ... xn) "ipat"` : open the invariant `N` and establish that
  it is timeless so no laters have to be added.
- `iTimeless "H"` : strip a later of a timeless hypotheses `H` in case the
  conclusion is a primitive view shifts or weakest precondition.

Miscellaneous
-------------

- The tactic `done` is extended so that it also performs `iAssumption` and
  introduces pure connectives.
- The proof mode adds hints to the core `eauto` database so that `eauto`
  automatically introduces: conjunctions and disjunctions, universal and
  existential quantifiers, implications and wand, always and later modalities,
  primitive view shifts, and pure connectives.

Introduction patterns
=====================

Introduction patterns are used to perform introductions and eliminations of
multiple connectives on the fly. The proof mode supports the following
introduction patterns:

- `H` : create a hypothesis named H.
- `?` : create an anonymous hypothesis.
- `_` : remove the hypothesis.
- `$` : frame the hypothesis in the goal.
- `# ipat` : move the hypothesis to the persistent context.
- `%` : move the hypothesis to the pure Coq context (anonymously).
- `[ipat ipat]` : (separating) conjunction elimination.
- `[ipat|ipat]` : disjunction elimination.
- `[]` : false elimination.

Apart from this, there are the following introduction patterns that can only
appear at the top level:

- `!` : introduce a box (provided that the spatial context is empty).
- `>` : introduce a later (which strips laters from all hypotheses).
- `{H1 ... Hn}` : clear `H1 ... Hn`.
- `{$H1 ... $Hn}` : frame `H1 ... Hn` (this pattern can be mixed with the
  previous pattern, e.g., `{$H1 H2 $H3}`).
- `/=` : perform `simpl`.
- `*` : introduce all universal quantifiers.
- `**` : introduce all universal quantifiers, as well as all arrows and wands.

For example, given:

        ∀ x, x = 0 ⊢ □ (P → False ∨ □ (Q ∧ ▷ R) -★ P ★ ▷ (R ★ Q ∧ x = pred 2)).

You can write

        iIntros (x) "% ! $ [[] | #[HQ HR]] /= >".

which results in:

        x : nat
        H : x = 0
        ______________________________________(1/1)
        "HQ" : Q
        "HR" : R
        --------------------------------------□
        R ★ Q ∧ x = 1


Specialization patterns
=======================

Since we are reasoning in a spatial logic, when eliminating a lemma or
hypotheses of type ``P_0 -★ ... -★ P_n -★ R`` one has to specify how the
hypotheses are split between the premises. The proof mode supports the following
so called specification patterns to express this splitting:

- `H` : use the hypothesis `H` (it should match the premise exactly). If `H` is
  spatial, it will be consumed.
- `[H1 ... Hn]` : generate a goal with the spatial hypotheses `H1 ... Hn` and
  all persistent hypotheses. The hypotheses `H1 ... Hn` will be consumed.
- `[-H1 ... Hn]`  : negated form of the above pattern
- `=>[H1 ... Hn]` : same as the above pattern, but can only be used if the goal
  is a primitive view shift, in which case the view shift will be kept in the
  goal of the premise too.
- `[#]` : This pattern can be used when eliminating `P -★ Q` when either `P` or
  `Q` is persistent. In this case, all hypotheses are available in the goal for
  the premise as none will be consumed.
- `[%]` : This pattern can be used when eliminating `P -★ Q` when `P` is pure.
  It will generate a Coq goal for `P` and does not consume any hypotheses.
- `*` : instantiate all top-level universal quantifiers with meta variables.

For example, given:

        H : □ P -★ P 2 -★ x = 0 -★ Q1 ∗ Q2

You can write:

        iDestruct ("H" with "[#] [H1 H2] [%]") as "[H4 H5]".

Proof mode terms
================

Many of the proof mode tactics (such as `iDestruct`, `iApply`, `iRewrite`) can
take both hypotheses and lemmas, and allow one to instantiate universal
quantifiers and implications/wands of these hypotheses/lemmas on the fly.

The syntax for the arguments of these tactics, called _proof mode terms_, is:

        (H $! t1 ... tn with "spat1 .. spatn")

Here, `H` can be both a hypothesis, as well as a Coq lemma whose conclusion is
of the shape `P ⊢ Q`. In the above, `t1 ... tn` are arbitrary Coq terms used
for instantiation of universal quantifiers, and `spat1 .. spatn` are
specialization patterns to eliminate implications and wands.

Proof mode terms can be written down using the following short hands too:

        (H with "spat1 .. spatn")
        (H $! t1 ... tn)
        H

