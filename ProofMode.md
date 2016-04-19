The proof mode has the following major features:

=== Intro patterns ===

Similar to Coq's intro tactic, the Iris iIntros tactic can take a list of intro patterns to perform destructions on the fly. Apart from the standard intro patterns (like "?" for creating an anonymous hypothesis, "[p p]" for eliminating a (separating) conjunction, "[p|p]" for eliminating a disjunction, and "[]" for eliminating False, it supports:

  # pat   :  move the hypothesis to the persistent context
  %       :  move the hypothesis to the pure Coq context
             as an anonymous assumption
  !       :  introduce a box (this pattern can only appear at the
             to-level, and can be used only if the spatial context
             is empty)

So, for example, given:

  ∀ x, x = 0 → □ (P → □ (Q ∧ ▷ R) -★ ▷ (P ★ R ★ Q ∧ x = 0))

You can write: iIntros {x} "% ! HP #[HQ HR]", which results in:

  H : x = 0
  ______________________________________(1/1)
​​​  "HQ" : Q
  "HR" : ▷ R
  --------------------------------------□
​​  "HP" : P
  --------------------------------------★
  ▷ (P ★ R ★ Q ∧ x = 0)

(Syntax subject to improvements :))

(Due to limitations of Ltac, introductions for universal quantifiers always have to appear at the beginning and cannot be mixed).


=== Extensibility ===

The destruction patterns "[p p]" and "[p|p]" do not just work for (separating) conjunctions and disjunctions. For example, when having:

  "H" : l ↦{q} v

You can write iDestruct "H" as "[H1 H2]" to split the fractional maps to connective into:

  "H1" : l ↦{q/2} v
  "H2" : l ↦{q/2} v

The proof mode can be extended using type classes to support all kinds of "destructable" connectives.

I am using type classes for extensibility in many places. The core proof mode thus works for uPred M with any cmra M, and is not tied to the entire Iris logic.


=== Later ===

The proof mode has a tactic iNext to introduce a later. This tactic will remove a later in the conclusion, and removes laters in all hypotheses. In the above example, when having:

​​​  "HQ" : Q
  "HR" : ▷ R
  --------------------------------------□
​​  "HP" : P
  --------------------------------------★
  ▷ (P ★ R ★ Q ∧ x = 0)

The tactic iNext will remove the later in HR and in the goal. All other hypotheses are left as if. The iNext tactic is extensible; my means of declaring appropriate type class instances you can also make it strip laters below certain connectives (like below ★).

Apart from that, tactics like iDestruct are able to distribute laters. So, when having:

  H : ▷ (P ★ Q)

iDestruct will turn it into H1 : ▷ P and H2 ▷ Q. This can of course be tweaked by declaring type class instances.


=== Separating conjunction and framing ===

When proving a separating conjunction P ★ Q, one has to split the spatial hypotheses. The Iris tactics iSplitL and iSplitR take a list of hypotheses that have to be used to prove the conjunct on the left, respectively, the right, the goal for other other conjunct will have all remaining hypotheses.

Apart from that, there is the tactic iFrame which takes a list of hypotheses to frame in the goal. For example, having:

  "HQ" : Q
  "HR" : R
  --------------------------------------□
​​  "HP" : P
  --------------------------------------★
  P ★ R ★ Q ∧ x = 0

The tactic iFrame "HQ HP" will turn the goal into "R ★ x = 0". Note that persistent hypotheses are kept, only spatial hypotheses disappear. So in the example ,"HQ" is kept, but "HP" is gone, after framing.

The iFrame tactic is able to frame under quantifiers and primitive viewshifts. None of this is hard coded, but instead, the tactic can be extended by declaring appropriate type classes, for example, to make it frame under weakest precondition.


=== Apply and specialization patterns ===

Given an hypothesis that is an implication:

  ​​"H" : P_0 -★ ... -★ P_n -★ R

One cannot just "apply" this hypothesis (as in ordinary Coq) since we are in a spatial logic. So, when applying a lemma you have to specify which hypotheses are used for which premises. For this, Iris has the following, so called, specialization patterns:

  H            : use hypothesis H (it should match the premise exactly)
  [H1 ... Hn]  : use hypotheses H1 ... Hn
  -[H1 ... Hn] : use all hypotheses but H1 ... Hn
                 (you can write - instead of -[])
  #            : determine that the premise is persistent, in this
                 case all hypotheses can be used (and do not
                 disappear)

So, in the above you may write:

  iApply "H" "[H1 H2] # H3"

This means: create a goal with hypotheses H1 and H2 for the first premise, establish that the second premise is persistent and use all hypotheses for that one, and match the third premise with H3 exactly.

These specialization patterns can be used for many more tactics, for example, you can write:

  iDestruct "H" "spec_pattern" as "intro_pattern"
  iSpecialize "H" "spec_pattern"
  iPoseProof "H" "spec_pattern" as "H2"

I noticed that these specialization patterns are not enough, so there are even more. Take the following lemma:

  own_valid : ∀ γ a, own γ a ⊢ ✓ a

Given "H" : own γ a you may want to write:

  iPoseProof own_valid "H" as "Hvalid"

But in this case "H" will disappear (and you would loose information). So, there are also the following specialization patterns:

  H !     : use hypothesis H and establish that the range of
            the applied/specialized hypothesis/lemma is persistent
  - !     : dito, but generate a goal to prove the premise in which
            all hypotheses can be used.

So, in the above you can write:

   iPoseProof own_valid "H !" as "Hvalid"

(Yet again, suggestions for improvement of syntax are welcome, as well as a less ad-hoc solution).

Note that many tactics (like iDestruct, iSpecialize, iPoseProof) work for on both hypotheses and lemmas. These may be an entailments, equivalences, arrows, wands, or bi-implications.


=== View shifts ===

Many of the Iris tactics (such as iLeft and iRight for introducing disjunctions, iExists for introducing existential quantifiers, and iFrame for framing) work under primitive view shifts.

Next to that, there is the tactic iPvs that can be used to eliminate a primitive view shift (for example, to allocate ghost state or an invariant, or to perform frame preserving updates). The syntax is:

  iPvs "hyp" "spec_pattern" as "intro_pattern"

Allocating ghost state is as simple as:

  iPvs (own_alloc OneShotPending) as {γ} "Hγ".

Allocating an invariant is as simple as:

  iPvs (inv_alloc N _ (one_shot_inv γ l))
    "[Hl Hγ]" as "#HN".

This creates a goal in which you have to prove ▷ one_shot_inv γ l using the hypotheses Hl and Hγ. The as "#HN" moves the allocated invariant to the persistent context.

The iApply tactic also works under primitive viewshifts, so given:

  "H" : P -★ Q

The tactic iApply "H" will turn the goal |={E}=> Q into |={E}=> P (and gets rid of "H" depending on whether H is spatial or not).

Apart from that, I have implemented tactics:

+ iTimeless "H": to strip of a later of a timeless hypotheses (type classes are used to establish timelessness)
+ iPvsAssert P as "intro_pat" with "single_spec_pat": to assert a view shift and then eliminate it
+ iInv "N" as "intro_pat" : to open the invariant N

All of these tactics also work in case the goal is a weakest precondition. In fact, it works for any connective that is declared as a "frame shifting assertion" (an abstraction that Ralf came up with to characterize connectives around which you can view shift).


=== Symbolic execution ===

The proof mode has tactics:

  wp_store
  wp_alloc l as "Hl"
  wp_load
  wp_seq

to perform interactive symbolic execution (and similar for many of the programming language connectives). For example, to prove:

  WP let: "x" := ref InjL #0 in ... {{ Φ }}

The tactic wp_alloc l as "Hl" will generate a hypotheses "Hl" : l ↦ InjLV #0" and change the goal into:

 WP let: "x" := %l in ... {{ Φ }}

Apart from that, it strips laters (since we have performed a step). Next, the tactic wp_let will reduce the let binding (and once more, strip laters when possible).

Most of these tactics are improvements of the tactics that we already had, but are better integrated into the proof mode.

Notably, there is also the tactic:

  wp_apply lem "spec_pattern"

Which given a goal WP e {{ Φ }} will look for a redex on which lem matches, and uses the bind rule to apply the lemma. This tactic is very useful to use lemmas corresponding to specifications of earlier proven connectives (see heap_lang/lib/barrier/client.v for example).


=== Rewriting ===

We have an internalized equality in the logic (which is defined in the model in terms of the distance relation on COFEs). I have implemented the tactics iRewrite "Heq" and iRewrite "Heq" in "H" to rewrite using the internalized equality. These tactic heavily piggy back on the Coq setoid rewrite machinery to establish non-expansiveness of the connectives involved.


=== Error messages ===

I have put some effort in making the tactics of the proof mode generate sensible error messages (instead of just failing with some arbitrary error message from the underlying Coq tactic). This turned out to be pretty difficult due to Ltac's backtracking semantics (and most of all, many of its oddities...)


=== Implementation ===

The basic idea of the implementation is surprisingly simple. The proof mode is just syntactic sugar for a judgment:

  Δ_persistent ; Δ_spatial  ⊢  Q

(See the file proofmode/notation.v. Warning: it uses unicode whitespace characters to make pretty printing work).

The basic forms of all tactics are just Coq lemmas, for example, wand introduction corresponds to the following lemma:

  Lemma tac_wand_intro Δ Δ' i P Q :
    envs_app false (Esnoc Enil i P) Δ = Some Δ' →
    Δ' ⊢ Q →
    Δ ⊢ (P -★ Q).

Next to that, I am using Ltac and logic programming with type classes to tie everything together. The proof mode is implemented entirely in Coq and does not involve any OCaml plugins.
