From iris.proofmode Require Import tactics.

Lemma demo_1 (M : cmraT) (P1 P2 P3 : nat → uPred M) :
  True ⊢ (∀ (x y : nat) a b,
    x ≡ y →
    □ (uPred_ownM (a ⋅ b) -★
    (∃ y1 y2 c, P1 ((x + y1) + y2) ∧ True ∧ □ uPred_ownM c) -★
    ▷ (∀ z, P2 z) -★
    ▷ (∀ n m : nat, P1 n → □ ((True ∧ P2 n) → □ (n = n ↔ P3 n))) -★
    ▷ (x = 0) ∨ ∃ x z, ▷ P3 (x + z) ★ uPred_ownM b ★ uPred_ownM (core b))).
Proof.
  iIntros {i [|j] a b ?} "! [Ha Hb] H1 H2 H3"; setoid_subst.
  { iLeft. by iNext. }
  iRight.
  iDestruct "H1" as {z1 z2 c} "(H1&_&#Hc)".
  iRevert {a b} "Ha Hb". iIntros {b a} "Hb Ha".
  iAssert (uPred_ownM (a ⋅ core a))%I as "[Ha #Hac]" with "[Ha]".
  { by rewrite cmra_core_r. }
  iFrame "Ha Hac".
  iExists (S j + z1), z2.
  iNext.
  iApply "H3" { _ 0 } "H1 ! [H2] !".
  - iSplit. done. iApply "H2".
  - done.
Qed.

Lemma demo_2 (M : cmraT) (P1 P2 P3 P4 Q : uPred M) (P5 : nat → uPredC M):
    (P2 ★ (P3 ★ Q) ★ True ★ P1 ★ P2 ★ (P4 ★ (∃ x:nat, P5 x ∨ P3)) ★ True)
  ⊢ (P1 -★ (True ★ True) -★ (((P2 ∧ False ∨ P2 ∧ 0 = 0) ★ P3) ★ Q ★ P1 ★ True) ∧
     (P2 ∨ False) ∧ (False → P5 0)).
Proof.
  (* Intro-patterns do something :) *)
  iIntros "[H2 ([H3 HQ]&?&H1&H2'&foo&_)] ? [??]".
  (* To test destruct: can also be part of the intro-pattern *)
  iDestruct "foo" as "[_ meh]".
  repeat iSplit; [|by iLeft|iIntros "#[]"].
  iFrame "H2".
  (* split takes a list of hypotheses just for the LHS *)
  iSplitL "H3".
  * iFrame "H3". by iRight.
  * iSplitL "HQ". iAssumption. by iSplitL "H1".
Qed.

Lemma demo_3 (M : cmraT) (P1 P2 P3 : uPred M) :
  (P1 ★ P2 ★ P3) ⊢ (▷ P1 ★ ▷ (P2 ★ ∃ x, (P3 ∧ x = 0) ∨ P3)).
Proof. iIntros "($ & $ & H)". iFrame "H". simpl. iNext. by iExists 0. Qed.