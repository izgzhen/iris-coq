From iris.proofmode Require Import tactics.
From iris.program_logic Require Import invariants.

Lemma demo_0 {M : ucmraT} (P Q : uPred M) :
  □ (P ∨ Q) ⊢ (∀ x, x = 0 ∨ x = 1) → (Q ∨ P).
Proof.
  iIntros "#H #H2".
  (* should remove the disjunction "H" *)
  iDestruct "H" as "[?|?]"; last by iLeft.
  (* should keep the disjunction "H" because it is instantiated *)
  iDestruct ("H2" $! 10) as "[%|%]". done. done.
Qed.

Lemma demo_1 (M : ucmraT) (P1 P2 P3 : nat → uPred M) :
  True ⊢ ∀ (x y : nat) a b,
    x ≡ y →
    □ (uPred_ownM (a ⋅ b) -★
    (∃ y1 y2 c, P1 ((x + y1) + y2) ∧ True ∧ □ uPred_ownM c) -★
    □ ▷ (∀ z, P2 z ∨ True → P2 z) -★
    ▷ (∀ n m : nat, P1 n → □ ((True ∧ P2 n) → □ (n = n ↔ P3 n))) -★
    ▷ (x = 0) ∨ ∃ x z, ▷ P3 (x + z) ★ uPred_ownM b ★ uPred_ownM (core b)).
Proof.
  iIntros (i [|j] a b ?) "!# [Ha Hb] H1 #H2 H3"; setoid_subst.
  { iLeft. by iNext. }
  iRight.
  iDestruct "H1" as (z1 z2 c) "(H1&_&#Hc)".
  iPoseProof "Hc" as "foo".
  iRevert (a b) "Ha Hb". iIntros (b a) "Hb {foo} Ha".
  iAssert (uPred_ownM (a ⋅ core a)) with "[Ha]" as "[Ha #Hac]".
  { by rewrite cmra_core_r. }
  iIntros "{$Hac $Ha}".
  iExists (S j + z1), z2.
  iNext.
  iApply ("H3" $! _ 0 with "H1 []").
  - iSplit. done. iApply "H2". iLeft. iApply "H2". by iRight.
  - done.
Qed.

Lemma demo_2 (M : ucmraT) (P1 P2 P3 P4 Q : uPred M) (P5 : nat → uPredC M):
    P2 ★ (P3 ★ Q) ★ True ★ P1 ★ P2 ★ (P4 ★ (∃ x:nat, P5 x ∨ P3)) ★ True
  ⊢ P1 -★ (True ★ True) -★ (((P2 ∧ False ∨ P2 ∧ 0 = 0) ★ P3) ★ Q ★ P1 ★ True) ∧
     (P2 ∨ False) ∧ (False → P5 0).
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

Lemma demo_3 (M : ucmraT) (P1 P2 P3 : uPred M) :
  P1 ★ P2 ★ P3 ⊢ ▷ P1 ★ ▷ (P2 ★ ∃ x, (P3 ∧ x = 0) ∨ P3).
Proof. iIntros "($ & $ & H)". iFrame "H". iNext. by iExists 0. Qed.

Definition foo {M} (P : uPred M) := (P → P)%I.
Definition bar {M} : uPred M := (∀ P, foo P)%I.

Lemma demo_4 (M : ucmraT) : True ⊢ @bar M.
Proof. iIntros. iIntros (P) "HP". done. Qed.

Lemma demo_5 (M : ucmraT) (x y : M) (P : uPred M) :
  (∀ z, P → z ≡ y) ⊢ (P -★ (x,x) ≡ (y,x)).
Proof.
  iIntros "H1 H2".
  iRewrite (uPred.internal_eq_sym x x with "[#]"); first done.
  iRewrite -("H1" $! _ with "[-]"); first done.
  done.
Qed.

Lemma demo_6 (M : ucmraT) (P Q : uPred M) :
  True ⊢ ∀ x y z : nat,
    x = plus 0 x → y = 0 → z = 0 → P → □ Q → foo (x ≡ x).
Proof.
  iIntros (a) "*".
  iIntros "#Hfoo **".
  by iIntros "# _".
Qed.

Lemma demo_7 (M : ucmraT) (P Q1 Q2 : uPred M) : P ★ (Q1 ∧ Q2) ⊢ P ★ Q1.
Proof. iIntros "[H1 [H2 _]]". by iFrame. Qed.

Section iris.
  Context `{invG Σ}.
  Implicit Types E : coPset.
  Implicit Types P Q : iProp Σ.

  Lemma demo_8 N E P Q R :
    nclose N ⊆ E →
    (True -★ P -★ inv N Q -★ True -★ R) ⊢ P -★ ▷ Q ={E}=★ R.
  Proof.
    iIntros (?) "H HP HQ".
    iApply ("H" with "[#] HP >[HQ] >").
    - done.
    - by iApply inv_alloc.
    - done.
  Qed.
End iris.

Lemma demo_9 (M : ucmraT) (x y z : M) :
  ✓ x → ■ (y ≡ z) ⊢ (✓ x ∧ ✓ x ∧ y ≡ z : uPred M).
Proof. iIntros (Hv) "Hxy". by iFrame (Hv Hv) "Hxy". Qed.
