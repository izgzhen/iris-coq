From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
Set Default Proof Using "Type".

Section tests.
Context {M : ucmraT}.
Lemma demo_0 (P Q : uPred M) :
  □ (P ∨ Q) -∗ (∀ x, ⌜x = 0⌝ ∨ ⌜x = 1⌝) → (Q ∨ P).
Proof.
  iIntros "#H #H2".
  (* should remove the disjunction "H" *)
  iDestruct "H" as "[?|?]"; last by iLeft.
  (* should keep the disjunction "H" because it is instantiated *)
  iDestruct ("H2" $! 10) as "[%|%]". done. done.
Qed.

Lemma demo_1 (P1 P2 P3 : nat → uPred M) :
  (∀ (x y : nat) a b,
    x ≡ y →
    □ (uPred_ownM (a ⋅ b) -∗
    (∃ y1 y2 c, P1 ((x + y1) + y2) ∧ True ∧ □ uPred_ownM c) -∗
    □ ▷ (∀ z, P2 z ∨ True → P2 z) -∗
    ▷ (∀ n m : nat, P1 n → □ ((True ∧ P2 n) → □ (⌜n = n⌝ ↔ P3 n))) -∗
    ▷ ⌜x = 0⌝ ∨ ∃ x z, ▷ P3 (x + z) ∗ uPred_ownM b ∗ uPred_ownM (core b)))%I.
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
  iApply ("H3" $! _ 0 with "[$]").
  - iSplit. done. iApply "H2". iLeft. iApply "H2". by iRight.
  - done.
Qed.

Lemma demo_2 (P1 P2 P3 P4 Q : uPred M) (P5 : nat → uPredC M):
  P2 ∗ (P3 ∗ Q) ∗ True ∗ P1 ∗ P2 ∗ (P4 ∗ (∃ x:nat, P5 x ∨ P3)) ∗ True -∗
    P1 -∗ (True ∗ True) -∗
  (((P2 ∧ False ∨ P2 ∧ ⌜0 = 0⌝) ∗ P3) ∗ Q ∗ P1 ∗ True) ∧
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

Lemma demo_3 (P1 P2 P3 : uPred M) :
  P1 ∗ P2 ∗ P3 -∗ ▷ P1 ∗ ▷ (P2 ∗ ∃ x, (P3 ∧ ⌜x = 0⌝) ∨ P3).
Proof. iIntros "($ & $ & H)". iFrame "H". iNext. by iExists 0. Qed.

Definition foo (P : uPred M) := (P → P)%I.
Definition bar : uPred M := (∀ P, foo P)%I.

Lemma demo_4 : True -∗ bar.
Proof. iIntros. iIntros (P) "HP //". Qed.

Lemma demo_5 (x y : M) (P : uPred M) :
  (∀ z, P → z ≡ y) -∗ (P -∗ (x,x) ≡ (y,x)).
Proof.
  iIntros "H1 H2".
  iRewrite (uPred.internal_eq_sym x x with "[# //]").
  iRewrite -("H1" $! _ with "[- //]").
  done.
Qed.

Lemma demo_6 (P Q : uPred M) :
  (∀ x y z : nat,
    ⌜x = plus 0 x⌝ → ⌜y = 0⌝ → ⌜z = 0⌝ → P → □ Q → foo (x ≡ x))%I.
Proof.
  iIntros (a) "*".
  iIntros "#Hfoo **".
  iIntros "# _ //".
Qed.

Lemma demo_7 (P Q1 Q2 : uPred M) : P ∗ (Q1 ∧ Q2) -∗ P ∗ Q1.
Proof. iIntros "[H1 [H2 _]]". by iFrame. Qed.

Section iris.
  Context `{invG Σ}.
  Implicit Types E : coPset.
  Implicit Types P Q : iProp Σ.

  Lemma demo_8 N E P Q R :
    ↑N ⊆ E →
    (True -∗ P -∗ inv N Q -∗ True -∗ R) -∗ P -∗ ▷ Q ={E}=∗ R.
  Proof.
    iIntros (?) "H HP HQ".
    iApply ("H" with "[% //] [$] [> HQ] [> //]").
    by iApply inv_alloc.
  Qed.
End iris.

Lemma demo_9 (x y z : M) :
  ✓ x → ⌜y ≡ z⌝ -∗ (✓ x ∧ ✓ x ∧ y ≡ z : uPred M).
Proof. iIntros (Hv) "Hxy". by iFrame (Hv Hv) "Hxy". Qed.

Lemma demo_10 (P Q : uPred M) : P -∗ Q -∗ True.
Proof.
  iIntros "HP HQ".
  iAssert True%I as "#_". { by iClear "HP HQ". }
  iAssert True%I with "[HP]" as "#_". { Fail iClear "HQ". by iClear "HP". }
  iAssert True%I as %_. { by iClear "HP HQ". }
  iAssert True%I with "[HP]" as %_. { Fail iClear "HQ". by iClear "HP". }
  done.
Qed.

Lemma demo_11 (P Q R : uPred M) :
  (P -∗ True -∗ True -∗ Q -∗ R) -∗ P -∗ Q -∗ R.
Proof. iIntros "H HP HQ". by iApply ("H" with "[$]"). Qed.

(* Check coercions *)
Lemma demo_12 (P : Z → uPred M) : (∀ x, P x) -∗ ∃ x, P x.
Proof. iIntros "HP". iExists (0:nat). iApply ("HP" $! (0:nat)). Qed.

Lemma demo_13 (P : uPred M) : (|==> False) -∗ |==> P.
Proof. iIntros. iAssert False%I with "[> - //]" as %[]. Qed.

Lemma demo_14 (P : uPred M) : False -∗ P.
Proof. iIntros "H". done. Qed.

(* Check instantiation and dependent types *)
Lemma demo_15 (P : ∀ n, vec nat n → uPred M) :
  (∀ n v, P n v) -∗ ∃ n v, P n v.
Proof.
  iIntros "H". iExists _, [#10].
  iSpecialize ("H" $! _ [#10]). done.
Qed.

Lemma demo_16 (P Q R : uPred M) `{!PersistentP R} :
  P -∗ Q -∗ R -∗ R ∗ Q ∗ P ∗ R ∨ False.
Proof. eauto with iFrame. Qed.

Lemma demo_17 (P Q R : uPred M) `{!PersistentP R} :
  P -∗ Q -∗ R -∗ R ∗ Q ∗ P ∗ R ∨ False.
Proof. iIntros "HP HQ #HR". iCombine "HR HQ HP HR" as "H". auto. Qed.

Lemma test_iNext_evar (P : uPred M) :
  P -∗ True.
Proof.
  iIntros "HP". iAssert (▷ _ -∗ ▷ P)%I as "?"; last done.
  iIntros "?". iNext. iAssumption.
Qed.

Lemma test_iNext_sep1 (P Q : uPred M)
    (R1 := (P ∗ Q)%I) (R2 := (▷ P ∗ ▷ Q)%I) :
  (▷ P ∗ ▷ Q) ∗ R1 ∗ R2 -∗ ▷ (P ∗ Q) ∗ ▷ R1 ∗ R2.
Proof.
  iIntros "H". iNext.
  rewrite {1 2}(lock R1). (* check whether R1 has not been unfolded *) done.
Qed.

Lemma test_iNext_sep2 (P Q : uPred M) :
  ▷ P ∗ ▷ Q -∗ ▷ (P ∗ Q).
Proof.
  iIntros "H". iNext. iExact "H". (* Check that the laters are all gone. *)
Qed.

Lemma test_frame_persistent (P Q : uPred M) :
  □ P -∗ Q -∗ □ (P ∗ P) ∗ (P ∧ Q ∨ Q).
Proof. iIntros "#HP". iFrame "HP". iIntros "$". Qed.

Lemma test_split_box (P Q : uPred M) :
  □ P -∗ □ (P ∗ P).
Proof. iIntros "#?". by iSplit. Qed.

Lemma test_specialize_persistent (P Q : uPred M) :
  □ P -∗ (□ P -∗ Q) -∗ Q.
Proof. iIntros "#HP HPQ". by iSpecialize ("HPQ" with "HP"). Qed.
End tests.
