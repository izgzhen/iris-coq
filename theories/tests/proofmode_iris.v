From iris.proofmode Require Import tactics.
From iris.base_logic Require Import proofmode lib.invariants.

Section base_logic_tests.
  Context {M : ucmraT}.
  Implicit Types P Q R : uPred M.

  Lemma test_random_stuff (P1 P2 P3 : nat → uPred M) :
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

  Lemma test_iFrame_pure (x y z : M) :
    ✓ x → ⌜y ≡ z⌝ -∗ (✓ x ∧ ✓ x ∧ y ≡ z : uPred M).
  Proof. iIntros (Hv) "Hxy". by iFrame (Hv) "Hxy". Qed.

  Lemma test_iAssert_modality P : (|==> False) -∗ |==> P.
  Proof. iIntros. iAssert False%I with "[> - //]" as %[]. Qed.
End base_logic_tests.

Section iris_tests.
  Context `{invG Σ}.

  Lemma test_masks  N E P Q R :
    ↑N ⊆ E →
    (True -∗ P -∗ inv N Q -∗ True -∗ R) -∗ P -∗ ▷ Q ={E}=∗ R.
  Proof.
    iIntros (?) "H HP HQ".
    iApply ("H" with "[% //] [$] [> HQ] [> //]").
    by iApply inv_alloc.
  Qed.
End iris_tests.
