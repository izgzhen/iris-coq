From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap.
Set Default Proof Using "Type".

Section tests.
Context {M : ucmraT}.
Implicit Types P Q R : uPred M.

Lemma demo_0 P Q : □ (P ∨ Q) -∗ (∀ x, ⌜x = 0⌝ ∨ ⌜x = 1⌝) → (Q ∨ P).
Proof.
  iIntros "###H #H2".
  (* should remove the disjunction "H" *)
  iDestruct "H" as "[#?|#?]"; last by iLeft.
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
  iRevert (a b) "Ha Hb". iIntros (b a) "? {foo} Ha".
  iAssert (uPred_ownM (a ⋅ core a)) with "[Ha]" as "[Ha #Hac]".
  { by rewrite cmra_core_r. }
  iIntros "{$Hac $Ha}".
  iExists (S j + z1), z2.
  iNext.
  iApply ("H3" $! _ 0 with "[$]").
  - iSplit. done. iApply "H2". iLeft. iApply "H2". by iRight.
  - done.
Qed.

Lemma demo_2 P1 P2 P3 P4 Q (P5 : nat → uPredC M):
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

Lemma demo_3 P1 P2 P3 :
  P1 ∗ P2 ∗ P3 -∗ ▷ P1 ∗ ▷ (P2 ∗ ∃ x, (P3 ∧ ⌜x = 0⌝) ∨ P3).
Proof. iIntros "($ & $ & H)". iFrame "H". iNext. by iExists 0. Qed.

Definition foo (P : uPred M) := (P → P)%I.
Definition bar : uPred M := (∀ P, foo P)%I.

Lemma test_unfold_constants : True -∗ bar.
Proof. iIntros. iIntros (P) "HP //". Qed.

Lemma test_iRewrite (x y : M) P :
  (∀ z, P → z ≡ y) -∗ (P -∗ (x,x) ≡ (y,x)).
Proof.
  iIntros "H1 H2".
  iRewrite (uPred.internal_eq_sym x x with "[# //]").
  iRewrite -("H1" $! _ with "[- //]").
  done.
Qed.

Lemma test_iIntros_persistent P Q `{!Persistent Q} : (P → Q → P ∗ Q)%I.
Proof. iIntros "H1 H2". by iFrame. Qed.

Lemma test_iIntros_pure (ψ φ : Prop) P : ψ → (⌜ φ ⌝ → P → ⌜ φ ∧ ψ ⌝ ∧ P)%I.
Proof. iIntros (??) "H". auto. Qed.

Lemma test_fast_iIntros P Q :
  (∀ x y z : nat,
    ⌜x = plus 0 x⌝ → ⌜y = 0⌝ → ⌜z = 0⌝ → P → □ Q → foo (x ≡ x))%I.
Proof.
  iIntros (a) "*".
  iIntros "#Hfoo **".
  iIntros "# _ //".
Qed.

Lemma test_very_fast_iIntros P :
  ∀ x y : nat, ⌜ x = y ⌝ -∗ P -∗ P.
Proof. by iIntros. Qed.

Lemma test_iDestruct_spatial_and P Q1 Q2 : P ∗ (Q1 ∧ Q2) -∗ P ∗ Q1.
Proof. iIntros "[H [? _]]". by iFrame. Qed.

Lemma test_iFrame_pure (x y z : M) :
  ✓ x → ⌜y ≡ z⌝ -∗ (✓ x ∧ ✓ x ∧ y ≡ z : uPred M).
Proof. iIntros (Hv) "Hxy". by iFrame (Hv Hv) "Hxy". Qed.

Lemma test_iFrame_disjunction_1 P1 P2 Q1 Q2 :
  □ P1 -∗ Q2 -∗ P2 -∗ (P1 ∗ P2 ∗ False ∨ P2) ∗ (Q1 ∨ Q2).
Proof. iIntros "#HP1 HQ2 HP2". iFrame "HP1 HQ2 HP2". Qed.
Lemma test_iFrame_disjunction_2 P : P -∗ (True ∨ True) ∗ P.
Proof. iIntros "HP". iFrame "HP". auto. Qed.

Lemma test_iAssert_persistent P Q : P -∗ Q -∗ True.
Proof.
  iIntros "HP HQ".
  iAssert True%I as "#_". { by iClear "HP HQ". }
  iAssert True%I with "[HP]" as "#_". { Fail iClear "HQ". by iClear "HP". }
  iAssert True%I as %_. { by iClear "HP HQ". }
  iAssert True%I with "[HP]" as %_. { Fail iClear "HQ". by iClear "HP". }
  done.
Qed.

Lemma test_iSpecialize_auto_frame P Q R :
  (P -∗ True -∗ True -∗ Q -∗ R) -∗ P -∗ Q -∗ R.
Proof. iIntros "H ? HQ". by iApply ("H" with "[$]"). Qed.

(* Check coercions *)
Lemma test_iExist_coercion (P : Z → uPred M) : (∀ x, P x) -∗ ∃ x, P x.
Proof. iIntros "HP". iExists (0:nat). iApply ("HP" $! (0:nat)). Qed.

Lemma test_iExist_tc `{Collection A C} P : (∃ x1 x2 : gset positive, P -∗ P)%I.
Proof. iExists {[ 1%positive ]}, ∅. auto. Qed.

Lemma test_iSpecialize_tc P : (∀ x y z : gset positive, P) -∗ P.
Proof. iIntros "H". iSpecialize ("H" $! ∅ {[ 1%positive ]} ∅). done. Qed.

Lemma test_iAssert_modality P : (|==> False) -∗ |==> P.
Proof. iIntros. iAssert False%I with "[> - //]" as %[]. Qed.

Lemma test_iAssumption_False P : False -∗ P.
Proof. iIntros "H". done. Qed.

(* Check instantiation and dependent types *)
Lemma test_iSpecialize_dependent_type (P : ∀ n, vec nat n → uPred M) :
  (∀ n v, P n v) -∗ ∃ n v, P n v.
Proof.
  iIntros "H". iExists _, [#10].
  iSpecialize ("H" $! _ [#10]). done.
Qed.

Lemma test_eauto_iFrame P Q R `{!Persistent R} :
  P -∗ Q -∗ R -∗ R ∗ Q ∗ P ∗ R ∨ False.
Proof. eauto 10 with iFrame. Qed.

Lemma test_iCombine_persistent P Q R `{!Persistent R} :
  P -∗ Q -∗ R -∗ R ∗ Q ∗ P ∗ R ∨ False.
Proof. iIntros "HP HQ #HR". iCombine "HR HQ HP HR" as "H". auto. Qed.

Lemma test_iNext_evar P : P -∗ True.
Proof.
  iIntros "HP". iAssert (▷ _ -∗ ▷ P)%I as "?"; last done.
  iIntros "?". iNext. iAssumption.
Qed.

Lemma test_iNext_sep1 P Q
    (R1 := (P ∗ Q)%I) (R2 := (▷ P ∗ ▷ Q)%I) :
  (▷ P ∗ ▷ Q) ∗ R1 ∗ R2 -∗ ▷ (P ∗ Q) ∗ ▷ R1 ∗ R2.
Proof.
  iIntros "H". iNext.
  rewrite {1 2}(lock R1). (* check whether R1 has not been unfolded *) done.
Qed.

Lemma test_iNext_sep2 P Q : ▷ P ∗ ▷ Q -∗ ▷ (P ∗ Q).
Proof.
  iIntros "H". iNext. iExact "H". (* Check that the laters are all gone. *)
Qed.

Lemma test_iNext_quantifier (Φ : M → M → uPred M) :
  (∀ y, ∃ x, ▷ Φ x y) -∗ ▷ (∀ y, ∃ x, Φ x y).
Proof. iIntros "H". iNext. done. Qed.

Lemma test_iFrame_persistent (P Q : uPred M) :
  □ P -∗ Q -∗ □ (P ∗ P) ∗ (P ∧ Q ∨ Q).
Proof. iIntros "#HP". iFrame "HP". iIntros "$". Qed.

Lemma test_iSplit_persistently P Q : □ P -∗ □ (P ∗ P).
Proof. iIntros "#?". by iSplit. Qed.

Lemma test_iSpecialize_persistent P Q :
  □ P -∗ (□ P -∗ Q) -∗ Q.
Proof. iIntros "#HP HPQ". by iSpecialize ("HPQ" with "HP"). Qed.

Lemma test_iLöb P : (∃ n, ▷^n P)%I.
Proof.
  iLöb as "IH". iDestruct "IH" as (n) "IH".
  by iExists (S n).
Qed.

Lemma test_iInduction_wf (x : nat) P Q :
  □ P -∗ Q -∗ ⌜ (x + 0 = x)%nat ⌝.
Proof.
  iIntros "#HP HQ".
  iInduction (lt_wf x) as [[|x] _] "IH"; simpl; first done.
  rewrite (inj_iff S). by iApply ("IH" with "[%]"); first omega.
Qed.

Lemma test_iIntros_start_proof :
  (True : uPred M)%I.
Proof.
  (* Make sure iIntros actually makes progress and enters the proofmode. *)
  progress iIntros. done.
Qed.

Lemma test_True_intros : (True : uPred M) -∗ True.
Proof.
  iIntros "?". done.
Qed.

Lemma test_iPoseProof_let P Q :
  (let R := True%I in R ∗ P ⊢ Q) →
  P ⊢ Q.
Proof.
  iIntros (help) "HP".
  iPoseProof (help with "[$HP]") as "?". done.
Qed.

Lemma test_iIntros_let P :
  ∀ Q, let R := True%I in P -∗ R -∗ Q -∗ P ∗ Q.
Proof. iIntros (Q R) "$ HR $". Qed.

Lemma test_iIntros_modalities P :
  (□ ▷ ∀ x : nat, ⌜ x = 0 ⌝ -∗ ⌜ x = 0 ⌝ → False -∗ P -∗ P)%I.
Proof.
  iIntros (x ??).
  iIntros "* **". (* Test that fast intros do not work under modalities *)
  iIntros ([]).
Qed.

Lemma test_iIntros_rewrite P (x1 x2 x3 x4 : nat) :
  x1 = x2 → (⌜ x2 = x3 ⌝ ∗ ⌜ x3 ≡ x4 ⌝ ∗ P) -∗ ⌜ x1 = x4 ⌝ ∗ P.
Proof. iIntros (?) "(-> & -> & $)"; auto. Qed.

(* A bunch of test cases from #127 to establish that tactics behave the same on
`⌜ φ ⌝ → P` and `∀ _ : φ, P` *)
Lemma test_forall_nondep_1 (φ : Prop) :
  φ → (∀ _ : φ, False : uPred M) -∗ False.
Proof. iIntros (Hφ) "Hφ". by iApply "Hφ". Qed.
Lemma test_forall_nondep_2 (φ : Prop) :
  φ → (∀ _ : φ, False : uPred M) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" with "[% //]"). done. Qed.
Lemma test_forall_nondep_3 (φ : Prop) :
  φ → (∀ _ : φ, False : uPred M) -∗ False.
Proof. iIntros (Hφ) "Hφ". unshelve iSpecialize ("Hφ" $! _). done. done. Qed.
Lemma test_forall_nondep_4 (φ : Prop) :
  φ → (∀ _ : φ, False : uPred M) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" $! Hφ); done. Qed.

Lemma test_pure_impl_1 (φ : Prop) :
  φ → (⌜φ⌝ → False : uPred M) -∗ False.
Proof. iIntros (Hφ) "Hφ". by iApply "Hφ". Qed.
Lemma test_pure_impl_2 (φ : Prop) :
  φ → (⌜φ⌝ → False : uPred M) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" with "[% //]"). done. Qed.
Lemma test_pure_impl_3 (φ : Prop) :
  φ → (⌜φ⌝ → False : uPred M) -∗ False.
Proof. iIntros (Hφ) "Hφ". unshelve iSpecialize ("Hφ" $! _). done. done. Qed.
Lemma test_pure_impl_4 (φ : Prop) :
  φ → (⌜φ⌝ → False : uPred M) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" $! Hφ). done. Qed.

Lemma test_forall_nondep_impl2 (φ : Prop) P :
  φ → P -∗ (∀ _ : φ, P -∗ False : uPred M) -∗ False.
Proof.
  iIntros (Hφ) "HP Hφ".
  Fail iSpecialize ("Hφ" with "HP").
  iSpecialize ("Hφ" with "[% //] HP"). done.
Qed.

Lemma test_pure_impl2 (φ : Prop) P :
  φ → P -∗ (⌜φ⌝ → P -∗ False : uPred M) -∗ False.
Proof.
  iIntros (Hφ) "HP Hφ".
  Fail iSpecialize ("Hφ" with "HP").
  iSpecialize ("Hφ" with "[% //] HP"). done.
Qed.

Lemma test_iNext_laterN_later P n : ▷ ▷^n P ⊢ ▷^n ▷ P.
Proof. iIntros "H". iNext. by iNext. Qed.
Lemma test_iNext_later_laterN P n : ▷^n ▷ P ⊢ ▷ ▷^n P.
Proof. iIntros "H". iNext. by iNext. Qed.
Lemma test_iNext_laterN_laterN P n1 n2 : ▷ ▷^n1 ▷^n2 P ⊢ ▷^n1 ▷^n2 ▷ P.
Proof. iIntros "H". iNext. iNext. by iNext. Qed.

Lemma test_iEval x y : ⌜ (y + x)%nat = 1 ⌝ -∗ ⌜ S (x + y) = 2%nat ⌝ : uPred M.
Proof.
  iIntros (H).
  iEval (rewrite (Nat.add_comm x y) // H).
  done.
Qed.

(* TODO: This test is broken in Coq 8.6. Should be restored once we drop Coq
8.6 support. See also issue #108. *)
(*
Lemma test_iIntros_pure : (⌜ ¬False ⌝ : uPred M)%I.
Proof. by iIntros (?). Qed.
*)
End tests.

Section more_tests.
  Context `{invG Σ}.
  Implicit Types P Q R : iProp Σ.

  Lemma test_masks  N E P Q R :
    ↑N ⊆ E →
    (True -∗ P -∗ inv N Q -∗ True -∗ R) -∗ P -∗ ▷ Q ={E}=∗ R.
  Proof.
    iIntros (?) "H HP HQ".
    iApply ("H" with "[% //] [$] [> HQ] [> //]").
    by iApply inv_alloc.
  Qed.
End more_tests.
