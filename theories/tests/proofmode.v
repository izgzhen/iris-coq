From iris.proofmode Require Import tactics.
From stdpp Require Import gmap.
Set Default Proof Using "Type".

Section tests.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.

Lemma demo_0 P Q : □ (P ∨ Q) -∗ (∀ x, ⌜x = 0⌝ ∨ ⌜x = 1⌝) → (Q ∨ P).
Proof.
  iIntros "H #H2". iDestruct "H" as "###H".
  (* should remove the disjunction "H" *)
  iDestruct "H" as "[#?|#?]"; last by iLeft.
  (* should keep the disjunction "H" because it is instantiated *)
  iDestruct ("H2" $! 10) as "[%|%]". done. done.
Qed.

Lemma demo_2 P1 P2 P3 P4 Q (P5 : nat → PROP) `{!Affine P4, !Absorbing P2} :
  P2 ∗ (P3 ∗ Q) ∗ True ∗ P1 ∗ P2 ∗ (P4 ∗ (∃ x:nat, P5 x ∨ P3)) ∗ emp -∗
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
  - iFrame "H3". iRight. auto.
  - iSplitL "HQ". iAssumption. by iSplitL "H1".
Qed.

Lemma demo_3 P1 P2 P3 :
  P1 ∗ P2 ∗ P3 -∗ P1 ∗ ▷ (P2 ∗ ∃ x, (P3 ∧ ⌜x = 0⌝) ∨ P3).
Proof. iIntros "($ & $ & $)". iNext. by iExists 0. Qed.

Definition foo (P : PROP) := (P -∗ P)%I.
Definition bar : PROP := (∀ P, foo P)%I.

Lemma test_unfold_constants : bar.
Proof. iIntros (P) "HP //". Qed.

Lemma test_iRewrite {A : ofeT} (x y : A) P :
  □ (∀ z, P -∗ <affine> (z ≡ y)) -∗ (P -∗ P ∧ (x,x) ≡ (y,x)).
Proof.
  iIntros "#H1 H2".
  iRewrite (bi.internal_eq_sym x x with "[# //]").
  iRewrite -("H1" $! _ with "[- //]").
  auto.
Qed.

Lemma test_iDestruct_and_emp P Q `{!Persistent P, !Persistent Q} :
  P ∧ emp -∗ emp ∧ Q -∗ <affine> (P ∗ Q).
Proof. iIntros "[#? _] [_ #?]". auto. Qed.

Lemma test_iIntros_persistent P Q `{!Persistent Q} : (P → Q → P ∧ Q)%I.
Proof. iIntros "H1 #H2". by iFrame. Qed.

Lemma test_iIntros_pure (ψ φ : Prop) P : ψ → (⌜ φ ⌝ → P → ⌜ φ ∧ ψ ⌝ ∧ P)%I.
Proof. iIntros (??) "H". auto. Qed.

Lemma test_iIntros_pure_not : (⌜ ¬False ⌝ : PROP)%I.
Proof. by iIntros (?). Qed.

Lemma test_fast_iIntros P Q :
  (∀ x y z : nat,
    ⌜x = plus 0 x⌝ → ⌜y = 0⌝ → ⌜z = 0⌝ → P → □ Q → foo (x ≡ x))%I.
Proof.
  iIntros (a) "*".
  iIntros "#Hfoo **".
  iIntros "_ //".
Qed.

Lemma test_very_fast_iIntros P :
  ∀ x y : nat, (⌜ x = y ⌝ → P -∗ P)%I.
Proof. by iIntros. Qed.

(** Prior to 0b84351c this used to loop, now `iAssumption` instantiates `R` with
`False` and performs false elimination. *)
Lemma test_iAssumption_evar_ex_false : ∃ R, R ⊢ ∀ P, P.
Proof. eexists. iIntros "?" (P). iAssumption. Qed.

Lemma test_iAssumption_affine P Q R `{!Affine P, !Affine R} : P -∗ Q -∗ R -∗ Q.
Proof. iIntros "H1 H2 H3". iAssumption. Qed.

Lemma test_iDestruct_spatial_and P Q1 Q2 : P ∗ (Q1 ∧ Q2) -∗ P ∗ Q1.
Proof. iIntros "[H [? _]]". by iFrame. Qed.

Lemma test_iAssert_persistent P Q : P -∗ Q -∗ True.
Proof.
  iIntros "HP HQ".
  iAssert True%I as "#_". { by iClear "HP HQ". }
  iAssert True%I with "[HP]" as "#_". { Fail iClear "HQ". by iClear "HP". }
  iAssert True%I as %_. { by iClear "HP HQ". }
  iAssert True%I with "[HP]" as %_. { Fail iClear "HQ". by iClear "HP". }
  done.
Qed.

Lemma test_iAssert_persistently P : □ P -∗ True.
Proof.
  iIntros "HP". iAssert (□ P)%I with "[# //]" as "#H". done.
Qed.

Lemma test_iSpecialize_auto_frame P Q R :
  (P -∗ True -∗ True -∗ Q -∗ R) -∗ P -∗ Q -∗ R.
Proof. iIntros "H ? HQ". by iApply ("H" with "[$]"). Qed.

Lemma test_iEmp_intro P Q R `{!Affine P, !Persistent Q, !Affine R} :
  P -∗ Q → R -∗ emp.
Proof. iIntros "HP #HQ HR". iEmpIntro. Qed.

(* Check coercions *)
Lemma test_iExist_coercion (P : Z → PROP) : (∀ x, P x) -∗ ∃ x, P x.
Proof. iIntros "HP". iExists (0:nat). iApply ("HP" $! (0:nat)). Qed.

Lemma test_iExist_tc `{Collection A C} P : (∃ x1 x2 : gset positive, P -∗ P)%I.
Proof. iExists {[ 1%positive ]}, ∅. auto. Qed.

Lemma test_iSpecialize_tc P : (∀ x y z : gset positive, P) -∗ P.
Proof.
  iIntros "H".
  (* FIXME: this [unshelve] and [apply _] should not be needed. *)
  unshelve iSpecialize ("H" $! ∅ {[ 1%positive ]} ∅); try apply _. done.
Qed.

Lemma test_iFrame_pure {A : ofeT} (φ : Prop) (y z : A) :
  φ → <affine> ⌜y ≡ z⌝ -∗ (⌜ φ ⌝ ∧ ⌜ φ ⌝ ∧ y ≡ z : PROP).
Proof. iIntros (Hv) "#Hxy". iFrame (Hv) "Hxy". Qed.

Lemma test_iFrame_disjunction_1 P1 P2 Q1 Q2 :
  BiAffine PROP →
  □ P1 -∗ Q2 -∗ P2 -∗ (P1 ∗ P2 ∗ False ∨ P2) ∗ (Q1 ∨ Q2).
Proof. intros ?. iIntros "#HP1 HQ2 HP2". iFrame "HP1 HQ2 HP2". Qed.
Lemma test_iFrame_disjunction_2 P : P -∗ (True ∨ True) ∗ P.
Proof. iIntros "HP". iFrame "HP". auto. Qed.

Lemma test_iFrame_conjunction_1 P Q :
  P -∗ Q -∗ (P ∗ Q) ∧ (P ∗ Q).
Proof. iIntros "HP HQ". iFrame "HP HQ". Qed.
Lemma test_iFrame_conjunction_2 P Q :
  P -∗ Q -∗ (P ∧ P) ∗ (Q ∧ Q).
Proof. iIntros "HP HQ". iFrame "HP HQ". Qed.

Lemma test_iAssert_modality P : ◇ False -∗ ▷ P.
Proof.
  iIntros "HF".
  iAssert (<affine> False)%I with "[> -]" as %[].
  by iMod "HF".
Qed.

Lemma test_iMod_affinely_timeless P `{!Timeless P} :
  <affine> ▷ P -∗ ◇ <affine> P.
Proof. iIntros "H". iMod "H". done. Qed.

Lemma test_iAssumption_False P : False -∗ P.
Proof. iIntros "H". done. Qed.

(* Check instantiation and dependent types *)
Lemma test_iSpecialize_dependent_type (P : ∀ n, vec nat n → PROP) :
  (∀ n v, P n v) -∗ ∃ n v, P n v.
Proof.
  iIntros "H". iExists _, [#10].
  iSpecialize ("H" $! _ [#10]). done.
Qed.

Lemma test_eauto_iFrame P Q R `{!Persistent R} :
  P -∗ Q -∗ R → R ∗ Q ∗ P ∗ R ∨ False.
Proof. eauto 10 with iFrame. Qed.

Lemma test_iCombine_persistent P Q R `{!Persistent R} :
  P -∗ Q -∗ R → R ∗ Q ∗ P ∗ R ∨ False.
Proof. iIntros "HP HQ #HR". iCombine "HR HQ HP HR" as "H". auto. Qed.

Lemma test_iNext_evar P : P -∗ True.
Proof.
  iIntros "HP". iAssert (▷ _ -∗ ▷ P)%I as "?"; last done.
  iIntros "?". iNext. iAssumption.
Qed.

Lemma test_iNext_sep1 P Q (R1 := (P ∗ Q)%I) :
  (▷ P ∗ ▷ Q) ∗ R1 -∗ ▷ ((P ∗ Q) ∗ R1).
Proof.
  iIntros "H". iNext.
  rewrite {1 2}(lock R1). (* check whether R1 has not been unfolded *) done.
Qed.

Lemma test_iNext_sep2 P Q : ▷ P ∗ ▷ Q -∗ ▷ (P ∗ Q).
Proof.
  iIntros "H". iNext. iExact "H". (* Check that the laters are all gone. *)
Qed.

Lemma test_iNext_quantifier {A} (Φ : A → A → PROP) :
  (∀ y, ∃ x, ▷ Φ x y) -∗ ▷ (∀ y, ∃ x, Φ x y).
Proof. iIntros "H". iNext. done. Qed.

Lemma test_iFrame_persistent (P Q : PROP) :
  □ P -∗ Q -∗ <pers> (P ∗ P) ∗ (P ∗ Q ∨ Q).
Proof. iIntros "#HP". iFrame "HP". iIntros "$". Qed.

Lemma test_iSplit_persistently P Q : □ P -∗ <pers> (P ∗ P).
Proof. iIntros "#?". by iSplit. Qed.

Lemma test_iSpecialize_persistent P Q : □ P -∗ (<pers> P → Q) -∗ Q.
Proof. iIntros "#HP HPQ". by iSpecialize ("HPQ" with "HP"). Qed.

Lemma test_iDestruct_persistent P (Φ : nat → PROP) `{!∀ x, Persistent (Φ x)}:
  □ (P -∗ ∃ x, Φ x) -∗
  P -∗ ∃ x, Φ x ∗ P.
Proof.
  iIntros "#H HP". iDestruct ("H" with "HP") as (x) "#H2". eauto with iFrame.
Qed.

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
  (True : PROP)%I.
Proof.
  (* Make sure iIntros actually makes progress and enters the proofmode. *)
  progress iIntros. done.
Qed.

Lemma test_True_intros : (True : PROP) -∗ True.
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
  ∀ Q, let R := emp%I in P -∗ R -∗ Q -∗ P ∗ Q.
Proof. iIntros (Q R) "$ _ $". Qed.

Lemma test_foo P Q : <affine> ▷ (Q ≡ P) -∗ <affine> ▷ Q -∗ <affine> ▷ P.
Proof.
  iIntros "#HPQ HQ !#". iNext. by iRewrite "HPQ" in "HQ".
Qed.

Lemma test_iIntros_modalities `(!Absorbing P) :
  (<pers> (▷ ∀  x : nat, ⌜ x = 0 ⌝ → ⌜ x = 0 ⌝ -∗ False -∗ P -∗ P))%I.
Proof.
  iIntros (x ??).
  iIntros "* **". (* Test that fast intros do not work under modalities *)
  iIntros ([]).
Qed.

Lemma test_iIntros_rewrite P (x1 x2 x3 x4 : nat) :
  x1 = x2 → (⌜ x2 = x3 ⌝ ∗ ⌜ x3 ≡ x4 ⌝ ∗ P) -∗ ⌜ x1 = x4 ⌝ ∗ P.
Proof. iIntros (?) "(-> & -> & $)"; auto. Qed.

Lemma test_iNext_affine P Q : <affine> ▷ (Q ≡ P) -∗ <affine> ▷ Q -∗ <affine> ▷ P.
Proof. iIntros "#HPQ HQ !#". iNext. by iRewrite "HPQ" in "HQ". Qed.

Lemma test_iAlways P Q R :
  □ P -∗ <pers> Q → R -∗ <pers> <affine> <affine> P ∗ □ Q.
Proof. iIntros "#HP #HQ HR". iSplitL. iAlways. done. iAlways. done. Qed.

(* A bunch of test cases from #127 to establish that tactics behave the same on
`⌜ φ ⌝ → P` and `∀ _ : φ, P` *)
Lemma test_forall_nondep_1 (φ : Prop) :
  φ → (∀ _ : φ, False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". by iApply "Hφ". Qed.
Lemma test_forall_nondep_2 (φ : Prop) :
  φ → (∀ _ : φ, False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" with "[% //]"). done. Qed.
Lemma test_forall_nondep_3 (φ : Prop) :
  φ → (∀ _ : φ, False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". unshelve iSpecialize ("Hφ" $! _). done. done. Qed.
Lemma test_forall_nondep_4 (φ : Prop) :
  φ → (∀ _ : φ, False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" $! Hφ); done. Qed.

Lemma test_pure_impl_1 (φ : Prop) :
  φ → (⌜φ⌝ → False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". by iApply "Hφ". Qed.
Lemma test_pure_impl_2 (φ : Prop) :
  φ → (⌜φ⌝ → False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" with "[% //]"). done. Qed.
Lemma test_pure_impl_3 (φ : Prop) :
  φ → (⌜φ⌝ → False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". unshelve iSpecialize ("Hφ" $! _). done. done. Qed.
Lemma test_pure_impl_4 (φ : Prop) :
  φ → (⌜φ⌝ → False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" $! Hφ). done. Qed.

Lemma test_forall_nondep_impl2 (φ : Prop) P :
  φ → P -∗ (∀ _ : φ, P -∗ False : PROP) -∗ False.
Proof.
  iIntros (Hφ) "HP Hφ".
  Fail iSpecialize ("Hφ" with "HP").
  iSpecialize ("Hφ" with "[% //] HP"). done.
Qed.

Lemma test_pure_impl2 (φ : Prop) P :
  φ → P -∗ (⌜φ⌝ → P -∗ False : PROP) -∗ False.
Proof.
  iIntros (Hφ) "HP Hφ".
  Fail iSpecialize ("Hφ" with "HP").
  iSpecialize ("Hφ" with "[% //] HP"). done.
Qed.

Lemma test_iNext_laterN_later P n : ▷ ▷^n P -∗ ▷^n ▷ P.
Proof. iIntros "H". iNext. by iNext. Qed.
Lemma test_iNext_later_laterN P n : ▷^n ▷ P -∗ ▷ ▷^n P.
Proof. iIntros "H". iNext. by iNext. Qed.
Lemma test_iNext_plus_1 P n1 n2 : ▷ ▷^n1 ▷^n2 P -∗ ▷^n1 ▷^n2 ▷ P.
Proof. iIntros "H". iNext. iNext. by iNext. Qed.
Lemma test_iNext_plus_2 P n m : ▷^n ▷^m P -∗ ▷^(n+m) P.
Proof. iIntros "H". iNext. done. Qed.
Lemma test_iNext_plus_3 P Q n m k :
  ▷^m ▷^(2 + S n + k) P -∗ ▷^m ▷ ▷^(2 + S n) Q -∗ ▷^k ▷ ▷^(S (S n + S m)) (P ∗ Q).
Proof. iIntros "H1 H2". iNext. iNext. iNext. iFrame. Qed.

Lemma test_iNext_unfold P Q n m (R := (▷^n P)%I) :
  R ⊢ ▷^m True.
Proof.
  iIntros "HR". iNext.
  match goal with |-  context [ R ] => idtac | |- _ => fail end.
  done.
Qed.

Lemma test_iNext_fail P Q a b c d e f g h i j:
  ▷^(a + b) ▷^(c + d + e) P -∗ ▷^(f + g + h + i + j) True.
Proof. iIntros "H". iNext. done. Qed.

Lemma test_specialize_affine_pure (φ : Prop) P :
  φ → (<affine> ⌜φ⌝ -∗ P) ⊢ P.
Proof.
  iIntros (Hφ) "H". by iSpecialize ("H" with "[% //]").
Qed.

Lemma test_assert_affine_pure (φ : Prop) P :
  φ → P ⊢ P ∗ <affine> ⌜φ⌝.
Proof. iIntros (Hφ). iAssert (<affine> ⌜φ⌝)%I with "[%]" as "$"; auto. Qed.
Lemma test_assert_pure (φ : Prop) P :
  φ → P ⊢ P ∗ ⌜φ⌝.
Proof. iIntros (Hφ). iAssert ⌜φ⌝%I with "[%]" as "$"; auto. Qed.

Lemma test_iEval x y : ⌜ (y + x)%nat = 1 ⌝ -∗ ⌜ S (x + y) = 2%nat ⌝ : PROP.
Proof.
  iIntros (H).
  iEval (rewrite (Nat.add_comm x y) // H).
  done.
Qed.

Lemma test_iFrame_later_1 P Q : P ∗ ▷ Q -∗ ▷ (P ∗ ▷ Q).
Proof. iIntros "H". iFrame "H". auto. Qed.

Lemma test_iFrame_later_2 P Q : ▷ P ∗ ▷ Q -∗ ▷ (▷ P ∗ ▷ Q).
Proof. iIntros "H". iFrame "H". auto. Qed.

Lemma test_with_ident P Q R : P -∗ Q -∗ (P -∗ Q -∗ R) -∗ R.
Proof.
  iIntros "? HQ H".
  iMatchHyp (fun H _ =>
    iApply ("H" with [spec_patterns.SIdent H; spec_patterns.SIdent "HQ"])).
Qed.

Lemma iFrame_with_evar_r P Q :
  ∃ R, (P -∗ Q -∗ P ∗ R) ∧ R = Q.
Proof.
  eexists. split. iIntros "HP HQ". iFrame. iApply "HQ". done.
Qed.
Lemma iFrame_with_evar_l P Q :
  ∃ R, (P -∗ Q -∗ R ∗ P) ∧ R = Q.
Proof.
  eexists. split. iIntros "HP HQ". Fail iFrame "HQ".
  by iSplitR "HP". done.
Qed.
Lemma iFrame_with_evar_persistent P Q :
  ∃ R, (P -∗ □ Q -∗ P ∗ R ∗ Q) ∧ R = emp%I.
Proof.
  eexists. split. iIntros "HP #HQ". iFrame "HQ HP". iEmpIntro. done.
Qed.

Lemma test_iAccu P Q R S :
  ∃ PP, (□P -∗ Q -∗ R -∗ S -∗ PP) ∧ PP = (Q ∗ R ∗ S)%I.
Proof.
  eexists. split. iIntros "#? ? ? ?". iAccu. done.
Qed.

End tests.
