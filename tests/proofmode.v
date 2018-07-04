From iris.proofmode Require Import tactics intro_patterns.
From stdpp Require Import gmap hlist.
Set Default Proof Using "Type".

Section tests.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.

Lemma demo_0 P Q : □ (P ∨ Q) -∗ (∀ x, ⌜x = 0⌝ ∨ ⌜x = 1⌝) → (Q ∨ P).
Proof.
  iIntros "H #H2". Show. iDestruct "H" as "###H".
  (* should remove the disjunction "H" *)
  iDestruct "H" as "[#?|#?]"; last by iLeft. Show.
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
Proof. iIntros "[#? _] [_ #?]". Show. auto. Qed.

Lemma test_iIntros_persistent P Q `{!Persistent Q} : (P → Q → P ∧ Q)%I.
Proof. iIntros "H1 #H2". by iFrame "∗#". Qed.

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

Lemma test_done_goal_evar Q : ∃ P, Q ⊢ P.
Proof. eexists. iIntros "H". Fail done. iAssumption. Qed.

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

Lemma test_iSpecialize_pure (φ : Prop) Q R:
  φ → (⌜φ⌝ -∗ Q) → Q.
Proof. iIntros (HP HPQ). iDestruct (HPQ $! HP) as "?". done. Qed.

Lemma test_iSpecialize_Coq_entailment P Q R :
  P → (P -∗ Q) → Q.
Proof. iIntros (HP HPQ). iDestruct (HPQ $! HP) as "?". done. Qed.

Lemma test_iEmp_intro P Q R `{!Affine P, !Persistent Q, !Affine R} :
  P -∗ Q → R -∗ emp.
Proof. iIntros "HP #HQ HR". iEmpIntro. Qed.

Lemma test_fresh P Q:
  (P ∗ Q) -∗ (P ∗ Q).
Proof.
  iIntros "H".
  let H1 := iFresh in
  let H2 := iFresh in
  let pat :=constr:(IList [cons (IIdent H1) (cons (IIdent H2) nil)]) in 
  iDestruct "H" as pat.
  iFrame.
Qed.

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

Lemma test_iFrame_later `{BiAffine PROP} P Q : P -∗ Q -∗ ▷ P ∗ Q.
Proof. iIntros "H1 H2". by iFrame "H1". Qed.

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

(* Check that typeclasses are not resolved too early *)
Lemma test_TC_resolution `{!BiAffine PROP} (Φ : nat → PROP) l x :
  x ∈ l → ([∗ list] y ∈ l, Φ y) -∗ Φ x.
Proof.
  iIntros (Hp) "HT".
  iDestruct (big_sepL_elem_of _ _ _ Hp with "HT") as "Hp".
  done.
Qed.

Lemma test_eauto_iFrame P Q R `{!Persistent R} :
  P -∗ Q -∗ R → R ∗ Q ∗ P ∗ R ∨ False.
Proof. eauto 10 with iFrame. Qed.

Lemma test_iCombine_persistent P Q R `{!Persistent R} :
  P -∗ Q -∗ R → R ∗ Q ∗ P ∗ R ∨ False.
Proof. iIntros "HP HQ #HR". iCombine "HR HQ HP HR" as "H". auto. Qed.

Lemma test_iCombine_frame P Q R `{!Persistent R} :
  P -∗ Q -∗ R → R ∗ Q ∗ P ∗ R.
Proof. iIntros "HP HQ #HR". iCombine "HQ HP HR" as "$". by iFrame. Qed.

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
Proof. iIntros "H1 H2". iNext. iNext. iNext. iFrame. Show. iModIntro. done. Qed.

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
Proof. iIntros (Hφ). iAssert ⌜φ⌝%I with "[%]" as "$"; auto with iFrame. Qed.

Lemma test_iEval x y : ⌜ (y + x)%nat = 1 ⌝ -∗ ⌜ S (x + y) = 2%nat ⌝ : PROP.
Proof.
  iIntros (H).
  iEval (rewrite (Nat.add_comm x y) // H).
  done.
Qed.

Lemma test_iIntros_pure_neg : (⌜ ¬False ⌝ : PROP)%I.
Proof. by iIntros (?). Qed.

Lemma test_iPureIntro_absorbing (φ : Prop) :
  φ → sbi_emp_valid (PROP:=PROP) (<absorb> ⌜φ⌝)%I.
Proof. intros ?. iPureIntro. done. Qed.

Lemma test_iFrame_later_1 P Q : P ∗ ▷ Q -∗ ▷ (P ∗ ▷ Q).
Proof. iIntros "H". iFrame "H". Show. auto. Qed.

Lemma test_iFrame_later_2 P Q : ▷ P ∗ ▷ Q -∗ ▷ (▷ P ∗ ▷ Q).
Proof. iIntros "H". iFrame "H". Show. auto. Qed.

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
  iSplitR "HP"; iAssumption. done.
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

Lemma test_iAssumption_evar P : ∃ R, (R ⊢ P) ∧ R = P.
Proof.
  eexists. split.
  - iIntros "H". iAssumption.
  (* Now verify that the evar was chosen as desired (i.e., it should not pick False). *)
  - reflexivity.
Qed.

Lemma test_iAssumption_False_no_loop : ∃ R, R ⊢ ∀ P, P.
Proof. eexists. iIntros "?" (P). done. Qed.

Lemma test_apply_affine_impl `{!BiPlainly PROP} (P : PROP) :
  P -∗ (∀ Q : PROP, ■ (Q -∗ <pers> Q) → ■ (P -∗ Q) → Q).
Proof. iIntros "HP" (Q) "_ #HPQ". by iApply "HPQ". Qed.

Lemma test_apply_affine_wand `{!BiPlainly PROP} (P : PROP) :
  P -∗ (∀ Q : PROP, <affine> ■ (Q -∗ <pers> Q) -∗ <affine> ■ (P -∗ Q) -∗ Q).
Proof. iIntros "HP" (Q) "_ #HPQ". by iApply "HPQ". Qed.

Lemma test_and_sep (P Q R : PROP) : P ∧ (Q ∗ □ R) ⊢ (P ∧ Q) ∗ □ R.
Proof.
  iIntros "H". repeat iSplit.
  - iDestruct "H" as "[$ _]".
  - iDestruct "H" as "[_ [$ _]]".
  - iDestruct "H" as "[_ [_ #$]]".
Qed.

Lemma test_and_sep_2 (P Q R : PROP) `{!Persistent R, !Affine R} :
  P ∧ (Q ∗ R) ⊢ (P ∧ Q) ∗ R.
Proof.
  iIntros "H". repeat iSplit.
  - iDestruct "H" as "[$ _]".
  - iDestruct "H" as "[_ [$ _]]".
  - iDestruct "H" as "[_ [_ #$]]".
Qed.

Lemma test_and_sep_affine_bi `{BiAffine PROP} P Q : □ P ∧ Q ⊢ □ P ∗ Q.
Proof.
  iIntros "[??]". iSplit; last done. Show. done.
Qed.

Lemma test_big_sepL_simpl x (l : list nat) P :
   P -∗
  ([∗ list] k↦y ∈ l, <affine> ⌜ y = y ⌝) -∗
  ([∗ list] y ∈ x :: l, <affine> ⌜ y = y ⌝) -∗
  P.
Proof. iIntros "HP ??". Show. simpl. Show. done. Qed.

Lemma test_big_sepL2_simpl x1 x2 (l1 l2 : list nat) P :
  P -∗
  ([∗ list] k↦y1;y2 ∈ []; l2, <affine> ⌜ y1 = y2 ⌝) -∗
  ([∗ list] y1;y2 ∈ x1 :: l1; (x2 :: l2) ++ l2, <affine> ⌜ y1 = y2 ⌝) -∗
  P ∨ ([∗ list] y1;y2 ∈ x1 :: l1; x2 :: l2, True).
Proof. iIntros "HP ??". Show. simpl. Show. by iLeft. Qed.

Lemma test_big_sepL2_iDestruct (Φ : nat → nat → PROP) x1 x2 (l1 l2 : list nat) :
  ([∗ list] y1;y2 ∈ x1 :: l1; x2 :: l2, Φ y1 y2) -∗
  <absorb> Φ x1 x2.
Proof. iIntros "[??]". Show. iFrame. Qed.

Lemma test_big_sepL2_iFrame (Φ : nat → nat → PROP) (l1 l2 : list nat) P :
  Φ 0 10 -∗ ([∗ list] y1;y2 ∈ l1;l2, Φ y1 y2) -∗
  ([∗ list] y1;y2 ∈ (0 :: l1);(10 :: l2), Φ y1 y2).
Proof. iIntros "$ ?". iFrame. Qed.

Lemma test_lemma_1 (b : bool) :
  emp ⊢@{PROP} □?b True.
Proof. destruct b; simpl; eauto. Qed.
Lemma test_reducing_after_iDestruct : emp ⊢@{PROP} True.
Proof.
  iIntros "H". iDestruct (test_lemma_1 true with "H") as "H". Show. done.
Qed.

Lemma test_lemma_2 (b : bool) :
  □?b emp ⊢@{PROP} emp.
Proof. destruct b; simpl; eauto. Qed.
Lemma test_reducing_after_iApply : emp ⊢@{PROP} emp.
Proof.
  iIntros "#H". iApply (test_lemma_2 true). Show. auto.
Qed.

Lemma test_lemma_3 (b : bool) :
  □?b emp ⊢@{PROP} ⌜b = b⌝.
Proof. destruct b; simpl; eauto. Qed.
Lemma test_reducing_after_iApply_late_evar : emp ⊢@{PROP} ⌜true = true⌝.
Proof.
  iIntros "#H". iApply (test_lemma_3). Show. auto.
Qed.

Section wandM.
  Import proofmode.base.
  Lemma test_wandM mP Q R :
    (mP -∗? Q) -∗ (Q -∗ R) -∗ (mP -∗? R).
  Proof.
    iIntros "HPQ HQR HP". Show.
    iApply "HQR". iApply "HPQ". Show.
    done.
  Qed.
End wandM.

Definition big_op_singleton_def (P : nat → PROP) (l : list nat) :=
  ([∗ list] n ∈ l, P n)%I.
Lemma test_iApply_big_op_singleton (P : nat → PROP) :
  P 1 -∗ big_op_singleton_def P [1].
Proof. iIntros "?". iApply big_sepL_singleton. iAssumption. Qed.

End tests.

(** Test specifically if certain things print correctly. *)
Section printing_tests.
Context {PROP : sbi} `{!BiFUpd PROP}.
Implicit Types P Q R : PROP.

Check "elim_mod_accessor".
Lemma elim_mod_accessor {X : Type} E1 E2 α (β : X → PROP) γ :
  accessor (fupd E1 E2) (fupd E2 E1) α β γ -∗ |={E1}=> True.
Proof. iIntros ">Hacc". Show. Abort.

(* Test line breaking of long assumptions. *)
Section linebreaks.
Lemma print_long_line (P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P : PROP) :
  P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P ∗
  P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P
  -∗ True.
Proof.
  iIntros "HP". Show. Undo. iIntros "?". Show.
Abort.

(* This is specifically crafted such that not having the printing box in
   the proofmode notation breaks the output. *)
Local Notation "'TESTNOTATION' '{{' P '|' Q '}' '}'" := (P ∧ Q)%I
  (format "'TESTNOTATION'  '{{'  P  '|'  '/' Q  '}' '}'") : bi_scope.
Lemma print_long_line (P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P : PROP) :
  TESTNOTATION {{ P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P | P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P }}
  -∗ True.
Proof.
  iIntros "HP". Show. Undo. iIntros "?". Show.
Abort.

Lemma long_impl (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  (PPPPPPPPPPPPPPPPP → (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ))%I.
Proof.
  iStartProof. Show.
Abort.
Lemma long_impl_nested (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  (PPPPPPPPPPPPPPPPP → (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ) → (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ))%I.
Proof.
  iStartProof. Show.
Abort.
Lemma long_wand (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  (PPPPPPPPPPPPPPPPP -∗ (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ))%I.
Proof.
  iStartProof. Show.
Abort.
Lemma long_wand_nested (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  (PPPPPPPPPPPPPPPPP -∗ (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ) -∗ (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ))%I.
Proof.
  iStartProof. Show.
Abort.
Lemma long_fupd E (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  PPPPPPPPPPPPPPPPP ={E}=∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ.
Proof.
  iStartProof. Show.
Abort.
Lemma long_fupd_nested E1 E2 (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  PPPPPPPPPPPPPPPPP ={E1,E2}=∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ
  ={E1,E2}=∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ.
Proof.
  iStartProof. Show.
Abort.
End linebreaks.

End printing_tests.

(** Test error messages *)
Section error_tests.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.

Check "iAlways_spatial_non_empty".
Lemma iAlways_spatial_non_empty P :
  P -∗ □ emp.
Proof. iIntros "HP". Fail iAlways. Abort.

Check "iDestruct_bad_name".
Lemma iDestruct_bad_name P :
  P -∗ P.
Proof. iIntros "HP". Fail iDestruct "HQ" as "HP". Abort.

Check "iIntros_dup_name".
Lemma iIntros_dup_name P Q :
  P -∗ Q -∗ ∀ x y : (), P.
Proof.
  iIntros "HP". Fail iIntros "HP".
  iIntros "HQ" (x). Fail iIntros (x).
Abort.

Check "iSplit_one_of_many".
Lemma iSplit_one_of_many P :
  P -∗ P -∗ P ∗ P.
Proof.
  iIntros "HP1 HP2". Fail iSplitL "HP1 HPx". Fail iSplitL "HPx HP1".
Abort.

Check "iExact_fail".
Lemma iExact_fail P Q :
  <affine> P -∗ Q -∗ <affine> P.
Proof.
  iIntros "HP". Fail iExact "HQ". iIntros "HQ". Fail iExact "HQ". Fail iExact "HP".
Abort.

Check "iClear_fail".
Lemma iClear_fail P : P -∗ P.
Proof. Fail iClear "HP". iIntros "HP". Fail iClear "HP". Abort.

Check "iSpecializeArgs_fail".
Lemma iSpecializeArgs_fail P :
  (∀ x : nat, P) -∗ P.
Proof. iIntros "HP". Fail iSpecialize ("HP" $! true). Abort.

Check "iStartProof_fail".
Lemma iStartProof_fail : 0 = 0.
Proof. Fail iStartProof. Abort.

Check "iPoseProof_fail".
Lemma iPoseProof_fail P : P -∗ P.
Proof.
  Fail iPoseProof (eq_refl 0) as "H".
  iIntros "H". Fail iPoseProof bi.and_intro as "H".
Abort.

Check "iRevert_fail".
Lemma iRevert_fail P : P -∗ P.
Proof. Fail iRevert "H". Abort.

Check "iDestruct_fail".
Lemma iDestruct_fail P : P -∗ <absorb> P.
Proof. iIntros "HP". Fail iDestruct "HP" as "{HP}". Fail iDestruct "HP" as "[{HP}]". Abort.

Check "iApply_fail".
Lemma iApply_fail P Q : P -∗ Q.
Proof. iIntros "HP". Fail iApply "HP". Abort.

End error_tests.
