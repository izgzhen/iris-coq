From stdpp Require Import namespaces.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* Program logic adequacy *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
}.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ κ t3 σ3, step (t2, σ2) κ (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists κ, (t2' ++ e3 :: t2'' ++ efs), σ3; econstructor; eauto.
Qed.

Section adequacy.
Context `{irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t := ([∗ list] ef ∈ t, WP ef @ s; ⊤ {{ _, True }})%I.

Lemma wp_step s E e1 σ1 κ κs e2 σ2 efs Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 (κ ++ κs) ∗ WP e1 @ s; E {{ Φ }}
  ={E, ∅}▷=∗ (state_interp σ2 κs ∗ WP e2 @ s; E {{ Φ }} ∗ wptp s efs).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "[Hσ H]".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 with "Hσ") as "(_ & H)".
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  by iIntros "!> !>".
Qed.

Lemma wptp_step s e1 t1 t2 κ κs σ1 σ2 Φ :
  step (e1 :: t1,σ1) κ (t2, σ2) →
  state_interp σ1 (κ ++ κs) ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1
  ==∗ ∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗ |={⊤, ∅}▷=> (state_interp σ2 κs ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2').
Proof.
  iIntros (Hstep) "(HW & He & Ht)".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iSplitR; first by eauto.
    iFrame "Ht". iApply wp_step; eauto with iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "($ & He' & $)". iFrame "He".
    iApply wp_step; eauto with iFrame.
Qed.

Lemma wptp_steps s n e1 t1 κs κs' t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1 ⊢
  |={⊤, ∅}▷=>^n (∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗ state_interp σ2 κs' ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2').
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl; induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "(?&?&?)"; iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "H". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite <- app_assoc.
  iMod (wptp_step with "H") as (e1' t1'') "[% H]"; first eauto; simplify_eq.
  iMod "H". iModIntro; iNext. iMod "H". iModIntro.
  by iApply IH.
Qed.

Lemma wptp_result s n e1 t1 κs κs' v2 t2 σ1 σ2 φ :
  nsteps n (e1 :: t1, σ1) κs (of_val v2 :: t2, σ2) →
  state_interp σ1 (κs ++ κs') ∗
  WP e1 @ s; ⊤ {{ v, ∀ σ, state_interp σ κs' ={⊤,∅}=∗ ⌜φ v σ⌝ }} ∗
  wptp s t1 ⊢
  |={⊤, ∅}▷=>^(S n) ⌜φ v2 σ2⌝.
Proof.
  intros. rewrite Nat_iter_S_r wptp_steps //.
  apply step_fupdN_mono.
  iDestruct 1 as (e2 t2' ?) "(Hσ & H & _)"; simplify_eq.
  iMod (wp_value_inv' with "H") as "H".
  iMod (later_fupd_plain false ⊤ ∅ (⌜φ v2 σ2⌝)%I with "[H Hσ]") as ">#%".
  { rewrite //=. by iMod ("H" with "Hσ") as "$". }
  iApply (step_fupd_mask_mono ∅ _ _ ∅); auto.
Qed.

Lemma wp_safe E e σ κs Φ :
  state_interp σ κs -∗ WP e @ E {{ Φ }} ={E, ∅}▷=∗ ⌜is_Some (to_val e) ∨ reducible e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?.
  { iApply (step_fupd_mask_mono ∅ _ _ ∅); eauto. set_solver. }
  iMod (later_fupd_plain false E ∅ (⌜reducible e σ⌝)%I with "[H Hσ]") as ">#%".
  { rewrite //=. by iMod ("H" $! σ [] κs with "Hσ") as "($&H)". }
  iApply step_fupd_intro; first by set_solver+. 
  iIntros "!> !%". by right.
Qed.

Lemma wptp_safe n e1 κs κs' e2 t1 t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) → e2 ∈ t2 →
  state_interp σ1 (κs ++ κs') ∗ WP e1 {{ Φ }} ∗ wptp NotStuck t1
  ⊢ |={⊤, ∅}▷=>^(S n) ⌜is_Some (to_val e2) ∨ reducible e2 σ2⌝.
Proof.
  intros ? He2. rewrite Nat_iter_S_r wptp_steps //.
  apply step_fupdN_mono.
  iDestruct 1 as (e2' t2' ?) "(Hw & H & Htp)"; simplify_eq.
  apply elem_of_cons in He2 as [<-|?].
  - iMod (wp_safe with "Hw H") as "$"; auto.
  - iMod (wp_safe with "Hw [Htp]") as "$"; auto. by iApply (big_sepL_elem_of with "Htp").
Qed.

Lemma wptp_invariance s n e1 κs κs' e2 t1 t2 σ1 σ2 φ Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  (state_interp σ2 κs' ={⊤,∅}=∗ ⌜φ⌝) ∗ state_interp σ1 (κs ++ κs') ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1
  ⊢ |={⊤, ∅}▷=>^(S n) |={⊤,∅}=> ⌜φ⌝.
Proof.
  intros ?. rewrite Nat_iter_S_r wptp_steps // step_fupdN_frame_l.
  apply step_fupdN_mono.
  iIntros "[Hback H]"; iDestruct "H" as (e2' t2' ->) "[Hσ _]".
  iSpecialize ("Hback" with "Hσ").
  iApply (step_fupd_mask_mono ∅ _ _ ∅); auto.
Qed.
End adequacy.

Theorem wp_strong_adequacy Σ Λ `{invPreG Σ} s e σ φ :
  (∀ `{Hinv : invG Σ} κs,
     (|={⊤}=> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ∀ σ, stateI σ [] ={⊤,∅}=∗ ⌜φ v σ⌝ }})%I) →
  adequate s e σ φ.
Proof.
  intros Hwp; split.
  - intros t2 σ2 v2 [n [κs ?]]%erased_steps_nsteps.
    eapply (step_fupdN_soundness' _ (S (S n))).
    iIntros (Hinv).
    rewrite Nat_iter_S.
    iMod Hwp as (Istate) "[HI Hwp]".
    iApply (step_fupd_mask_mono ∅ _ _ ∅); auto. iModIntro. iNext; iModIntro.
    iApply (@wptp_result _ _ (IrisG _ _ _ Hinv Istate) _ _ _ _ _ []); eauto with iFrame.
  - destruct s; last done. intros t2 σ2 e2 _ [n [κs ?]]%erased_steps_nsteps ?.
    eapply (step_fupdN_soundness' _ (S (S n))).
    iIntros (Hinv).
    rewrite Nat_iter_S.
    iMod Hwp as (Istate) "[HI Hwp]".
    iApply (step_fupd_mask_mono ∅ _ _ ∅); auto.
    iApply (@wptp_safe _ _ (IrisG _ _ _ Hinv Istate) _ _ _ []); [by eauto..|].
    rewrite app_nil_r. eauto with iFrame.
Qed.

Theorem wp_adequacy Σ Λ `{invPreG Σ} s e σ φ :
  (∀ `{Hinv : invG Σ} κs,
     (|={⊤}=> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }})%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply (wp_strong_adequacy Σ _)=> Hinv κs.
  iMod Hwp as (stateI) "[Hσ H]". iExists stateI. iIntros "{$Hσ} !>".
  iApply (wp_wand with "H"). iIntros (v ? σ') "_".
  iMod (fupd_intro_mask' ⊤ ∅) as "_"; auto.
Qed.

Theorem wp_invariance Σ Λ `{invPreG Σ} s e σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ} κs κs',
     (|={⊤}=> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 (κs ++ κs') ∗ WP e @ s; ⊤ {{ _, True }} ∗ (stateI σ2 κs' ={⊤,∅}=∗ ⌜φ⌝))%I) →
  rtc erased_step ([e], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (step_fupdN_soundness _ (S (S n))).
  iIntros (Hinv).
  rewrite Nat_iter_S.
  iMod (Hwp Hinv κs []) as (Istate) "(HIstate & Hwp & Hclose)".
  iApply (step_fupd_mask_mono ∅ _ _ ∅); auto.
  iApply (@wptp_invariance _ _ (IrisG _ _ _ Hinv Istate)); eauto with iFrame.
Qed.

(* An equivalent version that does not require finding [fupd_intro_mask'], but
can be confusing to use. *)
Corollary wp_invariance' Σ Λ `{invPreG Σ} s e σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ} κs κs',
     (|={⊤}=> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 κs ∗ WP e @ s; ⊤ {{ _, True }} ∗ (stateI σ2 κs' -∗ ∃ E, |={⊤,E}=> ⌜φ⌝))%I) →
  rtc erased_step ([e], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp. eapply wp_invariance; first done.
  intros Hinv κs κs'. iMod (Hwp Hinv) as (stateI) "(? & ? & Hφ)".
  iModIntro. iExists stateI. iFrame. iIntros "Hσ".
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  iMod (fupd_intro_mask') as "_"; last by iModIntro. solve_ndisj.
Qed.
