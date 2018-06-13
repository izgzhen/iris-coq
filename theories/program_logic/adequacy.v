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

Notation wptp s t := ([∗ list] ef ∈ t, WP ef @ s; ⊤ {{ _, fork_post }})%I.

Lemma wp_step s e1 σ1 κ κs e2 σ2 efs m Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 (κ ++ κs) m -∗ WP e1 @ s; ⊤ {{ Φ }} ={⊤,∅}▷=∗
  state_interp σ2 κs (length efs + m) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s efs.
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 with "Hσ") as "(_ & H)".
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  by iIntros "!> !>".
Qed.

Lemma wptp_step s e1 t1 t2 κ κs σ1 σ2 Φ :
  step (e1 :: t1,σ1) κ (t2, σ2) →
  state_interp σ1 (κ ++ κs) (length t1) -∗ WP e1 @ s; ⊤ {{ Φ }} -∗ wptp s t1 ==∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  |={⊤,∅}▷=> state_interp σ2 κs (pred (length t2)) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2'.
Proof.
  iIntros (Hstep) "Hσ He Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iModIntro. iSplitR; first by eauto.
    iMod (wp_step with "Hσ He") as "H"; first done.
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)".
    iIntros "!>". rewrite Nat.add_comm app_length. iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iFrame "He". iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iModIntro. iMod (wp_step with "Hσ He1") as "H"; first done.
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)". iIntros "!>".
    rewrite !app_length /= !app_length.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by omega. iFrame.
Qed.

Lemma wptp_steps s n e1 t1 κs κs' t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗ WP e1 @ s; ⊤ {{ Φ }} -∗ wptp s t1
  ={⊤,∅}▷=∗^n ∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 κs' (pred (length t2)) ∗
    WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2'.
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "???"; iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "Hσ He Ht". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iMod (wptp_step with "Hσ He Ht") as (e1' t1'' ?) ">H"; first eauto; simplify_eq.
  iIntros "!> !>". iMod "H" as "(Hσ & He & Ht)". iModIntro.
  by iApply (IH with "Hσ He Ht").
Qed.

Lemma wptp_result φ κs' s n e1 t1 κs v2 t2 σ1 σ2  :
  nsteps n (e1 :: t1, σ1) κs (of_val v2 :: t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WP e1 @ s; ⊤ {{ v, ∀ σ, state_interp σ κs' (length t2) ={⊤,∅}=∗ ⌜φ v σ⌝ }} -∗
  wptp s t1 ={⊤,∅}▷=∗^(S n) ⌜φ v2 σ2⌝.
Proof.
  iIntros (?) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht") as "H"; first done.
  iApply (step_fupdN_wand with "H").
  iDestruct 1 as (e2 t2' ?) "(Hσ & H & _)"; simplify_eq.
  iMod (wp_value_inv' with "H") as "H".
  iMod (fupd_plain_mask_empty _ ⌜φ v2 σ2⌝%I with "[H Hσ]") as %?.
  { by iMod ("H" with "Hσ") as "$". }
  by iApply step_fupd_intro.
Qed.

Lemma wptp_all_result φ κs' s n e1 t1 κs v2 vs2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (of_val <$> v2 :: vs2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WP e1 @ s; ⊤ {{ v,
    let m' := length vs2 in
    state_interp σ2 κs' m' -∗ [∗] replicate m' fork_post ={⊤,∅}=∗ ⌜φ v ⌝ }} -∗
  wptp s t1
  ={⊤,∅}▷=∗^(S n) ⌜φ v2 ⌝.
Proof.
  iIntros (Hstep) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht") as "H"; first done.
  iApply (step_fupdN_wand with "H").
  iDestruct 1 as (e2 t2' ?) "(Hσ & H & Hvs)"; simplify_eq/=.
  rewrite fmap_length. iMod (wp_value_inv' with "H") as "H".
  iAssert ([∗] replicate (length vs2) fork_post)%I with "[> Hvs]" as "Hm".
  { clear Hstep. iInduction vs2 as [|v vs] "IH"; csimpl; first by iFrame.
    iDestruct "Hvs" as "[Hv Hvs]".
    iMod (wp_value_inv' with "Hv") as "$". by iApply "IH". }
  iMod (fupd_plain_mask_empty _ ⌜φ v2⌝%I with "[H Hm Hσ]") as %?.
  { iApply ("H" with "Hσ Hm"). }
  by iApply step_fupd_intro.
Qed.

Lemma wp_safe κs m e σ Φ :
  state_interp σ κs m -∗
  WP e {{ Φ }} ={⊤,∅}▷=∗ ⌜is_Some (to_val e) ∨ reducible e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?.
  { iApply step_fupd_intro. set_solver. eauto. }
  iMod (fupd_plain_mask_empty _ ⌜reducible e σ⌝%I with "[H Hσ]") as %?.
  { by iMod ("H" $! σ [] κs with "Hσ") as "[$ H]". }
  iApply step_fupd_intro; first by set_solver+. 
  iIntros "!> !%". by right.
Qed.

Lemma wptp_safe κs' n e1 κs e2 t1 t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) → e2 ∈ t2 →
  state_interp σ1 (κs ++ κs') (length t1) -∗ WP e1 {{ Φ }} -∗ wptp NotStuck t1
  ={⊤,∅}▷=∗^(S n) ⌜is_Some (to_val e2) ∨ reducible e2 σ2⌝.
Proof.
  iIntros (? He2) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps  with "Hσ He Ht") as "H"; first done.
  iApply (step_fupdN_wand with "H").
  iDestruct 1 as (e2' t2' ?) "(Hσ & H & Ht)"; simplify_eq.
  apply elem_of_cons in He2 as [<-|(t1''&t2''&->)%elem_of_list_split].
  - iMod (wp_safe with "Hσ H") as "$"; auto.
  - iDestruct "Ht" as "(_ & He2 & _)". by iMod (wp_safe with "Hσ He2").
Qed.

Lemma wptp_invariance φ s n e1 κs κs' e2 t1 t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  (state_interp σ2 κs' (pred (length t2)) ={⊤,∅}=∗ ⌜φ⌝) -∗
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WP e1 @ s; ⊤ {{ Φ }} -∗ wptp s t1
  ={⊤,∅}▷=∗^(S n) ⌜φ⌝.
Proof.
  iIntros (?) "Hφ Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps _ n with "Hσ He Ht") as "H"; first done.
  iApply (step_fupdN_wand with "H"). iDestruct 1 as (e2' t2' ->) "[Hσ _]".
  iSpecialize ("Hφ" with "Hσ").
  iMod (fupd_plain_mask_empty _ ⌜φ⌝%I with "Hφ") as %?.
  by iApply step_fupd_intro.
Qed.
End adequacy.

Theorem wp_strong_adequacy Σ Λ `{invPreG Σ} s e σ φ :
  (∀ `{Hinv : invG Σ} κs,
     (|={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI fork_post in
       (* This could be strengthened so that φ also talks about the number 
       of forked-off threads *)
       stateI σ κs 0 ∗ WP e @ s; ⊤ {{ v, ∀ σ m, stateI σ [] m ={⊤,∅}=∗ ⌜φ v σ⌝ }})%I) →
  adequate s e σ φ.
Proof.
  intros Hwp; split.
  - intros t2 σ2 v2 [n [κs ?]]%erased_steps_nsteps.
    eapply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S.
    iMod (Hwp _ (κs ++ [])) as (stateI fork_post) "[Hσ Hwp]".
    iApply step_fupd_intro; first done. iModIntro.
    iApply (@wptp_result _ _ (IrisG _ _ _ Hinv stateI fork_post) with "[Hσ] [Hwp]"); eauto.
    iApply (wp_wand with "Hwp"). iIntros (v) "H"; iIntros (σ'). iApply "H".
  - destruct s; last done. intros t2 σ2 e2 _ [n [κs ?]]%erased_steps_nsteps ?.
    eapply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S.
    iMod (Hwp _ (κs ++ [])) as (stateI fork_post) "[Hσ Hwp]".
    iApply step_fupd_intro; first done. iModIntro.
    iApply (@wptp_safe _ _ (IrisG _ _ _ Hinv stateI fork_post) with "[Hσ] Hwp"); eauto.
Qed.

Theorem wp_adequacy Σ Λ `{invPreG Σ} s e σ φ :
  (∀ `{Hinv : invG Σ} κs,
     (|={⊤}=> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv (λ σ κs _, stateI σ κs) True%I in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }})%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply (wp_strong_adequacy Σ _)=> Hinv κs.
  iMod Hwp as (stateI) "[Hσ H]". iExists (λ σ κs _, stateI σ κs), True%I.
  iIntros "{$Hσ} !>".
  iApply (wp_wand with "H"). iIntros (v ? σ') "_".
  iIntros "_". by iApply fupd_mask_weaken.
Qed.

Theorem wp_strong_all_adequacy Σ Λ `{invPreG Σ} s e σ1 v vs σ2 φ :
  (∀ `{Hinv : invG Σ} κs,
     (|={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI fork_post in
       stateI σ1 κs 0 ∗ WP e @ s; ⊤ {{ v,
         let m := length vs in
         stateI σ2 [] m -∗ [∗] replicate m fork_post ={⊤,∅}=∗ ⌜ φ v ⌝ }})%I) →
  rtc erased_step ([e], σ1) (of_val <$> v :: vs, σ2) →
  φ v.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iApply step_fupd_intro; first done. iModIntro.
  iApply (@wptp_all_result _ _ (IrisG _ _ _ Hinv stateI fork_post)
    with "[Hσ] [Hwp]"); eauto. by rewrite right_id_L.
Qed.

Theorem wp_invariance Σ Λ `{invPreG Σ} s e σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ} κs κs',
     (|={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI fork_post in
       stateI σ1 (κs ++ κs') 0 ∗ WP e @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 κs' (pred (length t2)) ={⊤,∅}=∗ ⌜φ⌝))%I) →
  rtc erased_step ([e], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  apply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S.
  iMod (Hwp Hinv κs []) as (Istate fork_post) "(Hσ & Hwp & Hclose)".
  iApply step_fupd_intro; first done.
  iApply (@wptp_invariance _ _ (IrisG _ _ _ Hinv Istate fork_post)
    with "Hclose [Hσ] [Hwp]"); eauto.
Qed.

(* An equivalent version that does not require finding [fupd_intro_mask'], but
can be confusing to use. *)
Corollary wp_invariance' Σ Λ `{invPreG Σ} s e σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ} κs κs',
     (|={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI fork_post in
       stateI σ1 κs 0 ∗ WP e @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 κs' (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝))%I) →
  rtc erased_step ([e], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp. eapply wp_invariance; first done.
  intros Hinv κs κs'. iMod (Hwp Hinv) as (stateI fork_post) "(? & ? & Hφ)".
  iModIntro. iExists stateI, fork_post. iFrame. iIntros "Hσ".
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_weaken; first set_solver.
Qed.
