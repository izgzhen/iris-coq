(** Some derived lemmas for ectx-based languages *)
From iris.program_logic Require Export ectx_language.
From iris.program_logic Require Export total_weakestpre total_lifting.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section wp.
Context {Λ : ectxLanguage} `{irisG Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Hint Resolve head_prim_reducible_no_obs head_reducible_prim_step head_reducible_no_obs_reducible.

Lemma twp_lift_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κs, state_interp σ1 κs ={E,∅}=∗
    ⌜head_reducible_no_obs e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      ⌜κ = None⌝ ∗ state_interp σ2 κs ∗
      WP e2 @ s; E [{ Φ }] ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply (twp_lift_step _ E)=>//. iIntros (σ1 κs) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; [destruct s; auto|]. iIntros (κ e2 σ2 efs Hstep).
  iApply "H". by eauto.
Qed.

Lemma twp_lift_pure_head_step {s E Φ} e1 :
  (∀ σ1, head_reducible_no_obs e1 σ1) →
  (∀ σ1 κ e2 σ2 efs, head_step e1 σ1 κ e2 σ2 efs → κ = None ∧ σ1 = σ2) →
  (|={E}=> ∀ κ e2 efs σ, ⌜head_step e1 σ κ e2 σ efs⌝ →
    WP e2 @ s; E [{ Φ }] ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof using Hinh.
  iIntros (??) ">H". iApply twp_lift_pure_step; eauto.
  iIntros "!>" (?????). iApply "H"; eauto.
Qed.

Lemma twp_lift_atomic_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κs, state_interp σ1 κs ={E}=∗
    ⌜head_reducible_no_obs e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜κ = None⌝ ∗ state_interp σ2 κs ∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply twp_lift_atomic_step; eauto.
  iIntros (σ1 κs) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iIntros (κ e2 σ2 efs Hstep). iApply "H"; eauto.
Qed.

Lemma twp_lift_atomic_head_step_no_fork {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κs, state_interp σ1 κs ={E}=∗
    ⌜head_reducible_no_obs e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜κ = None⌝ ∗ ⌜efs = []⌝ ∗ state_interp σ2 κs ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply twp_lift_atomic_head_step; eauto.
  iIntros (σ1 κs) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iIntros (κ v2 σ2 efs Hstep).
  iMod ("H" with "[# //]") as "($ & % & $ & $)"; subst; auto.
Qed.

Lemma twp_lift_pure_det_head_step {s E Φ} e1 e2 efs :
  (∀ σ1, head_reducible_no_obs e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = None ∧ σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
  (|={E}=> WP e2 @ s; E [{ Φ }] ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof using Hinh. eauto 10 using twp_lift_pure_det_step. Qed.

Lemma twp_lift_pure_det_head_step_no_fork {s E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible_no_obs e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = None ∧ σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  WP e2 @ s; E [{ Φ }] ⊢ WP e1 @ s; E [{ Φ }].
Proof using Hinh.
  intros. rewrite -(twp_lift_pure_det_step e1 e2 []) /= ?right_id; eauto.
Qed.
End wp.
