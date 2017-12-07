(** Some derived lemmas for ectx-based languages *)
From iris.program_logic Require Export ectx_language weakestpre lifting.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section wp.
Context {Λ : ectxLanguage} `{irisG Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Hint Resolve head_prim_reducible head_reducible_prim_step.
Hint Resolve (reducible_not_val _ inhabitant).
Hint Resolve head_stuck_stuck.

Lemma wp_lift_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step=>//. iIntros (σ1) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iNext. iIntros (e2 σ2 efs) "%".
  iApply "H"; eauto.
Qed.

Lemma wp_lift_head_stuck E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ, state_interp σ ={E,∅}=∗ ⌜head_stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (??) "H". iApply wp_lift_stuck; first done.
  iIntros (σ) "Hσ". iMod ("H" with "Hσ") as "%". by auto.
Qed.

Lemma wp_lift_pure_head_step {s E E' Φ} e1 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (|={E,E'}▷=> ∀ e2 efs σ, ⌜head_step e1 σ e2 σ efs⌝ →
    WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  iIntros (??) "H". iApply wp_lift_pure_step; eauto.
  { by destruct s; auto. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (????). iApply "H"; eauto.
Qed.

Lemma wp_lift_pure_head_stuck E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ, head_stuck e σ) →
  WP e @ E ?{{ Φ }}%I.
Proof using Hinh.
  iIntros (?? Hstuck). iApply wp_lift_head_stuck; [done|done|].
  iIntros (σ) "_". iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
  by auto.
Qed.

Lemma wp_lift_atomic_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iNext. iIntros (e2 σ2 efs) "%".
  iApply "H"; auto.
Qed.

Lemma wp_lift_atomic_head_step_no_fork {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 ∗ default False (to_val e2) Φ)
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 efs) "%".
  iMod ("H" $! v2 σ2 efs with "[# //]") as "(% & $ & $)"; subst; auto.
Qed.

Lemma wp_lift_pure_det_head_step {s E E' Φ} e1 e2 efs :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 efs); eauto.
  destruct s; by auto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork {s E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 []) /= ?right_id; eauto.
  destruct s; by auto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork' {s E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  ▷ WP e2 @ E {{ Φ }} ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ _ {{ _ }})%I]wp_lift_pure_det_head_step_no_fork //.
  rewrite -step_fupd_intro //.
Qed.
End wp.
