From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section lifting.
Context `{irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Lemma wp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1) "Hσ".
  iMod ("H" with "Hσ") as "(%&?)". iModIntro. iSplit. by destruct s. done.
Qed.

Lemma wp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ, state_interp σ ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1) "Hσ".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iIntros "!>" (e2 σ2 efs) "%". by case: (Hirr e2 σ2 efs).
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_pure_step `{Inhabited (state Λ)} s E E' Φ e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (|={E,E'}▷=> ∀ e2 efs σ, ⌜prim_step e1 σ e2 σ efs⌝ →
    WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). destruct s; last done.
      by eapply reducible_not_val. }
  iIntros (σ1) "Hσ". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first by set_solver. iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 efs ?).
  destruct (Hstep σ1 e2 σ2 efs); auto; subst.
  iMod "Hclose" as "_". iFrame "Hσ". iMod "H". iApply "H"; auto.
Qed.

Lemma wp_lift_pure_stuck `{Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) →
  True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ) "_". iMod (fupd_intro_mask' E ∅) as "_".
    by set_solver. by auto.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step s E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro; iNext; iIntros (e2 σ2 efs) "%". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "($ & HΦ & $)"; first by eauto.
  destruct (to_val e2) eqn:?; last by iExFalso.
  by iApply wp_value.
Qed.

Lemma wp_lift_pure_det_step `{Inhabited (state Λ)} {s E E' Φ} e1 e2 efs :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step s E E'); try done.
  { by intros; eapply Hpuredet. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  by iIntros (e' efs' σ (_&->&->)%Hpuredet).
Qed.

Lemma wp_pure_step_fupd `{Inhabited (state Λ)} s E E' e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros ([??] Hφ) "HWP".
  iApply (wp_lift_pure_det_step with "[HWP]").
  - intros σ. specialize (pure_exec_safe σ). destruct s; eauto using reducible_not_val.
  - destruct s; naive_solver.
  - by rewrite bi.big_sepL_nil right_id.
Qed.

Lemma wp_pure_step_later `{Inhabited (state Λ)} s E e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros ??. rewrite -wp_pure_step_fupd //. rewrite -step_fupd_intro //.
Qed.
End lifting.
