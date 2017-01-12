From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export big_op.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section lifting.
Context `{irisG Λ Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Lemma wp_lift_step E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof. by rewrite wp_unfold /wp_pre=> ->. Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_pure_step `{Inhabited (state Λ)} E Φ e1 :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (▷ ∀ e2 efs σ, ⌜prim_step e1 σ e2 σ efs⌝ →
    WP e2 @ E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { eapply reducible_not_val, (Hsafe inhabitant). }
  iIntros (σ1) "Hσ". iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro. iSplit; [done|]; iNext; iIntros (e2 σ2 efs ?).
  destruct (Hstep σ1 e2 σ2 efs); auto; subst.
  iMod "Hclose"; iModIntro. iFrame "Hσ". iApply "H"; auto.
Qed.

Lemma wp_lift_atomic_step {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro; iNext; iIntros (e2 σ2 efs) "%". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "($ & HΦ & $)"; first by eauto.
  destruct (to_val e2) eqn:?; last by iExFalso.
  by iApply wp_value.
Qed.

Lemma wp_lift_pure_det_step `{Inhabited (state Λ)} {E Φ} e1 e2 efs :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
  ▷ (WP e2 @ E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "?". iApply (wp_lift_pure_step E); try done.
  by intros; eapply Hpuredet. iNext. by iIntros (e' efs' σ (_&->&->)%Hpuredet).
Qed.
End lifting.
