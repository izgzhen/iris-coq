From iris.program_logic Require Export total_weakestpre.
From iris.bi Require Export big_op.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section lifting.
Context `{irisG Λ Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Lemma twp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 κs, state_interp σ1 κs ={E,∅}=∗
    ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
    ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      ⌜κ = None⌝ ∗ state_interp σ2 κs ∗ WP e2 @ s; E [{ Φ }] ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof. by rewrite twp_unfold /twp_pre=> ->. Qed.

(** Derived lifting lemmas. *)

Lemma twp_lift_pure_step `{Inhabited (state Λ)} s E Φ e1 :
  (∀ σ1, reducible_no_obs e1 σ1) →
  (∀ σ1 κ e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = None /\ σ1 = σ2) →
  (|={E}=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ →
    WP e2 @ s; E [{ Φ }] ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (Hsafe Hstep) "H". iApply twp_lift_step.
  { eapply reducible_not_val, reducible_no_obs_reducible, (Hsafe inhabitant). }
  iIntros (σ1 κs) "Hσ". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first set_solver.
  iSplit; [by destruct s|]. iIntros (κ e2 σ2 efs Hstep').
  destruct (Hstep σ1 κ e2 σ2 efs); auto; subst.
  iMod "Hclose" as "_". iModIntro. iSplit; first done.
  iFrame "Hσ". iApply "H"; auto.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma twp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κs, state_interp σ1 κs ={E}=∗
    ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
    ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜κ = None⌝ ∗ state_interp σ2 κs ∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply (twp_lift_step _ E _ e1)=>//; iIntros (σ1 κs) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iIntros "!>" (κ e2 σ2 efs) "%". iMod "Hclose" as "_".
  iMod ("H" $! κ e2 σ2 efs with "[#]") as "($ & $ & HΦ & $)"; first by eauto.
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply twp_value; last done. by apply of_to_val.
Qed.

Lemma twp_lift_pure_det_step `{Inhabited (state Λ)} {s E Φ} e1 e2 efs :
  (∀ σ1, reducible_no_obs e1 σ1) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' → κ = None /\ σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
  (|={E}=> WP e2 @ s; E [{ Φ }] ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (? Hpuredet) ">H". iApply (twp_lift_pure_step _ E); try done.
  { by naive_solver. }
  by iIntros "!>" (κ e' efs' σ (->&_&->&->)%Hpuredet).
Qed.

Lemma twp_pure_step `{Inhabited (state Λ)} s E e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  WP e2 @ s; E [{ Φ }] ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros ([??] Hφ) "HWP".
  iApply (twp_lift_pure_det_step with "[HWP]"); [eauto|naive_solver|auto].
Qed.

End lifting.
