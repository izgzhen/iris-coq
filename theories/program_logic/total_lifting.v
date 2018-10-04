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
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ s; E [{ Φ }] ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof. by rewrite twp_unfold /twp_pre=> ->. Qed.

(** Derived lifting lemmas. *)
Lemma twp_lift_pure_step `{Inhabited (state Λ)} s E Φ e1 :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (|={E}=> ∀ e2 efs σ, ⌜prim_step e1 σ e2 σ efs⌝ →
    WP e2 @ s; E [{ Φ }] ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (Hsafe Hstep) "H". iApply twp_lift_step.
  { eapply reducible_not_val, (Hsafe inhabitant). }
  iIntros (σ1) "Hσ". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first set_solver.
  iSplit; [by destruct s|]; iIntros (e2 σ2 efs ?).
  destruct (Hstep σ1 e2 σ2 efs); auto; subst.
  iMod "Hclose" as "_". iFrame "Hσ". iApply "H"; auto.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma twp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply (twp_lift_step _ E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iIntros "!>" (e2 σ2 efs) "%". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "($ & HΦ & $)"; first by eauto.
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply twp_value; last done. by apply of_to_val.
Qed.

Lemma twp_lift_pure_det_step `{Inhabited (state Λ)} {s E Φ} e1 e2 efs :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
  (|={E}=> WP e2 @ s; E [{ Φ }] ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ _, True }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (? Hpuredet) ">H". iApply (twp_lift_pure_step _ E); try done.
  { by intros; eapply Hpuredet. }
  by iIntros "!>" (e' efs' σ (_&->&->)%Hpuredet).
Qed.

Lemma twp_pure_step `{Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  WP e2 @ s; E [{ Φ }] ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply twp_lift_pure_det_step; [done|naive_solver|].
  iModIntro. rewrite /= right_id. by iApply "IH".
Qed.
End lifting.
