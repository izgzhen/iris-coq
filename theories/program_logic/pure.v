From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
Set Default Proof Using "Type".

Section pure.
Context {expr val ectx state} {Λ : EctxLanguage expr val ectx state}.
Context `{irisG (ectx_lang expr) Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.

Class PureExec (P : Prop) (e1 e2 : expr) := {
  pure_exec_safe : 
    P -> ∀ σ, head_reducible e1 σ;
  pure_exec_puredet : 
    P -> ∀ σ1 e2' σ2 efs, head_step e1 σ1 e2' σ2 efs -> σ1=σ2 /\ e2=e2' /\ [] = efs;
  }.

Lemma wp_pure `{Inhabited state} K E E' e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  (|={E,E'}▷=> WP fill K e2 @ E {{ Φ }}) ⊢ WP fill K e1 @ E {{ Φ }}.
Proof.
  iIntros (? Hφ) "HWP".
  iApply wp_bind.
  iApply (wp_lift_pure_det_head_step_no_fork with "[HWP]").
  { destruct (pure_exec_safe Hφ inhabitant) as (? & ? & ? & Hst).
    eapply ectx_language.val_stuck.
    apply Hst. }
  { apply (pure_exec_safe Hφ). }
  { apply (pure_exec_puredet Hφ). }
  iApply wp_bind_inv.
  iExact "HWP".
Qed.


Lemma wp_pure' `{Inhabited state} K E e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  (▷ WP fill K e2 @ E {{ Φ }}) ⊢ WP fill K e1 @ E {{ Φ }}.
Proof. 
  intros ? ?.
  rewrite -wp_pure //.
  rewrite -step_fupd_intro //.
Qed.

End pure.
