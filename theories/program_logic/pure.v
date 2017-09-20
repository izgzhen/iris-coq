From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting language ectx_language.
Set Default Proof Using "Type".

Section pure_language.
Context `{irisG Λ Σ}.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types φ : Prop.
Implicit Types e : expr Λ.

Class PureExec (P : Prop) (e1 e2 : expr Λ) := {
  pure_exec_safe : 
    P -> ∀ σ, language.reducible e1 σ;
  pure_exec_puredet : 
    P -> ∀ σ1 e2' σ2 efs, language.prim_step e1 σ1 e2' σ2 efs -> σ1=σ2 /\ e2=e2' /\ [] = efs;
  }.

Lemma wp_pure `{Inhabited (state Λ)} E E' e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  (|={E,E'}▷=> WP e2 @ E {{ Φ }}) ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (? Hφ) "HWP".
  iApply (wp_lift_pure_det_step with "[HWP]").
  { apply (pure_exec_safe Hφ). }
  { apply (pure_exec_puredet Hφ). }
  rewrite big_sepL_nil right_id //.
Qed.

Lemma wp_pure' `{Inhabited (state Λ)} E e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  (▷ WP e2 @ E {{ Φ }}) ⊢ WP e1 @ E {{ Φ }}.
Proof. 
  intros ? ?.
  rewrite -wp_pure //.
  rewrite -step_fupd_intro //.
Qed.

Lemma hoist_pred_pureexec (P : Prop) (e1 e2 : expr Λ) :
  (P → PureExec True e1 e2) →
  PureExec P e1 e2.
Proof.
  intros HPE.
  split; intros HP; destruct (HPE HP); eauto.
Qed.

End pure_language.

Section pure_ectx_language.
Context {expr val ectx state} {Λ : EctxLanguage expr val ectx state}.
Context `{irisG (ectx_lang expr) Σ} {Hinh : Inhabited state}.

Lemma det_head_step_pureexec (e1 e2 : expr) :
  (∀ σ, head_reducible e1 σ) →
  (∀ σ1 e2' σ2 efs, head_step e1 σ1 e2' σ2 efs -> σ1=σ2 /\ e2=e2' /\ [] = efs) →
  PureExec True e1 e2.
Proof.
  intros Hp1 Hp2.
  split; intros _.
  - intros σ. destruct (Hp1 σ) as (? & ? & ? & ?).
    do 3 eexists. simpl.
    eapply (Ectx_step _ _ _ _ _ empty_ectx); eauto using fill_empty.
  - move => σ1 e2' σ2 efs /=.
    intros ?%head_reducible_prim_step; eauto.
Qed.

End pure_ectx_language.
