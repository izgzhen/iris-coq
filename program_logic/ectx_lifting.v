(** Some derived lemmas for ectx-based languages *)
From iris.program_logic Require Export ectx_language weakestpre lifting.
From iris.program_logic Require Import ownership.
From iris.proofmode Require Import weakestpre.

Section wp.
Context {expr val ectx state} {Λ : EctxLanguage expr val ectx state}.
Context `{irisG (ectx_lang expr) Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.
Hint Resolve head_prim_reducible head_reducible_prim_step.

Lemma wp_ectx_bind {E e} K Φ :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. apply: weakestpre.wp_bind. Qed.

Lemma wp_lift_head_step E Φ e1 :
  to_val e1 = None →
  (|={E,∅}=> ∃ σ1, ■ head_reducible e1 σ1 ★ ▷ ownP σ1 ★
    ▷ ∀ e2 σ2 efs, ■ head_step e1 σ1 e2 σ2 efs ★ ownP σ2
          ={∅,E}=★ WP e2 @ E {{ Φ }} ★ [★ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step E); try done.
  iVs "H" as (σ1) "(%&Hσ1&Hwp)". iVsIntro. iExists σ1.
  iSplit; first by eauto. iFrame. iNext. iIntros (e2 σ2 efs) "[% ?]".
  iApply "Hwp". by eauto.
Qed.

Lemma wp_lift_pure_head_step E Φ e1 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (▷ ∀ e2 efs σ, ■ head_step e1 σ e2 σ efs →
    WP e2 @ E {{ Φ }} ★ [★ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (???) "H". iApply wp_lift_pure_step; eauto. iNext.
  iIntros (????). iApply "H". eauto.
Qed.

Lemma wp_lift_atomic_head_step {E Φ} e1 σ1 :
  atomic e1 →
  head_reducible e1 σ1 →
  ▷ ownP σ1 ★ ▷ (∀ v2 σ2 efs,
  ■ head_step e1 σ1 (of_val v2) σ2 efs ∧ ownP σ2 -★
    (|={E}=> Φ v2) ★ [★ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (??) "[? H]". iApply wp_lift_atomic_step; eauto. iFrame. iNext.
  iIntros (???) "[% ?]". iApply "H". eauto.
Qed.

Lemma wp_lift_atomic_det_head_step {E Φ e1} σ1 v2 σ2 efs :
  atomic e1 →
  head_reducible e1 σ1 →
  (∀ e2' σ2' efs', head_step e1 σ1 e2' σ2' efs' →
    σ2 = σ2' ∧ to_val e2' = Some v2 ∧ efs = efs') →
  ▷ ownP σ1 ★ ▷ (ownP σ2 -★
    (|={E}=> Φ v2) ★ [★ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof. eauto using wp_lift_atomic_det_step. Qed.

Lemma wp_lift_atomic_det_head_step' {E Φ e1} σ1 v2 σ2 :
  atomic e1 →
  head_reducible e1 σ1 →
  (∀ e2' σ2' efs', head_step e1 σ1 e2' σ2' efs' →
    σ2 = σ2' ∧ to_val e2' = Some v2 ∧ [] = efs') →
  ▷ ownP σ1 ★ ▷ (ownP σ2 ={E}=★ Φ v2) ⊢ WP e1 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_head_step σ1 v2 σ2 [])
    ?big_sepL_nil ?right_id; eauto.
Qed.

Lemma wp_lift_pure_det_head_step {E Φ} e1 e2 efs :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs', head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
  ▷ (WP e2 @ E {{ Φ }} ★ [★ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof. eauto using wp_lift_pure_det_step. Qed.

Lemma wp_lift_pure_det_head_step' {E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs', head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  ▷ WP e2 @ E {{ Φ }} ⊢ WP e1 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 []) ?big_sepL_nil ?right_id; eauto.
Qed.
End wp.
