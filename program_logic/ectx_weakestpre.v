From iris.program_logic Require Export ectx_language weakestpre lifting.
From iris.program_logic Require Import ownership.

Section wp.
Context {expr val ectx state} {Λ : EctxLanguage expr val ectx state}.
Context {Σ : iFunctor}.
Implicit Types P : iProp (ectx_lang Λ) Σ.
Implicit Types Φ : val → iProp (ectx_lang Λ) Σ.
Implicit Types v : val.
Implicit Types e : expr.
Hint Resolve head_prim_reducible head_reducible_prim_step.

Notation wp_fork ef := (default True ef (flip (wp ⊤) (λ _, True)))%I.

Lemma wp_ectx_bind {E e} K Φ :
  WP e @ E {{ λ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. apply: weakestpre.wp_bind. Qed.

Lemma wp_lift_head_step E1 E2
    (φ : expr → state → option expr → Prop) Φ e1 σ1 :
  E2 ⊆ E1 → to_val e1 = None →
  head_reducible e1 σ1 →
  (∀ e2 σ2 ef, head_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  (|={E1,E2}=> ▷ ownP σ1 ★ ▷ ∀ e2 σ2 ef,
    (■ φ e2 σ2 ef ∧ ownP σ2) -★ |={E2,E1}=> WP e2 @ E1 {{ Φ }} ★ wp_fork ef)
  ⊢ WP e1 @ E1 {{ Φ }}.
Proof. eauto using wp_lift_step. Qed.

Lemma wp_lift_pure_head_step E (φ : expr → option expr → Prop) Φ e1 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2 ef, head_step e1 σ1 e2 σ2 ef → σ1 = σ2 ∧ φ e2 ef) →
  (▷ ∀ e2 ef, ■ φ e2 ef → WP e2 @ E {{ Φ }} ★ wp_fork ef) ⊢ WP e1 @ E {{ Φ }}.
Proof. eauto using wp_lift_pure_step. Qed.

Lemma wp_lift_atomic_head_step {E Φ} e1
    (φ : expr → state → option expr → Prop) σ1 :
  atomic e1 →
  head_reducible e1 σ1 →
  (∀ e2 σ2 ef,
    head_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  (▷ ownP σ1 ★ ▷ ∀ v2 σ2 ef, ■ φ (of_val v2) σ2 ef ∧ ownP σ2 -★ Φ v2 ★ wp_fork ef)
  ⊢ WP e1 @ E {{ Φ }}.
Proof. eauto using wp_lift_atomic_step. Qed.

Lemma wp_lift_atomic_det_head_step {E Φ e1} σ1 v2 σ2 ef :
  atomic e1 →
  head_reducible e1 σ1 →
  (∀ e2' σ2' ef', head_step e1 σ1 e2' σ2' ef' →
    σ2 = σ2' ∧ to_val e2' = Some v2 ∧ ef = ef') →
  (▷ ownP σ1 ★ ▷ (ownP σ2 -★ Φ v2 ★ wp_fork ef)) ⊢ WP e1 @ E {{ Φ }}.
Proof. eauto using wp_lift_atomic_det_step. Qed.

Lemma wp_lift_pure_det_head_step {E Φ} e1 e2 ef :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 ef', head_step e1 σ1 e2' σ2 ef' → σ1 = σ2 ∧ e2 = e2' ∧ ef = ef')→
  ▷ (WP e2 @ E {{ Φ }} ★ wp_fork ef) ⊢ WP e1 @ E {{ Φ }}.
Proof. eauto using wp_lift_pure_det_step. Qed.
End wp.
