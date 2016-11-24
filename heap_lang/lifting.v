From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import fin_maps.
Import uPred.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (atomic _) => solve_atomic.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.

Local Hint Constructors head_step.
Local Hint Resolve alloc_fresh.
Local Hint Resolve to_of_val.

Section lifting.
Context `{irisG heap_lang Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {E e} K Φ :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. exact: wp_ectx_bind. Qed.

Lemma wp_bind_ctxi {E e} Ki Φ :
  WP e @ E {{ v, WP fill_item Ki (of_val v) @ E {{ Φ }} }} ⊢
     WP fill_item Ki e @ E {{ Φ }}.
Proof. exact: weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e Φ :
  ▷ Φ (LitV LitUnit) ∗ ▷ WP e {{ _, True }} ⊢ WP Fork e @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (Fork e) (Lit LitUnit) [e]) //=; eauto.
  - by rewrite later_sep -(wp_value _ _ (Lit _)) // big_sepL_singleton.
  - intros; inv_head_step; eauto.
Qed.

Lemma wp_rec E f x erec e1 e2 Φ :
  e1 = Rec f x erec →
  is_Some (to_val e2) →
  Closed (f :b: x :b: []) erec →
  ▷ WP subst' x e2 (subst' f e1 erec) @ E {{ Φ }} ⊢ WP App e1 e2 @ E {{ Φ }}.
Proof.
  intros -> [v2 ?] ?. rewrite -(wp_lift_pure_det_head_step_no_fork (App _ _)
    (subst' x e2 (subst' f (Rec f x erec) erec))); eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_un_op E op e v v' Φ :
  to_val e = Some v →
  un_op_eval op v = Some v' →
  ▷ Φ v' ⊢ WP UnOp op e @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step_no_fork (UnOp op _) (of_val v'))
    -?wp_value'; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_bin_op E op e1 e2 v1 v2 v' Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  bin_op_eval op v1 v2 = Some v' →
  ▷ (Φ v') ⊢ WP BinOp op e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step_no_fork (BinOp op _ _) (of_val v'))
    -?wp_value'; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_if_true E e1 e2 Φ :
  ▷ WP e1 @ E {{ Φ }} ⊢ WP If (Lit (LitBool true)) e1 e2 @ E {{ Φ }}.
Proof.
  apply wp_lift_pure_det_head_step_no_fork; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_if_false E e1 e2 Φ :
  ▷ WP e2 @ E {{ Φ }} ⊢ WP If (Lit (LitBool false)) e1 e2 @ E {{ Φ }}.
Proof.
  apply wp_lift_pure_det_head_step_no_fork; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_fst E e1 v1 e2 Φ :
  to_val e1 = Some v1 → is_Some (to_val e2) →
  ▷ Φ v1 ⊢ WP Fst (Pair e1 e2) @ E {{ Φ }}.
Proof.
  intros ? [v2 ?].
  rewrite -(wp_lift_pure_det_head_step_no_fork (Fst _) e1) -?wp_value; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_snd E e1 e2 v2 Φ :
  is_Some (to_val e1) → to_val e2 = Some v2 →
  ▷ Φ v2 ⊢ WP Snd (Pair e1 e2) @ E {{ Φ }}.
Proof.
  intros [v1 ?] ?.
  rewrite -(wp_lift_pure_det_head_step_no_fork (Snd _) e2) -?wp_value; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_case_inl E e0 e1 e2 Φ :
  is_Some (to_val e0) →
  ▷ WP App e1 e0 @ E {{ Φ }} ⊢ WP Case (InjL e0) e1 e2 @ E {{ Φ }}.
Proof.
  intros [v0 ?].
  rewrite -(wp_lift_pure_det_head_step_no_fork (Case _ _ _) (App e1 e0)); eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_case_inr E e0 e1 e2 Φ :
  is_Some (to_val e0) →
  ▷ WP App e2 e0 @ E {{ Φ }} ⊢ WP Case (InjR e0) e1 e2 @ E {{ Φ }}.
Proof.
  intros [v0 ?].
  rewrite -(wp_lift_pure_det_head_step_no_fork (Case _ _ _) (App e2 e0)); eauto.
  intros; inv_head_step; eauto.
Qed.
End lifting.
