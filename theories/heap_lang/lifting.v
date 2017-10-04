From iris.base_logic Require Export gen_heap.
From iris.program_logic Require Export weakestpre lifting.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".
Import uPred.

(** Basic rules for language operations. *)

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ
}.

Instance heapG_irisG `{heapG Σ} : irisG heap_lang Σ := {
  iris_invG := heapG_invG;
  state_interp := gen_heap_ctx
}.
Global Opaque iris_invG.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : uPred_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : uPred_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : uPred_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
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
Context `{heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {E e} K Φ :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. exact: wp_ectx_bind. Qed.

Lemma wp_bindi {E e} Ki Φ :
  WP e @ E {{ v, WP fill_item Ki (of_val v) @ E {{ Φ }} }} ⊢
     WP fill_item Ki e @ E {{ Φ }}.
Proof. exact: weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e Φ :
  ▷ Φ (LitV LitUnit) ∗ ▷ WP e {{ _, True }} ⊢ WP Fork e @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (Fork e) (Lit LitUnit) [e]) //=; eauto.
  - by rewrite -step_fupd_intro // later_sep -(wp_value _ _ (Lit _)) // right_id.
  - intros; inv_head_step; eauto.
Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  repeat lazymatch goal with
  | H: IntoVal ?e _ |- _ => rewrite -(of_to_val e _ into_val); clear H
  | H: AsRec _ _ _ _ |- _ => rewrite H; clear H
  end;
  apply det_head_step_pure_exec; [ solve_exec_safe | solve_exec_puredet ].

Global Instance pure_rec f x (erec e1 e2 : expr) (v2 : val)
    `{!IntoVal e2 v2, AsRec e1 f x erec, Closed (f :b: x :b: []) erec} :
  PureExec True (App e1 e2) (subst' x e2 (subst' f e1 erec)).
Proof. solve_pure_exec. Qed.

Global Instance pure_unop op e v v' `{!IntoVal e v} :
  PureExec (un_op_eval op v = Some v') (UnOp op e) (of_val v').
Proof. solve_pure_exec. Qed.

Global Instance pure_binop op e1 e2 v1 v2 v' `{!IntoVal e1 v1, !IntoVal e2 v2} :
  PureExec (bin_op_eval op v1 v2 = Some v') (BinOp op e1 e2) (of_val v').
Proof. solve_pure_exec. Qed.

Global Instance pure_if_true e1 e2 :
  PureExec True (If (Lit (LitBool true)) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Global Instance pure_if_false e1 e2 :
  PureExec True (If (Lit (LitBool false)) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_fst e1 e2 v1 v2 `{!IntoVal e1 v1, !IntoVal e2 v2} :
  PureExec True (Fst (Pair e1 e2)) e1.
Proof. solve_pure_exec. Qed.

Global Instance pure_snd e1 e2 v1 v2 `{!IntoVal e1 v1, !IntoVal e2 v2} :
  PureExec True (Snd (Pair e1 e2)) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inl e0 v e1 e2 `{!IntoVal e0 v} :
  PureExec True (Case (InjL e0) e1 e2) (App e1 e0).
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inr e0 v e1 e2 `{!IntoVal e0 v} :
  PureExec True (Case (InjR e0) e1 e2) (App e2 e0).
Proof. solve_pure_exec. Qed.

(** Heap *)
Lemma wp_alloc E e v :
  to_val e = Some v →
  {{{ True }}} Alloc e @ E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
Proof.
  iIntros (<-%of_to_val Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_alloc with "Hσ") as "[Hσ Hl]"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_load E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Lit (LitLoc l)) @ E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_store E l v' e v :
  to_val e = Some v →
  {{{ ▷ l ↦ v' }}} Store (Lit (LitLoc l)) e @ E {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (<-%of_to_val Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.

Lemma wp_cas_fail E l q v' e1 v1 e2 v2 :
  to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 →
  {{{ ▷ l ↦{q} v' }}} CAS (Lit (LitLoc l)) e1 e2 @ E
  {{{ RET LitV (LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (<-%of_to_val <-%of_to_val ? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_suc E l e1 v1 e2 v2 :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  {{{ ▷ l ↦ v1 }}} CAS (Lit (LitLoc l)) e1 e2 @ E
  {{{ RET LitV (LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (<-%of_to_val <-%of_to_val Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.

(** Proof rules for derived constructs *)
Lemma wp_seq E e1 e2 Φ :
  is_Some (to_val e1) → Closed [] e2 →
  ▷ WP e2 @ E {{ Φ }} ⊢ WP Seq e1 e2 @ E {{ Φ }}.
Proof. iIntros ([? ?] ?). rewrite -wp_pure_step_later; by eauto. Qed.

Lemma wp_skip E Φ : ▷ Φ (LitV LitUnit) ⊢ WP Skip @ E {{ Φ }}.
Proof. rewrite -wp_seq; last eauto. by rewrite -wp_value. Qed.

Lemma wp_match_inl E e0 x1 e1 x2 e2 Φ :
  is_Some (to_val e0) → Closed (x1 :b: []) e1 →
  ▷ WP subst' x1 e0 e1 @ E {{ Φ }} ⊢ WP Match (InjL e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. iIntros ([? ?] ?) "?". rewrite -!wp_pure_step_later; by eauto. Qed.

Lemma wp_match_inr E e0 x1 e1 x2 e2 Φ :
  is_Some (to_val e0) → Closed (x2 :b: []) e2 →
  ▷ WP subst' x2 e0 e2 @ E {{ Φ }} ⊢ WP Match (InjR e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. iIntros ([? ?] ?) "?". rewrite -!wp_pure_step_later; by eauto. Qed.
End lifting.
