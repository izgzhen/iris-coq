From iris.program_logic Require Export ectx_weakestpre.
From iris.program_logic Require Import ownership. (* for ownP *)
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics.
From iris.proofmode Require Import weakestpre.
Import uPred.
Local Hint Extern 0 (head_reducible _ _) => do_head_step eauto 2.

Section lifting.
Context {Σ : iFunctor}.
Implicit Types P Q : iProp heap_lang Σ.
Implicit Types Φ : val → iProp heap_lang Σ.
Implicit Types ef : option (expr []).

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {E e} K Φ :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. exact: wp_ectx_bind. Qed.

Lemma wp_bindi {E e} Ki Φ :
  WP e @ E {{ v, WP fill_item Ki (of_val v) @ E {{ Φ }} }} ⊢
     WP fill_item Ki e @ E {{ Φ }}.
Proof. exact: weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateful reductions. *)
Lemma wp_alloc_pst E σ e v Φ :
  to_val e = Some v →
  (▷ ownP σ ★ ▷ (∀ l, σ !! l = None ∧ ownP (<[l:=v]>σ) -★ Φ (LocV l)))
  ⊢ WP Alloc e @ E {{ Φ }}.
Proof.
  (* TODO: This works around ssreflect bug #22. *)
  intros. set (φ (e' : expr []) σ' ef := ∃ l,
    ef = None ∧ e' = Loc l ∧ σ' = <[l:=v]>σ ∧ σ !! l = None).
  rewrite -(wp_lift_atomic_head_step (Alloc e) φ σ) // /φ;
    last (by intros; inv_head_step; eauto 8); last (by simpl; eauto).
  iIntros  "[$ HΦ] >"; iIntros {v2 σ2 ef} "[% HP]".
  (* FIXME: I should not have to refer to "H0". *)
  destruct H0 as (l & -> & [= <-]%of_to_val_flip & -> & ?); simpl.
  iSplit; last done. iApply "HΦ"; by iSplit.
Qed.

Lemma wp_load_pst E σ l v Φ :
  σ !! l = Some v →
  (▷ ownP σ ★ ▷ (ownP σ -★ Φ v)) ⊢ WP Load (Loc l) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_head_step σ v σ None) ?right_id //;
    last (by intros; inv_head_step; eauto using to_of_val); simpl; by eauto.
Qed.

Lemma wp_store_pst E σ l e v v' Φ :
  to_val e = Some v → σ !! l = Some v' →
  (▷ ownP σ ★ ▷ (ownP (<[l:=v]>σ) -★ Φ (LitV LitUnit)))
  ⊢ WP Store (Loc l) e @ E {{ Φ }}.
Proof.
  intros. rewrite-(wp_lift_atomic_det_head_step σ (LitV LitUnit) (<[l:=v]>σ) None)
    ?right_id //; last (by intros; inv_head_step; eauto); simpl; by eauto.
Qed.

Lemma wp_cas_fail_pst E σ l e1 v1 e2 v2 v' Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 → σ !! l = Some v' → v' ≠ v1 →
  (▷ ownP σ ★ ▷ (ownP σ -★ Φ (LitV $ LitBool false)))
  ⊢ WP CAS (Loc l) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_head_step σ (LitV $ LitBool false) σ None)
    ?right_id //; last (by intros; inv_head_step; eauto);
    simpl; by eauto 10.
Qed.

Lemma wp_cas_suc_pst E σ l e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 → σ !! l = Some v1 →
  (▷ ownP σ ★ ▷ (ownP (<[l:=v2]>σ) -★ Φ (LitV $ LitBool true)))
  ⊢ WP CAS (Loc l) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_head_step σ (LitV $ LitBool true)
    (<[l:=v2]>σ) None) ?right_id //; last (by intros; inv_head_step; eauto);
    simpl; by eauto 10.
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e Φ :
  (▷ Φ (LitV LitUnit) ★ ▷ WP e {{ _, True }}) ⊢ WP Fork e @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (Fork e) (Lit LitUnit) (Some e)) //=;
    last by intros; inv_head_step; eauto.
  rewrite later_sep -(wp_value _ _ (Lit _)) //.
Qed.

Lemma wp_rec E f x e1 e2 v Φ :
  to_val e2 = Some v →
  ▷ WP subst' x e2 (subst' f (Rec f x e1) e1) @ E {{ Φ }}
  ⊢ WP App (Rec f x e1) e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step (App _ _)
    (subst' x e2 (subst' f (Rec f x e1) e1)) None) //= ?right_id;
    intros; inv_head_step; eauto.
Qed.

Lemma wp_rec' E f x erec e1 e2 v2 Φ :
  e1 = Rec f x erec →
  to_val e2 = Some v2 →
  ▷ WP subst' x e2 (subst' f e1 erec) @ E {{ Φ }}
  ⊢ WP App e1 e2 @ E {{ Φ }}.
Proof. intros ->. apply wp_rec. Qed.

Lemma wp_un_op E op l l' Φ :
  un_op_eval op l = Some l' →
  ▷ Φ (LitV l') ⊢ WP UnOp op (Lit l) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step (UnOp op _) (Lit l') None)
    ?right_id -?wp_value //; intros; inv_head_step; eauto.
Qed.

Lemma wp_bin_op E op l1 l2 l' Φ :
  bin_op_eval op l1 l2 = Some l' →
  ▷ Φ (LitV l') ⊢ WP BinOp op (Lit l1) (Lit l2) @ E {{ Φ }}.
Proof.
  intros Heval. rewrite -(wp_lift_pure_det_head_step (BinOp op _ _) (Lit l') None)
    ?right_id -?wp_value //; intros; inv_head_step; eauto.
Qed.

Lemma wp_if_true E e1 e2 Φ :
  ▷ WP e1 @ E {{ Φ }} ⊢ WP If (Lit (LitBool true)) e1 e2 @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (If _ _ _) e1 None)
    ?right_id //; intros; inv_head_step; eauto.
Qed.

Lemma wp_if_false E e1 e2 Φ :
  ▷ WP e2 @ E {{ Φ }} ⊢ WP If (Lit (LitBool false)) e1 e2 @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (If _ _ _) e2 None)
    ?right_id //; intros; inv_head_step; eauto.
Qed.

Lemma wp_fst E e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  ▷ Φ v1 ⊢ WP Fst (Pair e1 e2) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step (Fst _) e1 None)
    ?right_id -?wp_value //; intros; inv_head_step; eauto.
Qed.

Lemma wp_snd E e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  ▷ Φ v2 ⊢ WP Snd (Pair e1 e2) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step (Snd _) e2 None)
    ?right_id -?wp_value //; intros; inv_head_step; eauto.
Qed.

Lemma wp_case_inl E e0 v0 e1 e2 Φ :
  to_val e0 = Some v0 →
  ▷ WP App e1 e0 @ E {{ Φ }} ⊢ WP Case (InjL e0) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step (Case _ _ _)
    (App e1 e0) None) ?right_id //; intros; inv_head_step; eauto.
Qed.

Lemma wp_case_inr E e0 v0 e1 e2 Φ :
  to_val e0 = Some v0 →
  ▷ WP App e2 e0 @ E {{ Φ }} ⊢ WP Case (InjR e0) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step (Case _ _ _)
    (App e2 e0) None) ?right_id //; intros; inv_head_step; eauto.
Qed.
End lifting.
