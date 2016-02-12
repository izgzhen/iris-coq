Require Export program_logic.weakestpre heap_lang.heap_lang.
Require Import program_logic.lifting.
Require Import program_logic.ownership. (* for ownP *)
Require Import heap_lang.tactics.
Export heap_lang. (* Prefer heap_lang names over language names. *)
Import uPred.
Local Hint Extern 0 (language.reducible _ _) => do_step ltac:(eauto 2).

Section lifting.
Context {Σ : iFunctor}.
Implicit Types P : iProp heap_lang Σ.
Implicit Types Q : val → iProp heap_lang Σ.
Implicit Types K : ectx.
Implicit Types ef : option expr.

(** Bind. *)
Lemma wp_bind {E e} K Q :
  wp E e (λ v, wp E (fill K (of_val v)) Q) ⊑ wp E (fill K e) Q.
Proof. apply weakestpre.wp_bind. Qed.

Lemma wp_bindi {E e} Ki Q :
  wp E e (λ v, wp E (fill_item Ki (of_val v)) Q) ⊑ wp E (fill_item Ki e) Q.
Proof. apply weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateful reductions. *)
Lemma wp_alloc_pst E σ e v Q :
  to_val e = Some v →
  (ownP σ ★ ▷ (∀ l, σ !! l = None ∧ ownP (<[l:=v]>σ) -★ Q (LocV l)))
       ⊑ wp E (Alloc e) Q.
Proof.
  (* TODO RJ: This works around ssreflect bug #22. *)
  intros. set (φ v' σ' ef := ∃ l,
    ef = None ∧ v' = LocV l ∧ σ' = <[l:=v]>σ ∧ σ !! l = None).
  rewrite -(wp_lift_atomic_step (Alloc e) φ σ) // /φ;
    last by intros; inv_step; eauto 8.
  apply sep_mono, later_mono; first done.
  apply forall_intro=>e2; apply forall_intro=>σ2; apply forall_intro=>ef.
  apply wand_intro_l.
  rewrite always_and_sep_l -assoc -always_and_sep_l.
  apply const_elim_l=>-[l [-> [-> [-> ?]]]].
  by rewrite (forall_elim l) right_id const_equiv // left_id wand_elim_r.
Qed.

Lemma wp_load_pst E σ l v Q :
  σ !! l = Some v →
  (ownP σ ★ ▷ (ownP σ -★ Q v)) ⊑ wp E (Load (Loc l)) Q.
Proof.
  intros. rewrite -(wp_lift_atomic_det_step σ v σ None) ?right_id //;
    last by intros; inv_step; eauto using to_of_val.
Qed.

Lemma wp_store_pst E σ l e v v' Q :
  to_val e = Some v → σ !! l = Some v' →
  (ownP σ ★ ▷ (ownP (<[l:=v]>σ) -★ Q (LitV LitUnit))) ⊑ wp E (Store (Loc l) e) Q.
Proof.
  intros. rewrite -(wp_lift_atomic_det_step σ (LitV LitUnit) (<[l:=v]>σ) None)
    ?right_id //; last by intros; inv_step; eauto.
Qed.

Lemma wp_cas_fail_pst E σ l e1 v1 e2 v2 v' Q :
  to_val e1 = Some v1 → to_val e2 = Some v2 → σ !! l = Some v' → v' ≠ v1 →
  (ownP σ ★ ▷ (ownP σ -★ Q (LitV $ LitBool false))) ⊑ wp E (Cas (Loc l) e1 e2) Q.
Proof.
  intros. rewrite -(wp_lift_atomic_det_step σ (LitV $ LitBool false) σ None)
    ?right_id //; last by intros; inv_step; eauto.
Qed.

Lemma wp_cas_suc_pst E σ l e1 v1 e2 v2 Q :
  to_val e1 = Some v1 → to_val e2 = Some v2 → σ !! l = Some v1 →
  (ownP σ ★ ▷ (ownP (<[l:=v2]>σ) -★ Q (LitV $ LitBool true)))
  ⊑ wp E (Cas (Loc l) e1 e2) Q.
Proof.
  intros. rewrite -(wp_lift_atomic_det_step σ (LitV $ LitBool true) (<[l:=v2]>σ) None)
    ?right_id //; last by intros; inv_step; eauto.
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e :
  ▷ wp (Σ:=Σ) coPset_all e (λ _, True) ⊑ wp E (Fork e) (λ v, v = LitV LitUnit).
Proof.
  rewrite -(wp_lift_pure_det_step (Fork e) (Lit LitUnit) (Some e)) //=;
    last by intros; inv_step; eauto.
  apply later_mono, sep_intro_True_l; last done.
  by rewrite -(wp_value _ _ (Lit _)) //; apply const_intro.
Qed.

(* For the lemmas involving substitution, we only derive a preliminary version.
   The final version is defined in substitution.v. *)
Lemma wp_rec' E f x e1 e2 v Q :
  to_val e2 = Some v →
  ▷ wp E (subst (subst e1 f (RecV f x e1)) x v) Q ⊑ wp E (App (Rec f x e1) e2) Q.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (App _ _)
    (subst (subst e1 f (RecV f x e1)) x v) None) ?right_id //=;
    intros; inv_step; eauto.
Qed.

Lemma wp_un_op E op l l' Q :
  un_op_eval op l = Some l' →
  ▷ Q (LitV l') ⊑ wp E (UnOp op (Lit l)) Q.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (UnOp op _) (Lit l') None)
    ?right_id -?wp_value //; intros; inv_step; eauto.
Qed.

Lemma wp_bin_op E op l1 l2 l' Q :
  bin_op_eval op l1 l2 = Some l' →
  ▷ Q (LitV l') ⊑ wp E (BinOp op (Lit l1) (Lit l2)) Q.
Proof.
  intros Heval. rewrite -(wp_lift_pure_det_step (BinOp op _ _) (Lit l') None)
    ?right_id -?wp_value //; intros; inv_step; eauto.
Qed.

Lemma wp_if_true E e1 e2 Q : ▷ wp E e1 Q ⊑ wp E (If (Lit $ LitBool true) e1 e2) Q.
Proof.
  rewrite -(wp_lift_pure_det_step (If _ _ _) e1 None)
    ?right_id //; intros; inv_step; eauto.
Qed.

Lemma wp_if_false E e1 e2 Q : ▷ wp E e2 Q ⊑ wp E (If (Lit $ LitBool false) e1 e2) Q.
Proof.
  rewrite -(wp_lift_pure_det_step (If _ _ _) e2 None)
    ?right_id //; intros; inv_step; eauto.
Qed.

Lemma wp_fst E e1 v1 e2 v2 Q :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  ▷ Q v1 ⊑ wp E (Fst $ Pair e1 e2) Q.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (Fst _) e1 None)
    ?right_id -?wp_value //; intros; inv_step; eauto.
Qed.

Lemma wp_snd E e1 v1 e2 v2 Q :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  ▷ Q v2 ⊑ wp E (Snd $ Pair e1 e2) Q.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (Snd _) e2 None)
    ?right_id -?wp_value //; intros; inv_step; eauto.
Qed.

Lemma wp_case_inl' E e0 v0 x1 e1 x2 e2 Q :
  to_val e0 = Some v0 →
  ▷ wp E (subst e1 x1 v0) Q ⊑ wp E (Case (InjL e0) x1 e1 x2 e2) Q.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (Case _ _ _ _ _)
    (subst e1 x1 v0) None) ?right_id //; intros; inv_step; eauto.
Qed.

Lemma wp_case_inr' E e0 v0 x1 e1 x2 e2 Q :
  to_val e0 = Some v0 →
  ▷ wp E (subst e2 x2 v0) Q ⊑ wp E (Case (InjR e0) x1 e1 x2 e2) Q.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (Case _ _ _ _ _)
    (subst e2 x2 v0) None) ?right_id //; intros; inv_step; eauto.
Qed.

End lifting.
