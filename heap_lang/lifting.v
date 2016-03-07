From program_logic Require Export weakestpre.
From heap_lang Require Export lang.
From program_logic Require Import lifting.
From program_logic Require Import ownership. (* for ownP *)
From heap_lang Require Import tactics.
Import uPred.
Local Hint Extern 0 (language.reducible _ _) => do_step ltac:(eauto 2).

Section lifting.
Context {Σ : iFunctor}.
Implicit Types P Q : iProp heap_lang Σ.
Implicit Types Φ : val → iProp heap_lang Σ.
Implicit Types K : ectx.
Implicit Types ef : option (expr []).

(** Bind. *)
Lemma wp_bind {E e} K Φ :
  #> e @ E {{ λ v, #> fill K (of_val v) @ E {{ Φ }}}} ⊑ #> fill K e @ E {{ Φ }}.
Proof. apply weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateful reductions. *)
Lemma wp_alloc_pst E σ e v Φ :
  to_val e = Some v →
  (▷ ownP σ ★ ▷ (∀ l, σ !! l = None ∧ ownP (<[l:=v]>σ) -★ Φ (LocV l)))
  ⊑ #> Alloc e @ E {{ Φ }}.
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

Lemma wp_load_pst E σ l v Φ :
  σ !! l = Some v →
  (▷ ownP σ ★ ▷ (ownP σ -★ Φ v)) ⊑ #> Load (Loc l) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_step σ v σ None) ?right_id //;
    last by intros; inv_step; eauto using to_of_val.
Qed.

Lemma wp_store_pst E σ l e v v' Φ :
  to_val e = Some v → σ !! l = Some v' →
  (▷ ownP σ ★ ▷ (ownP (<[l:=v]>σ) -★ Φ (LitV LitUnit)))
  ⊑ #> Store (Loc l) e @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_step σ (LitV LitUnit) (<[l:=v]>σ) None)
    ?right_id //; last by intros; inv_step; eauto.
Qed.

Lemma wp_cas_fail_pst E σ l e1 v1 e2 v2 v' Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 → σ !! l = Some v' → v' ≠ v1 →
  (▷ ownP σ ★ ▷ (ownP σ -★ Φ (LitV $ LitBool false)))
  ⊑ #> CAS (Loc l) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_step σ (LitV $ LitBool false) σ None)
    ?right_id //; last by intros; inv_step; eauto.
Qed.

Lemma wp_cas_suc_pst E σ l e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 → σ !! l = Some v1 →
  (▷ ownP σ ★ ▷ (ownP (<[l:=v2]>σ) -★ Φ (LitV $ LitBool true)))
  ⊑ #> CAS (Loc l) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_step σ (LitV $ LitBool true)
    (<[l:=v2]>σ) None) ?right_id //; last by intros; inv_step; eauto.
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e Φ :
  (▷ Φ (LitV LitUnit) ★ ▷ #> e {{ λ _, True }}) ⊑ #> Fork e @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_step (Fork e) (Lit LitUnit) (Some e)) //=;
    last by intros; inv_step; eauto.
  rewrite later_sep -(wp_value _ _ (Lit _)) //.
Qed.

Lemma wp_rec E f x e1 e2 v Φ :
  to_val e2 = Some v →
  ▷ #> subst' x e2 (subst' f (Rec f x e1) e1) @ E {{ Φ }}
  ⊑ #> App (Rec f x e1) e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (App _ _)
    (subst' x e2 (subst' f (Rec f x e1) e1)) None) //= ?right_id;
    intros; inv_step; eauto.
Qed.

Lemma wp_rec' E f x erec e1 e2 v2 Φ :
  e1 = Rec f x erec →
  to_val e2 = Some v2 →
  ▷ #> subst' x e2 (subst' f e1 erec) @ E {{ Φ }}
  ⊑ #> App e1 e2 @ E {{ Φ }}.
Proof. intros ->. apply wp_rec. Qed.

Lemma wp_un_op E op l l' Φ :
  un_op_eval op l = Some l' →
  ▷ Φ (LitV l') ⊑ #> UnOp op (Lit l) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (UnOp op _) (Lit l') None)
    ?right_id -?wp_value //; intros; inv_step; eauto.
Qed.

Lemma wp_bin_op E op l1 l2 l' Φ :
  bin_op_eval op l1 l2 = Some l' →
  ▷ Φ (LitV l') ⊑ #> BinOp op (Lit l1) (Lit l2) @ E {{ Φ }}.
Proof.
  intros Heval. rewrite -(wp_lift_pure_det_step (BinOp op _ _) (Lit l') None)
    ?right_id -?wp_value //; intros; inv_step; eauto.
Qed.

Lemma wp_if_true E e1 e2 Φ :
  ▷ #> e1 @ E {{ Φ }} ⊑ #> If (Lit (LitBool true)) e1 e2 @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_step (If _ _ _) e1 None)
    ?right_id //; intros; inv_step; eauto.
Qed.

Lemma wp_if_false E e1 e2 Φ :
  ▷ #> e2 @ E {{ Φ }} ⊑ #> If (Lit (LitBool false)) e1 e2 @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_step (If _ _ _) e2 None)
    ?right_id //; intros; inv_step; eauto.
Qed.

Lemma wp_fst E e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  ▷ Φ v1 ⊑ #> Fst (Pair e1 e2) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (Fst _) e1 None)
    ?right_id -?wp_value //; intros; inv_step; eauto.
Qed.

Lemma wp_snd E e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  ▷ Φ v2 ⊑ #> Snd (Pair e1 e2) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (Snd _) e2 None)
    ?right_id -?wp_value //; intros; inv_step; eauto.
Qed.

Lemma wp_case_inl E e0 v0 e1 e2 Φ :
  to_val e0 = Some v0 →
  ▷ #> App e1 e0 @ E {{ Φ }} ⊑ #> Case (InjL e0) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (Case _ _ _)
    (App e1 e0) None) ?right_id //; intros; inv_step; eauto.
Qed.

Lemma wp_case_inr E e0 v0 e1 e2 Φ :
  to_val e0 = Some v0 →
  ▷ #> App e2 e0 @ E {{ Φ }} ⊑ #> Case (InjR e0) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_step (Case _ _ _)
    (App e2 e0) None) ?right_id //; intros; inv_step; eauto.
Qed.

End lifting.
