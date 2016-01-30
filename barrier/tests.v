(** This file is essentially a bunch of testcases. *)
Require Import modures.logic.
Require Import barrier.lifting.
Import uPred.

Module LangTests.
  Definition add :=  Plus (LitNat 21) (LitNat 21).
  Goal ∀ σ, prim_step add σ (LitNat 42) σ None.
  Proof.
    constructor.
  Qed.

  Definition rec := Rec (App (Var 0) (Var 1)). (* fix f x => f x *)
  Definition rec_app := App rec (LitNat 0).
  Goal ∀ σ, prim_step rec_app σ rec_app σ None.
  Proof.
    move=>?. eapply BetaS.
    reflexivity.
  Qed.

  Definition lam := Lam (Plus (Var 0) (LitNat 21)).
  Goal ∀ σ, prim_step (App lam (LitNat 21)) σ add σ None.
  Proof.
    move=>?. eapply BetaS. reflexivity.
  Qed.
End LangTests.

Module ParamTests.
  Print Assumptions Σ.
End ParamTests.

Module LiftingTests.
  (* TODO RJ: Some syntactic sugar for language expressions would be nice. *)
  Definition e3 := Load (Var 0).
  Definition e2 := Seq (Store (Var 0) (Plus (Load (Var 0)) (LitNat 1))) e3.
  Definition e := Let (Alloc (LitNat 1)) e2.
  Goal ∀ σ E, (ownP (Σ:=Σ) σ) ⊑ (wp (Σ:=Σ) E e (λ v, ■(v = LitNatV 2))).
  Proof.
    move=> σ E. rewrite /e.
    rewrite -(wp_bind _ _ (LetCtx EmptyCtx e2)). rewrite -wp_alloc_pst; last done.
    apply sep_intro_True_r; first done.
    rewrite -later_intro. apply forall_intro=>l.
    apply wand_intro_l. rewrite right_id. apply const_elim_l; move=>_.
    rewrite -wp_lam -later_intro. asimpl.
    rewrite -(wp_bind _ _ (SeqCtx (StoreRCtx (LocV _)
                                   (PlusLCtx EmptyCtx _)) (Load (Loc _)))).
    rewrite -wp_load_pst; first (apply sep_intro_True_r; first done); last first.
    { apply: lookup_insert. } (* RJ TODO: figure out why apply and eapply fail. *)
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    rewrite -(wp_bind _ _ (SeqCtx (StoreRCtx (LocV _) EmptyCtx) (Load (Loc _)))).
    rewrite -wp_plus -later_intro.
    rewrite -(wp_bind _ _ (SeqCtx EmptyCtx (Load (Loc _)))).
    rewrite -wp_store_pst; first (apply sep_intro_True_r; first done); last first.
    { apply: lookup_insert. }
    { reflexivity. }
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    rewrite -wp_lam -later_intro. asimpl.
    rewrite -wp_load_pst; first (apply sep_intro_True_r; first done); last first.
    { apply: lookup_insert. }
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    by apply const_intro.
  Qed.
End LiftingTests.
