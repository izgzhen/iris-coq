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
    rewrite -(wp_bind _ _ (LetCtx EmptyCtx e2)). rewrite -wp_mono.
    { eapply wp_alloc; done. }
    move=>v; apply exist_elim=>l. apply const_elim_l; move=>[-> _] {v}.
    rewrite (later_intro (ownP _)); apply wp_lam. asimpl.
    rewrite -(wp_bind _ _ (SeqCtx (StoreRCtx (LocV _)
                                   (PlusLCtx EmptyCtx _)) (Load (Loc _)))).
    rewrite -wp_mono.
    { eapply wp_load. apply: lookup_insert. } (* RJ TODO: figure out why apply and eapply fail. *)
    move=>v; apply const_elim_l; move=>-> {v}.
    rewrite -(wp_bind _ _ (SeqCtx (StoreRCtx (LocV _) EmptyCtx) (Load (Loc _)))).
    rewrite -wp_plus -later_intro.
    rewrite -(wp_bind _ _ (SeqCtx EmptyCtx (Load (Loc _)))).
    rewrite -wp_mono.
    { eapply wp_store; first reflexivity. apply: lookup_insert. }
    move=>v; apply const_elim_l; move=>-> {v}.
    rewrite (later_intro (ownP _)); apply wp_lam. asimpl.
    rewrite -wp_mono.
    { eapply wp_load. apply: lookup_insert. }
    move=>v; apply const_elim_l; move=>-> {v}.
    by apply const_intro.
  Qed.
End LiftingTests.
