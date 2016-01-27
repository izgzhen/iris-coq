(** This file is essentially a bunch of testcases. *)
Require Import modures.base.
Require Import barrier.lifting.

Module LangTests.
  Definition add := Op2 plus (Lit 21) (Lit 21).

  Goal ∀ σ, prim_step add σ (Lit 42) σ None.
  Proof.
    apply Op2S.
  Qed.

  Definition rec := Rec (App (Var 1) (Var 0)). (* fix f x => f x *)
  Definition rec_app := App rec (Lit 0).
  Goal ∀ σ, prim_step rec_app σ rec_app σ None.
  Proof.
    move=>?. eapply BetaS. (* Honestly, I have no idea why this works. *)
    reflexivity.
  Qed.

  Definition lam := Lam (Op2 plus (Var 0) (Lit 21)).
  Goal ∀ σ, prim_step (App lam (Lit 21)) σ add σ None.
  Proof.
    move=>?. eapply BetaS. reflexivity.
  Qed.
End LangTests.

Module ParamTests.
  Print Assumptions Σ.
End ParamTests.
