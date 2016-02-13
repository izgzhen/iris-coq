(** This file tests a bunch of things. *)
From program_logic Require Import model.

Module ModelTest. (* Make sure we got the notations right. *)
  Definition iResTest {Λ : language} {Σ : iFunctor}
    (w : iWld Λ Σ) (p : iPst Λ) (g : iGst Λ Σ) : iRes Λ Σ := Res w p (Some g).
End ModelTest.
