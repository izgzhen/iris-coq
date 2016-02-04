(** This file tests a bunch of things. *)
Require Import program_logic.model.

Module ModelTest. (* Make sure we got the notations right. *)
  Definition iResTest {Λ : language} {Σ : iFunctor}
    (w : iWld Λ Σ) (p : iPst Λ) (g : iGst Λ Σ) : iRes Λ Σ := Res w p g.
End ModelTest.
