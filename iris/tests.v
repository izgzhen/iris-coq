(** This file tests a bunch of things. *)
Require Import iris.model.

Module ModelTest. (* Make sure we got the notations right. *)
  Definition iResTest (Σ : iParam) (w : iWld Σ) (p : iPst Σ) (g : iGst Σ) : iRes Σ := Res w p g.
End ModelTest.
