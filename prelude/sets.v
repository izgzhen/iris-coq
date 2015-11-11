(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements sets as functions into Prop. *)
Require Export prelude.

Record set (A : Type) : Type := mkSet { set_car : A → Prop }.
Arguments mkSet {_} _.
Arguments set_car {_} _ _.
Definition set_all {A} : set A := mkSet (λ _, True).
Instance set_empty {A} : Empty (set A) := mkSet (λ _, False).
Instance set_singleton {A} : Singleton A (set A) := λ x, mkSet (x =).
Instance set_elem_of {A} : ElemOf A (set A) := λ x X, set_car X x.
Instance set_union {A} : Union (set A) := λ X1 X2, mkSet (λ x, x ∈ X1 ∨ x ∈ X2).
Instance set_intersection {A} : Intersection (set A) := λ X1 X2,
  mkSet (λ x, x ∈ X1 ∧ x ∈ X2).
Instance set_difference {A} : Difference (set A) := λ X1 X2,
  mkSet (λ x, x ∈ X1 ∧ x ∉ X2).
Instance set_collection : Collection A (set A).
Proof. by split; [split | |]; repeat intro. Qed.

Instance set_ret : MRet set := λ A (x : A), {[ x ]}.
Instance set_bind : MBind set := λ A B (f : A → set B) (X : set A),
  mkSet (λ b, ∃ a, b ∈ f a ∧ a ∈ X).
Instance set_fmap : FMap set := λ A B (f : A → B) (X : set A),
  mkSet (λ b, ∃ a, b = f a ∧ a ∈ X).
Instance set_join : MJoin set := λ A (XX : set (set A)),
  mkSet (λ a, ∃ X, a ∈ X ∧ X ∈ XX).
Instance set_collection_monad : CollectionMonad set.
Proof. by split; try apply _. Qed.

Global Opaque set_union set_intersection.