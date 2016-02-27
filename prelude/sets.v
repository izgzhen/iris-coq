(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements sets as functions into Prop. *)
From prelude Require Export collections.

Record set (A : Type) : Type := mkSet { set_car : A → Prop }.
Add Printing Constructor set.
Arguments mkSet {_} _.
Arguments set_car {_} _ _.
Notation "{[ x | P ]}" := (mkSet (λ x, P))
  (at level 1, format "{[  x  |  P  ]}") : C_scope.

Instance set_elem_of {A} : ElemOf A (set A) := λ x X, set_car X x.

Instance set_top {A} : Top (set A) := {[ _ | True ]}.
Instance set_empty {A} : Empty (set A) := {[ _ | False ]}.
Instance set_singleton {A} : Singleton A (set A) := λ y, {[ x | y = x ]}.
Instance set_union {A} : Union (set A) := λ X1 X2, {[ x | x ∈ X1 ∨ x ∈ X2 ]}.
Instance set_intersection {A} : Intersection (set A) := λ X1 X2,
  {[ x | x ∈ X1 ∧ x ∈ X2 ]}.
Instance set_difference {A} : Difference (set A) := λ X1 X2,
  {[ x | x ∈ X1 ∧ x ∉ X2 ]}.
Instance set_collection : Collection A (set A).
Proof. split; [split | |]; by repeat intro. Qed.

Lemma elem_of_top {A} (x : A) : x ∈ ⊤ ↔ True.
Proof. done. Qed.
Lemma elem_of_mkSet {A} (P : A → Prop) x : x ∈ {[ x | P x ]} ↔ P x.
Proof. done. Qed.
Lemma not_elem_of_mkSet {A} (P : A → Prop) x : x ∉ {[ x | P x ]} ↔ ¬P x.
Proof. done. Qed.
Lemma top_subseteq {A} (X : set A) : X ⊆ ⊤.
Proof. done. Qed.
Hint Resolve top_subseteq.

Instance set_ret : MRet set := λ A (x : A), {[ x ]}.
Instance set_bind : MBind set := λ A B (f : A → set B) (X : set A),
  mkSet (λ b, ∃ a, b ∈ f a ∧ a ∈ X).
Instance set_fmap : FMap set := λ A B (f : A → B) (X : set A),
  {[ b | ∃ a, b = f a ∧ a ∈ X ]}.
Instance set_join : MJoin set := λ A (XX : set (set A)),
  {[ a | ∃ X, a ∈ X ∧ X ∈ XX ]}.
Instance set_collection_monad : CollectionMonad set.
Proof. by split; try apply _. Qed.

Instance set_unfold_set_all {A} (x : A) : SetUnfold (x ∈ (⊤ : set A)) True.
Proof. by constructor. Qed.
Instance set_unfold_mkSet {A} (P : A → Prop) x Q :
  SetUnfoldSimpl (P x) Q → SetUnfold (x ∈ mkSet P) Q.
Proof. intros HPQ. constructor. apply HPQ. Qed.

Global Opaque set_elem_of set_top set_empty set_singleton.
Global Opaque set_union set_intersection set_difference.
Global Opaque set_ret set_bind set_fmap set_join.