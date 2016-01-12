(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import Ascii.
Require Export String prelude.countable.

(** * Fix scopes *)
Open Scope string_scope.
Open Scope list_scope.
Infix "+:+" := String.append (at level 60, right associativity) : C_scope.
Arguments String.append _ _ : simpl never.

(** * Decision of equality *)
Instance assci_eq_dec : ∀ a1 a2, Decision (a1 = a2) := ascii_dec.
Instance string_eq_dec (s1 s2 : string) : Decision (s1 = s2).
Proof. solve_decision. Defined.
Instance: Injective (=) (=) (String.append s1).
Proof. intros s1 ???. induction s1; simplify_equality'; f_equal'; auto. Qed.

(* Reverse *)
Fixpoint string_rev_app (s1 s2 : string) : string :=
  match s1 with
  | "" => s2
  | String a s1 => string_rev_app s1 (String a s2)
  end.
Definition string_rev (s : string) : string := string_rev_app s "".

(** * Encoding and decoding *)
(** In order to reuse or existing implementation of radix-2 search trees over
positive binary naturals [positive], we define an injection [string_to_pos]
from [string] into [positive]. *)
Fixpoint digits_to_pos (βs : list bool) : positive :=
  match βs with
  | [] => xH
  | false :: βs => (digits_to_pos βs)~0
  | true :: βs => (digits_to_pos βs)~1
  end%positive.
Definition ascii_to_digits (a : Ascii.ascii) : list bool :=
  match a with
  | Ascii.Ascii β1 β2 β3 β4 β5 β6 β7 β8 => [β1;β2;β3;β4;β5;β6;β7;β8]
  end.
Fixpoint string_to_pos (s : string) : positive :=
  match s with
  | EmptyString => xH
  | String a s => string_to_pos s ++ digits_to_pos (ascii_to_digits a)
  end%positive.
Fixpoint digits_of_pos (p : positive) : list bool :=
  match p with
  | xH => []
  | p~0 => false :: digits_of_pos p
  | p~1 => true :: digits_of_pos p
  end%positive.
Fixpoint ascii_of_digits (βs : list bool) : ascii :=
  match βs with
  | [] => zero
  | β :: βs => Ascii.shift β (ascii_of_digits βs)
  end.
Fixpoint string_of_digits (βs : list bool) : string :=
  match βs with
  | β1 :: β2 :: β3 :: β4 :: β5 :: β6 :: β7 :: β8 :: βs =>
     String (ascii_of_digits [β1;β2;β3;β4;β5;β6;β7;β8]) (string_of_digits βs)
  | _ => EmptyString
  end.
Definition string_of_pos (p : positive) : string :=
  string_of_digits (digits_of_pos p).
Lemma string_of_to_pos s : string_of_pos (string_to_pos s) = s.
Proof.
  unfold string_of_pos. by induction s as [|[[][][][][][][][]]]; f_equal'.
Qed.
Program Instance string_countable : Countable string := {|
  encode := string_to_pos; decode p := Some (string_of_pos p)
|}.
Solve Obligations with naive_solver eauto using string_of_to_pos with f_equal.

