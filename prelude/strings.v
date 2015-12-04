(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files implements an efficient implementation of finite maps whose keys
range over Coq's data type of strings [string]. The implementation uses radix-2
search trees (uncompressed Patricia trees) as implemented in the file [pmap]
and guarantees logarithmic-time operations. *)
Require Export prelude.fin_maps prelude.pretty.
Require Import Ascii String prelude.gmap.

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

(** * Maps and sets *)
Notation stringmap := (gmap string).
Notation stringset := (gset string).

(** * Generating fresh strings *)
Local Open Scope N_scope.
Let R {A} (s : string) (m : stringmap A) (n1 n2 : N) :=
  n2 < n1 ∧ is_Some (m !! (s +:+ pretty (n1 - 1))).
Lemma fresh_string_step {A} s (m : stringmap A) n x :
  m !! (s +:+ pretty n) = Some x → R s m (1 + n) n.
Proof. split; [lia|]. replace (1 + n - 1) with n by lia; eauto. Qed.
Lemma fresh_string_R_wf {A} s (m : stringmap A) : wf (R s m).
Proof.
  induction (map_wf m) as [m _ IH]. intros n1; constructor; intros n2 [Hn Hs].
  specialize (IH _ (delete_subset m (s +:+ pretty (n2 - 1)) Hs) n2).
  cut (n2 - 1 < n2); [|lia]. clear n1 Hn Hs; revert IH; generalize (n2 - 1).
  intros n1. induction 1 as [n2 _ IH]; constructor; intros n3 [??].
  apply IH; [|lia]; split; [lia|].
  by rewrite lookup_delete_ne by (intros ?; simplify_equality'; lia).
Qed.
Definition fresh_string_go {A} (s : string) (m : stringmap A) (n : N)
    (go : ∀ n', R s m n' n → string) : string :=
  let s' := s +:+ pretty n in
  match Some_dec (m !! s') with
  | inleft (_↾Hs') => go (1 + n)%N (fresh_string_step s m n _ Hs')
  | inright _ => s'
  end.
Definition fresh_string {A} (m : stringmap A) (s : string) : string :=
  match m !! s with
  | None => s
  | Some _ =>
     Fix_F _ (fresh_string_go s m) (wf_guard 32 (fresh_string_R_wf s m) 0)
  end.
Lemma fresh_string_fresh {A} (m : stringmap A) s : m !! fresh_string m s = None.
Proof.
  unfold fresh_string. destruct (m !! s) as [a|] eqn:Hs; [clear a Hs|done].
  generalize 0 (wf_guard 32 (fresh_string_R_wf s m) 0); revert m.
  fix 3; intros m n [?]; simpl; unfold fresh_string_go at 1; simpl.
  destruct (Some_dec (m !! _)) as [[??]|?]; auto.
Qed.
