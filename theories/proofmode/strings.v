From stdpp Require Import strings.
From iris.algebra Require Import base.
From Coq Require Import Ascii.
Set Default Proof Using "Type".

Local Notation "b1 && b2" := (if b1 then b2 else false) : bool_scope.

Lemma lazy_andb_true (b1 b2 : bool) : b1 && b2 = true ↔ b1 = true ∧ b2 = true.
Proof. destruct b1, b2; intuition congruence. Qed.

Definition beq (b1 b2 : bool) : bool :=
  match b1, b2 with
  | false, false | true, true => true
  | _, _ => false
  end.

Definition ascii_beq (x y : ascii) : bool :=
  let 'Ascii x1 x2 x3 x4 x5 x6 x7 x8 := x in
  let 'Ascii y1 y2 y3 y4 y5 y6 y7 y8 := y in
  beq x1 y1 && beq x2 y2 && beq x3 y3 && beq x4 y4 &&
    beq x5 y5 && beq x6 y6 && beq x7 y7 && beq x8 y8.

Fixpoint string_beq (s1 s2 : string) : bool :=
  match s1, s2 with 
  | "", "" => true
  | String a1 s1, String a2 s2 => ascii_beq a1 a2 && string_beq s1 s2
  | _, _ => false
  end.

Lemma beq_true b1 b2 : beq b1 b2 = true ↔ b1 = b2.
Proof. destruct b1, b2; simpl; intuition congruence. Qed.

Lemma ascii_beq_true x y : ascii_beq x y = true ↔ x = y.
Proof.
  destruct x, y; rewrite /= !lazy_andb_true !beq_true. intuition congruence.
Qed.

Lemma string_beq_true s1 s2 : string_beq s1 s2 = true ↔ s1 = s2.
Proof.
  revert s2. induction s1 as [|x s1 IH]=> -[|y s2] //=.
  rewrite lazy_andb_true ascii_beq_true IH. intuition congruence.
Qed.

Lemma string_beq_reflect s1 s2 : reflect (s1 = s2) (string_beq s1 s2).
Proof. apply iff_reflect. by rewrite string_beq_true. Qed.
