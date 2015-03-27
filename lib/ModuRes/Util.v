Require Import Ssreflect.ssreflect.
Require Import SetoidClass.

Ltac find_rewrite1 t0 t1 := match goal with
                            | H: t0 = t1 |- _ => rewrite-> H
                            | H: t0 == t1 |- _ => rewrite-> H
                            | H: t1 = t0 |- _ => rewrite<- H
                            | H: t1 == t0 |- _ => rewrite<- H
                            end.
Ltac find_rewrite2 t0 t1 t2 := find_rewrite1 t0 t1; find_rewrite1 t1 t2.
Ltac find_rewrite3 t0 t1 t2 t3 := find_rewrite2 t0 t1 t2; find_rewrite1 t2 t3.


Tactic Notation "ddes" constr(T) "at" integer_list(pos) "as" simple_intropattern(pat) "deqn:" ident(EQ) :=
  (generalize (@eq_refl _ (T)) as EQ; pattern (T) at pos;
   destruct (T) as pat; move => EQ).
