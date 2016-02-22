From prelude Require Export base tactics.

Section definitions.
  Context {A T : Type} `{∀ a b : A, Decision (a = b)}.
  Global Instance fn_insert : Insert A T (A → T) :=
    λ a t f b, if decide (a = b) then t else f b.
  Global Instance fn_alter : Alter A T (A → T) :=
    λ (g : T → T) a f b, if decide (a = b) then g (f a) else f b.
End definitions.

(* For now, we only have the properties here that do not need a notion
   of equality of functions. *)

Section functions.
  Context {A T : Type} `{∀ a b : A, Decision (a = b)}.

  Lemma fn_lookup_insert (f : A → T) a t : <[a:=t]>f a = t.
  Proof. unfold insert, fn_insert. by destruct (decide (a = a)). Qed.
  Lemma fn_lookup_insert_rev  (f : A → T) a t1 t2 :
    <[a:=t1]>f a = t2 → t1 = t2.
  Proof. rewrite fn_lookup_insert. congruence. Qed.
  Lemma fn_lookup_insert_ne (f : A → T) a b t : a ≠ b → <[a:=t]>f b = f b.
  Proof. unfold insert, fn_insert. by destruct (decide (a = b)). Qed.

  Lemma fn_lookup_alter (g : T → T) (f : A → T) a : alter g a f a = g (f a).
  Proof. unfold alter, fn_alter. by destruct (decide (a = a)). Qed.
  Lemma fn_lookup_alter_ne (g : T → T) (f : A → T) a b :
    a ≠ b → alter g a f b = f b.
  Proof. unfold alter, fn_alter. by destruct (decide (a = b)). Qed.

End functions.

(** "Cons-ing" of functions from nat to T *)
Polymorphic Definition fn_cons {T : Type} (t : T) (f: nat → T) : nat → T :=
  λ n, match n with
       | O => t
       | S n => f n
       end.

Polymorphic Definition fn_mcons {T : Type} (ts : list T) (f : nat → T) : nat → T :=
    fold_right fn_cons f ts.

Infix ".::" := fn_cons (at level 60, right associativity) : C_scope.
Infix ".++" := fn_mcons (at level 60, right associativity) : C_scope.

Polymorphic Lemma fn_mcons_app {T : Type} (ts1 ts2 : list T) f :
  (ts1 ++ ts2) .++ f = ts1 .++ (ts2 .++ f).
Proof.
  unfold fn_mcons. rewrite fold_right_app. done.
Qed.
