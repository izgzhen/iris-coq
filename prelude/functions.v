From iris.prelude Require Export base tactics.

Section definitions.
  Context {A T : Type} `{∀ a b : A, Decision (a = b)}.
  Definition fn_insert (a : A) (t : T) (f : A → T) : A → T := λ b,
    if decide (a = b) then t else f b.
  Definition fn_alter (g : T → T) (a : A) (f : A → T) : A → T := λ b,
    if decide (a = b) then g (f a) else f b.
End definitions.

(* TODO: For now, we only have the properties here that do not need a notion
   of equality of functions. *)

Section functions.
  Context {A T : Type} `{∀ a b : A, Decision (a = b)}.

  Lemma fn_lookup_insert (f : A → T) a t : fn_insert a t f a = t.
  Proof. unfold fn_insert. by destruct (decide (a = a)). Qed.
  Lemma fn_lookup_insert_rev  (f : A → T) a t1 t2 :
    fn_insert a t1 f a = t2 → t1 = t2.
  Proof. rewrite fn_lookup_insert. congruence. Qed.
  Lemma fn_lookup_insert_ne (f : A → T) a b t : a ≠ b → fn_insert a t f b = f b.
  Proof. unfold fn_insert. by destruct (decide (a = b)). Qed.

  Lemma fn_lookup_alter (g : T → T) (f : A → T) a : fn_alter g a f a = g (f a).
  Proof. unfold fn_alter. by destruct (decide (a = a)). Qed.
  Lemma fn_lookup_alter_ne (g : T → T) (f : A → T) a b :
    a ≠ b → fn_alter g a f b = f b.
  Proof. unfold fn_alter. by destruct (decide (a = b)). Qed.
End functions.
