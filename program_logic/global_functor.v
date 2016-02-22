From program_logic Require Export ghost_ownership.

Module iFunctors.
  Inductive iFunctors :=
    | nil  : iFunctors
    | cons : iFunctor → iFunctors → iFunctors.
  Coercion singleton (F : iFunctor) : iFunctors := cons F nil.
End iFunctors.
Notation iFunctors := iFunctors.iFunctors.

Delimit Scope iFunctors_scope with iFunctors.
Bind Scope iFunctors_scope with iFunctors.
Arguments iFunctors.cons _ _%iFunctors.

Notation "[ ]" := iFunctors.nil (format "[ ]") : iFunctors_scope.
Notation "[ F ]" := (iFunctors.cons F iFunctors.nil) : iFunctors_scope.
Notation "[ F ; .. ; F' ]" :=
  (iFunctors.cons F .. (iFunctors.cons F' iFunctors.nil) ..) : iFunctors_scope.

Module iFunctorG.
  Definition nil : iFunctorG := const (constF unitRA).

  Definition cons (F : iFunctor) (Σ : iFunctorG) : iFunctorG :=
    λ n, match n with O => F | S n => Σ n end.

  Fixpoint app (Fs : iFunctors) (Σ : iFunctorG) : iFunctorG :=
    match Fs with
    | iFunctors.nil => Σ
    | iFunctors.cons F Fs => cons F (app Fs Σ)
    end.
End iFunctorG.

(** Cannot bind this scope with the [iFunctorG] since [iFunctorG] is a
notation hiding a more complex type. *)
Notation "#[ ]" := iFunctorG.nil (format "#[ ]").
Notation "#[ Fs ]" := (iFunctorG.app Fs iFunctorG.nil).
Notation "#[ Fs ; .. ; Fs' ]" :=
  (iFunctorG.app Fs .. (iFunctorG.app Fs' iFunctorG.nil) ..).

(** We need another typeclass to identify the *functor* in the Σ. Basing inG on
   the functor breaks badly because Coq is unable to infer the correct
   typeclasses, it does not unfold the functor. *)
Class inGF (Λ : language) (Σ : iFunctorG) (F : iFunctor) := InGF {
  inGF_id : gid;
  inGF_prf : F = Σ inGF_id;
}.
(* Avoid eager type class search: this line ensures that type class search
is only triggered if the first two arguments of inGF do not contain evars. Since
instance search for [inGF] is restrained, instances should always have [inGF] as
their first argument to avoid loops. For example, the instances [authGF_inGF]
and [auth_identity] otherwise create a cycle that pops up arbitrarily. *)
Hint Mode inGF + + - : typeclass_instances.

Lemma inGF_inG `{inGF Λ Σ F} : inG Λ Σ (F (laterC (iPreProp Λ (globalF Σ)))).
Proof. exists inGF_id. by rewrite -inGF_prf. Qed.
Instance inGF_here {Λ Σ} (F: iFunctor) : inGF Λ (iFunctorG.cons F Σ) F.
Proof. by exists 0. Qed.
Instance inGF_further {Λ Σ} (F F': iFunctor) :
  inGF Λ Σ F → inGF Λ (iFunctorG.cons F' Σ) F.
Proof. intros [i ?]. by exists (S i). Qed.
