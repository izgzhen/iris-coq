From program_logic Require Export ghost_ownership.

Module rFunctors.
  Inductive rFunctors :=
    | nil  : rFunctors
    | cons : rFunctor → rFunctors → rFunctors.
  Coercion singleton (F : rFunctor) : rFunctors := cons F nil.

  Fixpoint fold_right {A} (f : rFunctor → A → A) (a : A) (Fs : rFunctors) : A :=
    match Fs with
    | nil => a
    | cons F Fs => f F (fold_right f a Fs)
    end.
End rFunctors.
Notation rFunctors := rFunctors.rFunctors.

Delimit Scope rFunctors_scope with rFunctors.
Bind Scope rFunctors_scope with rFunctors.
Arguments rFunctors.cons _ _%rFunctors.

Notation "[ ]" := rFunctors.nil (format "[ ]") : rFunctors_scope.
Notation "[ F ]" := (rFunctors.cons F rFunctors.nil) : rFunctors_scope.
Notation "[ F ; .. ; F' ]" :=
  (rFunctors.cons F .. (rFunctors.cons F' rFunctors.nil) ..) : rFunctors_scope.

Module rFunctorG.
  Definition nil : rFunctorG := const (constRF unitR).

  Definition cons (F : rFunctor) (Σ : rFunctorG) : rFunctorG :=
    λ n, match n with O => F | S n => Σ n end.

  Fixpoint app (Fs : rFunctors) (Σ : rFunctorG) : rFunctorG :=
    match Fs with
    | rFunctors.nil => Σ
    | rFunctors.cons F Fs => cons F (app Fs Σ)
    end.
End rFunctorG.

(** Cannot bind this scope with the [rFunctorG] since [rFunctorG] is a
notation hiding a more complex type. *)
Notation "#[ ]" := rFunctorG.nil (format "#[ ]").
Notation "#[ Fs ]" := (rFunctorG.app Fs rFunctorG.nil).
Notation "#[ Fs ; .. ; Fs' ]" :=
  (rFunctorG.app Fs .. (rFunctorG.app Fs' rFunctorG.nil) ..).

(** We need another typeclass to identify the *functor* in the Σ. Basing inG on
   the functor breaks badly because Coq is unable to infer the correct
   typeclasses, it does not unfold the functor. *)
Class inGF (Λ : language) (Σ : rFunctorG) (F : rFunctor) := InGF {
  inGF_id : gid;
  inGF_prf : F = Σ inGF_id;
}.
(* Avoid eager type class search: this line ensures that type class search
is only triggered if the first two arguments of inGF do not contain evars. Since
instance search for [inGF] is restrained, instances should always have [inGF] as
their first argument to avoid loops. For example, the instances [authGF_inGF]
and [auth_identity] otherwise create a cycle that pops up arbitrarily. *)
Hint Mode inGF + + - : typeclass_instances.

Lemma inGF_inG `{inGF Λ Σ F} : inG Λ Σ (F (iPreProp Λ (globalF Σ))).
Proof. exists inGF_id. by rewrite -inGF_prf. Qed.
Instance inGF_here {Λ Σ} (F: rFunctor) : inGF Λ (rFunctorG.cons F Σ) F.
Proof. by exists 0. Qed.
Instance inGF_further {Λ Σ} (F F': rFunctor) :
  inGF Λ Σ F → inGF Λ (rFunctorG.cons F' Σ) F.
Proof. intros [i ?]. by exists (S i). Qed.

(** For modules that need more than one functor, we offer a typeclass
    [inGFs] to demand a list of rFunctor to be available. We do
    *not* register any instances that go from there to [inGF], to
    avoid cycles. *)
Class inGFs (Λ : language) (Σ : rFunctorG) (Fs : rFunctors) :=
  InGFs : (rFunctors.fold_right (λ F T, inGF Λ Σ F * T) () Fs)%type.

Instance inGFs_nil {Λ Σ} : inGFs Λ Σ [].
Proof. exact tt. Qed.
Instance inGFs_cons {Λ Σ} F Fs :
  inGF Λ Σ F → inGFs Λ Σ Fs → inGFs Λ Σ (rFunctors.cons F Fs).
Proof. by split. Qed.
