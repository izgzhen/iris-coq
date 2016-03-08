From algebra Require Export iprod.
From program_logic Require Export model.

(** Index of a CMRA in the product of global CMRAs. *)
Definition gid := nat.

(** Name of one instance of a particular CMRA in the ghost state. *)
Definition gname := positive.

(** The "default" iFunctor is constructed as the dependent product of
    a bunch of gFunctor. *)
Structure gFunctor := GFunctor {
  gFunctor_F :> rFunctor;
  gFunctor_contractive : rFunctorContractive gFunctor_F;
}.
Arguments GFunctor _ {_}.
Existing Instance gFunctor_contractive.

(** The global CMRA: Indexed product over a gid i to (gname --fin--> Σ i) *)
Definition globalF (Σ : gid → gFunctor) : iFunctor :=
  IFunctor (iprodRF (λ i, mapRF gname (Σ i))).
Notation gFunctors := (gid → gFunctor).
Notation iPropG Λ Σ := (iProp Λ (globalF Σ)).

Class inG (Λ : language) (Σ : gFunctors) (A : cmraT) := InG {
  inG_id : gid;
  inG_prf : A = Σ inG_id (iPreProp Λ (globalF Σ))
}.

Definition to_globalF `{inG Λ Σ A} (γ : gname) (a : A) : iGst Λ (globalF Σ) :=
  iprod_singleton inG_id {[ γ := cmra_transport inG_prf a ]}.

(** * Properties of to_globalC *)
Section to_globalF.
Context `{i : inG Λ Σ A}.
Implicit Types a : A.

Global Instance to_globalF_ne γ n : Proper (dist n ==> dist n) (to_globalF γ).
Proof. by intros a a' Ha; apply iprod_singleton_ne; rewrite Ha. Qed.
Lemma to_globalF_op γ a1 a2 :
  to_globalF γ (a1 ⋅ a2) ≡ to_globalF γ a1 ⋅ to_globalF γ a2.
Proof.
  by rewrite /to_globalF iprod_op_singleton map_op_singleton cmra_transport_op.
Qed.
Lemma to_globalF_core γ a : core (to_globalF γ a) ≡ to_globalF γ (core a).
Proof.
  by rewrite /to_globalF
    iprod_core_singleton map_core_singleton cmra_transport_core.
Qed.
Global Instance to_globalF_timeless γ m : Timeless m → Timeless (to_globalF γ m).
Proof. rewrite /to_globalF; apply _. Qed.
End to_globalF.

(** When instantiating the logic, we want to just plug together the
    requirements exported by the modules we use. To this end, we construct
    the "gFunctors" from a "list gFunctor", and have some typeclass magic
    to infer the inG. *)
Module gFunctorList.
  Inductive gFunctorList :=
    | nil  : gFunctorList
    | cons : gFunctor → gFunctorList → gFunctorList.
  Coercion singleton (F : gFunctor) : gFunctorList := cons F nil.

  Fixpoint fold_right {A} (f : gFunctor → A → A) (a : A) (Fs : gFunctorList) : A :=
    match Fs with
    | nil => a
    | cons F Fs => f F (fold_right f a Fs)
    end.
End gFunctorList.
Notation gFunctorList := gFunctorList.gFunctorList.

Delimit Scope gFunctor_scope with gFunctor.
Bind Scope gFunctor_scope with gFunctorList.
Arguments gFunctorList.cons _ _%gFunctor.

Notation "[ ]" := gFunctorList.nil (format "[ ]") : gFunctor_scope.
Notation "[ F ]" := (gFunctorList.cons F gFunctorList.nil) : gFunctor_scope.
Notation "[ F ; .. ; F' ]" :=
  (gFunctorList.cons F .. (gFunctorList.cons F' gFunctorList.nil) ..) : gFunctor_scope.

Module gFunctors.
  Definition nil : gFunctors := const (GFunctor (constRF unitR)).

  Definition cons (F : gFunctor) (Σ : gFunctors) : gFunctors :=
    λ n, match n with O => F | S n => Σ n end.

  Fixpoint app (Fs : gFunctorList) (Σ : gFunctors) : gFunctors :=
    match Fs with
    | gFunctorList.nil => Σ
    | gFunctorList.cons F Fs => cons F (app Fs Σ)
    end.
End gFunctors.

(** Cannot bind this scope with the [gFunctorG] since [gFunctorG] is a
notation hiding a more complex type. *)
Notation "#[ ]" := gFunctors.nil (format "#[ ]").
Notation "#[ Fs ]" := (gFunctors.app Fs gFunctors.nil).
Notation "#[ Fs ; .. ; Fs' ]" :=
  (gFunctors.app Fs .. (gFunctors.app Fs' gFunctors.nil) ..).

(** We need another typeclass to identify the *functor* in the Σ. Basing inG on
   the functor breaks badly because Coq is unable to infer the correct
   typeclasses, it does not unfold the functor. *)
Class inGF (Λ : language) (Σ : gFunctors) (F : gFunctor) := InGF {
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
Instance inGF_here {Λ Σ} (F: gFunctor) : inGF Λ (gFunctors.cons F Σ) F.
Proof. by exists 0. Qed.
Instance inGF_further {Λ Σ} (F F': gFunctor) :
  inGF Λ Σ F → inGF Λ (gFunctors.cons F' Σ) F.
Proof. intros [i ?]. by exists (S i). Qed.

(** For modules that need more than one functor, we offer a typeclass
    [inGFs] to demand a list of rFunctor to be available. We do
    *not* register any instances that go from there to [inGF], to
    avoid cycles. *)
Class inGFs (Λ : language) (Σ : gFunctors) (Fs : gFunctorList) :=
  InGFs : (gFunctorList.fold_right (λ F T, inGF Λ Σ F * T) () Fs)%type.

Instance inGFs_nil {Λ Σ} : inGFs Λ Σ [].
Proof. exact tt. Qed.
Instance inGFs_cons {Λ Σ} F Fs :
  inGF Λ Σ F → inGFs Λ Σ Fs → inGFs Λ Σ (gFunctorList.cons F Fs).
Proof. by split. Qed.
