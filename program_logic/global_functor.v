From iris.program_logic Require Export model.
From iris.algebra Require Import iprod gmap.

Class inG (Σ : gFunctors) (A : cmraT) := InG {
  inG_id : gid Σ;
  inG_prf : A = projT2 Σ inG_id (iPreProp Σ)
}.
Arguments inG_id {_ _} _.

Definition to_iRes `{i : inG Σ A} (γ : gname) (a : A) : iResUR Σ :=
  iprod_singleton (inG_id i) {[ γ := cmra_transport inG_prf a ]}.
Instance: Params (@to_iRes) 4.
Typeclasses Opaque to_iRes.

(** * Properties of [to_iRes] *)
Section to_iRes.
Context `{inG Σ A}.
Implicit Types a : A.

Global Instance to_iRes_ne γ n :
  Proper (dist n ==> dist n) (@to_iRes Σ A _ γ).
Proof. by intros a a' Ha; apply iprod_singleton_ne; rewrite Ha. Qed.
Lemma to_iRes_op γ a1 a2 :
  to_iRes γ (a1 ⋅ a2) ≡ to_iRes γ a1 ⋅ to_iRes γ a2.
Proof.
  by rewrite /to_iRes iprod_op_singleton op_singleton cmra_transport_op.
Qed.
Global Instance to_iRes_timeless γ a : Timeless a → Timeless (to_iRes γ a).
Proof. rewrite /to_iRes; apply _. Qed.
Global Instance to_iRes_persistent γ a :
  Persistent a → Persistent (to_iRes γ a).
Proof. rewrite /to_iRes; apply _. Qed.
End to_iRes.

(** When instantiating the logic, we want to just plug together the
    requirements exported by the modules we use. To this end, we construct
    the "gFunctors" from a "list gFunctor", and have some typeclass magic
    to infer the inG. *)
Module gFunctorList.
  Inductive T :=
    | nil  : T
    | cons : gFunctor → T → T.
  Coercion singleton (F : gFunctor) : T := cons F nil.

  Fixpoint app (Fs1 Fs2 : T) : T :=
    match Fs1 with nil => Fs2 | cons F Fs1 => cons F (app Fs1 Fs2) end.

  Fixpoint fold_right {A} (f : gFunctor → A → A) (a : A) (Fs : T) : A :=
    match Fs with
    | nil => a
    | cons F Fs => f F (fold_right f a Fs)
    end.
End gFunctorList.
Notation gFunctorList := gFunctorList.T.

Delimit Scope gFunctor_scope with gFunctor.
Bind Scope gFunctor_scope with gFunctorList.
Arguments gFunctorList.cons _ _%gFunctor.

Notation "[ ]" := gFunctorList.nil (format "[ ]") : gFunctor_scope.
Notation "[ F ]" := (gFunctorList.app F gFunctorList.nil) : gFunctor_scope.
Notation "[ F1 ; F2 ; .. ; Fn ]" :=
  (gFunctorList.app F1 (gFunctorList.app F2 ..
    (gFunctorList.app Fn gFunctorList.nil) ..)) : gFunctor_scope.

Module gFunctors.
  Definition nil : gFunctors := existT 0 (fin_0_inv _).

  Definition cons (F : gFunctor) (Σ : gFunctors) : gFunctors :=
    existT (S (projT1 Σ)) (fin_S_inv _ F (projT2 Σ)).

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
Notation "#[ Fs1 ; Fs2 ; .. ; Fsn ]" :=
  (gFunctors.app Fs1 (gFunctors.app Fs2 ..
    (gFunctors.app Fsn gFunctors.nil) ..)).

(** We need another typeclass to identify the *functor* in the Σ. Basing inG on
   the functor breaks badly because Coq is unable to infer the correct
   typeclasses, it does not unfold the functor. *)
Class inGF (Σ : gFunctors) (F : gFunctor) := InGF {
  inGF_id : gid Σ;
  inGF_prf : F = projT2 Σ inGF_id;
}.
(* Avoid eager type class search: this line ensures that type class search
is only triggered if the first two arguments of inGF do not contain evars. Since
instance search for [inGF] is restrained, instances should always have [inGF] as
their first argument to avoid loops. For example, the instances [authGF_inGF]
and [auth_identity] otherwise create a cycle that pops up arbitrarily. *)
Hint Mode inGF + - : typeclass_instances.

Lemma inGF_inG {Σ F} : inGF Σ F → inG Σ (F (iPreProp Σ)).
Proof. intros. exists inGF_id. by rewrite -inGF_prf. Qed.
Instance inGF_here {Σ} (F: gFunctor) : inGF (gFunctors.cons F Σ) F.
Proof. by exists 0%fin. Qed.
Instance inGF_further {Σ} (F F': gFunctor) :
  inGF Σ F → inGF (gFunctors.cons F' Σ) F.
Proof. intros [i ?]. by exists (FS i). Qed.

(** For modules that need more than one functor, we offer a typeclass
    [inGFs] to demand a list of rFunctor to be available. We do
    *not* register any instances that go from there to [inGF], to
    avoid cycles. *)
Class inGFs (Σ : gFunctors) (Fs : gFunctorList) :=
  InGFs : (gFunctorList.fold_right (λ F T, inGF Σ F * T) () Fs)%type.

Instance inGFs_nil {Σ} : inGFs Σ [].
Proof. exact tt. Qed.
Instance inGFs_cons {Σ} F Fs :
  inGF Σ F → inGFs Σ Fs → inGFs Σ (gFunctorList.cons F Fs).
Proof. by split. Qed.
