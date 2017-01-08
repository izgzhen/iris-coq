From iris.base_logic Require Export base_logic.
From iris.algebra Require Import iprod gmap.
From iris.algebra Require cofe_solver.
Import uPred.
Set Default Proof Using "Type".

(** In this file we construct the type [iProp] of propositions of the Iris
logic. This is done by solving the following recursive domain equation:

  iProp ≈ uPred (∀ i : gid, gname -fin-> (Σ i) iProp)

where:

  Σ : gFunctors  := lists of locally constractive functors
  i : gid        := indexes addressing individual functors in [Σ]
  γ : gname      := ghost variable names

The Iris logic is parametrized by a list of locally contractive functors [Σ]
from the category of COFEs to the category of CMRAs. These functors are
instantiated with [iProp], the type of Iris propositions, which allows one to
construct impredicate CMRAs, such as invariants and stored propositions using
the agreement CMRA. *)


(** * Locally contractive functors *)
(** The type [gFunctor] bundles a functor from the category of COFEs to the
category of CMRAs with a proof that it is locally contractive. *)
Structure gFunctor := GFunctor {
  gFunctor_F :> rFunctor;
  gFunctor_contractive : rFunctorContractive gFunctor_F;
}.
Arguments GFunctor _ {_}.
Existing Instance gFunctor_contractive.

(** The type [gFunctors] describes the parameters [Σ] of the Iris logic: lists
of [gFunctor]s.

Note that [gFunctors] is isomorphic to [list gFunctor], but defined in an
alternative way to avoid universe inconsistencies with respect to the universe
monomorphic [list] type. *)
Definition gFunctors := { n : nat & fin n → gFunctor }.

Definition gid (Σ : gFunctors) := fin (projT1 Σ).
Definition gFunctors_lookup (Σ : gFunctors) : gid Σ → gFunctor := projT2 Σ.
Coercion gFunctors_lookup : gFunctors >-> Funclass.

Definition gname := positive.

(** The resources functor [iResF Σ A := ∀ i : gid, gname -fin-> (Σ i) A]. *)
Definition iResF (Σ : gFunctors) : urFunctor :=
  iprodURF (λ i, gmapURF gname (Σ i)).


(** We define functions for the empty list of functors, the singleton list of
functors, and the append operator on lists of functors. These are used to
compose [gFunctors] out of smaller pieces. *)
Module gFunctors.
  Definition nil : gFunctors := existT 0 (fin_0_inv _).

  Definition singleton (F : gFunctor) : gFunctors :=
    existT 1 (fin_S_inv (λ _, gFunctor) F (fin_0_inv _)).

  Definition app (Σ1 Σ2 : gFunctors) : gFunctors :=
    existT (projT1 Σ1 + projT1 Σ2) (fin_plus_inv _ (projT2 Σ1) (projT2 Σ2)).
End gFunctors.

Coercion gFunctors.singleton : gFunctor >-> gFunctors.
Notation "#[ ]" := gFunctors.nil (format "#[ ]").
Notation "#[ Σ1 ; .. ; Σn ]" :=
  (gFunctors.app Σ1 .. (gFunctors.app Σn gFunctors.nil) ..).


(** * Subfunctors *)
(** In order to make proofs in the Iris logic modular, they are not done with
respect to some concrete list of functors [Σ], but are instead parametrized by
an arbitrary list of functors [Σ] that contains at least certain functors. For
example, the lock library is parameterized by a functor [Σ] that should have
the functors corresponding to the heap and the exclusive monoid to manage to
lock invariant.

The contraints to can be expressed using the type class [subG Σ1 Σ2], which
expresses that the functors [Σ1] are contained in [Σ2]. *)
Class subG (Σ1 Σ2 : gFunctors) := in_subG i : { j | Σ1 i = Σ2 j }.

(** Avoid trigger happy type class search: this line ensures that type class
search is only triggered if the arguments of [subG] do not contain evars. Since
instance search for [subG] is restrained, instances should always have [subG] as
their first parameter to avoid loops. For example, the instances [subG_authΣ]
and [auth_discrete] otherwise create a cycle that pops up arbitrarily. *)
Hint Mode subG + + : typeclass_instances.

Lemma subG_inv Σ1 Σ2 Σ : subG (gFunctors.app Σ1 Σ2) Σ → subG Σ1 Σ * subG Σ2 Σ.
Proof.
  move=> H; split.
  - move=> i; move: H=> /(_ (Fin.L _ i)) [j] /=. rewrite fin_plus_inv_L; eauto.
  - move=> i; move: H=> /(_ (Fin.R _ i)) [j] /=. rewrite fin_plus_inv_R; eauto.
Qed.

Instance subG_refl Σ : subG Σ Σ.
Proof. move=> i; by exists i. Qed.
Instance subG_app_l Σ Σ1 Σ2 : subG Σ Σ1 → subG Σ (gFunctors.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.L _ j). by rewrite /= fin_plus_inv_L.
Qed.
Instance subG_app_r Σ Σ1 Σ2 : subG Σ Σ2 → subG Σ (gFunctors.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.R _ j). by rewrite /= fin_plus_inv_R.
Qed.


(** * Solution of the recursive domain equation *)
(** We first declare a module type and then an instance of it so as to seal all of
the construction, this way we are sure we do not use any properties of the
construction, and also avoid Coq from blindly unfolding it. *)
Module Type iProp_solution_sig.
  Parameter iPreProp : gFunctors → ofeT.
  Parameter iResUR : gFunctors → ucmraT.

  Parameter iRes_singleton :
    ∀ {Σ} (i : gid Σ) (γ : gname) (a : Σ i (iPreProp Σ)), iResUR Σ.
  Parameter iRes_ne : ∀ Σ (i : gid Σ) γ, NonExpansive (iRes_singleton i γ).
  Parameter iRes_op : ∀ Σ (i : gid Σ) γ a1 a2,
    iRes_singleton i γ (a1 ⋅ a2) ≡ iRes_singleton i γ a1 ⋅ iRes_singleton i γ a2.
  Parameter iRes_valid : ∀ {M} Σ (i : gid Σ) γ a,
    ✓ iRes_singleton i γ a -∗ (✓ a : uPred M).
  Parameter iRes_timeless : ∀ Σ (i : gid Σ) γ a,
    Timeless a → Timeless (iRes_singleton i γ a).
  Parameter iRes_persistent : ∀ Σ (i : gid Σ) γ a,
    Persistent a → Persistent (iRes_singleton i γ a).
  Parameter iRes_updateP : ∀ Σ (i : gid Σ) γ
      (P : Σ i (iPreProp Σ) → Prop) (Q : iResUR Σ → Prop) a,
    a ~~>: P → (∀ b, P b → Q (iRes_singleton i γ b)) →
    iRes_singleton i γ a ~~>: Q.
  Parameter iRes_alloc_strong : ∀ Σ (i : gid Σ)
      (Q : iResUR Σ → Prop) (G : gset gname) (a : Σ i (iPreProp Σ)),
    ✓ a → (∀ γ, γ ∉ G → Q (iRes_singleton i γ a)) → ∅ ~~>: Q.
  Parameter iRes_alloc_unit_singleton : ∀ Σ (i : gid Σ) u γ,
    ✓ u → LeftId (≡) u (⋅) → ∅ ~~> iRes_singleton i γ u.

  Notation iProp Σ := (uPredC (iResUR Σ)).
  Parameter iProp_unfold: ∀ {Σ}, iProp Σ -n> iPreProp Σ.
  Parameter iProp_fold: ∀ {Σ}, iPreProp Σ -n> iProp Σ.
  Parameter iProp_fold_unfold: ∀ {Σ} (P : iProp Σ),
    iProp_fold (iProp_unfold P) ≡ P.
  Parameter iProp_unfold_fold: ∀ {Σ} (P : iPreProp Σ),
    iProp_unfold (iProp_fold P) ≡ P.
End iProp_solution_sig.

Module Export iProp_solution : iProp_solution_sig.
  Import cofe_solver.
  Definition iProp_result (Σ : gFunctors) :
    solution (uPredCF (iResF Σ)) := solver.result _.

  Definition iPreProp (Σ : gFunctors) : ofeT := iProp_result Σ.
  Definition iResUR (Σ : gFunctors) : ucmraT :=
    iprodUR (λ i, gmapUR gname (Σ i (iPreProp Σ))).

  Definition iRes_singleton {Σ}
      (i : gid Σ) (γ : gname) (a : Σ i (iPreProp Σ)) : iResUR Σ :=
    iprod_singleton i {[ γ := a ]}.
  Lemma iRes_ne Σ (i : gid Σ) γ : NonExpansive (iRes_singleton i γ).
  Proof. by intros n a a' Ha; apply iprod_singleton_ne; rewrite Ha. Qed.
  Lemma iRes_op Σ (i : gid Σ) γ a1 a2 :
    iRes_singleton i γ (a1 ⋅ a2) ≡ iRes_singleton i γ a1 ⋅ iRes_singleton i γ a2.
  Proof. by rewrite /iRes_singleton iprod_op_singleton op_singleton. Qed.
  Lemma iRes_valid {M} Σ (i : gid Σ) γ a :
    ✓ iRes_singleton i γ a -∗ (✓ a : uPred M).
  Proof.
    rewrite /iRes_singleton iprod_validI (forall_elim i) iprod_lookup_singleton.
    by rewrite gmap_validI (forall_elim γ) lookup_singleton option_validI.
  Qed.
  Definition iRes_timeless Σ (i : gid Σ) γ a :
    Timeless a → Timeless (iRes_singleton i γ a) := _.
  Definition iRes_persistent Σ (i : gid Σ) γ a :
    Persistent a → Persistent (iRes_singleton i γ a) := _.
  Lemma iRes_updateP Σ (i : gid Σ) γ (P : _ → Prop) (Q : iResUR Σ → Prop) a :
    a ~~>: P → (∀ b, P b → Q (iRes_singleton i γ b)) →
    iRes_singleton i γ a ~~>: Q.
  Proof.
    intros. eapply iprod_singleton_updateP;
      [by apply singleton_updateP'|naive_solver].
  Qed.
  Lemma iRes_alloc_strong Σ (i : gid Σ) (Q : _ → Prop) (G : gset gname) a :
    ✓ a → (∀ γ, γ ∉ G → Q (iRes_singleton i γ a)) → ∅ ~~>: Q.
  Proof.
    intros Ha ?. eapply iprod_singleton_updateP_empty;
      [eapply alloc_updateP_strong', Ha|naive_solver].
  Qed.
  Lemma iRes_alloc_unit_singleton Σ (i : gid Σ) u γ :
    ✓ u → LeftId (≡) u (⋅) → ∅ ~~> iRes_singleton i γ u.
  Proof.
    intros. by eapply iprod_singleton_update_empty, alloc_unit_singleton_update.
  Qed.

  Notation iProp Σ := (uPredC (iResUR Σ)).
  Definition iProp_unfold {Σ} : iProp Σ -n> iPreProp Σ :=
    solution_fold (iProp_result Σ).
  Definition iProp_fold {Σ} : iPreProp Σ -n> iProp Σ := solution_unfold _.
  Lemma iProp_fold_unfold {Σ} (P : iProp Σ) : iProp_fold (iProp_unfold P) ≡ P.
  Proof. apply solution_unfold_fold. Qed.
  Lemma iProp_unfold_fold {Σ} (P : iPreProp Σ) : iProp_unfold (iProp_fold P) ≡ P.
  Proof. apply solution_fold_unfold. Qed.
End iProp_solution.


(** * Properties of the solution to the recursive domain equation *)
Lemma iProp_unfold_equivI {Σ} (P Q : iProp Σ) :
  iProp_unfold P ≡ iProp_unfold Q ⊢ (P ≡ Q : iProp Σ).
Proof.
  rewrite -{2}(iProp_fold_unfold P) -{2}(iProp_fold_unfold Q).
  eapply (uPred.internal_eq_rewrite _ _ (λ z,
    iProp_fold (iProp_unfold P) ≡ iProp_fold z))%I; auto with I; solve_proper.
Qed.
