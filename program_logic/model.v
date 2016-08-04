From iris.algebra Require Export upred.
From iris.algebra Require Import iprod gmap.
From iris.algebra Require cofe_solver.

(* The Iris program logic is parametrized by a dependent product of a bunch of
[gFunctor]s, which are locally contractive functor from the category of COFEs to
the category of CMRAs. These functors are instantiated with [iProp], the type
of Iris propositions, which allows one to construct impredicate CMRAs, such as
invariants and stored propositions using the agreement CMRA. *)
Structure gFunctor := GFunctor {
  gFunctor_F :> rFunctor;
  gFunctor_contractive : rFunctorContractive gFunctor_F;
}.
Arguments GFunctor _ {_}.
Existing Instance gFunctor_contractive.

(** The global CMRA: Indexed product over a gid i to (gname --fin--> Σ i) *)
Definition gFunctors := { n : nat & fin n → gFunctor }.
Definition gid (Σ : gFunctors) := fin (projT1 Σ).

(** Name of one instance of a particular CMRA in the ghost state. *)
Definition gname := positive.

(** Solution of the recursive domain equation *)
Module Type iProp_solution_sig.
Parameter iPreProp : gFunctors → cofeT.
Definition iResUR (Σ : gFunctors) : ucmraT :=
  iprodUR (λ i, gmapUR gname (projT2 Σ i (iPreProp Σ))).
Definition iProp (Σ : gFunctors) : cofeT := uPredC (iResUR Σ).

Parameter iProp_unfold: ∀ {Σ}, iProp Σ -n> iPreProp Σ.
Parameter iProp_fold: ∀ {Σ}, iPreProp Σ -n> iProp Σ.
Parameter iProp_fold_unfold: ∀ {Σ} (P : iProp Σ),
  iProp_fold (iProp_unfold P) ≡ P.
Parameter iProp_unfold_fold: ∀ {Σ} (P : iPreProp Σ),
  iProp_unfold (iProp_fold P) ≡ P.
End iProp_solution_sig.

Module Export iProp_solution : iProp_solution_sig.
Import cofe_solver.
Definition iResF (Σ : gFunctors) : urFunctor :=
  iprodURF (λ i, gmapURF gname (projT2 Σ i)).
Definition iProp_result (Σ : gFunctors) :
  solution (uPredCF (iResF Σ)) := solver.result _.

Definition iPreProp (Σ : gFunctors) : cofeT := iProp_result Σ.
Definition iResUR (Σ : gFunctors) : ucmraT :=
  iprodUR (λ i, gmapUR gname (projT2 Σ i (iPreProp Σ))).
Definition iProp (Σ : gFunctors) : cofeT := uPredC (iResUR Σ).

Definition iProp_unfold {Σ} : iProp Σ -n> iPreProp Σ :=
  solution_fold (iProp_result Σ).
Definition iProp_fold {Σ} : iPreProp Σ -n> iProp Σ := solution_unfold _.
Lemma iProp_fold_unfold {Σ} (P : iProp Σ) : iProp_fold (iProp_unfold P) ≡ P.
Proof. apply solution_unfold_fold. Qed.
Lemma iProp_unfold_fold {Σ} (P : iPreProp Σ) : iProp_unfold (iProp_fold P) ≡ P.
Proof. apply solution_fold_unfold. Qed.
End iProp_solution.

Bind Scope uPred_scope with iProp.

Lemma iProp_unfold_equivI {Σ} (P Q : iProp Σ) :
  iProp_unfold P ≡ iProp_unfold Q ⊢ (P ≡ Q : iProp Σ).
Proof.
  rewrite -{2}(iProp_fold_unfold P) -{2}(iProp_fold_unfold Q).
  eapply (uPred.eq_rewrite _ _ (λ z,
    iProp_fold (iProp_unfold P) ≡ iProp_fold z))%I; auto with I; solve_proper.
Qed.
