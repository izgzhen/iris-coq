From algebra Require Export upred.
From program_logic Require Export resources.
From algebra Require Import cofe_solver.

(* The Iris program logic is parametrized by a locally contractive functor
from the category of COFEs to the category of CMRAs, which is instantiated
with [iProp]. The [iProp] can be used to construct impredicate CMRAs, such as
the stored propositions using the agreement CMRA. *)
Structure iFunctor := IFunctor {
  iFunctor_F :> rFunctor;
  iFunctor_contractive : rFunctorContractive iFunctor_F;
  iFunctor_empty (A : cofeT) : Empty (iFunctor_F A);
  iFunctor_identity (A : cofeT) : CMRAUnit (iFunctor_F A);
}.
Arguments IFunctor _ {_ _ _}.
Existing Instances iFunctor_contractive iFunctor_empty iFunctor_identity.

Module Type iProp_solution_sig.
Parameter iPreProp : language → iFunctor → cofeT.
Definition iGst (Λ : language) (Σ : iFunctor) : cmraT := Σ (iPreProp Λ Σ).
Definition iRes Λ Σ := res Λ (laterC (iPreProp Λ Σ)) (iGst Λ Σ).
Definition iResR Λ Σ := resR Λ (laterC (iPreProp Λ Σ)) (iGst Λ Σ).
Definition iWld Λ Σ := gmap positive (agree (laterC (iPreProp Λ Σ))).
Definition iPst Λ := excl (state Λ).
Definition iProp (Λ : language) (Σ : iFunctor) : cofeT := uPredC (iResR Λ Σ).

Parameter iProp_unfold: ∀ {Λ Σ}, iProp Λ Σ -n> iPreProp Λ Σ.
Parameter iProp_fold: ∀ {Λ Σ}, iPreProp Λ Σ -n> iProp Λ Σ.
Parameter iProp_fold_unfold: ∀ {Λ Σ} (P : iProp Λ Σ),
  iProp_fold (iProp_unfold P) ≡ P.
Parameter iProp_unfold_fold: ∀ {Λ Σ} (P : iPreProp Λ Σ),
  iProp_unfold (iProp_fold P) ≡ P.
End iProp_solution_sig.

Module Export iProp_solution : iProp_solution_sig.
Definition iProp_result (Λ : language) (Σ : iFunctor) :
  solution (uPredCF (resRF Λ (▶ ∙) Σ)) := solver.result _.

Definition iPreProp (Λ : language) (Σ : iFunctor) : cofeT := iProp_result Λ Σ.
Definition iGst (Λ : language) (Σ : iFunctor) : cmraT := Σ (iPreProp Λ Σ).
Definition iRes Λ Σ := res Λ (laterC (iPreProp Λ Σ)) (iGst Λ Σ).
Definition iResR Λ Σ := resR Λ (laterC (iPreProp Λ Σ)) (iGst Λ Σ).
Definition iWld Λ Σ := gmap positive (agree (laterC (iPreProp Λ Σ))).
Definition iPst Λ := excl (state Λ).

Definition iProp (Λ : language) (Σ : iFunctor) : cofeT := uPredC (iResR Λ Σ).
Definition iProp_unfold {Λ Σ} : iProp Λ Σ -n> iPreProp Λ Σ :=
  solution_fold (iProp_result Λ Σ).
Definition iProp_fold {Λ Σ} : iPreProp Λ Σ -n> iProp Λ Σ := solution_unfold _.
Lemma iProp_fold_unfold {Λ Σ} (P : iProp Λ Σ) : iProp_fold (iProp_unfold P) ≡ P.
Proof. apply solution_unfold_fold. Qed.
Lemma iProp_unfold_fold {Λ Σ} (P : iPreProp Λ Σ) :
  iProp_unfold (iProp_fold P) ≡ P.
Proof. apply solution_fold_unfold. Qed.
End iProp_solution.

Bind Scope uPred_scope with iProp.

Instance iProp_fold_inj n Λ Σ : Inj (dist n) (dist n) (@iProp_fold Λ Σ).
Proof. by intros X Y H; rewrite -(iProp_unfold_fold X) H iProp_unfold_fold. Qed.
Instance iProp_unfold_inj n Λ Σ :
  Inj (dist n) (dist n) (@iProp_unfold Λ Σ).
Proof. by intros X Y H; rewrite -(iProp_fold_unfold X) H iProp_fold_unfold. Qed.
