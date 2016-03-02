From algebra Require Export upred.
From program_logic Require Export resources.
From algebra Require Import cofe_solver.

(* The Iris program logic is parametrized by a functor from the category of
COFEs to the category of CMRAs, which is instantiated with [laterC iProp]. The
[laterC iProp] can be used to construct impredicate CMRAs, such as the stored
propositions using the agreement CMRA. *)
Definition iProp_result (Λ : language) (Σ : rFunctor) :
  solution (uPredCF (resRF Λ laterCF (laterRF Σ))).
Proof.
  (* Contractiveness should be derived from general properties about functors *)
  apply (solver.result _)=> A1 A2 B1 B2.
  intros n fg fg' Hf P; split=> n' -[???].
  apply uPredC_map_ne, resC_map_ne; simpl.
  - apply laterC_map_contractive=> i ?. by apply Hf.
  - apply rFunctor_ne; split; apply laterC_map_contractive=> i ?; by apply Hf.
Qed.

(* Solution *)
Definition iPreProp (Λ : language) (Σ : rFunctor) : cofeT := iProp_result Λ Σ.
Definition iGst (Λ : language) (Σ : rFunctor) : cmraT :=
  Σ (laterC (iPreProp Λ Σ)).
Definition iRes Λ Σ := res Λ (laterC (iPreProp Λ Σ)) (iGst Λ Σ).
Definition iResR Λ Σ := resR Λ (laterC (iPreProp Λ Σ)) (iGst Λ Σ).
Definition iWld Λ Σ := gmap positive (agree (laterC (iPreProp Λ Σ))).
Definition iPst Λ := excl (state Λ).

Definition iProp (Λ : language) (Σ : rFunctor) : cofeT := uPredC (iResR Λ Σ).
Definition iProp_unfold {Λ Σ} : iProp Λ Σ -n> iPreProp Λ Σ :=
  solution_fold (iProp_result Λ Σ).
Definition iProp_fold {Λ Σ} : iPreProp Λ Σ -n> iProp Λ Σ := solution_unfold _.
Lemma iProp_fold_unfold {Λ Σ} (P : iProp Λ Σ) : iProp_fold (iProp_unfold P) ≡ P.
Proof. apply solution_unfold_fold. Qed.
Lemma iProp_unfold_fold {Λ Σ} (P : iPreProp Λ Σ) :
  iProp_unfold (iProp_fold P) ≡ P.
Proof. apply solution_fold_unfold. Qed.
Bind Scope uPred_scope with iProp.

Instance iProp_fold_inj n Λ Σ : Inj (dist n) (dist n) (@iProp_fold Λ Σ).
Proof. by intros X Y H; rewrite -(iProp_unfold_fold X) H iProp_unfold_fold. Qed.
Instance iProp_unfold_inj n Λ Σ :
  Inj (dist n) (dist n) (@iProp_unfold Λ Σ).
Proof. by intros X Y H; rewrite -(iProp_fold_unfold X) H iProp_fold_unfold. Qed.
