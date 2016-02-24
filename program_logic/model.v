From algebra Require Export upred.
From program_logic Require Export resources.
From algebra Require Import cofe_solver.

(* The Iris program logic is parametrized by a functor from the category of
COFEs to the category of CMRAs, which is instantiated with [laterC iProp]. The
[laterC iProp] can be used to construct impredicate CMRAs, such as the stored
propositions using the agreement CMRA. *)

(* TODO RJ: Can we make use of resF, the resource functor? *)
Module iProp.
Definition F (Λ : language) (Σ : iFunctor) (A B : cofeT) : cofeT :=
  uPredC (resRA Λ Σ (laterC A)).
Definition map {Λ : language} {Σ : iFunctor} {A1 A2 B1 B2 : cofeT}
    (f : (A2 -n> A1) * (B1 -n> B2)) : F Λ Σ A1 B1 -n> F Λ Σ A2 B2 :=
  uPredC_map (resC_map (laterC_map (f.1))).
Definition result Λ Σ : solution (F Λ Σ).
Proof.
  apply (solver.result _ (@map Λ Σ)).
  - intros A B P. rewrite /map /= -{2}(uPred_map_id P). apply uPred_map_ext=> r.
    rewrite /= -{2}(res_map_id r); apply res_map_ext=>{r} r /=.
    by rewrite later_map_id.
  - intros A1 A2 A3 B1 B2 B3 f g f' g' P. rewrite /map /=.
    rewrite -uPred_map_compose. apply uPred_map_ext=>{P} r /=.
    rewrite -res_map_compose. apply res_map_ext=>{r} r /=.
    by rewrite -later_map_compose.
  - intros A1 A2 B1 B2 n f f' Hf P; split=> n' -[???].
    apply upredC_map_ne, resC_map_ne, laterC_map_contractive.
    by intros i ?; apply Hf.
Qed.
End iProp.

(* Solution *)
Definition iPreProp (Λ : language) (Σ : iFunctor) : cofeT := iProp.result Λ Σ.
Definition iRes Λ Σ := res Λ Σ (laterC (iPreProp Λ Σ)).
Definition iResRA Λ Σ := resRA Λ Σ (laterC (iPreProp Λ Σ)).
Definition iWld Λ Σ := mapRA positive (agreeRA (laterC (iPreProp Λ Σ))).
Definition iPst Λ := exclRA (istateC Λ).
Definition iGst Λ Σ := ifunctor_car Σ (laterC (iPreProp Λ Σ)).
Definition iProp (Λ : language) (Σ : iFunctor) : cofeT := uPredC (iResRA Λ Σ).
Definition iProp_unfold {Λ Σ} : iProp Λ Σ -n> iPreProp Λ Σ := solution_fold _.
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
