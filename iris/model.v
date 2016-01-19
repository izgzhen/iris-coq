Require Export modures.logic iris.resources.
Require Import modures.cofe_solver.

Module iProp.
Definition F (Σ : iParam) (A B : cofeT) : cofeT := uPredC (resRA Σ (laterC A)).
Definition map {Σ : iParam} {A1 A2 B1 B2 : cofeT}
    (f : (A2 -n> A1) * (B1 -n> B2)) : F Σ A1 B1 -n> F Σ A2 B2 :=
  uPredC_map (resRA_map (laterC_map (f.1))).
Definition result Σ : solution (F Σ).
Proof.
  apply (solver.result _ (@map Σ)).
  * intros A B r n ?; rewrite /uPred_holds /= /laterC_map /=. later_map_id res_map_id.
  * by intros A1 A2 A3 B1 B2 B3 f g f' g' P r n ?;
      rewrite /= /uPred_holds /= res_map_compose.
  * by intros A1 A2 B1 B2 n f f' [??] r;
      apply upredC_map_ne, resRA_map_contractive.
Qed.
End iProp.

(* Solution *)
Definition iPreProp (Σ : iParam) : cofeT := iProp.result Σ.
Notation res' Σ := (res Σ (iPreProp Σ)).
Notation icmra' Σ := (icmra Σ (laterC (iPreProp Σ))).
Definition iProp (Σ : iParam) : cofeT := uPredC (resRA Σ (iPreProp Σ)).
Definition iProp_unfold {Σ} : iProp Σ -n> iPreProp Σ := solution_fold _.
Definition iProp_fold {Σ} : iPreProp Σ -n> iProp Σ := solution_unfold _.
Lemma iProp_fold_unfold {Σ} (P : iProp Σ) : iProp_fold (iProp_unfold P) ≡ P.
Proof. apply solution_unfold_fold. Qed.
Lemma iProp_unfold_fold {Σ} (P : iPreProp Σ) : iProp_unfold (iProp_fold P) ≡ P.
Proof. apply solution_fold_unfold. Qed.
Bind Scope uPred_scope with iProp.

Instance iProp_fold_inj n Σ : Injective (dist n) (dist n) (@iProp_fold Σ).
Proof. by intros X Y H; rewrite -(iProp_unfold_fold X) H iProp_unfold_fold. Qed.
Instance iProp_unfold_inj n Σ : Injective (dist n) (dist n) (@iProp_unfold Σ).
Proof. by intros X Y H; rewrite -(iProp_fold_unfold X) H iProp_fold_unfold. Qed.
