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
  * intros A B P. rewrite /map /= -{2}(uPred_map_id P). apply uPred_map_ext=>r {P} /=.
    rewrite -{2}(res_map_id r). apply res_map_ext=>{r} r /=. by rewrite later_map_id.
  * intros A1 A2 A3 B1 B2 B3 f g f' g' P. rewrite /map /=.
    rewrite -uPred_map_compose. apply uPred_map_ext=>{P} r /=.
    rewrite -res_map_compose. apply res_map_ext=>{r} r /=.
    by rewrite -later_map_compose.
  * intros A1 A2 B1 B2 n f f' [??] P.
    by apply upredC_map_ne, resRA_map_ne, laterC_map_contractive.
Qed.
End iProp.

(* Solution *)
Definition iPreProp (Σ : iParam) : cofeT := iProp.result Σ.
Notation iRes Σ := (res Σ (laterC (iPreProp Σ))).
Notation iResRA Σ := (resRA Σ (laterC (iPreProp Σ))).
Notation iWld Σ := (mapRA positive (agreeRA (laterC (iPreProp Σ)))).
Notation iPst Σ := (exclRA (istateC Σ)).
Notation iGst Σ := (icmra Σ (laterC (iPreProp Σ))).
Definition iProp (Σ : iParam) : cofeT := uPredC (iResRA Σ).
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

Module Test. (* Make sure we got the notations right. *)
  Definition iResTest (Σ : iParam) (w : iWld Σ) (p : iPst Σ) (g : iGst Σ) : iRes Σ := Res w p g.
End Test.
