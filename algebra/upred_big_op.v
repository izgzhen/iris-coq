From algebra Require Export upred.

Fixpoint uPred_big_and {M} (Ps : list (uPred M)) :=
  match Ps with [] => True | P :: Ps => P ∧ uPred_big_and Ps end%I.
Instance: Params (@uPred_big_and) 1.
Notation "'Π∧' Ps" := (uPred_big_and Ps) (at level 20) : uPred_scope.
Fixpoint uPred_big_sep {M} (Ps : list (uPred M)) :=
  match Ps with [] => True | P :: Ps => P ★ uPred_big_sep Ps end%I.
Instance: Params (@uPred_big_sep) 1.
Notation "'Π★' Ps" := (uPred_big_sep Ps) (at level 20) : uPred_scope.

Class AlwaysStableL {M} (Ps : list (uPred M)) :=
  always_stableL : Forall AlwaysStable Ps.
Arguments always_stableL {_} _ {_}.

Section big_op.
Context {M : cmraT}.
Implicit Types P Q : uPred M.
Implicit Types Ps Qs : list (uPred M).
Implicit Types A : Type.

(* Big ops *)
Global Instance big_and_proper : Proper ((≡) ==> (≡)) (@uPred_big_and M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_sep_proper : Proper ((≡) ==> (≡)) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_and_perm : Proper ((≡ₚ) ==> (≡)) (@uPred_big_and M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  * by rewrite IH.
  * by rewrite !assoc (comm _ P).
  * etransitivity; eauto.
Qed.
Global Instance big_sep_perm : Proper ((≡ₚ) ==> (≡)) (@uPred_big_sep M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  * by rewrite IH.
  * by rewrite !assoc (comm _ P).
  * etransitivity; eauto.
Qed.
Lemma big_and_app Ps Qs : (Π∧ (Ps ++ Qs))%I ≡ (Π∧ Ps ∧ Π∧ Qs)%I.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?assoc ?IH. Qed.
Lemma big_sep_app Ps Qs : (Π★ (Ps ++ Qs))%I ≡ (Π★ Ps ★ Π★ Qs)%I.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?assoc ?IH. Qed.
Lemma big_sep_and Ps : (Π★ Ps) ⊑ (Π∧ Ps).
Proof. by induction Ps as [|P Ps IH]; simpl; auto with I. Qed.
Lemma big_and_elem_of Ps P : P ∈ Ps → (Π∧ Ps) ⊑ P.
Proof. induction 1; simpl; auto with I. Qed.
Lemma big_sep_elem_of Ps P : P ∈ Ps → (Π★ Ps) ⊑ P.
Proof. induction 1; simpl; auto with I. Qed.

(* Always stable *)
Local Notation AS := AlwaysStable.
Local Notation ASL := AlwaysStableL.
Global Instance big_and_always_stable Ps : ASL Ps → AS (Π∧ Ps).
Proof. induction 1; apply _. Qed.
Global Instance big_sep_always_stable Ps : ASL Ps → AS (Π★ Ps).
Proof. induction 1; apply _. Qed.

Global Instance nil_always_stable : ASL (@nil (uPred M)).
Proof. constructor. Qed.
Global Instance cons_always_stable P Ps : AS P → ASL Ps → ASL (P :: Ps).
Proof. by constructor. Qed.
Global Instance app_always_stable Ps Ps' : ASL Ps → ASL Ps' → ASL (Ps ++ Ps').
Proof. apply Forall_app_2. Qed.
Global Instance zip_with_always_stable {A B} (f : A → B → uPred M) xs ys :
  (∀ x y, AS (f x y)) → ASL (zip_with f xs ys).
Proof. unfold ASL=> ?; revert ys; induction xs=> -[|??]; constructor; auto. Qed.
End big_op.