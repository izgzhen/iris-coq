From algebra Require Export cmra.
From prelude Require Import gmap.

Fixpoint big_op {A : cmraT} `{Empty A} (xs : list A) : A :=
  match xs with [] => ∅ | x :: xs => x ⋅ big_op xs end.
Arguments big_op _ _ !_ /.
Instance: Params (@big_op) 2.
Definition big_opM `{Countable K} {A : cmraT} `{Empty A} (m : gmap K A) : A :=
  big_op (snd <$> map_to_list m).
Instance: Params (@big_opM) 5.

(** * Properties about big ops *)
Section big_op.
Context `{CMRAIdentity A}.

(** * Big ops *)
Lemma big_op_nil : big_op (@nil A) = ∅.
Proof. done. Qed.
Lemma big_op_cons x xs : big_op (x :: xs) = x ⋅ big_op xs.
Proof. done. Qed.
Global Instance big_op_permutation : Proper ((≡ₚ) ==> (≡)) big_op.
Proof.
  induction 1 as [|x xs1 xs2 ? IH|x y xs|xs1 xs2 xs3]; simpl; auto.
  - by rewrite IH.
  - by rewrite !assoc (comm _ x).
  - by trans (big_op xs2).
Qed.
Global Instance big_op_proper : Proper ((≡) ==> (≡)) big_op.
Proof. by induction 1; simpl; repeat apply (_ : Proper (_ ==> _ ==> _) op). Qed.
Lemma big_op_app xs ys : big_op (xs ++ ys) ≡ big_op xs ⋅ big_op ys.
Proof.
  induction xs as [|x xs IH]; simpl; first by rewrite ?left_id.
  by rewrite IH assoc.
Qed.
Lemma big_op_contains xs ys : xs `contains` ys → big_op xs ≼ big_op ys.
Proof.
  intros [xs' ->]%contains_Permutation.
  rewrite big_op_app; apply cmra_included_l.
Qed.
Lemma big_op_delete xs i x :
  xs !! i = Some x → x ⋅ big_op (delete i xs) ≡ big_op xs.
Proof. by intros; rewrite {2}(delete_Permutation xs i x). Qed.

Context `{Countable K}.
Implicit Types m : gmap K A.
Lemma big_opM_empty : big_opM (∅ : gmap K A) ≡ ∅.
Proof. unfold big_opM. by rewrite map_to_list_empty. Qed.
Lemma big_opM_insert m i x :
  m !! i = None → big_opM (<[i:=x]> m) ≡ x ⋅ big_opM m.
Proof. intros ?; by rewrite /big_opM map_to_list_insert. Qed.
Lemma big_opM_delete m i x :
  m !! i = Some x → x ⋅ big_opM (delete i m) ≡ big_opM m.
Proof.
  intros. by rewrite -{2}(insert_delete m i x) // big_opM_insert ?lookup_delete.
Qed.
Lemma big_opM_singleton i x : big_opM ({[i := x]} : gmap K A) ≡ x.
Proof.
  rewrite -insert_empty big_opM_insert /=; last auto using lookup_empty.
  by rewrite big_opM_empty right_id.
Qed.
Global Instance big_opM_proper : Proper ((≡) ==> (≡)) (big_opM : gmap K A → _).
Proof.
  intros m1; induction m1 as [|i x m1 ? IH] using map_ind.
  { by intros m2; rewrite (symmetry_iff (≡)) map_equiv_empty; intros ->. }
  intros m2 Hm2; rewrite big_opM_insert //.
  rewrite (IH (delete i m2)); last by rewrite -Hm2 delete_insert.
  destruct (map_equiv_lookup (<[i:=x]> m1) m2 i x)
    as (y&?&Hxy); auto using lookup_insert.
  rewrite Hxy -big_opM_insert; last auto using lookup_delete.
  by rewrite insert_delete.
Qed.
Lemma big_opM_lookup_valid n m i x : ✓{n} big_opM m → m !! i = Some x → ✓{n} x.
Proof.
  intros Hm ?; revert Hm; rewrite -(big_opM_delete _ i x) //.
  apply cmra_validN_op_l.
Qed.
End big_op.
