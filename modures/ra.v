Require Export prelude.collections prelude.relations prelude.fin_maps.
Require Export modures.base.

Class Valid (A : Type) := valid : A → Prop.
Instance: Params (@valid) 2.
Notation "✓" := valid (at level 1).

Class Unit (A : Type) := unit : A → A.
Instance: Params (@unit) 2.

Class Op (A : Type) := op : A → A → A.
Instance: Params (@op) 2.
Infix "⋅" := op (at level 50, left associativity) : C_scope.
Notation "(⋅)" := op (only parsing) : C_scope.

Definition included `{Equiv A, Op A} (x y : A) := ∃ z, y ≡ x ⋅ z.
Infix "≼" := included (at level 70) : C_scope.
Notation "(≼)" := included (only parsing) : C_scope.
Hint Extern 0 (?x ≼ ?x) => reflexivity.
Instance: Params (@included) 3.

Class Minus (A : Type) := minus : A → A → A.
Instance: Params (@minus) 2.
Infix "⩪" := minus (at level 40) : C_scope.

Class RA A `{Equiv A, Valid A, Unit A, Op A, Minus A} : Prop := {
  (* setoids *)
  ra_equivalence :> Equivalence ((≡) : relation A);
  ra_op_proper x :> Proper ((≡) ==> (≡)) (op x);
  ra_unit_proper :> Proper ((≡) ==> (≡)) unit;
  ra_valid_proper :> Proper ((≡) ==> impl) ✓;
  ra_minus_proper :> Proper ((≡) ==> (≡) ==> (≡)) minus;
  (* monoid *)
  ra_associative :> Associative (≡) (⋅);
  ra_commutative :> Commutative (≡) (⋅);
  ra_unit_l x : unit x ⋅ x ≡ x;
  ra_unit_idempotent x : unit (unit x) ≡ unit x;
  ra_unit_preserving x y : x ≼ y → unit x ≼ unit y;
  ra_valid_op_l x y : ✓ (x ⋅ y) → ✓ x;
  ra_op_minus x y : x ≼ y → x ⋅ y ⩪ x ≡ y
}.
Class RAIdentity A `{Equiv A, Valid A, Op A, Empty A} : Prop := {
  ra_empty_valid : ✓ ∅;
  ra_empty_l :> LeftId (≡) ∅ (⋅)
}.

Class RAMonotone
    `{Equiv A, Op A, Valid A, Equiv B, Op B, Valid B} (f : A → B) := {
  included_preserving x y : x ≼ y → f x ≼ f y;
  valid_preserving x : ✓ x → ✓ (f x)
}.

(** Big ops *)
Fixpoint big_op `{Op A, Empty A} (xs : list A) : A :=
  match xs with [] => ∅ | x :: xs => x ⋅ big_op xs end.
Arguments big_op _ _ _ !_ /.
Instance: Params (@big_op) 3.

Definition big_opM `{FinMapToList K A M, Op A, Empty A} (m : M) : A :=
  big_op (snd <$> map_to_list m).
Instance: Params (@big_opM) 6.

(** Updates *)
Definition ra_update_set `{Op A, Valid A} (x : A) (P : A → Prop) :=
  ∀ z, ✓ (x ⋅ z) → ∃ y, P y ∧ ✓ (y ⋅ z).
Instance: Params (@ra_update_set) 3.
Infix "⇝:" := ra_update_set (at level 70).
Definition ra_update `{Op A, Valid A} (x y : A) := ∀ z,
  ✓ (x ⋅ z) → ✓ (y ⋅ z).
Infix "⇝" := ra_update (at level 70).
Instance: Params (@ra_update) 3.

(** Properties **)
Section ra.
Context `{RA A}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

Global Instance ra_valid_proper' : Proper ((≡) ==> iff) ✓.
Proof. by intros ???; split; apply ra_valid_proper. Qed.
Global Instance ra_op_proper' : Proper ((≡) ==> (≡) ==> (≡)) (⋅).
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  by rewrite Hy (commutative _ x1) Hx (commutative _ y2).
Qed.
Lemma ra_valid_op_r x y : ✓ (x ⋅ y) → ✓ y.
Proof. rewrite (commutative _ x); apply ra_valid_op_l. Qed.

(** ** Units *)
Lemma ra_unit_r x : x ⋅ unit x ≡ x.
Proof. by rewrite (commutative _ x) ra_unit_l. Qed.
Lemma ra_unit_unit x : unit x ⋅ unit x ≡ unit x.
Proof. by rewrite -{2}(ra_unit_idempotent x) ra_unit_r. Qed.

(** ** Order *)
Instance ra_included_proper' : Proper ((≡) ==> (≡) ==> impl) (≼).
Proof. intros x1 x2 Hx y1 y2 Hy [z Hz]; exists z. by rewrite -Hy Hz Hx. Qed.
Global Instance ra_included_proper : Proper ((≡) ==> (≡) ==> iff) (≼).
Proof. by split; apply ra_included_proper'. Qed.
Lemma ra_included_l x y : x ≼ x ⋅ y.
Proof. by exists y. Qed.
Lemma ra_included_r x y : y ≼ x ⋅ y.
Proof. rewrite (commutative op); apply ra_included_l. Qed.
Global Instance: PreOrder included.
Proof.
  split; first by intros x; exists (unit x); rewrite ra_unit_r.
  intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2).
  by rewrite (associative _) -Hy -Hz.
Qed.
Lemma ra_included_unit x : unit x ≼ x.
Proof. by exists x; rewrite ra_unit_l. Qed.
Lemma ra_preserving_l x y z : x ≼ y → z ⋅ x ≼ z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (associative (⋅)). Qed.
Lemma ra_preserving_r x y z : x ≼ y → x ⋅ z ≼ y ⋅ z.
Proof. by intros; rewrite -!(commutative _ z); apply ra_preserving_l. Qed.

(** ** RAs with empty element *)
Context `{Empty A, !RAIdentity A}.

Global Instance ra_empty_r : RightId (≡) ∅ (⋅).
Proof. by intros x; rewrite (commutative op) (left_id _ _). Qed.
Lemma ra_unit_empty : unit ∅ ≡ ∅.
Proof. by rewrite -{2}(ra_unit_l ∅) (right_id _ _). Qed.
Lemma ra_empty_least x : ∅ ≼ x.
Proof. by exists x; rewrite (left_id _ _). Qed.

(** * Big ops *)
Global Instance big_op_permutation : Proper ((≡ₚ) ==> (≡)) big_op.
Proof.
  induction 1 as [|x xs1 xs2 ? IH|x y xs|xs1 xs2 xs3]; simpl; auto.
  * by rewrite IH.
  * by rewrite !(associative _) (commutative _ x).
  * by transitivity (big_op xs2).
Qed.
Global Instance big_op_proper : Proper ((≡) ==> (≡)) big_op.
Proof. by induction 1; simpl; repeat apply (_ : Proper (_ ==> _ ==> _) op). Qed.
Lemma big_op_app xs ys : big_op (xs ++ ys) ≡ big_op xs ⋅ big_op ys.
Proof.
  induction xs as [|x xs IH]; simpl; first by rewrite ?(left_id _ _).
  by rewrite IH (associative _).
Qed.

Context `{FinMap K M}.
Lemma big_opM_empty : big_opM (∅ : M A) ≡ ∅.
Proof. unfold big_opM. by rewrite map_to_list_empty. Qed.
Lemma big_opM_insert (m : M A) i x :
  m !! i = None → big_opM (<[i:=x]> m) ≡ x ⋅ big_opM m.
Proof. intros ?; by rewrite /big_opM map_to_list_insert. Qed.
Lemma big_opM_singleton i x : big_opM ({[i ↦ x]} : M A) ≡ x.
Proof.
  rewrite -insert_empty big_opM_insert /=; last auto using lookup_empty.
  by rewrite big_opM_empty (right_id _ _).
Qed.
Global Instance big_opM_proper : Proper ((≡) ==> (≡)) (big_opM : M A → _).
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
End ra.
