Require Export prelude.collections prelude.relations prelude.fin_maps.

Class Valid (A : Type) := valid : A → Prop.
Instance: Params (@valid) 2.

Class Unit (A : Type) := unit : A → A.
Instance: Params (@unit) 2.

Class Op (A : Type) := op : A → A → A.
Instance: Params (@op) 2.
Infix "⋅" := op (at level 50, left associativity) : C_scope.
Notation "(⋅)" := op (only parsing) : C_scope.

Class Included (A : Type) := included : relation A.
Instance: Params (@included) 2.
Infix "≼" := included (at level 70) : C_scope.
Notation "(≼)" := included (only parsing) : C_scope.
Hint Extern 0 (?x ≼ ?x) => reflexivity.

Class Minus (A : Type) := minus : A → A → A.
Instance: Params (@minus) 2.
Infix "⩪" := minus (at level 40) : C_scope.

Class RA A `{Equiv A, Valid A, Unit A, Op A, Included A, Minus A} : Prop := {
  (* setoids *)
  ra_equivalence :> Equivalence ((≡) : relation A);
  ra_op_proper x :> Proper ((≡) ==> (≡)) (op x);
  ra_unit_proper :> Proper ((≡) ==> (≡)) unit;
  ra_valid_proper :> Proper ((≡) ==> impl) valid;
  ra_minus_proper :> Proper ((≡) ==> (≡) ==> (≡)) minus;
  ra_included_proper x :> Proper ((≡) ==> impl) (included x);
  (* monoid *)
  ra_associative :> Associative (≡) (⋅);
  ra_commutative :> Commutative (≡) (⋅);
  ra_unit_l x : unit x ⋅ x ≡ x;
  ra_unit_idempotent x : unit (unit x) ≡ unit x;
  ra_unit_weaken x y : unit x ≼ unit (x ⋅ y);
  ra_valid_op_l x y : valid (x ⋅ y) → valid x;
  ra_included_l x y : x ≼ x ⋅ y;
  ra_op_minus x y : x ≼ y → x ⋅ y ⩪ x ≡ y
}.
Class RAEmpty A `{Equiv A, Valid A, Op A, Empty A} : Prop := {
  ra_empty_valid : valid ∅;
  ra_empty_l :> LeftId (≡) ∅ (⋅)
}.

(** Big ops *)
Fixpoint big_op `{Op A, Empty A} (xs : list A) : A :=
  match xs with [] => ∅ | x :: xs => x ⋅ big_op xs end.
Arguments big_op _ _ _ !_ /.
Instance: Params (@big_op) 3.

Definition big_opM `{FinMapToList K A M, Op B, Empty B}
  (f : K → A → list B) (m : M) : B := big_op (map_to_list m ≫= curry f).
Instance: Params (@big_opM) 4.

(** Updates *)
Definition ra_update_set `{Op A, Valid A} (x : A) (P : A → Prop) :=
  ∀ z, valid (x ⋅ z) → ∃ y, P y ∧ valid (y ⋅ z).
Instance: Params (@ra_update_set) 3.
Infix "⇝:" := ra_update_set (at level 70).
Definition ra_update `{Op A, Valid A} (x y : A) := ∀ z,
  valid (x ⋅ z) → valid (y ⋅ z).
Infix "⇝" := ra_update (at level 70).
Instance: Params (@ra_update) 3.

(** Properties **)
Section ra.
Context `{RA A}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

Global Instance ra_valid_proper' : Proper ((≡) ==> iff) valid.
Proof. by intros ???; split; apply ra_valid_proper. Qed.
Global Instance ra_op_proper' : Proper ((≡) ==> (≡) ==> (≡)) (⋅).
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  by rewrite Hy, (commutative _ x1), Hx, (commutative _ y2).
Qed.
Lemma ra_valid_op_r x y : valid (x ⋅ y) → valid y.
Proof. rewrite (commutative _ x); apply ra_valid_op_l. Qed.

(** ** Units *)
Lemma ra_unit_r x : x ⋅ unit x ≡ x.
Proof. by rewrite (commutative _ x), ra_unit_l. Qed.

(** ** Order *)
Lemma ra_included_spec x y : x ≼ y ↔ ∃ z, y ≡ x ⋅ z.
Proof.
  split; [by exists (y ⩪ x); rewrite ra_op_minus|].
  intros [z Hz]; rewrite Hz; apply ra_included_l.
Qed.
Global Instance ra_included_proper' : Proper ((≡) ==> (≡) ==> iff) (≼).
Proof.
  intros x1 x2 Hx y1 y2 Hy; rewrite !ra_included_spec.
  by setoid_rewrite Hx; setoid_rewrite Hy.
Qed.
Global Instance: PreOrder included.
Proof.
  split.
  * by intros x; rewrite ra_included_spec; exists (unit x); rewrite ra_unit_r.
  * intros x y z; rewrite ?ra_included_spec; intros [z1 Hy] [z2 Hz].
    exists (z1 ⋅ z2). by rewrite (associative _), <-Hy, <-Hz.
Qed.
Lemma ra_included_unit x : unit x ≼ x.
Proof. by rewrite ra_included_spec; exists x; rewrite ra_unit_l. Qed.
Lemma ra_included_r x y : y ≼ x ⋅ y.
Proof. rewrite (commutative _); apply ra_included_l. Qed.
Lemma ra_preserving_l x y z : x ≼ y → z ⋅ x ≼ z ⋅ y.
Proof.
  rewrite !ra_included_spec.
  by intros (z1&Hz1); exists z1; rewrite Hz1, (associative (⋅)).
Qed.
Lemma ra_preserving_r x y z : x ≼ y → x ⋅ z ≼ y ⋅ z.
Proof. by intros; rewrite <-!(commutative _ z); apply ra_preserving_l. Qed.
Lemma ra_unit_preserving x y : x ≼ y → unit x ≼ unit y.
Proof.
  rewrite ra_included_spec; intros [z Hy]; rewrite Hy; apply ra_unit_weaken.
Qed.

(** ** Properties of [(⇝)] relation *)
Global Instance ra_update_preorder : PreOrder ra_update.
Proof. split. by intros x y. intros x y y' ?? z ?; naive_solver. Qed.

(** ** RAs with empty element *)
Context `{Empty A, !RAEmpty A}.

Global Instance ra_empty_r : RightId (≡) ∅ (⋅).
Proof. by intros x; rewrite (commutative op), (left_id _ _). Qed.
Lemma ra_unit_empty x : unit ∅ ≡ ∅.
Proof. by rewrite <-(ra_unit_l ∅) at 2; rewrite (right_id _ _). Qed.
Lemma ra_empty_least x : ∅ ≼ x.
Proof. by rewrite ra_included_spec; exists x; rewrite (left_id _ _). Qed.

(** * Big ops *)
Global Instance big_op_permutation : Proper ((≡ₚ) ==> (≡)) big_op.
Proof.
  induction 1 as [|x xs1 xs2 ? IH|x y xs|xs1 xs2 xs3]; simpl; auto.
  * by rewrite IH.
  * by rewrite !(associative _), (commutative _ x).
  * by transitivity (big_op xs2).
Qed.
Global Instance big_op_proper : Proper ((≡) ==> (≡)) big_op.
Proof. by induction 1; simpl; repeat apply (_ : Proper (_ ==> _ ==> _) op). Qed.
Lemma big_op_app xs ys : big_op (xs ++ ys) ≡ big_op xs ⋅ big_op ys.
Proof.
  induction xs as [|x xs IH]; simpl; [by rewrite ?(left_id _ _)|].
  by rewrite IH, (associative _).
Qed.

Context `{FinMap K M}.
Context `{Equiv B} `{!Equivalence ((≡) : relation B)} (f : K → B → list A).
Lemma big_opM_empty : big_opM f (∅ : M B) ≡ ∅.
Proof. by unfold big_opM; rewrite map_to_list_empty. Qed.
Lemma big_opM_insert (m : M B) i (y : B) :
  m !! i = None → big_opM f (<[i:=y]> m) ≡ big_op (f i y) ⋅ big_opM f m.
Proof.
  intros ?; unfold big_opM.
  by rewrite map_to_list_insert, bind_cons, big_op_app by done.
Qed.
Lemma big_opM_singleton i (y : B) : big_opM f ({[i,y]} : M B) ≡ big_op (f i y).
Proof.
  unfold singleton, map_singleton.
  rewrite big_opM_insert by auto using lookup_empty; simpl.
  by rewrite big_opM_empty, (right_id _ _).
Qed.
Global Instance big_opM_proper :
  (∀ i, Proper ((≡) ==> (≡)) (f i)) → Proper ((≡) ==> (≡)) (big_opM f: M B → A).
Proof.
  intros Hf m1; induction m1 as [|i x m1 ? IH] using map_ind.
  { by intros m2; rewrite (symmetry_iff (≡) ∅), map_equiv_empty; intros ->. }
  intros m2 Hm2; rewrite big_opM_insert by done.
  rewrite (IH (delete i m2)) by (by rewrite <-Hm2, delete_insert).
  destruct (map_equiv_lookup (<[i:=x]> m1) m2 i x)
    as (y&?&Hxy); auto using lookup_insert.
  by rewrite Hxy, <-big_opM_insert, insert_delete by auto using lookup_delete.
Qed.
End ra.
