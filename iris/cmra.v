Require Export ra cofe cofe_instances.

Class ValidN (A : Type) := validN : nat → A → Prop.
Instance: Params (@validN) 3.

Class CMRA A `{Equiv A, Compl A,
    Unit A, Op A, Valid A, ValidN A, Included A, Minus A} : Prop := {
  (* setoids *)
  cmra_cofe :> Cofe A;
  cmra_op_ne n x :> Proper (dist n ==> dist n) (op x);
  cmra_unit_ne n :> Proper (dist n ==> dist n) unit;
  cmra_valid_ne n :> Proper (dist n ==> impl) (validN n);
  cmra_minus_ne n :> Proper (dist n ==> dist n ==> dist n) minus;
  cmra_included_proper x : Proper ((≡) ==> impl) (included x);
  (* valid *)
  cmra_valid_0 x : validN 0 x;
  cmra_valid_S n x : validN (S n) x → validN n x;
  cmra_valid_validN x : valid x ↔ ∀ n, validN n x;
  (* monoid *)
  cmra_associative : Associative (≡) (⋅);
  cmra_commutative : Commutative (≡) (⋅);
  cmra_unit_l x : unit x ⋅ x ≡ x;
  cmra_unit_idempotent x : unit (unit x) ≡ unit x;
  cmra_unit_weaken x y : unit x ≼ unit (x ⋅ y);
  cmra_valid_op_l n x y : validN n (x ⋅ y) → validN n x;
  cmra_included_l x y : x ≼ x ⋅ y;
  cmra_op_difference x y : x ≼ y → x ⋅ y ⩪ x ≡ y
}.
Class CMRAExtend A `{Equiv A, Dist A, Op A, ValidN A} :=
  cmra_extend_op x y1 y2 n :
    validN n x → x ={n}= y1 ⋅ y2 → { z | x ≡ z.1 ⋅ z.2 ∧ z ={n}= (y1,y2) }.

Class CMRAPreserving
    `{Included A, ValidN A, Included B, ValidN B} (f : A → B) := {
  included_preserving x y : x ≼ y → f x ≼ f y;
  validN_preserving n x : validN n x → validN n (f x)
}.

(** Bundeled version *)
Structure cmraT := CMRAT {
  cmra_car :> Type;
  cmra_equiv : Equiv cmra_car;
  cmra_dist : Dist cmra_car;
  cmra_compl : Compl cmra_car;
  cmra_unit : Unit cmra_car;
  cmra_op : Op cmra_car;
  cmra_valid : Valid cmra_car;
  cmra_validN : ValidN cmra_car;
  cmra_included : Included cmra_car;
  cmra_minus : Minus cmra_car;
  cmra_cmra : CMRA cmra_car;
  cmra_extend : CMRAExtend cmra_car
}.
Arguments CMRAT _ {_ _ _ _ _ _ _ _ _ _ _}.
Add Printing Constructor cmraT.
Existing Instances cmra_equiv cmra_dist cmra_compl cmra_unit cmra_op
  cmra_valid cmra_validN cmra_included cmra_minus cmra_cmra cmra_extend.
Coercion cmra_cofeC (A : cmraT) : cofeT := CofeT A.
Canonical Structure cmra_cofeC.

Section cmra.
Context `{cmra : CMRA A}.
Implicit Types x y z : A.

Global Instance cmra_valid_ne' : Proper (dist n ==> iff) (validN n).
Proof. by split; apply cmra_valid_ne. Qed.
Global Instance cmra_valid_proper : Proper ((≡) ==> iff) (validN n).
Proof. by intros n x1 x2 Hx; apply cmra_valid_ne', equiv_dist. Qed.
Global Instance cmra_ra : RA A.
Proof.
  split; try by (destruct cmra; eauto with typeclass_instances).
  * by intros x1 x2 Hx; rewrite !cmra_valid_validN; intros ? n; rewrite <-Hx.
  * intros x y; rewrite !cmra_valid_validN; intros ? n.
    by apply cmra_valid_op_l with y.
Qed.
Lemma cmra_valid_op_r x y n : validN n (x ⋅ y) → validN n y.
Proof. rewrite (commutative _ x); apply cmra_valid_op_l. Qed.
Lemma cmra_valid_included x y n : validN n y → x ≼ y → validN n x.
Proof.
  rewrite ra_included_spec; intros Hvalid [z Hy]; rewrite Hy in Hvalid.
  eauto using cmra_valid_op_l.
Qed.
Lemma cmra_valid_le x n n' : validN n x → n' ≤ n → validN n' x.
Proof. induction 2; eauto using cmra_valid_S. Qed.
Global Instance ra_op_ne n : Proper (dist n ==> dist n ==> dist n) (⋅).
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  by rewrite Hy, (commutative _ x1), Hx, (commutative _ y2).
Qed.
Lemma cmra_included_dist_l x1 x2 x1' n :
  x1 ≼ x2 → x1' ={n}= x1 → ∃ x2', x1' ≼ x2' ∧ x2' ={n}= x2.
Proof.
  rewrite ra_included_spec; intros [z Hx2] Hx1; exists (x1' ⋅ z); split.
  apply ra_included_l. by rewrite Hx1, Hx2.
Qed.
Lemma cmra_unit_valid x n : validN n x → validN n (unit x).
Proof. rewrite <-(cmra_unit_l x) at 1; apply cmra_valid_op_l. Qed.
End cmra.

(* Also via [cmra_cofe; cofe_equivalence] *)
Hint Cut [!*; ra_equivalence; cmra_ra] : typeclass_instances.
