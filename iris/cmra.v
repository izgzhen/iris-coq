Require Export iris.ra iris.cofe.

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
  cmra_op_minus x y : x ≼ y → x ⋅ y ⩪ x ≡ y
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
Arguments cmra_car _ : simpl never.
Arguments cmra_equiv _ _ _ : simpl never.
Arguments cmra_dist _ _ _ _ : simpl never.
Arguments cmra_compl _ _ : simpl never.
Arguments cmra_unit _ _ : simpl never.
Arguments cmra_op _ _ _ : simpl never.
Arguments cmra_valid _ _ : simpl never.
Arguments cmra_validN _ _ _ : simpl never.
Arguments cmra_included _ _ _ : simpl never.
Arguments cmra_minus _ _ _ : simpl never.
Arguments cmra_cmra _ : simpl never.
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
  split; try by (destruct cmra;
    eauto using ne_proper, ne_proper_2 with typeclass_instances).
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
Lemma cmra_unit_valid x n : validN n x → validN n (unit x).
Proof. rewrite <-(cmra_unit_l x) at 1; apply cmra_valid_op_l. Qed.
Lemma cmra_included_dist_l x1 x2 x1' n :
  x1 ≼ x2 → x1' ={n}= x1 → ∃ x2', x1' ≼ x2' ∧ x2' ={n}= x2.
Proof.
  rewrite ra_included_spec; intros [z Hx2] Hx1; exists (x1' ⋅ z); split.
  apply ra_included_l. by rewrite Hx1, Hx2.
Qed.
Lemma cmra_op_timeless `{!CMRAExtend A} x1 x2 :
  validN 1 (x1 ⋅ x2) → Timeless x1 → Timeless x2 → Timeless (x1 ⋅ x2).
Proof.
  intros ??? z Hz.
  destruct (cmra_extend_op z x1 x2 1) as ([y1 y2]&Hz'&?&?); auto; simpl in *.
  { by rewrite <-?Hz. }
  by rewrite Hz', (timeless x1 y1), (timeless x2 y2).
Qed.
End cmra.

Instance cmra_preserving_id `{CMRA A} : CMRAPreserving (@id A).
Proof. by split. Qed.

(* Also via [cmra_cofe; cofe_equivalence] *)
Hint Cut [!*; ra_equivalence; cmra_ra] : typeclass_instances.

(** Discrete *)
Section discrete.
  Context `{ra : RA A}.
  Existing Instances discrete_dist discrete_compl.
  Let discrete_cofe' : Cofe A := discrete_cofe.
  Instance discrete_validN : ValidN A := λ n x,
    match n with 0 => True | S n => valid x end.
  Instance discrete_cmra : CMRA A.
  Proof.
    split; try by (destruct ra; auto).
    * by intros [|n]; try apply ra_op_proper.
    * by intros [|n]; try apply ra_unit_proper.
    * by intros [|n]; try apply ra_valid_proper.
    * by intros [|n]; try apply ra_minus_proper.
    * by intros [|n].
    * intros x; split; intros Hvalid. by intros [|n]. apply (Hvalid 1).
    * by intros [|n]; try apply ra_valid_op_l.
  Qed.
  Instance discrete_extend : CMRAExtend A.
  Proof.
    intros x y1 y2 [|n] ??; [|by exists (y1,y2)].
    by exists (x,unit x); simpl; rewrite ra_unit_r.
  Qed.
  Definition discreteC : cmraT := CMRAT A.
End discrete.

(** Product *)
Instance prod_op `{Op A, Op B} : Op (A * B) := λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2).
Instance prod_empty `{Empty A, Empty B} : Empty (A * B) := (∅, ∅).
Instance prod_unit `{Unit A, Unit B} : Unit (A * B) := λ x,
  (unit (x.1), unit (x.2)).
Instance prod_valid `{Valid A, Valid B} : Valid (A * B) := λ x,
  valid (x.1) ∧ valid (x.2).
Instance prod_validN `{ValidN A, ValidN B} : ValidN (A * B) := λ n x,
  validN n (x.1) ∧ validN n (x.2).
Instance prod_included `{Included A, Included B} : Included (A * B) :=
  prod_relation (≼) (≼).
Instance prod_minus `{Minus A, Minus B} : Minus (A * B) := λ x y,
  (x.1 ⩪ y.1, x.2 ⩪ y.2).

Instance prod_cmra `{CMRA A, CMRA B} : CMRA (A * B).
Proof.
  split; try apply _.
  * by intros n x y1 y2 [Hy1 Hy2]; split; simpl in *; rewrite ?Hy1, ?Hy2.
  * by intros n y1 y2 [Hy1 Hy2]; split; simpl in *; rewrite ?Hy1, ?Hy2.
  * by intros n y1 y2 [Hy1 Hy2] [??]; split; simpl in *; rewrite <-?Hy1, <-?Hy2.
  * by intros n x1 x2 [Hx1 Hx2] y1 y2 [Hy1 Hy2];
      split; simpl in *; rewrite ?Hx1, ?Hx2, ?Hy1, ?Hy2.
  * by intros x y1 y2 [Hy1 Hy2] [??]; split; simpl in *; rewrite <-?Hy1, <-?Hy2.
  * split; apply cmra_valid_0.
  * by intros n x [??]; split; apply cmra_valid_S.
  * intros x; split; [by intros [??] n; split; apply cmra_valid_validN|].
    intros Hvalid; split; apply cmra_valid_validN; intros n; apply Hvalid.
  * split; simpl; apply (associative _).
  * split; simpl; apply (commutative _).
  * split; simpl; apply ra_unit_l.
  * split; simpl; apply ra_unit_idempotent.
  * split; apply ra_unit_weaken.
  * intros n x y [??]; split; simpl in *; eapply cmra_valid_op_l; eauto.
  * split; apply cmra_included_l.
  * by intros x y [??]; split; apply cmra_op_minus.
Qed.
Instance prod_ra_empty `{RAEmpty A, RAEmpty B} : RAEmpty (A * B).
Proof.
  repeat split; simpl; repeat apply ra_empty_valid; repeat apply (left_id _ _).
Qed.
Instance prod_cmra_extend `{CMRAExtend A, CMRAExtend B} : CMRAExtend (A * B).
Proof.
  intros x y1 y2 n [??] [??]; simpl in *.
  destruct (cmra_extend_op (x.1) (y1.1) (y2.1) n) as (z1&?&?&?); auto.
  destruct (cmra_extend_op (x.2) (y1.2) (y2.2) n) as (z2&?&?&?); auto.
  by exists ((z1.1,z2.1),(z1.2,z2.2)).
Qed.
Canonical Structure prodRA (A B : cmraT) : cmraT := CMRAT (A * B).
Instance prod_map_cmra_preserving `{CMRA A, CMRA A', CMRA B, CMRA B'}
  (f : A → A') (g : B → B') `{!CMRAPreserving f, !CMRAPreserving g} :
  CMRAPreserving (prod_map f g).
Proof.
  split.
  * by intros x1 x2 [??]; split; simpl; apply included_preserving.
  * by intros n x [??]; split; simpl; apply validN_preserving.
Qed.
Definition prodRA_map {A A' B B' : cmraT}
    (f : A -n> A') (g : B -n> B') : prodRA A B -n> prodRA A' B' :=
  CofeMor (prod_map f g : prodRA A B → prodRA A' B').
Instance prodRA_map_ne {A A' B B'} n :
  Proper (dist n==> dist n==> dist n) (@prodRA_map A A' B B') := prodC_map_ne n.
