Require Export modures.ra modures.cofe.

Class ValidN (A : Type) := validN : nat → A → Prop.
Instance: Params (@validN) 3.
Notation "✓{ n }" := (validN n) (at level 1, format "✓{ n }").

Definition includedN `{Dist A, Op A} (n : nat) (x y : A) := ∃ z, y ={n}= x ⋅ z.
Notation "x ≼{ n } y" := (includedN n x y)
  (at level 70, format "x  ≼{ n }  y") : C_scope.
Instance: Params (@includedN) 4.
Hint Extern 0 (?x ≼{_} ?x) => reflexivity.

Class CMRA A `{Equiv A, Compl A, Unit A, Op A, Valid A, ValidN A, Minus A} := {
  (* setoids *)
  cmra_cofe :> Cofe A;
  cmra_op_ne n x :> Proper (dist n ==> dist n) (op x);
  cmra_unit_ne n :> Proper (dist n ==> dist n) unit;
  cmra_valid_ne n :> Proper (dist n ==> impl) (✓{n});
  cmra_minus_ne n :> Proper (dist n ==> dist n ==> dist n) minus;
  (* valid *)
  cmra_valid_0 x : ✓{0} x;
  cmra_valid_S n x : ✓{S n} x → ✓{n} x;
  cmra_valid_validN x : ✓ x ↔ ∀ n, ✓{n} x;
  (* monoid *)
  cmra_associative : Associative (≡) (⋅);
  cmra_commutative : Commutative (≡) (⋅);
  cmra_unit_l x : unit x ⋅ x ≡ x;
  cmra_unit_idempotent x : unit (unit x) ≡ unit x;
  cmra_unit_preserving n x y : x ≼{n} y → unit x ≼{n} unit y;
  cmra_valid_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x;
  cmra_op_minus n x y : x ≼{n} y → x ⋅ y ⩪ x ={n}= y
}.
Class CMRAExtend A `{Equiv A, Dist A, Op A, ValidN A} :=
  cmra_extend_op n x y1 y2 :
    ✓{n} x → x ={n}= y1 ⋅ y2 → { z | x ≡ z.1 ⋅ z.2 ∧ z ={n}= (y1,y2) }.

Class CMRAMonotone
    `{Dist A, Op A, ValidN A, Dist B, Op B, ValidN B} (f : A → B) := {
  includedN_preserving n x y : x ≼{n} y → f x ≼{n} f y;
  validN_preserving n x : ✓{n} x → ✓{n} (f x)
}.

Hint Extern 0 (✓{0} _) => apply cmra_valid_0.

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
  cmra_minus : Minus cmra_car;
  cmra_cmra : CMRA cmra_car;
  cmra_extend : CMRAExtend cmra_car
}.
Arguments CMRAT _ {_ _ _ _ _ _ _ _ _ _}.
Arguments cmra_car _ : simpl never.
Arguments cmra_equiv _ _ _ : simpl never.
Arguments cmra_dist _ _ _ _ : simpl never.
Arguments cmra_compl _ _ : simpl never.
Arguments cmra_unit _ _ : simpl never.
Arguments cmra_op _ _ _ : simpl never.
Arguments cmra_valid _ _ : simpl never.
Arguments cmra_validN _ _ _ : simpl never.
Arguments cmra_minus _ _ _ : simpl never.
Arguments cmra_cmra _ : simpl never.
Add Printing Constructor cmraT.
Existing Instances cmra_equiv cmra_dist cmra_compl cmra_unit cmra_op
  cmra_valid cmra_validN cmra_minus cmra_cmra cmra_extend.
Coercion cmra_cofeC (A : cmraT) : cofeT := CofeT A.
Canonical Structure cmra_cofeC.

(** Updates *)
Definition cmra_updateP `{Op A, ValidN A} (x : A) (P : A → Prop) := ∀ z n,
  ✓{n} (x ⋅ z) → ∃ y, P y ∧ ✓{n} (y ⋅ z).
Instance: Params (@cmra_updateP) 3.
Infix "⇝:" := cmra_updateP (at level 70).
Definition cmra_update `{Op A, ValidN A} (x y : A) := ∀ z n,
  ✓{n} (x ⋅ z) → ✓{n} (y ⋅ z).
Infix "⇝" := cmra_update (at level 70).
Instance: Params (@cmra_update) 3.

(** Timeless validity *)
(* Not sure whether this is useful, see the rule [uPred_valid_elim_timeless]
in logic.v *)
Class ValidTimeless `{Valid A, ValidN A} (x : A) :=
  valid_timeless : validN 1 x → valid x.
Arguments valid_timeless {_ _ _} _ {_} _.

(** Properties **)
Section cmra.
Context `{cmra : CMRA A}.
Implicit Types x y z : A.

Lemma cmra_included_includedN x y : x ≼ y ↔ ∀ n, x ≼{n} y.
Proof.
  split; [by intros [z Hz] n; exists z; rewrite Hz|].
  intros Hxy; exists (y ⩪ x); apply equiv_dist; intros n.
  symmetry; apply cmra_op_minus, Hxy.
Qed.

Global Instance cmra_valid_ne' : Proper (dist n ==> iff) (✓{n}) | 1.
Proof. by split; apply cmra_valid_ne. Qed.
Global Instance cmra_valid_proper : Proper ((≡) ==> iff) (✓{n}) | 1.
Proof. by intros n x1 x2 Hx; apply cmra_valid_ne', equiv_dist. Qed.
Global Instance cmra_ra : RA A.
Proof.
  split; try by (destruct cmra;
    eauto using ne_proper, ne_proper_2 with typeclass_instances).
  * by intros x1 x2 Hx; rewrite !cmra_valid_validN; intros ? n; rewrite -Hx.
  * intros x y; rewrite !cmra_included_includedN.
    eauto using cmra_unit_preserving.
  * intros x y; rewrite !cmra_valid_validN; intros ? n.
    by apply cmra_valid_op_l with y.
  * intros x y [z Hz]; apply equiv_dist; intros n.
    by apply cmra_op_minus; exists z; rewrite Hz.
Qed.
Lemma cmra_valid_op_r x y n : ✓{n} (x ⋅ y) → ✓{n} y.
Proof. rewrite (commutative _ x); apply cmra_valid_op_l. Qed.
Lemma cmra_valid_le x n n' : ✓{n} x → n' ≤ n → ✓{n'} x.
Proof. induction 2; eauto using cmra_valid_S. Qed.
Global Instance ra_op_ne n : Proper (dist n ==> dist n ==> dist n) (⋅).
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  by rewrite Hy (commutative _ x1) Hx (commutative _ y2).
Qed.
Lemma cmra_unit_valid x n : ✓{n} x → ✓{n} (unit x).
Proof. rewrite -{1}(cmra_unit_l x); apply cmra_valid_op_l. Qed.

(** * Timeless *)
Lemma cmra_timeless_included_l `{!CMRAExtend A} x y :
  Timeless x → ✓{1} y → x ≼{1} y → x ≼ y.
Proof.
  intros ?? [x' ?].
  destruct (cmra_extend_op 1 y x x') as ([z z']&Hy&Hz&Hz'); auto; simpl in *.
  by exists z'; rewrite Hy (timeless x z).
Qed.
Lemma cmra_timeless_included_r n x y : Timeless y → x ≼{1} y → x ≼{n} y.
Proof. intros ? [x' ?]. exists x'. by apply equiv_dist, (timeless y). Qed.
Lemma cmra_op_timeless `{!CMRAExtend A} x1 x2 :
  ✓ (x1 ⋅ x2) → Timeless x1 → Timeless x2 → Timeless (x1 ⋅ x2).
Proof.
  intros ??? z Hz.
  destruct (cmra_extend_op 1 z x1 x2) as ([y1 y2]&Hz'&?&?); auto; simpl in *.
  { by rewrite -?Hz; apply cmra_valid_validN. }
  by rewrite Hz' (timeless x1 y1) // (timeless x2 y2).
Qed.

(** * Included *)
Global Instance cmra_included_ne n :
  Proper (dist n ==> dist n ==> iff) (includedN n) | 1.
Proof.
  intros x x' Hx y y' Hy; unfold includedN.
  by setoid_rewrite Hx; setoid_rewrite Hy.
Qed.
Global Instance cmra_included_proper : 
  Proper ((≡) ==> (≡) ==> iff) (includedN n) | 1.
Proof.
  intros n x x' Hx y y' Hy; unfold includedN.
  by setoid_rewrite Hx; setoid_rewrite Hy.
Qed.
Lemma cmra_included_0 x y : x ≼{0} y.
Proof. by exists (unit x). Qed.
Lemma cmra_included_S x y n : x ≼{S n} y → x ≼{n} y.
Proof. by intros [z Hz]; exists z; apply dist_S. Qed.

Lemma cmra_included_l n x y : x ≼{n} x ⋅ y.
Proof. by exists y. Qed.
Lemma cmra_included_r n x y : y ≼{n} x ⋅ y.
Proof. rewrite (commutative op); apply cmra_included_l. Qed.
Global Instance cmra_included_ord n : PreOrder (includedN n).
Proof.
  split.
  * by intros x; exists (unit x); rewrite ra_unit_r.
  * intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2).
    by rewrite (associative _) -Hy -Hz.
Qed.
Lemma cmra_valid_includedN x y n : ✓{n} y → x ≼{n} y → ✓{n} x.
Proof. intros Hyv [z Hy]; revert Hyv; rewrite Hy; apply cmra_valid_op_l. Qed.
Lemma cmra_valid_included x y n : ✓{n} y → x ≼ y → ✓{n} x.
Proof. rewrite cmra_included_includedN; eauto using cmra_valid_includedN. Qed.
Lemma cmra_included_dist_l x1 x2 x1' n :
  x1 ≼ x2 → x1' ={n}= x1 → ∃ x2', x1' ≼ x2' ∧ x2' ={n}= x2.
Proof.
  intros [z Hx2] Hx1; exists (x1' ⋅ z); split; auto using ra_included_l.
  by rewrite Hx1 Hx2.
Qed.

(** * Properties of [(⇝)] relation *)
Global Instance cmra_update_preorder : PreOrder cmra_update.
Proof. split. by intros x y. intros x y y' ?? z ?; naive_solver. Qed.
Lemma cmra_update_updateP x y : x ⇝ y ↔ x ⇝: (y =).
Proof.
  split.
  * by intros Hx z ?; exists y; split; [done|apply (Hx z)].
  * by intros Hx z n ?; destruct (Hx z n) as (?&<-&?).
Qed.
End cmra.

Instance cmra_monotone_id `{CMRA A} : CMRAMonotone (@id A).
Proof. by split. Qed.
Instance cmra_monotone_ra_monotone `{CMRA A, CMRA B} (f : A → B) :
  CMRAMonotone f → RAMonotone f.
Proof.
  split.
  * intros x y; rewrite !cmra_included_includedN.
    by intros ? n; apply includedN_preserving.
  * intros x; rewrite !cmra_valid_validN.
    by intros ? n; apply validN_preserving.
Qed.

Hint Extern 0 (_ ≼{0} _) => apply cmra_included_0.
(* Also via [cmra_cofe; cofe_equivalence] *)
Hint Cut [!*; ra_equivalence; cmra_ra] : typeclass_instances.

(** Discrete *)
Section discrete.
  Context `{ra : RA A}.
  Existing Instances discrete_dist discrete_compl.
  Let discrete_cofe' : Cofe A := discrete_cofe.
  Instance discrete_validN : ValidN A := λ n x,
    match n with 0 => True | S n => ✓ x end.
  Instance discrete_cmra : CMRA A.
  Proof.
    split; try by (destruct ra; auto).
    * by intros [|n]; try apply ra_op_proper.
    * by intros [|n]; try apply ra_unit_proper.
    * by intros [|n]; try apply ra_valid_proper.
    * by intros [|n]; try apply ra_minus_proper.
    * by intros [|n].
    * intros x; split; intros Hvalid. by intros [|n]. apply (Hvalid 1).
    * by intros [|n]; try apply ra_unit_preserving.
    * by intros [|n]; try apply ra_valid_op_l.
    * by intros [|n] x y; try apply ra_op_minus.
  Qed.
  Instance discrete_extend : CMRAExtend A.
  Proof.
    intros [|n] x y1 y2 ??; [|by exists (y1,y2)].
    by exists (x,unit x); simpl; rewrite ra_unit_r.
  Qed.
  Global Instance discrete_timeless (x : A) : ValidTimeless x.
  Proof. by intros ?. Qed.
  Definition discreteRA : cmraT := CMRAT A.
  Lemma discrete_updateP (x : A) (P : A → Prop) `{!Inhabited (sig P)} :
    (∀ z, ✓ (x ⋅ z) → ∃ y, P y ∧ ✓ (y ⋅ z)) → x ⇝: P.
  Proof.
    intros Hvalid z [|n]; [|apply Hvalid].
    by destruct (_ : Inhabited (sig P)) as [[y ?]]; exists y.
  Qed.
  Lemma discrete_update (x y : A) : (∀ z, ✓ (x ⋅ z) → ✓ (y ⋅ z)) → x ⇝ y.
  Proof. intros Hvalid z [|n]; [done|apply Hvalid]. Qed.
End discrete.
Arguments discreteRA _ {_ _ _ _ _ _}.

(** Product *)
Instance prod_op `{Op A, Op B} : Op (A * B) := λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2).
Instance prod_empty `{Empty A, Empty B} : Empty (A * B) := (∅, ∅).
Instance prod_unit `{Unit A, Unit B} : Unit (A * B) := λ x,
  (unit (x.1), unit (x.2)).
Instance prod_valid `{Valid A, Valid B} : Valid (A * B) := λ x,
  ✓ (x.1) ∧ ✓ (x.2).
Instance prod_validN `{ValidN A, ValidN B} : ValidN (A * B) := λ n x,
  ✓{n} (x.1) ∧ ✓{n} (x.2).
Instance prod_minus `{Minus A, Minus B} : Minus (A * B) := λ x y,
  (x.1 ⩪ y.1, x.2 ⩪ y.2).
Lemma prod_included `{Equiv A, Equiv B, Op A, Op B} (x y : A * B) :
  x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2.
Proof.
  split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto.
Qed.
Lemma prod_includedN `{Dist A, Dist B, Op A, Op B} (x y : A * B) n :
  x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2.
Proof.
  split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto.
Qed.
Instance prod_cmra `{CMRA A, CMRA B} : CMRA (A * B).
Proof.
  split; try apply _.
  * by intros n x y1 y2 [Hy1 Hy2]; split; simpl in *; rewrite ?Hy1 ?Hy2.
  * by intros n y1 y2 [Hy1 Hy2]; split; simpl in *; rewrite ?Hy1 ?Hy2.
  * by intros n y1 y2 [Hy1 Hy2] [??]; split; simpl in *; rewrite -?Hy1 -?Hy2.
  * by intros n x1 x2 [Hx1 Hx2] y1 y2 [Hy1 Hy2];
      split; simpl in *; rewrite ?Hx1 ?Hx2 ?Hy1 ?Hy2.
  * split; apply cmra_valid_0.
  * by intros n x [??]; split; apply cmra_valid_S.
  * intros x; split; [by intros [??] n; split; apply cmra_valid_validN|].
    intros Hvalid; split; apply cmra_valid_validN; intros n; apply Hvalid.
  * split; simpl; apply (associative _).
  * split; simpl; apply (commutative _).
  * split; simpl; apply ra_unit_l.
  * split; simpl; apply ra_unit_idempotent.
  * intros n x y; rewrite !prod_includedN.
    by intros [??]; split; apply cmra_unit_preserving.
  * intros n x y [??]; split; simpl in *; eapply cmra_valid_op_l; eauto.
  * intros x y n; rewrite prod_includedN; intros [??].
    by split; apply cmra_op_minus.
Qed.
Instance prod_ra_empty `{RAIdentity A, RAIdentity B} : RAIdentity (A * B).
Proof.
  repeat split; simpl; repeat apply ra_empty_valid; repeat apply (left_id _ _).
Qed.
Instance prod_cmra_extend `{CMRAExtend A, CMRAExtend B} : CMRAExtend (A * B).
Proof.
  intros n x y1 y2 [??] [??]; simpl in *.
  destruct (cmra_extend_op n (x.1) (y1.1) (y2.1)) as (z1&?&?&?); auto.
  destruct (cmra_extend_op n (x.2) (y1.2) (y2.2)) as (z2&?&?&?); auto.
  by exists ((z1.1,z2.1),(z1.2,z2.2)).
Qed.
Instance pair_timeless `{Valid A, ValidN A, Valid B, ValidN B} (x : A) (y : B) :
  ValidTimeless x → ValidTimeless y → ValidTimeless (x,y).
Proof. by intros ?? [??]; split; apply (valid_timeless _). Qed.
Canonical Structure prodRA (A B : cmraT) : cmraT := CMRAT (A * B).
Instance prod_map_cmra_monotone `{CMRA A, CMRA A', CMRA B, CMRA B'}
  (f : A → A') (g : B → B') `{!CMRAMonotone f, !CMRAMonotone g} :
  CMRAMonotone (prod_map f g).
Proof.
  split.
  * intros n x1 x2; rewrite !prod_includedN; intros [??]; simpl.
    by split; apply includedN_preserving.
  * by intros n x [??]; split; simpl; apply validN_preserving.
Qed.
Definition prodRA_map {A A' B B' : cmraT}
    (f : A -n> A') (g : B -n> B') : prodRA A B -n> prodRA A' B' :=
  CofeMor (prod_map f g : prodRA A B → prodRA A' B').
Instance prodRA_map_ne {A A' B B'} n :
  Proper (dist n==> dist n==> dist n) (@prodRA_map A A' B B') := prodC_map_ne n.
