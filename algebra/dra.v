Require Export algebra.cmra.

(** From disjoint pcm *)
Record validity {A} (P : A → Prop) : Type := Validity {
  validity_car : A;
  validity_is_valid : Prop;
  validity_prf : validity_is_valid → P validity_car
}.
Arguments Validity {_ _} _ _ _.
Arguments validity_car {_ _} _.
Arguments validity_is_valid {_ _} _.

Definition to_validity {A} {P : A → Prop} (x : A) : validity P :=
  Validity x (P x) id.
Instance validity_valid {A} (P : A → Prop) : Valid (validity P) :=
  validity_is_valid.
Instance validity_equiv `{Equiv A} (P : A → Prop) : Equiv (validity P) := λ x y,
  (valid x ↔ valid y) ∧ (valid x → validity_car x ≡ validity_car y).
Instance validity_equivalence `{Equiv A,!Equivalence ((≡) : relation A)} P :
  Equivalence ((≡) : relation (validity P)).
Proof.
  split; unfold equiv, validity_equiv.
  * by intros [x px ?]; simpl.
  * intros [x px ?] [y py ?]; naive_solver.
  * intros [x px ?] [y py ?] [z pz ?] [? Hxy] [? Hyz]; simpl in *.
    split; [|intros; transitivity y]; tauto.
Qed.
Instance validity_valid_proper `{Equiv A} (P : A → Prop) :
  Proper ((≡) ==> iff) (valid : validity P → Prop).
Proof. intros ?? [??]; naive_solver. Qed.

Definition dra_included `{Equiv A, Valid A, Disjoint A, Op A} := λ x y,
  ∃ z, y ≡ x ⋅ z ∧ ✓ z ∧ x ⊥ z.
Instance: Params (@dra_included) 4.
Local Infix "≼" := dra_included.

Class DRA A `{Equiv A, Valid A, Unit A, Disjoint A, Op A, Minus A} := {
  (* setoids *)
  dra_equivalence :> Equivalence ((≡) : relation A);
  dra_op_proper :> Proper ((≡) ==> (≡) ==> (≡)) (⋅);
  dra_unit_proper :> Proper ((≡) ==> (≡)) unit;
  dra_disjoint_proper :> ∀ x, Proper ((≡) ==> impl) (disjoint x);
  dra_minus_proper :> Proper ((≡) ==> (≡) ==> (≡)) minus;
  (* validity *)
  dra_op_valid x y : ✓ x → ✓ y → x ⊥ y → ✓ (x ⋅ y);
  dra_unit_valid x : ✓ x → ✓ unit x;
  dra_minus_valid x y : ✓ x → ✓ y → x ≼ y → ✓ (y ⩪ x);
  (* monoid *)
  dra_assoc :> Assoc (≡) (⋅);
  dra_disjoint_ll x y z : ✓ x → ✓ y → ✓ z → x ⊥ y → x ⋅ y ⊥ z → x ⊥ z;
  dra_disjoint_move_l x y z : ✓ x → ✓ y → ✓ z → x ⊥ y → x ⋅ y ⊥ z → x ⊥ y ⋅ z;
  dra_symmetric :> Symmetric (@disjoint A _);
  dra_comm x y : ✓ x → ✓ y → x ⊥ y → x ⋅ y ≡ y ⋅ x;
  dra_unit_disjoint_l x : ✓ x → unit x ⊥ x;
  dra_unit_l x : ✓ x → unit x ⋅ x ≡ x;
  dra_unit_idemp x : ✓ x → unit (unit x) ≡ unit x;
  dra_unit_preserving x y : ✓ x → ✓ y → x ≼ y → unit x ≼ unit y;
  dra_disjoint_minus x y : ✓ x → ✓ y → x ≼ y → x ⊥ y ⩪ x;
  dra_op_minus x y : ✓ x → ✓ y → x ≼ y → x ⋅ y ⩪ x ≡ y
}.

Section dra.
Context A `{DRA A}.
Arguments valid _ _ !_ /.
Hint Immediate dra_op_proper : typeclass_instances.

Instance: Proper ((≡) ==> (≡) ==> iff) (⊥).
Proof.
  intros x1 x2 Hx y1 y2 Hy; split.
  * by rewrite Hy (symmetry_iff (⊥) x1) (symmetry_iff (⊥) x2) Hx.
  * by rewrite -Hy (symmetry_iff (⊥) x2) (symmetry_iff (⊥) x1) -Hx.
Qed.
Lemma dra_disjoint_rl x y z : ✓ x → ✓ y → ✓ z → y ⊥ z → x ⊥ y ⋅ z → x ⊥ y.
Proof. intros ???. rewrite !(symmetry_iff _ x). by apply dra_disjoint_ll. Qed.
Lemma dra_disjoint_lr x y z : ✓ x → ✓ y → ✓ z → x ⊥ y → x ⋅ y ⊥ z → y ⊥ z.
Proof. intros ????. rewrite dra_comm //. by apply dra_disjoint_ll. Qed.
Lemma dra_disjoint_move_r x y z :
  ✓ x → ✓ y → ✓ z → y ⊥ z → x ⊥ y ⋅ z → x ⋅ y ⊥ z.
Proof.
  intros; symmetry; rewrite dra_comm; eauto using dra_disjoint_rl.
  apply dra_disjoint_move_l; auto; by rewrite dra_comm.
Qed.
Hint Immediate dra_disjoint_move_l dra_disjoint_move_r.
Hint Unfold dra_included.

Notation T := (validity (valid : A → Prop)).
Lemma validity_valid_car_valid (z : T) : ✓ z → ✓ validity_car z.
Proof. apply validity_prf. Qed.
Hint Resolve validity_valid_car_valid.
Program Instance validity_unit : Unit T := λ x,
  Validity (unit (validity_car x)) (✓ x) _.
Solve Obligations with naive_solver auto using dra_unit_valid.
Program Instance validity_op : Op T := λ x y,
  Validity (validity_car x ⋅ validity_car y)
           (✓ x ∧ ✓ y ∧ validity_car x ⊥ validity_car y) _.
Solve Obligations with naive_solver auto using dra_op_valid.
Program Instance validity_minus : Minus T := λ x y,
  Validity (validity_car x ⩪ validity_car y)
           (✓ x ∧ ✓ y ∧ validity_car y ≼ validity_car x) _.
Solve Obligations with naive_solver auto using dra_minus_valid.

Definition validity_ra : RA (discreteC T).
Proof.
  split.
  * intros ??? [? Heq]; split; simpl; [|by intros (?&?&?); rewrite Heq].
    split; intros (?&?&?); split_ands';
      first [rewrite ?Heq; tauto|rewrite -?Heq; tauto|tauto].
  * by intros ?? [? Heq]; split; [done|]; simpl; intros ?; rewrite Heq.
  * by intros ?? -> ?.
  * intros x1 x2 [? Hx] y1 y2 [? Hy];
      split; simpl; [|by intros (?&?&?); rewrite Hx // Hy].
    split; intros (?&?&z&?&?); split_ands'; try tauto.
    + exists z. by rewrite -Hy // -Hx.
    + exists z. by rewrite Hx ?Hy; tauto.
  * intros [x px ?] [y py ?] [z pz ?]; split; simpl;
      [intuition eauto 2 using dra_disjoint_lr, dra_disjoint_rl
      |by intros; rewrite assoc].
  * intros [x px ?] [y py ?]; split; naive_solver eauto using dra_comm.
  * intros [x px ?]; split;
      naive_solver eauto using dra_unit_l, dra_unit_disjoint_l.
  * intros [x px ?]; split; naive_solver eauto using dra_unit_idemp.
  * intros x y Hxy; exists (unit y ⩪ unit x).
    destruct x as [x px ?], y as [y py ?], Hxy as [[z pz ?] [??]]; simpl in *.
    assert (py → unit x ≼ unit y)
      by intuition eauto 10 using dra_unit_preserving.
    constructor; [|symmetry]; simpl in *;
      intuition eauto using dra_op_minus, dra_disjoint_minus, dra_unit_valid.
  * by intros [x px ?] [y py ?] (?&?&?).
  * intros [x px ?] [y py ?] [[z pz ?] [??]]; split; simpl in *;
      intuition eauto 10 using dra_disjoint_minus, dra_op_minus.
Qed.
Definition validityRA : cmraT := discreteRA validity_ra.
Definition validity_update (x y : validityRA) :
  (∀ z, ✓ x → ✓ z → validity_car x ⊥ z → ✓ y ∧ validity_car y ⊥ z) → x ~~> y.
Proof.
  intros Hxy. apply discrete_update.
  intros z (?&?&?); split_ands'; try eapply Hxy; eauto.
Qed.
End dra.
