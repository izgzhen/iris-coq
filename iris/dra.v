Require Export ra.

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

Local Notation V := valid.
Class DRA A `{Equiv A,Valid A,Unit A,Disjoint A,Op A,Included A, Minus A} := {
  (* setoids *)
  dra_equivalence :> Equivalence ((≡) : relation A);
  dra_op_proper :> Proper ((≡) ==> (≡) ==> (≡)) (⋅);
  dra_unit_proper :> Proper ((≡) ==> (≡)) unit;
  dra_disjoint_proper :> ∀ x, Proper ((≡) ==> impl) (disjoint x);
  dra_minus_proper :> Proper ((≡) ==> (≡) ==> (≡)) minus;
  dra_included_proper :> Proper ((≡) ==> (≡) ==> impl) included;
  (* validity *)
  dra_op_valid x y : V x → V y → x ⊥ y → V (x ⋅ y);
  dra_unit_valid x : V x → V (unit x);
  dra_minus_valid x y : V x → V y → x ≼ y → V (y ⩪ x);
  (* monoid *)
  dra_associative :> Associative (≡) (⋅);
  dra_disjoint_ll x y z : V x → V y → V z → x ⊥ y → x ⋅ y ⊥ z → x ⊥ z;
  dra_disjoint_move_l x y z : V x → V y → V z → x ⊥ y → x ⋅ y ⊥ z → x ⊥ y ⋅ z;
  dra_symmetric :> Symmetric (@disjoint A _);
  dra_commutative x y : V x → V y → x ⊥ y → x ⋅ y ≡ y ⋅ x;
  dra_unit_disjoint_l x : V x → unit x ⊥ x;
  dra_unit_l x : V x → unit x ⋅ x ≡ x;
  dra_unit_idempotent x : V x → unit (unit x) ≡ unit x;
  dra_unit_weaken x y : V x → V y → x ⊥ y → unit x ≼ unit (x ⋅ y);
  dra_included_l x y : V x → V y → x ⊥ y → x ≼ x ⋅ y;
  dra_disjoint_difference x y : V x → V y → x ≼ y → x ⊥ y ⩪ x;
  dra_op_difference x y : V x → V y → x ≼ y → x ⋅ y ⩪ x ≡ y
}.

Section dra.
Context A `{DRA A}.
Arguments valid _ _ !_ /.

Instance: Proper ((≡) ==> (≡) ==> impl) (⊥).
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  by rewrite Hy, (symmetry_iff (⊥) x1), (symmetry_iff (⊥) x2), Hx.
Qed.
Lemma dra_disjoint_rl x y z : V x → V y → V z → y ⊥ z → x ⊥ y ⋅ z → x ⊥ y.
Proof. intros ???. rewrite !(symmetry_iff _ x). by apply dra_disjoint_ll. Qed.
Lemma dra_disjoint_lr x y z : V x → V y → V z → x ⊥ y → x ⋅ y ⊥ z → y ⊥ z.
Proof.
  intros ????. rewrite dra_commutative by done. by apply dra_disjoint_ll.
Qed.
Lemma dra_disjoint_move_r x y z :
  V x → V y → V z → y ⊥ z → x ⊥ y ⋅ z → x ⋅ y ⊥ z.
Proof.
  intros; symmetry; rewrite dra_commutative by eauto using dra_disjoint_rl.
  apply dra_disjoint_move_l; auto; by rewrite dra_commutative.
Qed.
Hint Immediate dra_associative dra_commutative dra_unit_disjoint_l
  dra_unit_l dra_unit_idempotent dra_unit_weaken dra_included_l
  dra_op_difference dra_disjoint_difference dra_disjoint_rl
  dra_disjoint_lr dra_disjoint_move_l dra_disjoint_move_r.

Notation T := (validity (valid : A → Prop)).
Program Instance validity_unit : Unit T := λ x,
  Validity (unit (validity_car x)) (V x) _.
Next Obligation. by apply dra_unit_valid, validity_prf. Qed.
Program Instance validity_op : Op T := λ x y,
  Validity (validity_car x ⋅ validity_car y)
           (V x ∧ V y ∧ validity_car x ⊥ validity_car y) _.
Next Obligation. by apply dra_op_valid; try apply validity_prf. Qed.
Instance validity_included : Included T := λ x y,
  V y → V x ∧ validity_car x ≼ validity_car y.
Program Instance validity_minus : Minus T := λ x y,
  Validity (validity_car x ⩪ validity_car y)
           (V x ∧ V y ∧ validity_car y ≼ validity_car x) _.
Next Obligation. by apply dra_minus_valid; try apply validity_prf. Qed.
Instance validity_ra : RA T.
Proof.
  split.
  * apply _.
  * intros ??? [? Heq]; split; simpl; [|by intros (?&?&?); rewrite Heq].
    split; intros (?&?&?); split_ands';
      first [by rewrite ?Heq by tauto|by rewrite <-?Heq by tauto|tauto].
  * by intros ?? [? Heq]; split; [done|]; simpl; intros ?; rewrite Heq.
  * by intros ?? Heq ?; rewrite <-Heq.
  * intros x1 x2 [? Hx] y1 y2 [? Hy];
      split; simpl; [|by intros (?&?&?); rewrite Hx, Hy].
    split; intros (?&?&?); split_ands'; try tauto.
    + by rewrite <-Hx, <-Hy by done.
    + by rewrite Hx, Hy by tauto.
  * intros ??? [? Heq] Hle; split; [apply Hle; tauto|].
    rewrite <-Heq by tauto; apply Hle; tauto.
  * intros [x px ?] [y py ?] [z pz ?];
      split; simpl; [naive_solver|intros; apply (associative _)].
  * intros [x px ?] [y py ?]; split; naive_solver.
  * intros [x px ?]; split; naive_solver.
  * intros [x px ?]; split; naive_solver.
  * intros [x px ?] [y py ?]; split; naive_solver.
  * by intros [x px ?] [y py ?] (?&?&?).
  * intros [x px ?] [y py ?]; split; naive_solver.
  * intros [x px ?] [y py ?];
      unfold included, validity_included; split; naive_solver.
Qed.
Definition dra_update (x y : T) :
  (∀ z, V x → V z → validity_car x ⊥ z → V y ∧ validity_car y ⊥ z) → x ⇝ y.
Proof.
  intros Hxy z (?&?&?); split_ands'; auto;
    eapply Hxy; eauto; by eapply validity_prf.
Qed.
End dra.
