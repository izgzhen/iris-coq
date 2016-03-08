From algebra Require Export cmra.

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

Definition dra_included `{Equiv A, Valid A, Disjoint A, Op A} := λ x y,
  ∃ z, y ≡ x ⋅ z ∧ ✓ z ∧ x ⊥ z.
Instance: Params (@dra_included) 4.
Local Infix "≼" := dra_included.

Class DRA A `{Equiv A, Valid A, Core A, Disjoint A, Op A, Div A} := {
  (* setoids *)
  dra_equivalence :> Equivalence ((≡) : relation A);
  dra_op_proper :> Proper ((≡) ==> (≡) ==> (≡)) (⋅);
  dra_core_proper :> Proper ((≡) ==> (≡)) core;
  dra_valid_proper :> Proper ((≡) ==> impl) valid;
  dra_disjoint_proper :> ∀ x, Proper ((≡) ==> impl) (disjoint x);
  dra_div_proper :> Proper ((≡) ==> (≡) ==> (≡)) div;
  (* validity *)
  dra_op_valid x y : ✓ x → ✓ y → x ⊥ y → ✓ (x ⋅ y);
  dra_core_valid x : ✓ x → ✓ core x;
  dra_div_valid x y : ✓ x → ✓ y → x ≼ y → ✓ (y ÷ x);
  (* monoid *)
  dra_assoc :> Assoc (≡) (⋅);
  dra_disjoint_ll x y z : ✓ x → ✓ y → ✓ z → x ⊥ y → x ⋅ y ⊥ z → x ⊥ z;
  dra_disjoint_move_l x y z : ✓ x → ✓ y → ✓ z → x ⊥ y → x ⋅ y ⊥ z → x ⊥ y ⋅ z;
  dra_symmetric :> Symmetric (@disjoint A _);
  dra_comm x y : ✓ x → ✓ y → x ⊥ y → x ⋅ y ≡ y ⋅ x;
  dra_core_disjoint_l x : ✓ x → core x ⊥ x;
  dra_core_l x : ✓ x → core x ⋅ x ≡ x;
  dra_core_idemp x : ✓ x → core (core x) ≡ core x;
  dra_core_preserving x y : ✓ x → ✓ y → x ≼ y → core x ≼ core y;
  dra_disjoint_div x y : ✓ x → ✓ y → x ≼ y → x ⊥ y ÷ x;
  dra_op_div x y : ✓ x → ✓ y → x ≼ y → x ⋅ y ÷ x ≡ y
}.

Section dra.
Context A `{DRA A}.
Arguments valid _ _ !_ /.
Hint Immediate dra_op_proper : typeclass_instances.

Notation T := (validity (valid : A → Prop)).

Instance validity_valid : Valid T := validity_is_valid.
Instance validity_equiv : Equiv T := λ x y,
  (valid x ↔ valid y) ∧ (valid x → validity_car x ≡ validity_car y).
Instance validity_equivalence : Equivalence ((≡) : relation T).
Proof.
  split; unfold equiv, validity_equiv.
  - by intros [x px ?]; simpl.
  - intros [x px ?] [y py ?]; naive_solver.
  - intros [x px ?] [y py ?] [z pz ?] [? Hxy] [? Hyz]; simpl in *.
    split; [|intros; trans y]; tauto.
Qed.
Instance dra_valid_proper' : Proper ((≡) ==> iff) (valid : A → Prop).
Proof. by split; apply dra_valid_proper. Qed.
Instance to_validity_proper : Proper ((≡) ==> (≡)) to_validity.
Proof. by intros x1 x2 Hx; split; rewrite /= Hx. Qed.
Instance: Proper ((≡) ==> (≡) ==> iff) (⊥).
Proof.
  intros x1 x2 Hx y1 y2 Hy; split.
  - by rewrite Hy (symmetry_iff (⊥) x1) (symmetry_iff (⊥) x2) Hx.
  - by rewrite -Hy (symmetry_iff (⊥) x2) (symmetry_iff (⊥) x1) -Hx.
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

Lemma validity_valid_car_valid (z : T) : ✓ z → ✓ validity_car z.
Proof. apply validity_prf. Qed.
Hint Resolve validity_valid_car_valid.
Program Instance validity_core : Core T := λ x,
  Validity (core (validity_car x)) (✓ x) _.
Solve Obligations with naive_solver auto using dra_core_valid.
Program Instance validity_op : Op T := λ x y,
  Validity (validity_car x ⋅ validity_car y)
           (✓ x ∧ ✓ y ∧ validity_car x ⊥ validity_car y) _.
Solve Obligations with naive_solver auto using dra_op_valid.
Program Instance validity_div : Div T := λ x y,
  Validity (validity_car x ÷ validity_car y)
           (✓ x ∧ ✓ y ∧ validity_car y ≼ validity_car x) _.
Solve Obligations with naive_solver auto using dra_div_valid.

Definition validity_ra : RA (discreteC T).
Proof.
  split.
  - intros ??? [? Heq]; split; simpl; [|by intros (?&?&?); rewrite Heq].
    split; intros (?&?&?); split_and!;
      first [rewrite ?Heq; tauto|rewrite -?Heq; tauto|tauto].
  - by intros ?? [? Heq]; split; [done|]; simpl; intros ?; rewrite Heq.
  - intros ?? [??]; naive_solver.
  - intros x1 x2 [? Hx] y1 y2 [? Hy];
      split; simpl; [|by intros (?&?&?); rewrite Hx // Hy].
    split; intros (?&?&z&?&?); split_and!; try tauto.
    + exists z. by rewrite -Hy // -Hx.
    + exists z. by rewrite Hx ?Hy; tauto.
  - intros [x px ?] [y py ?] [z pz ?]; split; simpl;
      [intuition eauto 2 using dra_disjoint_lr, dra_disjoint_rl
      |by intros; rewrite assoc].
  - intros [x px ?] [y py ?]; split; naive_solver eauto using dra_comm.
  - intros [x px ?]; split;
      naive_solver eauto using dra_core_l, dra_core_disjoint_l.
  - intros [x px ?]; split; naive_solver eauto using dra_core_idemp.
  - intros x y Hxy; exists (core y ÷ core x).
    destruct x as [x px ?], y as [y py ?], Hxy as [[z pz ?] [??]]; simpl in *.
    assert (py → core x ≼ core y)
      by intuition eauto 10 using dra_core_preserving.
    constructor; [|symmetry]; simpl in *;
      intuition eauto using dra_op_div, dra_disjoint_div, dra_core_valid.
  - by intros [x px ?] [y py ?] (?&?&?).
  - intros [x px ?] [y py ?] [[z pz ?] [??]]; split; simpl in *;
      intuition eauto 10 using dra_disjoint_div, dra_op_div.
Qed.
Definition validityR : cmraT := discreteR validity_ra.
Instance validity_cmra_discrete :
  CMRADiscrete validityR := discrete_cmra_discrete _.

Lemma validity_update (x y : validityR) :
  (∀ z, ✓ x → ✓ z → validity_car x ⊥ z → ✓ y ∧ validity_car y ⊥ z) → x ~~> y.
Proof.
  intros Hxy; apply cmra_discrete_update=> z [?[??]].
  split_and!; try eapply Hxy; eauto.
Qed.

Lemma to_validity_op (x y : A) :
  (✓ (x ⋅ y) → ✓ x ∧ ✓ y ∧ x ⊥ y) →
  to_validity (x ⋅ y) ≡ to_validity x ⋅ to_validity y.
Proof. split; naive_solver auto using dra_op_valid. Qed.

Lemma to_validity_included x y:
  (✓ y ∧ to_validity x ≼ to_validity y)%C ↔ (✓ x ∧ x ≼ y).
Proof.
  split.
  - move=>[Hvl [z [Hvxz EQ]]]. move:(Hvl)=>Hvl'. apply Hvxz in Hvl'.
    destruct Hvl' as [? [? ?]].
    split; first done.
    exists (validity_car z). split_and!; last done.
    + apply EQ. assumption.
    + by apply validity_valid_car_valid.
  - intros (Hvl & z & EQ & ? & ?).
    assert (✓ y) by (rewrite EQ; apply dra_op_valid; done).
    split; first done. exists (to_validity z). split; first split.
    + intros _. simpl. split_and!; done.
    + intros _. setoid_subst. by apply dra_op_valid. 
    + intros _. rewrite /= EQ //.
Qed.
End dra.
