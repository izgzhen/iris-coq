Require Import Arith Program RelationClasses Morphisms.

Definition mask := nat -> Prop.

Definition maskS (m : mask) : mask := fun i => m (S i).

Definition mask_set (m : mask) i b : mask :=
  fun j => if eq_nat_dec i j then b else m j.

Definition mask_disj (m1 m2 : mask) :=
  forall i, ~ (m1 i /\ m2 i).

Definition mask_emp  : mask := const False.

Definition mask_full : mask := const True.

Definition mask_infinite (m : mask) :=
  forall i, exists j, j >= i /\ m j.

Definition mle (m1 m2 : mask) :=
  forall n, m1 n -> m2 n.
Definition meq (m1 m2 : mask) :=
  forall n, m1 n <-> m2 n.
Definition mcap (m1 m2 : mask) : mask :=
  fun i => (m1 : mask) i /\ (m2 : mask) i.
Definition mcup (m1 m2 : mask) : mask :=
  fun i => (m1 : mask) i \/ (m2 : mask) i.
Definition mminus (m1 m2 : mask) : mask :=
  fun i => (m1 : mask) i /\ ~ (m2 : mask) i.

Delimit Scope mask_scope with mask.
Notation "m1 == m2" := (meq m1 m2) (at level 70) : mask_scope.
Notation "m1 ⊆ m2"  := (mle m1 m2)  (at level 70) : mask_scope.
Notation "m1 ∩ m2" := (mcap m1 m2) (at level 40) : mask_scope.
Notation "m1 \  m2"  := (mminus m1 m2) (at level 30) : mask_scope.
Notation "m1 ∪ m2" := (mcup m1 m2) (at level 50) : mask_scope.
Notation "m1 # m2" := (mask_disj m1 m2) (at level 70) : mask_scope.

Open Scope mask_scope.

Lemma mask_set_nop m i :
  mask_set m i (m i) == m.
Proof.
  intros n; unfold mask_set.
  destruct (eq_nat_dec i n) as [EQ | NEQ]; [subst |]; reflexivity.
Qed.

Lemma mask_set_shadow m i b1 b2 :
  mask_set (mask_set m i b1) i b2 == mask_set m i b2.
Proof.
  intros n; unfold mask_set.
  destruct (eq_nat_dec i n); [subst |]; reflexivity.
Qed.

Lemma maskS_set_mask_O m b :
  maskS (mask_set m 0 b) == maskS m.
Proof.
  intros n; reflexivity.
Qed.

Lemma maskS_mask_set_S m b i :
  maskS (mask_set m (S i) b) == mask_set (maskS m) i b.
Proof.
  intros n; unfold maskS, mask_set.
  simpl; destruct (eq_nat_dec i n); reflexivity.
Qed.

Lemma mask_full_infinite : mask_infinite mask_full.
Proof.
  intros i; exists i; split; [now auto with arith | exact I].
Qed.

Instance meq_equiv : Equivalence meq.
Proof.
  split.
  - intros m n; reflexivity.
  - intros m1 m2 EQm n; symmetry; apply EQm.
  - intros m1 m2 m3 EQm12 EQm23 n; etransitivity; [apply EQm12 | apply EQm23].
Qed.

Instance mle_preo : PreOrder mle.
Proof.
  split.
  - intros m n; trivial.
  - intros m1 m2 m3 LEm12 LEm23 n Hm1; auto.
Qed.

Lemma mask_emp_union m :
  meq (m ∪ mask_emp) m.
Proof.
  intros k; unfold mcup, mask_emp, const. tauto.
Qed.

Lemma mask_full_union m :
  meq (mask_full ∪ m) mask_full.
Proof.
  intros i; unfold mcup, mask_full, const; tauto.
Qed.

Lemma mask_emp_disjoint m :
  mask_emp # m.
Proof.
  intros k; unfold mask_emp, const; tauto.
Qed.

Lemma mask_union_idem m :
  meq (m ∪ m) m.
Proof.
  intros k; unfold mcup; tauto.
Qed.

Global Instance mask_disj_sub : Proper (mle --> mle --> impl) mask_disj.
Proof.
  intros m1 m1' Hm1 m2 m2' Hm2 Hd k [Hm1' Hm2']; unfold flip in *.
  apply (Hd k); split; [apply Hm1, Hm1' | apply Hm2, Hm2'].
Qed.

Global Instance mask_disj_eq : Proper (meq ==> meq ==> iff) mask_disj.
Proof.
  intros m1 m1' EQm1 m2 m2' EQm2; split; intros Hd k [Hm1 Hm2];
  apply (Hd k); (split; [apply EQm1, Hm1 | apply EQm2, Hm2]).
Qed.
