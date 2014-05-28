Require Import Arith Program RelationClasses.

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

Notation "m1 == m2" := (meq m1 m2) (at level 70) : mask_scope.
Notation "m1 ⊆ m2"  := (mle m1 m2)  (at level 70) : mask_scope.
Notation "m1 ∩ m2" := (fun i => (m1 : mask) i /\ (m2 : mask) i) (at level 40) : mask_scope.
Notation "m1 \  m2"  := (fun i => (m1 : mask) i /\ ~ (m2 : mask) i) (at level 30) : mask_scope.
Notation "m1 ∪ m2" := (fun i => (m1 : mask) i \/ (m2 : mask) i) (at level 50) : mask_scope.
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

(*
Lemma mask_union_set_false m1 m2 i:
  mask_disj m1 m2 -> m1 i ->
  (set_mask m1 i False) \/1 m2 = set_mask (m1 \/1 m2) i False.
Proof.
move=>H_disj H_m1. extensionality j.
rewrite /set_mask.
case beq i j; last done.
apply Prop_ext. split; last tauto.
move=>[H_F|H_m2]; first tauto.
eapply H_disj; eassumption.
Qed.

Lemma set_mask_true_union m i:
  set_mask m i True = (set_mask mask_emp i True) \/1 m.
Proof.
extensionality j.
apply Prop_ext.
rewrite /set_mask /mask_emp.
case EQ_beq:(beq_nat i j); tauto.
Qed.

Lemma mask_disj_mle_l m1 m1' m2:
  m1 <=1 m1' ->
  mask_disj m1' m2 -> mask_disj m1 m2.
Proof.
move=>H_incl H_disj i.
firstorder.
Qed.

Lemma mask_disj_mle_r m1 m2 m2':
  m2 <=1 m2' ->
  mask_disj m1 m2' -> mask_disj m1 m2.
Proof.
move=>H_incl H_disj i.
firstorder.
Qed.

Lemma mle_union_l m1 m2:
  m1 <=1 m1 \/1 m2.
Proof.
move=>i. cbv. tauto.
Qed.

Lemma mle_union_r m1 m2:
  m1 <=1 m2 \/1 m1.
Proof.
move=>i. cbv. tauto.
Qed.

Lemma mle_set_false m i:
  (set_mask m i False) <=1 m.
Proof.
move=>j.
rewrite /set_mask.
case H: (beq_nat i j); done.
Qed.

Lemma mle_set_true m i:
  m <=1 (set_mask m i True).
Proof.
move=>j.
rewrite /set_mask.
case H: (beq_nat i j); done.
Qed.

Lemma mask_union_idem m:
  m \/1 m = m.
Proof.
extensionality i.
eapply Prop_ext.
tauto.
Qed.

Lemma mask_union_emp_r m:
  m \/1 mask_emp = m.
Proof.
extensionality i.
eapply Prop_ext.
rewrite/mask_emp /=.
tauto.
Qed.

Lemma mask_union_emp_l m:
  mask_emp \/1 m = m.
Proof.
extensionality j.
apply Prop_ext.
rewrite /mask_emp.
tauto.
Qed.
*)