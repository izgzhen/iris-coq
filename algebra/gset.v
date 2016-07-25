From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From iris.prelude Require Export collections gmap.

Inductive gset_disj K `{Countable K} :=
  | GSet : gset K → gset_disj K
  | GSetBot : gset_disj K.
Arguments GSet {_ _ _} _.
Arguments GSetBot {_ _ _}.

Section gset.
  Context `{Countable K}.
  Arguments op _ _ !_ !_ /.

  Canonical Structure gset_disjC := leibnizC (gset_disj K).

  Instance gset_disj_valid : Valid (gset_disj K) := λ X,
    match X with GSet _ => True | GSetBot => False end.
  Instance gset_disj_empty : Empty (gset_disj K) := GSet ∅.
  Instance gset_disj_op : Op (gset_disj K) := λ X Y,
    match X, Y with
    | GSet X, GSet Y => if decide (X ⊥ Y) then GSet (X ∪ Y) else GSetBot
    | _, _ => GSetBot
    end.
  Instance gset_disj_pcore : PCore (gset_disj K) := λ _, Some ∅.

  Ltac gset_disj_solve :=
    repeat (simpl || case_decide);
    first [apply (f_equal GSet)|done|exfalso]; set_solver by eauto.

  Lemma gset_disj_valid_inv_l X Y : ✓ (GSet X ⋅ Y) → ∃ Y', Y = GSet Y' ∧ X ⊥ Y'.
  Proof. destruct Y; repeat (simpl || case_decide); by eauto. Qed.
  Lemma gset_disj_union X Y : X ⊥ Y → GSet X ⋅ GSet Y = GSet (X ∪ Y).
  Proof. intros. by rewrite /= decide_True. Qed.
  Lemma gset_disj_valid_op X Y : ✓ (GSet X ⋅ GSet Y) ↔ X ⊥ Y.
  Proof. simpl. case_decide; by split. Qed.

  Lemma gset_disj_ra_mixin : RAMixin (gset_disj K).
  Proof.
    apply ra_total_mixin; eauto.
    - intros [?|]; destruct 1; gset_disj_solve.
    - by constructor.
    - by destruct 1.
    - intros [X1|] [X2|] [X3|]; gset_disj_solve.
    - intros [X1|] [X2|]; gset_disj_solve.
    - intros [X|]; gset_disj_solve.
    - exists (GSet ∅); gset_disj_solve.
    - intros [X1|] [X2|]; gset_disj_solve.
  Qed.
  Canonical Structure gset_disjR := discreteR (gset_disj K) gset_disj_ra_mixin.

  Lemma gset_disj_ucmra_mixin : UCMRAMixin (gset_disj K).
  Proof. split; try apply _ || done. intros [X|]; gset_disj_solve. Qed.
  Canonical Structure gset_disjUR :=
    discreteUR (gset_disj K) gset_disj_ra_mixin gset_disj_ucmra_mixin.

  Context `{Fresh K (gset K), !FreshSpec K (gset K)}.
  Arguments op _ _ _ _ : simpl never.

  Lemma updateP_alloc_strong (Q : gset_disj K → Prop) (I : gset K) X :
    (∀ i, i ∉ X → i ∉ I → Q (GSet ({[i]} ∪ X))) → GSet X ~~>: Q.
  Proof.
    intros HQ; apply cmra_discrete_updateP=> ? /gset_disj_valid_inv_l [Y [->?]].
    destruct (exist_fresh (X ∪ Y ∪ I)) as [i ?].
    exists (GSet ({[ i ]} ∪ X)); split.
    - apply HQ; set_solver by eauto.
    - apply gset_disj_valid_op. set_solver by eauto.
  Qed.
  Lemma updateP_alloc (Q : gset_disj K → Prop) X :
    (∀ i, i ∉ X → Q (GSet ({[i]} ∪ X))) → GSet X ~~>: Q.
  Proof. move=>??. eapply updateP_alloc_strong with (I:=∅); by eauto. Qed.
  Lemma updateP_alloc_strong' (I : gset K) X :
    GSet X ~~>: λ Y, ∃ i, Y = GSet ({[ i ]} ∪ X) ∧ i ∉ I ∧ i ∉ X.
  Proof. eauto using updateP_alloc_strong. Qed.
  Lemma updateP_alloc' X : GSet X ~~>: λ Y, ∃ i, Y = GSet ({[ i ]} ∪ X) ∧ i ∉ X.
  Proof. eauto using updateP_alloc. Qed.

  Lemma alloc_singleton_local_update X i Xf :
    i ∉ X → i ∉ Xf → GSet X ~l~> GSet ({[i]} ∪ X) @ Some (GSet Xf).
  Proof.
    intros ??; apply local_update_total; split; simpl.
    - rewrite !gset_disj_valid_op; set_solver.
    - intros mZ ?%gset_disj_valid_op HXf.
      rewrite -gset_disj_union -?assoc ?HXf ?cmra_opM_assoc; set_solver.
  Qed.
End gset.
