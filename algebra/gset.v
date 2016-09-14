From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From iris.prelude Require Export collections gmap mapset.

(* The union CMRA *)
Section gset.
  Context `{Countable K}.
  Implicit Types X Y : gset K.

  Canonical Structure gsetC := leibnizC (gset K).

  Instance gset_valid : Valid (gset K) := λ _, True.
  Instance gset_op : Op (gset K) := union.
  Instance gset_pcore : PCore (gset K) := λ X, Some X.

  Lemma gset_op_union X Y : X ⋅ Y = X ∪ Y.
  Proof. done. Qed.
  Lemma gset_core_self X : core X = X.
  Proof. done. Qed.
  Lemma gset_included X Y : X ≼ Y ↔ X ⊆ Y.
  Proof.
    split.
    - intros [Z ->]. rewrite gset_op_union. set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L. by exists Z.
  Qed.

  Lemma gset_ra_mixin : RAMixin (gset K).
  Proof.
    apply ra_total_mixin; eauto.
    - solve_proper.
    - solve_proper.
    - solve_proper.
    - intros X1 X2 X3. by rewrite !gset_op_union assoc_L.
    - intros X1 X2. by rewrite !gset_op_union comm_L.
    - intros X. by rewrite gset_op_union gset_core_self union_idemp_L.
  Qed.
  Canonical Structure gsetR := discreteR (gset K) gset_ra_mixin.

  Lemma gset_ucmra_mixin : UCMRAMixin (gset K).
  Proof. split. done. intros X. by rewrite gset_op_union left_id_L. done. Qed.
  Canonical Structure gsetUR :=
    discreteUR (gset K) gset_ra_mixin gset_ucmra_mixin.

  Lemma gset_opM X mY : X ⋅? mY = X ∪ from_option id ∅ mY.
  Proof. destruct mY; by rewrite /= ?right_id_L. Qed.

  Lemma gset_update X Y : X ~~> Y.
  Proof. done. Qed.

  Lemma gset_local_update X Y mXf : X ⊆ Y → X ~l~> Y @ mXf.
  Proof.
    intros (Z&->&?)%subseteq_disjoint_union_L.
    intros; apply local_update_total; split; [done|]; simpl.
    intros mZ _. rewrite !gset_opM=> HX. by rewrite (comm_L _ X) -!assoc_L HX.
  Qed.

  Global Instance gmap_persistent X : Persistent X.
  Proof. by apply persistent_total; rewrite gset_core_self. Qed.

End gset.

Arguments gsetR _ {_ _}.
Arguments gsetUR _ {_ _}.

(* The disjoint union CMRA *)
Inductive gset_disj K `{Countable K} :=
  | GSet : gset K → gset_disj K
  | GSetBot : gset_disj K.
Arguments GSet {_ _ _} _.
Arguments GSetBot {_ _ _}.

Section gset_disj.
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

  Lemma gset_disj_included X Y : GSet X ≼ GSet Y ↔ X ⊆ Y.
  Proof.
    split.
    - move=> [[Z|]]; simpl; try case_decide; set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L.
      exists (GSet Z). gset_disj_solve.
  Qed.
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

  Arguments op _ _ _ _ : simpl never.

  Lemma gset_disj_alloc_updateP_strong P (Q : gset_disj K → Prop) X :
    (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) →
    (∀ i, i ∉ X → P i → Q (GSet ({[i]} ∪ X))) → GSet X ~~>: Q.
  Proof.
    intros Hfresh HQ.
    apply cmra_discrete_updateP=> ? /gset_disj_valid_inv_l [Y [->?]].
    destruct (Hfresh (X ∪ Y)) as (i&?&?); first set_solver.
    exists (GSet ({[ i ]} ∪ X)); split.
    - apply HQ; set_solver by eauto.
    - apply gset_disj_valid_op. set_solver by eauto.
  Qed.
  Lemma gset_disj_alloc_updateP_strong' P X :
    (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) →
    GSet X ~~>: λ Y, ∃ i, Y = GSet ({[ i ]} ∪ X) ∧ i ∉ X ∧ P i.
  Proof. eauto using gset_disj_alloc_updateP_strong. Qed.

  Lemma gset_disj_alloc_empty_updateP_strong P (Q : gset_disj K → Prop) :
    (∀ Y : gset K, ∃ j, j ∉ Y ∧ P j) →
    (∀ i, P i → Q (GSet {[i]})) → GSet ∅ ~~>: Q.
  Proof.
    intros. apply (gset_disj_alloc_updateP_strong P); eauto.
    intros i; rewrite right_id_L; auto.
  Qed.
  Lemma gset_disj_alloc_empty_updateP_strong' P :
    (∀ Y : gset K, ∃ j, j ∉ Y ∧ P j) →
    GSet ∅ ~~>: λ Y, ∃ i, Y = GSet {[ i ]} ∧ P i.
  Proof. eauto using gset_disj_alloc_empty_updateP_strong. Qed.

  Section fresh_updates.
    Context `{Fresh K (gset K), !FreshSpec K (gset K)}.

    Lemma gset_disj_alloc_updateP (Q : gset_disj K → Prop) X :
      (∀ i, i ∉ X → Q (GSet ({[i]} ∪ X))) → GSet X ~~>: Q.
    Proof.
      intro; eapply gset_disj_alloc_updateP_strong with (λ _, True); eauto.
      intros Y ?; exists (fresh Y); eauto using is_fresh.
    Qed.
    Lemma gset_disj_alloc_updateP' X :
      GSet X ~~>: λ Y, ∃ i, Y = GSet ({[ i ]} ∪ X) ∧ i ∉ X.
    Proof. eauto using gset_disj_alloc_updateP. Qed.

    Lemma gset_disj_alloc_empty_updateP (Q : gset_disj K → Prop) :
      (∀ i, Q (GSet {[i]})) → GSet ∅ ~~>: Q.
    Proof.
      intro. apply gset_disj_alloc_updateP. intros i; rewrite right_id_L; auto.
    Qed.
    Lemma gset_disj_alloc_empty_updateP' : GSet ∅ ~~>: λ Y, ∃ i, Y = GSet {[ i ]}.
    Proof. eauto using gset_disj_alloc_empty_updateP. Qed.
  End fresh_updates.

  Lemma gset_disj_alloc_local_update X i Xf :
    i ∉ X → i ∉ Xf → GSet X ~l~> GSet ({[i]} ∪ X) @ Some (GSet Xf).
  Proof.
    intros ??; apply local_update_total; split; simpl.
    - rewrite !gset_disj_valid_op; set_solver.
    - intros mZ ?%gset_disj_valid_op HXf.
      rewrite -gset_disj_union -?assoc ?HXf ?cmra_opM_assoc; set_solver.
  Qed.
  Lemma gset_disj_alloc_empty_local_update i Xf :
    i ∉ Xf → GSet ∅ ~l~> GSet {[i]} @ Some (GSet Xf).
  Proof.
    intros. rewrite -(right_id_L _ _ {[i]}).
    apply gset_disj_alloc_local_update; set_solver.
  Qed.
End gset_disj.

Arguments gset_disjR _ {_ _}.
Arguments gset_disjUR _ {_ _}.
