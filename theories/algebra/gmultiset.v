From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From stdpp Require Export collections gmultiset countable.
Set Default Proof Using "Type".

(* The multiset union CMRA *)
Section gmultiset.
  Context `{Countable K}.
  Implicit Types X Y : gmultiset K.

  Canonical Structure gmultisetC := discreteC (gmultiset K).

  Instance gmultiset_valid : Valid (gmultiset K) := λ _, True.
  Instance gmultiset_validN : ValidN (gmultiset K) := λ _ _, True.
  Instance gmultiset_unit : Unit (gmultiset K) := (∅ : gmultiset K).
  Instance gmultiset_op : Op (gmultiset K) := union.
  Instance gmultiset_pcore : PCore (gmultiset K) := λ X, Some ∅.

  Lemma gmultiset_op_union X Y : X ⋅ Y = X ∪ Y.
  Proof. done. Qed.
  Lemma gmultiset_core_empty X : core X = ∅.
  Proof. done. Qed.
  Lemma gmultiset_included X Y : X ≼ Y ↔ X ⊆ Y.
  Proof.
    split.
    - intros [Z ->%leibniz_equiv].
      rewrite gmultiset_op_union. apply gmultiset_union_subseteq_l.
    - intros ->%gmultiset_union_difference. by exists (Y ∖ X).
  Qed.

  Lemma gmultiset_ra_mixin : RAMixin (gmultiset K).
  Proof.
    apply ra_total_mixin; eauto.
    - by intros X Y Z ->%leibniz_equiv.
    - by intros X Y ->%leibniz_equiv.
    - solve_proper.
    - intros X1 X2 X3. by rewrite !gmultiset_op_union assoc_L.
    - intros X1 X2. by rewrite !gmultiset_op_union comm_L.
    - intros X. by rewrite gmultiset_core_empty left_id.
    - intros X1 X2 HX. rewrite !gmultiset_core_empty. exists ∅.
      by rewrite left_id.
  Qed.

  Canonical Structure gmultisetR := discreteR (gmultiset K) gmultiset_ra_mixin.

  Global Instance gmultiset_cmra_discrete : CmraDiscrete gmultisetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma gmultiset_ucmra_mixin : UcmraMixin (gmultiset K).
  Proof. split. done. intros X. by rewrite gmultiset_op_union left_id_L. done. Qed.
  Canonical Structure gmultisetUR := UcmraT (gmultiset K) gmultiset_ucmra_mixin.

  Global Instance gmultiset_cancelable X : Cancelable X.
  Proof.
    apply: discrete_cancelable=> Y Z _ ?. fold_leibniz. by apply (inj (X ∪)).
  Qed.

  Lemma gmultiset_opM X mY : X ⋅? mY = X ∪ from_option id ∅ mY.
  Proof. destruct mY; by rewrite /= ?right_id_L. Qed.

  Lemma gmultiset_update X Y : X ~~> Y.
  Proof. done. Qed.

  Lemma gmultiset_local_update_alloc X Y X' : (X,Y) ~l~> (X ∪ X', Y ∪ X').
  Proof.
    rewrite local_update_unital_discrete=> Z' _ /leibniz_equiv_iff->.
    split. done. rewrite !gmultiset_op_union.
    by rewrite -!assoc (comm _ Z' X').
  Qed.

  Lemma gmultiset_local_update_dealloc X Y X' : X' ⊆ X → X' ⊆ Y → (X,Y) ~l~> (X ∖ X', Y ∖ X').
  Proof.
    intros ->%gmultiset_union_difference ->%gmultiset_union_difference.
    rewrite local_update_unital_discrete=> Z' _ /leibniz_equiv_iff->.
    split. done. rewrite !gmultiset_op_union=> x.
    repeat (rewrite multiplicity_difference || rewrite multiplicity_union).
    omega.
  Qed.
End gmultiset.

Arguments gmultisetC _ {_ _}.
Arguments gmultisetR _ {_ _}.
Arguments gmultisetUR _ {_ _}.
