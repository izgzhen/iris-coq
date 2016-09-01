From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From iris.prelude Require Export collections coPset.

(** This is pretty much the same as algebra/gset, but I was not able to
generalize the construction without breaking canonical structures. *)

Inductive coPset_disj :=
  | CoPset : coPset → coPset_disj
  | CoPsetBot : coPset_disj.

Section coPset.
  Arguments op _ _ !_ !_ /.
  Canonical Structure coPset_disjC := leibnizC coPset_disj.

  Instance coPset_disj_valid : Valid coPset_disj := λ X,
    match X with CoPset _ => True | CoPsetBot => False end.
  Instance coPset_disj_empty : Empty coPset_disj := CoPset ∅.
  Instance coPset_disj_op : Op coPset_disj := λ X Y,
    match X, Y with
    | CoPset X, CoPset Y => if decide (X ⊥ Y) then CoPset (X ∪ Y) else CoPsetBot
    | _, _ => CoPsetBot
    end.
  Instance coPset_disj_pcore : PCore coPset_disj := λ _, Some ∅.

  Ltac coPset_disj_solve :=
    repeat (simpl || case_decide);
    first [apply (f_equal CoPset)|done|exfalso]; set_solver by eauto.

  Lemma coPset_included X Y : CoPset X ≼ CoPset Y ↔ X ⊆ Y.
  Proof.
    split.
    - move=> [[Z|]]; simpl; try case_decide; set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L.
      exists (CoPset Z). coPset_disj_solve.
  Qed.
  Lemma coPset_disj_valid_inv_l X Y :
    ✓ (CoPset X ⋅ Y) → ∃ Y', Y = CoPset Y' ∧ X ⊥ Y'.
  Proof. destruct Y; repeat (simpl || case_decide); by eauto. Qed.
  Lemma coPset_disj_union X Y : X ⊥ Y → CoPset X ⋅ CoPset Y = CoPset (X ∪ Y).
  Proof. intros. by rewrite /= decide_True. Qed.
  Lemma coPset_disj_valid_op X Y : ✓ (CoPset X ⋅ CoPset Y) ↔ X ⊥ Y.
  Proof. simpl. case_decide; by split. Qed.

  Lemma coPset_disj_ra_mixin : RAMixin coPset_disj.
  Proof.
    apply ra_total_mixin; eauto.
    - intros [?|]; destruct 1; coPset_disj_solve.
    - by constructor.
    - by destruct 1.
    - intros [X1|] [X2|] [X3|]; coPset_disj_solve.
    - intros [X1|] [X2|]; coPset_disj_solve.
    - intros [X|]; coPset_disj_solve.
    - exists (CoPset ∅); coPset_disj_solve.
    - intros [X1|] [X2|]; coPset_disj_solve.
  Qed.
  Canonical Structure coPset_disjR := discreteR coPset_disj coPset_disj_ra_mixin.

  Lemma coPset_disj_ucmra_mixin : UCMRAMixin coPset_disj.
  Proof. split; try apply _ || done. intros [X|]; coPset_disj_solve. Qed.
  Canonical Structure coPset_disjUR :=
    discreteUR coPset_disj coPset_disj_ra_mixin coPset_disj_ucmra_mixin.
End coPset.
