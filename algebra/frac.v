From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export cmra.

Notation frac := Qp (only parsing).

Section frac.
Canonical Structure fracC := leibnizC frac.

Instance frac_valid : Valid frac := λ x, (x ≤ 1)%Qc.
Instance frac_pcore : PCore frac := λ _, None.
Instance frac_op : Op frac := λ x y, (x + y)%Qp.

Definition frac_ra_mixin : RAMixin frac.
Proof.
  split; try apply _; try done.
  unfold valid, op, frac_op, frac_valid. intros x y. trans (x+y)%Qp; last done.
  rewrite -{1}(Qcplus_0_r x) -Qcplus_le_mono_l; auto using Qclt_le_weak.
Qed.
Canonical Structure fracR := discreteR frac frac_ra_mixin.
End frac.

(** Exclusive *)
Global Instance frac_full_exclusive : Exclusive 1%Qp.
Proof.
  move=> y /Qcle_not_lt [] /=. by rewrite -{1}(Qcplus_0_r 1) -Qcplus_lt_mono_l.
Qed.
