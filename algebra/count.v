From iris.algebra Require Export cmra.
From iris.algebra Require Import upred.
Notation count := nat (only parsing).

Section count.
Canonical Structure countC := leibnizC count.

Instance count_valid : Valid count := λ _, True.
Instance count_pcore : PCore count := λ _, None.
Instance count_op : Op count := λ x y, (x + y)%nat.

Definition count_ra_mixin : RAMixin nat.
Proof. by split; try apply _. Qed.
Canonical Structure countR := discreteR count count_ra_mixin.
End count.

(** Internalized properties *)
Lemma count_equivI {M} (x y : count) : x ≡ y ⊣⊢ (x = y : uPred M).
Proof. by uPred.unseal. Qed.
Lemma count_validI {M} (x : count) : ✓ x ⊣⊢ (True : uPred M).
Proof. by uPred.unseal. Qed.
