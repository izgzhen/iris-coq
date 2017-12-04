From iris.bi Require Export interface.
From iris.algebra Require Import monoid.
From stdpp Require Import hlist.

Definition bi_iff {PROP : bi} (P Q : PROP) : PROP := ((P → Q) ∧ (Q → P))%I.
Arguments bi_iff {_} _%I _%I : simpl never.
Instance: Params (@bi_iff) 1.
Infix "↔" := bi_iff : bi_scope.

Definition bi_wand_iff {PROP : bi} (P Q : PROP) : PROP :=
  ((P -∗ Q) ∧ (Q -∗ P))%I.
Arguments bi_wand_iff {_} _%I _%I : simpl never.
Instance: Params (@bi_wand_iff) 1.
Infix "∗-∗" := bi_wand_iff (at level 95, no associativity) : bi_scope.

Class Plain {PROP : bi} (P : PROP) := plain : P ⊢ bi_plainly P.
Arguments Plain {_} _%I : simpl never.
Arguments plain {_} _%I {_}.
Hint Mode Plain + ! : typeclass_instances.
Instance: Params (@Plain) 1.

Class Persistent {PROP : bi} (P : PROP) := persistent : P ⊢ bi_persistently P.
Arguments Persistent {_} _%I : simpl never.
Arguments persistent {_} _%I {_}.
Hint Mode Persistent + ! : typeclass_instances.
Instance: Params (@Persistent) 1.

Definition bi_affinely {PROP : bi} (P : PROP) : PROP := (emp ∧ P)%I.
Arguments bi_affinely {_} _%I : simpl never.
Instance: Params (@bi_affinely) 1.
Typeclasses Opaque bi_affinely.
Notation "□ P" := (bi_affinely (bi_persistently P))%I
  (at level 20, right associativity) : bi_scope.
Notation "■ P" := (bi_affinely (bi_plainly P))%I
  (at level 20, right associativity) : bi_scope.

Class Affine {PROP : bi} (Q : PROP) := affine : Q ⊢ emp.
Arguments Affine {_} _%I : simpl never.
Arguments affine {_} _%I {_}.
Hint Mode Affine + ! : typeclass_instances.

Class BiAffine (PROP : bi) := absorbing_bi (Q : PROP) : Affine Q.
Existing Instance absorbing_bi | 0.

Class BiPositive (PROP : bi) :=
  bi_positive (P Q : PROP) : bi_affinely (P ∗ Q) ⊢ bi_affinely P ∗ Q.

Definition bi_absorbingly {PROP : bi} (P : PROP) : PROP := (True ∗ P)%I.
Arguments bi_absorbingly {_} _%I : simpl never.
Instance: Params (@bi_absorbingly) 1.
Typeclasses Opaque bi_absorbingly.

Class Absorbing {PROP : bi} (P : PROP) := absorbing : bi_absorbingly P ⊢ P.
Arguments Absorbing {_} _%I : simpl never.
Arguments absorbing {_} _%I.

Definition bi_plainly_if {PROP : bi} (p : bool) (P : PROP) : PROP :=
  (if p then bi_plainly P else P)%I.
Arguments bi_plainly_if {_} !_ _%I /.
Instance: Params (@bi_plainly_if) 2.
Typeclasses Opaque bi_plainly_if.

Definition bi_persistently_if {PROP : bi} (p : bool) (P : PROP) : PROP :=
  (if p then bi_persistently P else P)%I.
Arguments bi_persistently_if {_} !_ _%I /.
Instance: Params (@bi_persistently_if) 2.
Typeclasses Opaque bi_persistently_if.

Definition bi_affinely_if {PROP : bi} (p : bool) (P : PROP) : PROP :=
  (if p then bi_affinely P else P)%I.
Arguments bi_affinely_if {_} !_ _%I /.
Instance: Params (@bi_affinely_if) 2.
Typeclasses Opaque bi_affinely_if.
Notation "□? p P" := (bi_affinely_if p (bi_persistently_if p P))%I
  (at level 20, p at level 9, P at level 20,
   right associativity, format "□? p  P") : bi_scope.
Notation "■? p P" := (bi_affinely_if p (bi_plainly_if p P))%I
  (at level 20, p at level 9, P at level 20,
   right associativity, format "■? p  P") : bi_scope.

Fixpoint bi_hexist {PROP : bi} {As} : himpl As PROP → PROP :=
  match As return himpl As PROP → PROP with
  | tnil => id
  | tcons A As => λ Φ, ∃ x, bi_hexist (Φ x)
  end%I.
Fixpoint bi_hforall {PROP : bi} {As} : himpl As PROP → PROP :=
  match As return himpl As PROP → PROP with
  | tnil => id
  | tcons A As => λ Φ, ∀ x, bi_hforall (Φ x)
  end%I.

Definition bi_laterN {PROP : sbi} (n : nat) (P : PROP) : PROP :=
  Nat.iter n bi_later P.
Arguments bi_laterN {_} !_%nat_scope _%I.
Instance: Params (@bi_laterN) 2.
Notation "▷^ n P" := (bi_laterN n P)
  (at level 20, n at level 9, P at level 20, format "▷^ n  P") : bi_scope.
Notation "▷? p P" := (bi_laterN (Nat.b2n p) P)
  (at level 20, p at level 9, P at level 20, format "▷? p  P") : bi_scope.

Definition bi_except_0 {PROP : sbi} (P : PROP) : PROP := (▷ False ∨ P)%I.
Arguments bi_except_0 {_} _%I : simpl never.
Notation "◇ P" := (bi_except_0 P) (at level 20, right associativity) : bi_scope.
Instance: Params (@bi_except_0) 1.
Typeclasses Opaque bi_except_0.

Class Timeless {PROP : sbi} (P : PROP) := timeless : ▷ P ⊢ ◇ P.
Arguments Timeless {_} _%I : simpl never.
Arguments timeless {_} _%I {_}.
Hint Mode Timeless + ! : typeclass_instances.
Instance: Params (@Timeless) 1.
