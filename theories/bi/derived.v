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

Class AffineBI (PROP : bi) := absorbing_bi (Q : PROP) : Affine Q.
Existing Instance absorbing_bi | 0.

Class PositiveBI (PROP : bi) :=
  positive_bi (P Q : PROP) : bi_affinely (P ∗ Q) ⊢ bi_affinely P ∗ Q.

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

Module bi.
Import interface.bi.
Section bi_derived.
Context {PROP : bi}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.
Implicit Types Ps : list PROP.
Implicit Types A : Type.

Hint Extern 100 (NonExpansive _) => solve_proper.

(* Force implicit argument PROP *)
Notation "P ⊢ Q" := (@bi_entails PROP P%I Q%I).
Notation "P ⊣⊢ Q" := (equiv (A:=bi_car PROP) P%I Q%I).

(* Derived stuff about the entailment *)
Global Instance entails_anti_sym : AntiSymm (⊣⊢) (@bi_entails PROP).
Proof. intros P Q ??. by apply equiv_spec. Qed.
Lemma equiv_entails P Q : (P ⊣⊢ Q) → (P ⊢ Q).
Proof. apply equiv_spec. Qed.
Lemma equiv_entails_sym P Q : (Q ⊣⊢ P) → (P ⊢ Q).
Proof. apply equiv_spec. Qed.
Global Instance entails_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> iff) ((⊢) : relation PROP).
Proof.
  move => P1 P2 /equiv_spec [HP1 HP2] Q1 Q2 /equiv_spec [HQ1 HQ2]; split=>?.
  - by trans P1; [|trans Q1].
  - by trans P2; [|trans Q2].
Qed.
Lemma entails_equiv_l P Q R : (P ⊣⊢ Q) → (Q ⊢ R) → (P ⊢ R).
Proof. by intros ->. Qed.
Lemma entails_equiv_r P Q R : (P ⊢ Q) → (Q ⊣⊢ R) → (P ⊢ R).
Proof. by intros ? <-. Qed.
 Global Instance bi_valid_proper : Proper ((⊣⊢) ==> iff) (@bi_valid PROP).
Proof. solve_proper. Qed.
Global Instance bi_valid_mono : Proper ((⊢) ==> impl) (@bi_valid PROP).
Proof. solve_proper. Qed.
Global Instance bi_valid_flip_mono :
  Proper (flip (⊢) ==> flip impl) (@bi_valid PROP).
Proof. solve_proper. Qed.

(* Propers *)
Global Instance pure_proper : Proper (iff ==> (⊣⊢)) (@bi_pure PROP) | 0.
Proof. intros φ1 φ2 Hφ. apply equiv_dist=> n. by apply pure_ne. Qed.
Global Instance and_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_and PROP) := ne_proper_2 _.
Global Instance or_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_or PROP) := ne_proper_2 _.
Global Instance impl_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_impl PROP) := ne_proper_2 _.
Global Instance sep_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_sep PROP) := ne_proper_2 _.
Global Instance wand_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_wand PROP) := ne_proper_2 _.
Global Instance forall_proper A :
  Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_forall PROP A).
Proof.
  intros Φ1 Φ2 HΦ. apply equiv_dist=> n.
  apply forall_ne=> x. apply equiv_dist, HΦ.
Qed.
Global Instance exist_proper A :
  Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_exist PROP A).
Proof.
  intros Φ1 Φ2 HΦ. apply equiv_dist=> n.
  apply exist_ne=> x. apply equiv_dist, HΦ.
Qed.
Global Instance internal_eq_proper (A : ofeT) :
  Proper ((≡) ==> (≡) ==> (⊣⊢)) (@bi_internal_eq PROP A) := ne_proper_2 _.
Global Instance plainly_proper :
  Proper ((⊣⊢) ==> (⊣⊢)) (@bi_plainly PROP) := ne_proper _.
Global Instance persistently_proper :
  Proper ((⊣⊢) ==> (⊣⊢)) (@bi_persistently PROP) := ne_proper _.

(* Derived logical stuff *)
Lemma and_elim_l' P Q R : (P ⊢ R) → P ∧ Q ⊢ R.
Proof. by rewrite and_elim_l. Qed.
Lemma and_elim_r' P Q R : (Q ⊢ R) → P ∧ Q ⊢ R.
Proof. by rewrite and_elim_r. Qed.
Lemma or_intro_l' P Q R : (P ⊢ Q) → P ⊢ Q ∨ R.
Proof. intros ->; apply or_intro_l. Qed.
Lemma or_intro_r' P Q R : (P ⊢ R) → P ⊢ Q ∨ R.
Proof. intros ->; apply or_intro_r. Qed.
Lemma exist_intro' {A} P (Ψ : A → PROP) a : (P ⊢ Ψ a) → P ⊢ ∃ a, Ψ a.
Proof. intros ->; apply exist_intro. Qed.
Lemma forall_elim' {A} P (Ψ : A → PROP) : (P ⊢ ∀ a, Ψ a) → ∀ a, P ⊢ Ψ a.
Proof. move=> HP a. by rewrite HP forall_elim. Qed.

Hint Resolve pure_intro forall_intro.
Hint Resolve or_elim or_intro_l' or_intro_r'.
Hint Resolve and_intro and_elim_l' and_elim_r'.

Lemma impl_intro_l P Q R : (Q ∧ P ⊢ R) → P ⊢ Q → R.
Proof. intros HR; apply impl_intro_r; rewrite -HR; auto. Qed.
Lemma impl_elim P Q R : (P ⊢ Q → R) → (P ⊢ Q) → P ⊢ R.
Proof. intros. rewrite -(impl_elim_l' P Q R); auto. Qed.
Lemma impl_elim_r' P Q R : (Q ⊢ P → R) → P ∧ Q ⊢ R.
Proof. intros; apply impl_elim with P; auto. Qed.
Lemma impl_elim_l P Q : (P → Q) ∧ P ⊢ Q.
Proof. by apply impl_elim_l'. Qed.
Lemma impl_elim_r P Q : P ∧ (P → Q) ⊢ Q.
Proof. by apply impl_elim_r'. Qed.

Lemma False_elim P : False ⊢ P.
Proof. by apply (pure_elim' False). Qed.
Lemma True_intro P : P ⊢ True.
Proof. by apply pure_intro. Qed.
Hint Immediate False_elim.

Lemma and_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∧ P' ⊢ Q ∧ Q'.
Proof. auto. Qed.
Lemma and_mono_l P P' Q : (P ⊢ Q) → P ∧ P' ⊢ Q ∧ P'.
Proof. by intros; apply and_mono. Qed.
Lemma and_mono_r P P' Q' : (P' ⊢ Q') → P ∧ P' ⊢ P ∧ Q'.
Proof. by apply and_mono. Qed.

Lemma or_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∨ P' ⊢ Q ∨ Q'.
Proof. auto. Qed.
Lemma or_mono_l P P' Q : (P ⊢ Q) → P ∨ P' ⊢ Q ∨ P'.
Proof. by intros; apply or_mono. Qed.
Lemma or_mono_r P P' Q' : (P' ⊢ Q') → P ∨ P' ⊢ P ∨ Q'.
Proof. by apply or_mono. Qed.

Lemma impl_mono P P' Q Q' : (Q ⊢ P) → (P' ⊢ Q') → (P → P') ⊢ Q → Q'.
Proof.
  intros HP HQ'; apply impl_intro_l; rewrite -HQ'.
  apply impl_elim with P; eauto.
Qed.
Lemma forall_mono {A} (Φ Ψ : A → PROP) :
  (∀ a, Φ a ⊢ Ψ a) → (∀ a, Φ a) ⊢ ∀ a, Ψ a.
Proof.
  intros HP. apply forall_intro=> a; rewrite -(HP a); apply forall_elim.
Qed.
Lemma exist_mono {A} (Φ Ψ : A → PROP) :
  (∀ a, Φ a ⊢ Ψ a) → (∃ a, Φ a) ⊢ ∃ a, Ψ a.
Proof. intros HΦ. apply exist_elim=> a; rewrite (HΦ a); apply exist_intro. Qed.

Global Instance and_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@bi_and PROP).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance and_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_and PROP).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance or_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@bi_or PROP).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance or_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_or PROP).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance impl_mono' :
  Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@bi_impl PROP).
Proof. by intros P P' HP Q Q' HQ; apply impl_mono. Qed.
Global Instance impl_flip_mono' :
  Proper ((⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_impl PROP).
Proof. by intros P P' HP Q Q' HQ; apply impl_mono. Qed.
Global Instance forall_mono' A :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_forall PROP A).
Proof. intros P1 P2; apply forall_mono. Qed.
Global Instance forall_flip_mono' A :
  Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) (@bi_forall PROP A).
Proof. intros P1 P2; apply forall_mono. Qed.
Global Instance exist_mono' A :
  Proper (pointwise_relation _ ((⊢)) ==> (⊢)) (@bi_exist PROP A).
Proof. intros P1 P2; apply exist_mono. Qed.
Global Instance exist_flip_mono' A :
  Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) (@bi_exist PROP A).
Proof. intros P1 P2; apply exist_mono. Qed.

Global Instance and_idem : IdemP (⊣⊢) (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_idem : IdemP (⊣⊢) (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_comm : Comm (⊣⊢) (@bi_and PROP).
Proof. intros P Q; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_and : LeftId (⊣⊢) True%I (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_True : RightId (⊣⊢) True%I (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance False_and : LeftAbsorb (⊣⊢) False%I (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_False : RightAbsorb (⊣⊢) False%I (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_or : LeftAbsorb (⊣⊢) True%I (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_True : RightAbsorb (⊣⊢) True%I (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance False_or : LeftId (⊣⊢) False%I (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_False : RightId (⊣⊢) False%I (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_assoc : Assoc (⊣⊢) (@bi_and PROP).
Proof. intros P Q R; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_comm : Comm (⊣⊢) (@bi_or PROP).
Proof. intros P Q; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_assoc : Assoc (⊣⊢) (@bi_or PROP).
Proof. intros P Q R; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_impl : LeftId (⊣⊢) True%I (@bi_impl PROP).
Proof.
  intros P; apply (anti_symm (⊢)).
  - by rewrite -(left_id True%I (∧)%I (_ → _)%I) impl_elim_r.
  - by apply impl_intro_l; rewrite left_id.
Qed.

Lemma False_impl P : (False → P) ⊣⊢ True.
Proof.
  apply (anti_symm (⊢)); [by auto|].
  apply impl_intro_l. rewrite left_absorb. auto.
Qed.

Lemma exists_impl_forall {A} P (Ψ : A → PROP) :
  ((∃ x : A, Ψ x) → P) ⊣⊢ ∀ x : A, Ψ x → P.
Proof.
  apply equiv_spec; split.
  - apply forall_intro=>x. by rewrite -exist_intro.
  - apply impl_intro_r, impl_elim_r', exist_elim=>x.
    apply impl_intro_r. by rewrite (forall_elim x) impl_elim_r.
Qed.

Lemma or_and_l P Q R : P ∨ Q ∧ R ⊣⊢ (P ∨ Q) ∧ (P ∨ R).
Proof.
  apply (anti_symm (⊢)); first auto.
  do 2 (apply impl_elim_l', or_elim; apply impl_intro_l); auto.
Qed.
Lemma or_and_r P Q R : P ∧ Q ∨ R ⊣⊢ (P ∨ R) ∧ (Q ∨ R).
Proof. by rewrite -!(comm _ R) or_and_l. Qed.
Lemma and_or_l P Q R : P ∧ (Q ∨ R) ⊣⊢ P ∧ Q ∨ P ∧ R.
Proof.
  apply (anti_symm (⊢)); last auto.
  apply impl_elim_r', or_elim; apply impl_intro_l; auto.
Qed.
Lemma and_or_r P Q R : (P ∨ Q) ∧ R ⊣⊢ P ∧ R ∨ Q ∧ R.
Proof. by rewrite -!(comm _ R) and_or_l. Qed.
Lemma and_exist_l {A} P (Ψ : A → PROP) : P ∧ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∧ Ψ a.
Proof.
  apply (anti_symm (⊢)).
  - apply impl_elim_r'. apply exist_elim=>a. apply impl_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=>a. apply and_intro; first by rewrite and_elim_l.
    by rewrite -(exist_intro a) and_elim_r.
Qed.
Lemma and_exist_r {A} P (Φ: A → PROP) : (∃ a, Φ a) ∧ P ⊣⊢ ∃ a, Φ a ∧ P.
Proof.
  rewrite -(comm _ P) and_exist_l. apply exist_proper=>a. by rewrite comm.
Qed.
Lemma or_exist {A} (Φ Ψ : A → PROP) :
  (∃ a, Φ a ∨ Ψ a) ⊣⊢ (∃ a, Φ a) ∨ (∃ a, Ψ a).
Proof.
  apply (anti_symm (⊢)).
  - apply exist_elim=> a. by rewrite -!(exist_intro a).
  - apply or_elim; apply exist_elim=> a; rewrite -(exist_intro a); auto.
Qed.

Lemma and_alt P Q : P ∧ Q ⊣⊢ ∀ b : bool, if b then P else Q.
Proof.
   apply (anti_symm _); first apply forall_intro=> -[]; auto.
   by apply and_intro; [rewrite (forall_elim true)|rewrite (forall_elim false)].
Qed.
Lemma or_alt P Q : P ∨ Q ⊣⊢ ∃ b : bool, if b then P else Q.
Proof.
  apply (anti_symm _); last apply exist_elim=> -[]; auto.
  by apply or_elim; [rewrite -(exist_intro true)|rewrite -(exist_intro false)].
Qed.

Lemma entails_equiv_and P Q : (P ⊣⊢ Q ∧ P) ↔ (P ⊢ Q).
Proof. split. by intros ->; auto. intros; apply (anti_symm _); auto. Qed.

Global Instance iff_ne : NonExpansive2 (@bi_iff PROP).
Proof. unfold bi_iff; solve_proper. Qed.
Global Instance iff_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_iff PROP) := ne_proper_2 _.

Lemma iff_refl Q P : Q ⊢ P ↔ P.
Proof. rewrite /bi_iff; apply and_intro; apply impl_intro_l; auto. Qed.

(* Equality stuff *)
Hint Resolve internal_eq_refl.
Lemma equiv_internal_eq {A : ofeT} P (a b : A) : a ≡ b → P ⊢ a ≡ b.
Proof. intros ->. auto. Qed.
Lemma internal_eq_rewrite' {A : ofeT} a b (Ψ : A → PROP) P
  {HΨ : NonExpansive Ψ} : (P ⊢ a ≡ b) → (P ⊢ Ψ a) → P ⊢ Ψ b.
Proof.
  intros Heq HΨa. rewrite -(idemp bi_and P) {1}Heq HΨa.
  apply impl_elim_l'. by apply internal_eq_rewrite.
Qed.

Lemma internal_eq_sym {A : ofeT} (a b : A) : a ≡ b ⊢ b ≡ a.
Proof. apply (internal_eq_rewrite' a b (λ b, b ≡ a)%I); auto. Qed.
Lemma internal_eq_iff P Q : P ≡ Q ⊢ P ↔ Q.
Proof. apply (internal_eq_rewrite' P Q (λ Q, P ↔ Q))%I; auto using iff_refl. Qed.

Lemma f_equiv {A B : ofeT} (f : A → B) `{!NonExpansive f} x y :
  x ≡ y ⊢ f x ≡ f y.
Proof. apply (internal_eq_rewrite' x y (λ y, f x ≡ f y)%I); auto. Qed.

Lemma prod_equivI {A B : ofeT} (x y : A * B) : x ≡ y ⊣⊢ x.1 ≡ y.1 ∧ x.2 ≡ y.2.
Proof.
  apply (anti_symm _).
  - apply and_intro; apply f_equiv; apply _.
  - rewrite {3}(surjective_pairing x) {3}(surjective_pairing y).
    apply (internal_eq_rewrite' (x.1) (y.1) (λ a, (x.1,x.2) ≡ (a,y.2))%I); auto.
    apply (internal_eq_rewrite' (x.2) (y.2) (λ b, (x.1,x.2) ≡ (x.1,b))%I); auto.
Qed.
Lemma sum_equivI {A B : ofeT} (x y : A + B) :
  x ≡ y ⊣⊢
    match x, y with
    | inl a, inl a' => a ≡ a' | inr b, inr b' => b ≡ b' | _, _ => False
    end.
Proof.
  apply (anti_symm _).
  - apply (internal_eq_rewrite' x y (λ y,
             match x, y with
             | inl a, inl a' => a ≡ a' | inr b, inr b' => b ≡ b' | _, _ => False
             end)%I); auto.
    destruct x; auto.
  - destruct x as [a|b], y as [a'|b']; auto; apply f_equiv, _.
Qed.
Lemma option_equivI {A : ofeT} (x y : option A) :
  x ≡ y ⊣⊢ match x, y with
           | Some a, Some a' => a ≡ a' | None, None => True | _, _ => False
           end.
Proof.
  apply (anti_symm _).
  - apply (internal_eq_rewrite' x y (λ y,
             match x, y with
             | Some a, Some a' => a ≡ a' | None, None => True | _, _ => False
             end)%I); auto.
    destruct x; auto.
  - destruct x as [a|], y as [a'|]; auto. apply f_equiv, _.
Qed.

Lemma sig_equivI {A : ofeT} (P : A → Prop) (x y : sig P) : `x ≡ `y ⊣⊢ x ≡ y.
Proof. apply (anti_symm _). apply sig_eq. apply f_equiv, _. Qed.

Lemma ofe_fun_equivI {A} {B : A → ofeT} (f g : ofe_fun B) : f ≡ g ⊣⊢ ∀ x, f x ≡ g x.
Proof.
  apply (anti_symm _); auto using fun_ext.
  apply (internal_eq_rewrite' f g (λ g, ∀ x : A, f x ≡ g x)%I); auto.
  intros n h h' Hh; apply forall_ne=> x; apply internal_eq_ne; auto.
Qed.
Lemma ofe_morC_equivI {A B : ofeT} (f g : A -n> B) : f ≡ g ⊣⊢ ∀ x, f x ≡ g x.
Proof.
  apply (anti_symm _).
  - apply (internal_eq_rewrite' f g (λ g, ∀ x : A, f x ≡ g x)%I); auto.
  - rewrite -(ofe_fun_equivI (ofe_mor_car _ _ f) (ofe_mor_car _ _ g)).
    set (h1 (f : A -n> B) :=
      exist (λ f : A -c> B, NonExpansive (f : A → B)) f (ofe_mor_ne A B f)).
    set (h2 (f : sigC (λ f : A -c> B, NonExpansive (f : A → B))) :=
      @CofeMor A B (`f) (proj2_sig f)).
    assert (∀ f, h2 (h1 f) = f) as Hh by (by intros []).
    assert (NonExpansive h2) by (intros ??? EQ; apply EQ).
    by rewrite -{2}[f]Hh -{2}[g]Hh -f_equiv -sig_equivI.
Qed.

(* BI Stuff *)
Hint Resolve sep_mono.
Lemma sep_mono_l P P' Q : (P ⊢ Q) → P ∗ P' ⊢ Q ∗ P'.
Proof. by intros; apply sep_mono. Qed.
Lemma sep_mono_r P P' Q' : (P' ⊢ Q') → P ∗ P' ⊢ P ∗ Q'.
Proof. by apply sep_mono. Qed.
Global Instance sep_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@bi_sep PROP).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Global Instance sep_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_sep PROP).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Lemma wand_mono P P' Q Q' : (Q ⊢ P) → (P' ⊢ Q') → (P -∗ P') ⊢ Q -∗ Q'.
Proof.
  intros HP HQ; apply wand_intro_r. rewrite HP -HQ. by apply wand_elim_l'.
Qed.
Global Instance wand_mono' : Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@bi_wand PROP).
Proof. by intros P P' HP Q Q' HQ; apply wand_mono. Qed.
Global Instance wand_flip_mono' :
  Proper ((⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_wand PROP).
Proof. by intros P P' HP Q Q' HQ; apply wand_mono. Qed.

Global Instance sep_comm : Comm (⊣⊢) (@bi_sep PROP).
Proof. intros P Q; apply (anti_symm _); auto using sep_comm'. Qed.
Global Instance sep_assoc : Assoc (⊣⊢) (@bi_sep PROP).
Proof.
  intros P Q R; apply (anti_symm _); auto using sep_assoc'.
  by rewrite !(comm _ P) !(comm _ _ R) sep_assoc'.
Qed.
Global Instance emp_sep : LeftId (⊣⊢) emp%I (@bi_sep PROP).
Proof. intros P; apply (anti_symm _); auto using emp_sep_1, emp_sep_2. Qed.
Global Instance sep_emp : RightId (⊣⊢) emp%I (@bi_sep PROP).
Proof. by intros P; rewrite comm left_id. Qed.

Global Instance sep_False : LeftAbsorb (⊣⊢) False%I (@bi_sep PROP).
Proof. intros P; apply (anti_symm _); auto using wand_elim_l'. Qed.
Global Instance False_sep : RightAbsorb (⊣⊢) False%I (@bi_sep PROP).
Proof. intros P. by rewrite comm left_absorb. Qed.

Lemma True_sep_2 P : P ⊢ True ∗ P.
Proof. rewrite -{1}[P](left_id emp%I bi_sep). auto using sep_mono. Qed.
Lemma sep_True_2 P : P ⊢ P ∗ True.
Proof. by rewrite comm -True_sep_2. Qed.

Lemma sep_intro_valid_l P Q R : P → (R ⊢ Q) → R ⊢ P ∗ Q.
Proof. intros ? ->. rewrite -{1}(left_id emp%I _ Q). by apply sep_mono. Qed.
Lemma sep_intro_valid_r P Q R : (R ⊢ P) → Q → R ⊢ P ∗ Q.
Proof. intros -> ?. rewrite comm. by apply sep_intro_valid_l. Qed.
Lemma sep_elim_valid_l P Q R : P → (P ∗ R ⊢ Q) → R ⊢ Q.
Proof. intros <- <-. by rewrite left_id. Qed.
Lemma sep_elim_valid_r P Q R : P → (R ∗ P ⊢ Q) → R ⊢ Q.
Proof. intros <- <-. by rewrite right_id. Qed.

Lemma wand_intro_l P Q R : (Q ∗ P ⊢ R) → P ⊢ Q -∗ R.
Proof. rewrite comm; apply wand_intro_r. Qed.
Lemma wand_elim_l P Q : (P -∗ Q) ∗ P ⊢ Q.
Proof. by apply wand_elim_l'. Qed.
Lemma wand_elim_r P Q : P ∗ (P -∗ Q) ⊢ Q.
Proof. rewrite (comm _ P); apply wand_elim_l. Qed.
Lemma wand_elim_r' P Q R : (Q ⊢ P -∗ R) → P ∗ Q ⊢ R.
Proof. intros ->; apply wand_elim_r. Qed.
Lemma wand_apply P Q R S : (P ⊢ Q -∗ R) → (S ⊢ P ∗ Q) → S ⊢ R.
Proof. intros HR%wand_elim_l' HQ. by rewrite HQ. Qed.
Lemma wand_frame_l P Q R : (Q -∗ R) ⊢ P ∗ Q -∗ P ∗ R.
Proof. apply wand_intro_l. rewrite -assoc. apply sep_mono_r, wand_elim_r. Qed.
Lemma wand_frame_r P Q R : (Q -∗ R) ⊢ Q ∗ P -∗ R ∗ P.
Proof.
  apply wand_intro_l. rewrite ![(_ ∗ P)%I]comm -assoc.
  apply sep_mono_r, wand_elim_r.
Qed.

Lemma emp_wand P : (emp -∗ P) ⊣⊢ P.
Proof.
  apply (anti_symm _).
  - by rewrite -[(emp -∗ P)%I]left_id wand_elim_r.
  - apply wand_intro_l. by rewrite left_id.
Qed.
Lemma False_wand P : (False -∗ P) ⊣⊢ True.
Proof.
  apply (anti_symm (⊢)); [by auto|].
  apply wand_intro_l. rewrite left_absorb. auto.
Qed.

Lemma wand_curry P Q R : (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R).
Proof.
  apply (anti_symm _).
  - apply wand_intro_l. by rewrite (comm _ P) -assoc !wand_elim_r.
  - do 2 apply wand_intro_l. by rewrite assoc (comm _ Q) wand_elim_r.
Qed.

Lemma sep_and_l P Q R : P ∗ (Q ∧ R) ⊢ (P ∗ Q) ∧ (P ∗ R).
Proof. auto. Qed.
Lemma sep_and_r P Q R : (P ∧ Q) ∗ R ⊢ (P ∗ R) ∧ (Q ∗ R).
Proof. auto. Qed.
Lemma sep_or_l P Q R : P ∗ (Q ∨ R) ⊣⊢ (P ∗ Q) ∨ (P ∗ R).
Proof.
  apply (anti_symm (⊢)); last by eauto 8.
  apply wand_elim_r', or_elim; apply wand_intro_l; auto.
Qed.
Lemma sep_or_r P Q R : (P ∨ Q) ∗ R ⊣⊢ (P ∗ R) ∨ (Q ∗ R).
Proof. by rewrite -!(comm _ R) sep_or_l. Qed.
Lemma sep_exist_l {A} P (Ψ : A → PROP) : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a.
Proof.
  intros; apply (anti_symm (⊢)).
  - apply wand_elim_r', exist_elim=>a. apply wand_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=> a; apply sep_mono; auto using exist_intro.
Qed.
Lemma sep_exist_r {A} (Φ: A → PROP) Q: (∃ a, Φ a) ∗ Q ⊣⊢ ∃ a, Φ a ∗ Q.
Proof. setoid_rewrite (comm _ _ Q); apply sep_exist_l. Qed.
Lemma sep_forall_l {A} P (Ψ : A → PROP) : P ∗ (∀ a, Ψ a) ⊢ ∀ a, P ∗ Ψ a.
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.
Lemma sep_forall_r {A} (Φ : A → PROP) Q : (∀ a, Φ a) ∗ Q ⊢ ∀ a, Φ a ∗ Q.
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.

Global Instance wand_iff_ne : NonExpansive2 (@bi_wand_iff PROP).
Proof. solve_proper. Qed.
Global Instance wand_iff_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_wand_iff PROP) := ne_proper_2 _.

Lemma wand_iff_refl P : emp ⊢ P ∗-∗ P.
Proof. apply and_intro; apply wand_intro_l; by rewrite right_id. Qed.

Lemma wand_entails P Q : (P -∗ Q)%I → P ⊢ Q.
Proof. intros. rewrite -[P]left_id. by apply wand_elim_l'. Qed.
Lemma entails_wand P Q : (P ⊢ Q) → (P -∗ Q)%I.
Proof. intros ->. apply wand_intro_r. by rewrite left_id. Qed.

Lemma equiv_wand_iff P Q : (P ⊣⊢ Q) → (P ∗-∗ Q)%I.
Proof. intros ->; apply wand_iff_refl. Qed.
Lemma wand_iff_equiv P Q : (P ∗-∗ Q)%I → (P ⊣⊢ Q).
Proof.
  intros HPQ; apply (anti_symm (⊢));
    apply wand_entails; rewrite /bi_valid HPQ /bi_wand_iff; auto.
Qed.

Lemma entails_impl P Q : (P ⊢ Q) → (P → Q)%I.
Proof. intros ->. apply impl_intro_l. auto. Qed.
Lemma impl_entails P Q `{!Affine P} : (P → Q)%I → P ⊢ Q.
Proof. intros HPQ. apply impl_elim with P=>//. by rewrite {1}(affine P). Qed.

Lemma equiv_iff P Q : (P ⊣⊢ Q) → (P ↔ Q)%I.
Proof. intros ->; apply iff_refl. Qed.
Lemma iff_equiv P Q `{!Affine P, !Affine Q} : (P ↔ Q)%I → (P ⊣⊢ Q).
Proof.
  intros HPQ; apply (anti_symm (⊢));
    apply: impl_entails; rewrite /bi_valid HPQ /bi_iff; auto.
Qed.

(* Pure stuff *)
Lemma pure_elim φ Q R : (Q ⊢ ⌜φ⌝) → (φ → Q ⊢ R) → Q ⊢ R.
Proof.
  intros HQ HQR. rewrite -(idemp (∧)%I Q) {1}HQ.
  apply impl_elim_l', pure_elim'=> ?. apply impl_intro_l.
  rewrite and_elim_l; auto.
Qed.
Lemma pure_mono φ1 φ2 : (φ1 → φ2) → ⌜φ1⌝ ⊢ ⌜φ2⌝.
Proof. auto using pure_elim', pure_intro. Qed.
Global Instance pure_mono' : Proper (impl ==> (⊢)) (@bi_pure PROP).
Proof. intros φ1 φ2; apply pure_mono. Qed.
Global Instance pure_flip_mono : Proper (flip impl ==> flip (⊢)) (@bi_pure PROP).
Proof. intros φ1 φ2; apply pure_mono. Qed.
Lemma pure_iff φ1 φ2 : (φ1 ↔ φ2) → ⌜φ1⌝ ⊣⊢ ⌜φ2⌝.
Proof. intros [??]; apply (anti_symm _); auto using pure_mono. Qed.
Lemma pure_elim_l φ Q R : (φ → Q ⊢ R) → ⌜φ⌝ ∧ Q ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.
Lemma pure_elim_r φ Q R : (φ → Q ⊢ R) → Q ∧ ⌜φ⌝ ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.

Lemma pure_True (φ : Prop) : φ → ⌜φ⌝ ⊣⊢ True.
Proof. intros; apply (anti_symm _); auto. Qed.
Lemma pure_False (φ : Prop) : ¬φ → ⌜φ⌝ ⊣⊢ False.
Proof. intros; apply (anti_symm _); eauto using pure_mono. Qed.

Lemma pure_and φ1 φ2 : ⌜φ1 ∧ φ2⌝ ⊣⊢ ⌜φ1⌝ ∧ ⌜φ2⌝.
Proof.
  apply (anti_symm _).
  - apply and_intro; apply pure_mono; tauto.
  - eapply (pure_elim φ1); [auto|]=> ?. rewrite and_elim_r. auto using pure_mono.
Qed.
Lemma pure_or φ1 φ2 : ⌜φ1 ∨ φ2⌝ ⊣⊢ ⌜φ1⌝ ∨ ⌜φ2⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[?|?]; auto using pure_mono.
  - apply or_elim; eauto using pure_mono.
Qed.
Lemma pure_impl φ1 φ2 : ⌜φ1 → φ2⌝ ⊣⊢ (⌜φ1⌝ → ⌜φ2⌝).
Proof.
  apply (anti_symm _).
  - apply impl_intro_l. rewrite -pure_and. apply pure_mono. naive_solver.
  - rewrite -pure_forall_2. apply forall_intro=> ?.
    by rewrite -(left_id True bi_and (_→_))%I (pure_True φ1) // impl_elim_r.
Qed.
Lemma pure_forall {A} (φ : A → Prop) : ⌜∀ x, φ x⌝ ⊣⊢ ∀ x, ⌜φ x⌝.
Proof.
  apply (anti_symm _); auto using pure_forall_2.
  apply forall_intro=> x. eauto using pure_mono.
Qed.
Lemma pure_exist {A} (φ : A → Prop) : ⌜∃ x, φ x⌝ ⊣⊢ ∃ x, ⌜φ x⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[x ?]. rewrite -(exist_intro x); auto using pure_mono.
  - apply exist_elim=> x. eauto using pure_mono.
Qed.

Lemma pure_impl_forall φ P : (⌜φ⌝ → P) ⊣⊢ (∀ _ : φ, P).
Proof.
  apply (anti_symm _).
  - apply forall_intro=> ?. by rewrite pure_True // left_id.
  - apply impl_intro_l, pure_elim_l=> Hφ. by rewrite (forall_elim Hφ).
Qed.
Lemma pure_alt φ : ⌜φ⌝ ⊣⊢ ∃ _ : φ, True.
Proof.
  apply (anti_symm _).
  - eapply pure_elim; eauto=> H. rewrite -(exist_intro H); auto.
  - by apply exist_elim, pure_intro.
Qed.
Lemma pure_wand_forall φ P `{!Absorbing P} : (⌜φ⌝ -∗ P) ⊣⊢ (∀ _ : φ, P).
Proof.
  apply (anti_symm _).
  - apply forall_intro=> Hφ.
    by rewrite -(left_id emp%I _ (_ -∗ _)%I) (pure_intro emp%I φ) // wand_elim_r.
  - apply wand_intro_l, wand_elim_l', pure_elim'=> Hφ.
    apply wand_intro_l. rewrite (forall_elim Hφ) comm. by apply absorbing.
Qed.

Lemma pure_internal_eq {A : ofeT} (x y : A) : ⌜x ≡ y⌝ ⊢ x ≡ y.
Proof. apply pure_elim'=> ->. apply internal_eq_refl. Qed.
Lemma discrete_eq {A : ofeT} (a b : A) : Discrete a → a ≡ b ⊣⊢ ⌜a ≡ b⌝.
Proof.
  intros. apply (anti_symm _); auto using discrete_eq_1, pure_internal_eq.
Qed.

(* Properties of the affinely modality *)
Global Instance affinely_ne : NonExpansive (@bi_affinely PROP).
Proof. solve_proper. Qed.
Global Instance affinely_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_affinely PROP).
Proof. solve_proper. Qed.
Global Instance affinely_mono' : Proper ((⊢) ==> (⊢)) (@bi_affinely PROP).
Proof. solve_proper. Qed.
Global Instance affinely_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_affinely PROP).
Proof. solve_proper. Qed.

Lemma affinely_elim_emp P : bi_affinely P ⊢ emp.
Proof. rewrite /bi_affinely; auto. Qed.
Lemma affinely_elim P : bi_affinely P ⊢ P.
Proof. rewrite /bi_affinely; auto. Qed.
Lemma affinely_mono P Q : (P ⊢ Q) → bi_affinely P ⊢ bi_affinely Q.
Proof. by intros ->. Qed.
Lemma affinely_idemp P : bi_affinely (bi_affinely P) ⊣⊢ bi_affinely P.
Proof. by rewrite /bi_affinely assoc idemp. Qed.

Lemma affinely_intro' P Q : (bi_affinely P ⊢ Q) → bi_affinely P ⊢ bi_affinely Q.
Proof. intros <-. by rewrite affinely_idemp. Qed.

Lemma affinely_False : bi_affinely False ⊣⊢ False.
Proof. by rewrite /bi_affinely right_absorb. Qed.
Lemma affinely_emp : bi_affinely emp ⊣⊢ emp.
Proof. by rewrite /bi_affinely (idemp bi_and). Qed.
Lemma affinely_or P Q : bi_affinely (P ∨ Q) ⊣⊢ bi_affinely P ∨ bi_affinely Q.
Proof. by rewrite /bi_affinely and_or_l. Qed.
Lemma affinely_and P Q : bi_affinely (P ∧ Q) ⊣⊢ bi_affinely P ∧ bi_affinely Q.
Proof.
  rewrite /bi_affinely -(comm _ P) (assoc _ (_ ∧ _)%I) -!(assoc _ P).
  by rewrite idemp !assoc (comm _ P).
Qed.
Lemma affinely_sep_2 P Q : bi_affinely P ∗ bi_affinely Q ⊢ bi_affinely (P ∗ Q).
Proof.
  rewrite /bi_affinely. apply and_intro.
  - by rewrite !and_elim_l right_id.
  - by rewrite !and_elim_r.
Qed.
Lemma affinely_sep `{PositiveBI PROP} P Q :
  bi_affinely (P ∗ Q) ⊣⊢ bi_affinely P ∗ bi_affinely Q.
Proof.
  apply (anti_symm _), affinely_sep_2.
  by rewrite -{1}affinely_idemp positive_bi !(comm _ (bi_affinely P)%I) positive_bi.
Qed.
Lemma affinely_forall {A} (Φ : A → PROP) :
  bi_affinely (∀ a, Φ a) ⊢ ∀ a, bi_affinely (Φ a).
Proof. apply forall_intro=> a. by rewrite (forall_elim a). Qed.
Lemma affinely_exist {A} (Φ : A → PROP) :
  bi_affinely (∃ a, Φ a) ⊣⊢ ∃ a, bi_affinely (Φ a).
Proof. by rewrite /bi_affinely and_exist_l. Qed.

Lemma affinely_True_emp : bi_affinely True ⊣⊢ bi_affinely emp.
Proof. apply (anti_symm _); rewrite /bi_affinely; auto. Qed.

Lemma affinely_and_l P Q : bi_affinely P ∧ Q ⊣⊢ bi_affinely (P ∧ Q).
Proof. by rewrite /bi_affinely assoc. Qed.
Lemma affinely_and_r P Q : P ∧ bi_affinely Q ⊣⊢ bi_affinely (P ∧ Q).
Proof. by rewrite /bi_affinely !assoc (comm _ P). Qed.
Lemma affinely_and_lr P Q : bi_affinely P ∧ Q ⊣⊢ P ∧ bi_affinely Q.
Proof. by rewrite affinely_and_l affinely_and_r. Qed.

(* Properties of the absorbingly modality *)
Global Instance absorbingly_ne : NonExpansive (@bi_absorbingly PROP).
Proof. solve_proper. Qed.
Global Instance absorbingly_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_absorbingly PROP).
Proof. solve_proper. Qed.
Global Instance absorbingly_mono' : Proper ((⊢) ==> (⊢)) (@bi_absorbingly PROP).
Proof. solve_proper. Qed.
Global Instance absorbingly_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_absorbingly PROP).
Proof. solve_proper. Qed.

Lemma absorbingly_intro P : P ⊢ bi_absorbingly P.
Proof. by rewrite /bi_absorbingly -True_sep_2. Qed.
Lemma absorbingly_mono P Q : (P ⊢ Q) → bi_absorbingly P ⊢ bi_absorbingly Q.
Proof. by intros ->. Qed.
Lemma absorbingly_idemp P : bi_absorbingly (bi_absorbingly P) ⊣⊢ bi_absorbingly P.
Proof.
  apply (anti_symm _), absorbingly_intro.
  rewrite /bi_absorbingly assoc. apply sep_mono; auto.
Qed.

Lemma absorbingly_pure φ : bi_absorbingly ⌜ φ ⌝ ⊣⊢ ⌜ φ ⌝.
Proof.
  apply (anti_symm _), absorbingly_intro.
  apply wand_elim_r', pure_elim'=> ?. apply wand_intro_l; auto.
Qed.
Lemma absorbingly_or P Q :
  bi_absorbingly (P ∨ Q) ⊣⊢ bi_absorbingly P ∨ bi_absorbingly Q.
Proof. by rewrite /bi_absorbingly sep_or_l. Qed.
Lemma absorbingly_and P Q :
  bi_absorbingly (P ∧ Q) ⊢ bi_absorbingly P ∧ bi_absorbingly Q.
Proof. apply and_intro; apply absorbingly_mono; auto. Qed.
Lemma absorbingly_forall {A} (Φ : A → PROP) :
  bi_absorbingly (∀ a, Φ a) ⊢ ∀ a, bi_absorbingly (Φ a).
Proof. apply forall_intro=> a. by rewrite (forall_elim a). Qed.
Lemma absorbingly_exist {A} (Φ : A → PROP) :
  bi_absorbingly (∃ a, Φ a) ⊣⊢ ∃ a, bi_absorbingly (Φ a).
Proof. by rewrite /bi_absorbingly sep_exist_l. Qed.

Lemma absorbingly_internal_eq {A : ofeT} (x y : A) : bi_absorbingly (x ≡ y) ⊣⊢ x ≡ y.
Proof.
  apply (anti_symm _), absorbingly_intro.
  apply wand_elim_r', (internal_eq_rewrite' x y (λ y, True -∗ x ≡ y)%I); auto.
  apply wand_intro_l, internal_eq_refl.
Qed.

Lemma absorbingly_sep P Q : bi_absorbingly (P ∗ Q) ⊣⊢ bi_absorbingly P ∗ bi_absorbingly Q.
Proof. by rewrite -{1}absorbingly_idemp /bi_absorbingly !assoc -!(comm _ P) !assoc. Qed.
Lemma absorbingly_True_emp : bi_absorbingly True ⊣⊢ bi_absorbingly emp.
Proof. by rewrite absorbingly_pure /bi_absorbingly right_id. Qed.
Lemma absorbingly_wand P Q : bi_absorbingly (P -∗ Q) ⊢ bi_absorbingly P -∗ bi_absorbingly Q.
Proof. apply wand_intro_l. by rewrite -absorbingly_sep wand_elim_r. Qed.

Lemma absorbingly_sep_l P Q : bi_absorbingly P ∗ Q ⊣⊢ bi_absorbingly (P ∗ Q).
Proof. by rewrite /bi_absorbingly assoc. Qed.
Lemma absorbingly_sep_r P Q : P ∗ bi_absorbingly Q ⊣⊢ bi_absorbingly (P ∗ Q).
Proof. by rewrite /bi_absorbingly !assoc (comm _ P). Qed.
Lemma absorbingly_sep_lr P Q : bi_absorbingly P ∗ Q ⊣⊢ P ∗ bi_absorbingly Q.
Proof. by rewrite absorbingly_sep_l absorbingly_sep_r. Qed.

Lemma affinely_absorbingly `{!PositiveBI PROP} P :
  bi_affinely (bi_absorbingly P) ⊣⊢ bi_affinely P.
Proof.
  apply (anti_symm _), affinely_mono, absorbingly_intro.
  by rewrite /bi_absorbingly affinely_sep affinely_True_emp affinely_emp left_id.
Qed.

(* Affine and absorbing propositions *)
Global Instance Affine_proper : Proper ((⊣⊢) ==> iff) (@Affine PROP).
Proof. solve_proper. Qed.
Global Instance Absorbing_proper : Proper ((⊣⊢) ==> iff) (@Absorbing PROP).
Proof. solve_proper. Qed.

Lemma affine_affinely P `{!Affine P} : bi_affinely P ⊣⊢ P.
Proof. rewrite /bi_affinely. apply (anti_symm _); auto. Qed.
Lemma absorbing_absorbingly P `{!Absorbing P} : bi_absorbingly P ⊣⊢ P.
Proof. by apply (anti_symm _), absorbingly_intro. Qed.

Lemma True_affine_all_affine P : Affine (True%I : PROP) → Affine P.
Proof. rewrite /Affine=> <-; auto. Qed.
Lemma emp_absorbing_all_absorbing P : Absorbing (emp%I : PROP) → Absorbing P.
Proof.
  intros. rewrite /Absorbing -{2}(left_id emp%I _ P).
  by rewrite -(absorbing emp) absorbingly_sep_l left_id.
Qed.

Lemma sep_elim_l P Q `{H : TCOr (Affine Q) (Absorbing P)} : P ∗ Q ⊢ P.
Proof.
  destruct H.
  - by rewrite (affine Q) right_id.
  - by rewrite (True_intro Q) comm.
Qed.
Lemma sep_elim_r P Q `{H : TCOr (Affine P) (Absorbing Q)} : P ∗ Q ⊢ Q.
Proof. by rewrite comm sep_elim_l. Qed.

Lemma sep_and P Q
    `{HPQ : TCOr (TCAnd (Affine P) (Affine Q)) (TCAnd (Absorbing P) (Absorbing Q))} :
  P ∗ Q ⊢ P ∧ Q.
Proof.
  destruct HPQ as [[??]|[??]];
    apply and_intro; apply: sep_elim_l || apply: sep_elim_r.
Qed.

Lemma affinely_intro P Q `{!Affine P} : (P ⊢ Q) → P ⊢ bi_affinely Q.
Proof. intros <-. by rewrite affine_affinely. Qed.

Lemma emp_and P `{!Affine P} : emp ∧ P ⊣⊢ P.
Proof. apply (anti_symm _); auto. Qed.
Lemma and_emp P `{!Affine P} : P ∧ emp ⊣⊢ P.
Proof. apply (anti_symm _); auto. Qed.
Lemma emp_or P `{!Affine P} : emp ∨ P ⊣⊢ emp.
Proof. apply (anti_symm _); auto. Qed.
Lemma or_emp P `{!Affine P} : P ∨ emp ⊣⊢ emp.
Proof. apply (anti_symm _); auto. Qed.

Lemma True_sep P `{!Absorbing P} : True ∗ P ⊣⊢ P.
Proof. apply (anti_symm _); auto using True_sep_2. Qed.
Lemma sep_True P `{!Absorbing P} : P ∗ True ⊣⊢ P.
Proof. by rewrite comm True_sep. Qed.

Section affine_bi.
  Context `{AffineBI PROP}.

  Global Instance affine_bi_absorbing P : Absorbing P | 0.
  Proof. by rewrite /Absorbing /bi_absorbingly (affine True%I) left_id. Qed.
  Global Instance affine_bi_positive : PositiveBI PROP.
  Proof. intros P Q. by rewrite !affine_affinely. Qed.

  Lemma True_emp : True ⊣⊢ emp.
  Proof. apply (anti_symm _); auto using affine. Qed.

  Global Instance emp_and' : LeftId (⊣⊢) emp%I (@bi_and PROP).
  Proof. intros P. by rewrite -True_emp left_id. Qed.
  Global Instance and_emp' : RightId (⊣⊢) emp%I (@bi_and PROP).
  Proof. intros P. by rewrite -True_emp right_id. Qed.

  Global Instance True_sep' : LeftId (⊣⊢) True%I (@bi_sep PROP).
  Proof. intros P. by rewrite True_emp left_id. Qed.
  Global Instance sep_True' : RightId (⊣⊢) True%I (@bi_sep PROP).
  Proof. intros P. by rewrite True_emp right_id. Qed.

  Lemma impl_wand_1 P Q : (P → Q) ⊢ P -∗ Q.
  Proof. apply wand_intro_l. by rewrite sep_and impl_elim_r. Qed.

  Lemma decide_emp φ `{!Decision φ} (P : PROP) :
    (if decide φ then P else emp) ⊣⊢ (⌜φ⌝ → P).
  Proof.
    destruct (decide _).
    - by rewrite pure_True // True_impl.
    - by rewrite pure_False // False_impl True_emp.
  Qed.
End affine_bi.

(* Properties of the persistence modality *)
Hint Resolve persistently_mono.
Global Instance persistently_mono' : Proper ((⊢) ==> (⊢)) (@bi_persistently PROP).
Proof. intros P Q; apply persistently_mono. Qed.
Global Instance persistently_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_persistently PROP).
Proof. intros P Q; apply persistently_mono. Qed.

Lemma absorbingly_persistently P :
  bi_absorbingly (bi_persistently P) ⊣⊢ bi_persistently P.
Proof.
  apply (anti_symm _), absorbingly_intro.
  by rewrite /bi_absorbingly comm persistently_absorbing.
Qed.

Lemma persistently_and_sep_assoc P Q R :
  bi_persistently P ∧ (Q ∗ R) ⊣⊢ (bi_persistently P ∧ Q) ∗ R.
Proof.
  apply (anti_symm (⊢)).
  - rewrite {1}persistently_idemp_2 persistently_and_sep_elim assoc.
    apply sep_mono_l, and_intro.
    + by rewrite and_elim_r persistently_absorbing.
    + by rewrite and_elim_l left_id.
  - apply and_intro.
    + by rewrite and_elim_l persistently_absorbing.
    + by rewrite and_elim_r.
Qed.
Lemma persistently_and_emp_elim P : emp ∧ bi_persistently P ⊢ P.
Proof. by rewrite comm persistently_and_sep_elim right_id and_elim_r. Qed.
Lemma persistently_elim_absorbingly P : bi_persistently P ⊢ bi_absorbingly P.
Proof.
  rewrite -(right_id True%I _ (bi_persistently _)%I) -{1}(left_id emp%I _ True%I).
  by rewrite persistently_and_sep_assoc (comm bi_and) persistently_and_emp_elim comm.
Qed.
Lemma persistently_elim P `{!Absorbing P} : bi_persistently P ⊢ P.
Proof. by rewrite persistently_elim_absorbingly absorbing_absorbingly. Qed.

Lemma persistently_idemp_1 P :
  bi_persistently (bi_persistently P) ⊢ bi_persistently P.
Proof. by rewrite persistently_elim_absorbingly absorbingly_persistently. Qed.
Lemma persistently_idemp P :
  bi_persistently (bi_persistently P) ⊣⊢ bi_persistently P.
Proof. apply (anti_symm _); auto using persistently_idemp_1, persistently_idemp_2. Qed.

Lemma persistently_intro' P Q :
  (bi_persistently P ⊢ Q) → bi_persistently P ⊢ bi_persistently Q.
Proof. intros <-. apply persistently_idemp_2. Qed.

Lemma persistently_pure φ : bi_persistently ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof.
  apply (anti_symm _).
  { by rewrite persistently_elim_absorbingly absorbingly_pure. }
  apply pure_elim'=> Hφ.
  trans (∀ x : False, bi_persistently True : PROP)%I; [by apply forall_intro|].
  rewrite persistently_forall_2. auto using persistently_mono, pure_intro.
Qed.
Lemma persistently_forall {A} (Ψ : A → PROP) :
  bi_persistently (∀ a, Ψ a) ⊣⊢ ∀ a, bi_persistently (Ψ a).
Proof.
  apply (anti_symm _); auto using persistently_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma persistently_exist {A} (Ψ : A → PROP) :
  bi_persistently (∃ a, Ψ a) ⊣⊢ ∃ a, bi_persistently (Ψ a).
Proof.
  apply (anti_symm _); auto using persistently_exist_1.
  apply exist_elim=> x. by rewrite (exist_intro x).
Qed.
Lemma persistently_and P Q :
  bi_persistently (P ∧ Q) ⊣⊢ bi_persistently P ∧ bi_persistently Q.
Proof. rewrite !and_alt persistently_forall. by apply forall_proper=> -[]. Qed.
Lemma persistently_or P Q :
  bi_persistently (P ∨ Q) ⊣⊢ bi_persistently P ∨ bi_persistently Q.
Proof. rewrite !or_alt persistently_exist. by apply exist_proper=> -[]. Qed.
Lemma persistently_impl P Q :
  bi_persistently (P → Q) ⊢ bi_persistently P → bi_persistently Q.
Proof.
  apply impl_intro_l; rewrite -persistently_and.
  apply persistently_mono, impl_elim with P; auto.
Qed.

Lemma persistently_sep_dup P :
  bi_persistently P ⊣⊢ bi_persistently P ∗ bi_persistently P.
Proof.
  apply (anti_symm _).
  - rewrite -{1}(idemp bi_and (bi_persistently _)).
    by rewrite -{2}(left_id emp%I _ (bi_persistently _))
      persistently_and_sep_assoc and_elim_l.
  - by rewrite persistently_absorbing.
Qed.

Lemma persistently_and_sep_l_1 P Q : bi_persistently P ∧ Q ⊢ bi_persistently P ∗ Q.
Proof.
  by rewrite -{1}(left_id emp%I _ Q%I) persistently_and_sep_assoc and_elim_l.
Qed.
Lemma persistently_and_sep_r_1 P Q : P ∧ bi_persistently Q ⊢ P ∗ bi_persistently Q.
Proof. by rewrite !(comm _ P) persistently_and_sep_l_1. Qed.

Lemma persistently_emp_intro P : P ⊢ bi_persistently emp.
Proof. by rewrite -plainly_elim_persistently -plainly_emp_intro. Qed.

Lemma persistently_internal_eq {A : ofeT} (a b : A) :
  bi_persistently (a ≡ b) ⊣⊢ a ≡ b.
Proof.
  apply (anti_symm (⊢)).
  { by rewrite persistently_elim_absorbingly absorbingly_internal_eq. }
  apply (internal_eq_rewrite' a b (λ b, bi_persistently (a ≡ b))%I); auto.
  rewrite -(internal_eq_refl emp%I a). apply persistently_emp_intro.
Qed.

Lemma persistently_True_emp : bi_persistently True ⊣⊢ bi_persistently emp.
Proof. apply (anti_symm _); auto using persistently_emp_intro. Qed.
Lemma persistently_and_sep P Q : bi_persistently (P ∧ Q) ⊢ bi_persistently (P ∗ Q).
Proof.
  rewrite persistently_and.
  rewrite -{1}persistently_idemp -persistently_and -{1}(left_id emp%I _ Q%I).
  by rewrite persistently_and_sep_assoc (comm bi_and) persistently_and_emp_elim.
Qed.

Lemma persistently_affinely P : bi_persistently (bi_affinely P) ⊣⊢ bi_persistently P.
Proof.
  by rewrite /bi_affinely persistently_and -persistently_True_emp
             persistently_pure left_id.
Qed.

Lemma and_sep_persistently P Q :
  bi_persistently P ∧ bi_persistently Q ⊣⊢ bi_persistently P ∗ bi_persistently Q.
Proof.
  apply (anti_symm _); auto using persistently_and_sep_l_1.
  apply and_intro.
  - by rewrite persistently_absorbing.
  - by rewrite comm persistently_absorbing.
Qed.
Lemma persistently_sep_2 P Q :
  bi_persistently P ∗ bi_persistently Q ⊢ bi_persistently (P ∗ Q).
Proof. by rewrite -persistently_and_sep persistently_and -and_sep_persistently. Qed.
Lemma persistently_sep `{PositiveBI PROP} P Q :
  bi_persistently (P ∗ Q) ⊣⊢ bi_persistently P ∗ bi_persistently Q.
Proof.
  apply (anti_symm _); auto using persistently_sep_2.
  rewrite -persistently_affinely affinely_sep -and_sep_persistently. apply and_intro.
  - by rewrite (affinely_elim_emp Q) right_id affinely_elim.
  - by rewrite (affinely_elim_emp P) left_id affinely_elim.
Qed.

Lemma persistently_wand P Q :
  bi_persistently (P -∗ Q) ⊢ bi_persistently P -∗ bi_persistently Q.
Proof. apply wand_intro_r. by rewrite persistently_sep_2 wand_elim_l. Qed.

Lemma persistently_entails_l P Q :
  (P ⊢ bi_persistently Q) → P ⊢ bi_persistently Q ∗ P.
Proof. intros; rewrite -persistently_and_sep_l_1; auto. Qed.
Lemma persistently_entails_r P Q :
  (P ⊢ bi_persistently Q) → P ⊢ P ∗ bi_persistently Q.
Proof. intros; rewrite -persistently_and_sep_r_1; auto. Qed.

Lemma persistently_impl_wand_2 P Q :
  bi_persistently (P -∗ Q) ⊢ bi_persistently (P → Q).
Proof.
  apply persistently_intro', impl_intro_r.
  rewrite -{2}(left_id emp%I _ P%I) persistently_and_sep_assoc.
  by rewrite (comm bi_and) persistently_and_emp_elim wand_elim_l.
Qed.

Section persistently_affinely_bi.
  Context `{AffineBI PROP}.

  Lemma persistently_emp : bi_persistently emp ⊣⊢ emp.
  Proof. by rewrite -!True_emp persistently_pure. Qed.

  Lemma persistently_and_sep_l P Q :
    bi_persistently P ∧ Q ⊣⊢ bi_persistently P ∗ Q.
  Proof.
    apply (anti_symm (⊢));
      eauto using persistently_and_sep_l_1, sep_and with typeclass_instances.
  Qed.
  Lemma persistently_and_sep_r P Q : P ∧ bi_persistently Q ⊣⊢ P ∗ bi_persistently Q.
  Proof. by rewrite !(comm _ P) persistently_and_sep_l. Qed.

  Lemma persistently_impl_wand P Q :
    bi_persistently (P → Q) ⊣⊢ bi_persistently (P -∗ Q).
  Proof.
    apply (anti_symm (⊢)); auto using persistently_impl_wand_2.
    apply persistently_intro', wand_intro_l.
    by rewrite -persistently_and_sep_r persistently_elim impl_elim_r.
  Qed.

  Lemma wand_alt P Q : (P -∗ Q) ⊣⊢ ∃ R, R ∗ bi_persistently (P ∗ R → Q).
  Proof.
    apply (anti_symm (⊢)).
    - rewrite -(right_id True%I bi_sep (P -∗ Q)%I) -(exist_intro (P -∗ Q)%I).
      apply sep_mono_r. rewrite -persistently_pure.
      apply persistently_intro', impl_intro_l.
      by rewrite wand_elim_r persistently_pure right_id.
    - apply exist_elim=> R. apply wand_intro_l.
      rewrite assoc -persistently_and_sep_r.
      by rewrite persistently_elim impl_elim_r.
  Qed.
  Lemma impl_alt P Q : (P → Q) ⊣⊢ ∃ R, R ∧ bi_persistently (P ∧ R -∗ Q).
  Proof.
    apply (anti_symm (⊢)).
    - rewrite -(right_id True%I bi_and (P → Q)%I) -(exist_intro (P → Q)%I).
      apply and_mono_r. rewrite -persistently_pure.
      apply persistently_intro', wand_intro_l.
      by rewrite impl_elim_r persistently_pure right_id.
    - apply exist_elim=> R. apply impl_intro_l.
      by rewrite assoc persistently_and_sep_r persistently_elim wand_elim_r.
  Qed.
End persistently_affinely_bi.

(* Properties of the plainness modality *)
Hint Resolve plainly_mono.
Global Instance plainly_mono' : Proper ((⊢) ==> (⊢)) (@bi_plainly PROP).
Proof. intros P Q; apply plainly_mono. Qed.
Global Instance plainly_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_plainly PROP).
Proof. intros P Q; apply plainly_mono. Qed.

Lemma persistently_plainly P : bi_persistently (bi_plainly P) ⊣⊢ bi_plainly P.
Proof.
  apply (anti_symm _).
  - by rewrite persistently_elim_absorbingly /bi_absorbingly comm plainly_absorbing.
  - by rewrite {1}plainly_idemp_2 plainly_elim_persistently.
Qed.
Lemma plainly_persistently P : bi_plainly (bi_persistently P) ⊣⊢ bi_plainly P.
Proof.
  apply (anti_symm _); first apply plainly_persistently_1.
  by rewrite {1}plainly_idemp_2 (plainly_elim_persistently P).
Qed.

Lemma absorbingly_plainly P : bi_absorbingly (bi_plainly P) ⊣⊢ bi_plainly P.
Proof. by rewrite -(persistently_plainly P) absorbingly_persistently. Qed.

Lemma plainly_and_sep_elim P Q : bi_plainly P ∧ Q -∗ (emp ∧ P) ∗ Q.
Proof. by rewrite plainly_elim_persistently persistently_and_sep_elim. Qed.
Lemma plainly_and_sep_assoc P Q R :
  bi_plainly P ∧ (Q ∗ R) ⊣⊢ (bi_plainly P ∧ Q) ∗ R.
Proof. by rewrite -(persistently_plainly P) persistently_and_sep_assoc. Qed.
Lemma plainly_and_emp_elim P : emp ∧ bi_plainly P ⊢ P.
Proof. by rewrite plainly_elim_persistently persistently_and_emp_elim. Qed.
Lemma plainly_elim_absorbingly P : bi_plainly P ⊢ bi_absorbingly P.
Proof. by rewrite plainly_elim_persistently persistently_elim_absorbingly. Qed.
Lemma plainly_elim P `{!Absorbing P} : bi_plainly P ⊢ P.
Proof. by rewrite plainly_elim_persistently persistently_elim. Qed.

Lemma plainly_idemp_1 P : bi_plainly (bi_plainly P) ⊢ bi_plainly P.
Proof. by rewrite plainly_elim_absorbingly absorbingly_plainly. Qed.
Lemma plainly_idemp P : bi_plainly (bi_plainly P) ⊣⊢ bi_plainly P.
Proof. apply (anti_symm _); auto using plainly_idemp_1, plainly_idemp_2. Qed.

Lemma plainly_intro' P Q : (bi_plainly P ⊢ Q) → bi_plainly P ⊢ bi_plainly Q.
Proof. intros <-. apply plainly_idemp_2. Qed.

Lemma plainly_pure φ : bi_plainly ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof.
  apply (anti_symm _); auto.
  - by rewrite plainly_elim_persistently persistently_pure.
  - apply pure_elim'=> Hφ.
    trans (∀ x : False, bi_plainly True : PROP)%I; [by apply forall_intro|].
    rewrite plainly_forall_2. by rewrite -(pure_intro _ φ).
Qed.
Lemma plainly_forall {A} (Ψ : A → PROP) :
  bi_plainly (∀ a, Ψ a) ⊣⊢ ∀ a, bi_plainly (Ψ a).
Proof.
  apply (anti_symm _); auto using plainly_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma plainly_exist {A} (Ψ : A → PROP) :
  bi_plainly (∃ a, Ψ a) ⊣⊢ ∃ a, bi_plainly (Ψ a).
Proof.
  apply (anti_symm _); auto using plainly_exist_1.
  apply exist_elim=> x. by rewrite (exist_intro x).
Qed.
Lemma plainly_and P Q : bi_plainly (P ∧ Q) ⊣⊢ bi_plainly P ∧ bi_plainly Q.
Proof. rewrite !and_alt plainly_forall. by apply forall_proper=> -[]. Qed.
Lemma plainly_or P Q : bi_plainly (P ∨ Q) ⊣⊢ bi_plainly P ∨ bi_plainly Q.
Proof. rewrite !or_alt plainly_exist. by apply exist_proper=> -[]. Qed.
Lemma plainly_impl P Q : bi_plainly (P → Q) ⊢ bi_plainly P → bi_plainly Q.
Proof.
  apply impl_intro_l; rewrite -plainly_and.
  apply plainly_mono, impl_elim with P; auto.
Qed.

Lemma plainly_sep_dup P : bi_plainly P ⊣⊢ bi_plainly P ∗ bi_plainly P.
Proof.
  apply (anti_symm _).
  - rewrite -{1}(idemp bi_and (bi_plainly _)).
    by rewrite -{2}(left_id emp%I _ (bi_plainly _)) plainly_and_sep_assoc and_elim_l.
  - by rewrite plainly_absorbing.
Qed.

Lemma plainly_and_sep_l_1 P Q : bi_plainly P ∧ Q ⊢ bi_plainly P ∗ Q.
Proof. by rewrite -{1}(left_id emp%I _ Q%I) plainly_and_sep_assoc and_elim_l. Qed.
Lemma plainly_and_sep_r_1 P Q : P ∧ bi_plainly Q ⊢ P ∗ bi_plainly Q.
Proof. by rewrite !(comm _ P) plainly_and_sep_l_1. Qed.

Lemma plainly_internal_eq {A:ofeT} (a b : A) : bi_plainly (a ≡ b) ⊣⊢ a ≡ b.
Proof.
  apply (anti_symm (⊢)).
  { by rewrite plainly_elim_absorbingly absorbingly_internal_eq. }
  apply (internal_eq_rewrite' a b (λ  b, bi_plainly (a ≡ b))%I); [solve_proper|done|].
  rewrite -(internal_eq_refl True%I a) plainly_pure; auto.
Qed.

Lemma plainly_True_emp : bi_plainly True ⊣⊢ bi_plainly emp.
Proof. apply (anti_symm _); auto using plainly_emp_intro. Qed.
Lemma plainly_and_sep P Q : bi_plainly (P ∧ Q) ⊢ bi_plainly (P ∗ Q).
Proof.
  rewrite plainly_and.
  rewrite -{1}plainly_idemp -plainly_and -{1}(left_id emp%I _ Q%I).
  by rewrite plainly_and_sep_assoc (comm bi_and) plainly_and_emp_elim.
Qed.

Lemma plainly_affinely P : bi_plainly (bi_affinely P) ⊣⊢ bi_plainly P.
Proof. by rewrite /bi_affinely plainly_and -plainly_True_emp plainly_pure left_id. Qed.

Lemma and_sep_plainly P Q :
  bi_plainly P ∧ bi_plainly Q ⊣⊢ bi_plainly P ∗ bi_plainly Q.
Proof.
  apply (anti_symm _); auto using plainly_and_sep_l_1.
  apply and_intro.
  - by rewrite plainly_absorbing.
  - by rewrite comm plainly_absorbing.
Qed.
Lemma plainly_sep_2 P Q :
  bi_plainly P ∗ bi_plainly Q ⊢ bi_plainly (P ∗ Q).
Proof. by rewrite -plainly_and_sep plainly_and -and_sep_plainly. Qed.
Lemma plainly_sep `{PositiveBI PROP} P Q :
  bi_plainly (P ∗ Q) ⊣⊢ bi_plainly P ∗ bi_plainly Q.
Proof.
  apply (anti_symm _); auto using plainly_sep_2.
  rewrite -plainly_affinely affinely_sep -and_sep_plainly. apply and_intro.
  - by rewrite (affinely_elim_emp Q) right_id affinely_elim.
  - by rewrite (affinely_elim_emp P) left_id affinely_elim.
Qed.

Lemma plainly_wand P Q : bi_plainly (P -∗ Q) ⊢ bi_plainly P -∗ bi_plainly Q.
Proof. apply wand_intro_r. by rewrite plainly_sep_2 wand_elim_l. Qed.

Lemma plainly_entails_l P Q : (P ⊢ bi_plainly Q) → P ⊢ bi_plainly Q ∗ P.
Proof. intros; rewrite -plainly_and_sep_l_1; auto. Qed.
Lemma plainly_entails_r P Q : (P ⊢ bi_plainly Q) → P ⊢ P ∗ bi_plainly Q.
Proof. intros; rewrite -plainly_and_sep_r_1; auto. Qed.

Lemma plainly_impl_wand_2 P Q : bi_plainly (P -∗ Q) ⊢ bi_plainly (P → Q).
Proof.
  apply plainly_intro', impl_intro_r.
  rewrite -{2}(left_id emp%I _ P%I) plainly_and_sep_assoc.
  by rewrite (comm bi_and) plainly_and_emp_elim wand_elim_l.
Qed.

Section plainly_affinely_bi.
  Context `{AffineBI PROP}.

  Lemma plainly_emp : bi_plainly emp ⊣⊢ emp.
  Proof. by rewrite -!True_emp plainly_pure. Qed.

  Lemma plainly_and_sep_l P Q : bi_plainly P ∧ Q ⊣⊢ bi_plainly P ∗ Q.
  Proof.
    apply (anti_symm (⊢));
      eauto using plainly_and_sep_l_1, sep_and with typeclass_instances.
  Qed.
  Lemma plainly_and_sep_r P Q : P ∧ bi_plainly Q ⊣⊢ P ∗ bi_plainly Q.
  Proof. by rewrite !(comm _ P) plainly_and_sep_l. Qed.

  Lemma plainly_impl_wand P Q : bi_plainly (P → Q) ⊣⊢ bi_plainly (P -∗ Q).
  Proof.
    apply (anti_symm (⊢)); auto using plainly_impl_wand_2.
    apply plainly_intro', wand_intro_l.
    by rewrite -plainly_and_sep_r plainly_elim impl_elim_r.
  Qed.

  Lemma wand_impl_persistently P Q : (bi_persistently P -∗ Q) ⊣⊢ (bi_persistently P → Q).
  Proof.
    apply (anti_symm (⊢)); [|by rewrite -impl_wand_1].
    apply impl_intro_l. by rewrite persistently_and_sep_l wand_elim_r.
  Qed.

  Lemma wand_impl_plainly P Q : (bi_plainly P -∗ Q) ⊣⊢ (bi_plainly P → Q).
  Proof.
    apply (anti_symm (⊢)); [|by rewrite -impl_wand_1].
    apply impl_intro_l. by rewrite plainly_and_sep_l wand_elim_r.
  Qed.
End plainly_affinely_bi.

(* The combined affinely persistently modality *)
Lemma affinely_persistently_elim P : □ P ⊢ P.
Proof. apply persistently_and_emp_elim. Qed.
Lemma affinely_persistently_intro' P Q : (□ P ⊢ Q) → □ P ⊢ □ Q.
Proof. intros <-. by rewrite persistently_affinely persistently_idemp. Qed.

Lemma affinely_persistently_emp : □ emp ⊣⊢ emp.
Proof.
  by rewrite -persistently_True_emp persistently_pure affinely_True_emp
             affinely_emp.
Qed.
Lemma affinely_persistently_and P Q : □ (P ∧ Q) ⊣⊢ □ P ∧ □ Q.
Proof. by rewrite persistently_and affinely_and. Qed.
Lemma affinely_persistently_or P Q : □ (P ∨ Q) ⊣⊢ □ P ∨ □ Q.
Proof. by rewrite persistently_or affinely_or. Qed.
Lemma affinely_persistently_exist {A} (Φ : A → PROP) : □ (∃ x, Φ x) ⊣⊢ ∃ x, □ Φ x.
Proof. by rewrite persistently_exist affinely_exist. Qed.
Lemma affinely_persistently_sep_2 P Q : □ P ∗ □ Q ⊢ □ (P ∗ Q).
Proof. by rewrite affinely_sep_2 persistently_sep_2. Qed.
Lemma affinely_persistently_sep `{PositiveBI PROP} P Q : □ (P ∗ Q) ⊣⊢ □ P ∗ □ Q.
Proof. by rewrite -affinely_sep -persistently_sep. Qed.

Lemma affinely_persistently_idemp P : □ □ P ⊣⊢ □ P.
Proof. by rewrite persistently_affinely persistently_idemp. Qed.

Lemma persistently_and_affinely_sep_l P Q : bi_persistently P ∧ Q ⊣⊢ □ P ∗ Q.
Proof.
  apply (anti_symm _).
  - by rewrite /bi_affinely -(comm bi_and (bi_persistently P))
      -persistently_and_sep_assoc left_id.
  - apply and_intro.
    + by rewrite affinely_elim persistently_absorbing.
    + by rewrite affinely_elim_emp left_id.
Qed.
Lemma persistently_and_affinely_sep_r P Q : P ∧ bi_persistently Q ⊣⊢ P ∗ □ Q.
Proof. by rewrite !(comm _ P) persistently_and_affinely_sep_l. Qed.
Lemma and_sep_affinely_persistently P Q : □ P ∧ □ Q ⊣⊢ □ P ∗ □ Q.
Proof.
  by rewrite -persistently_and_affinely_sep_l -affinely_and affinely_and_r.
Qed.

Lemma affinely_persistently_sep_dup P : □ P ⊣⊢ □ P ∗ □ P.
Proof.
  by rewrite -persistently_and_affinely_sep_l affinely_and_r affinely_and idemp.
Qed.

(* The combined affinely plainly modality *)
Lemma affinely_plainly_elim P : ■ P ⊢ P.
Proof. apply plainly_and_emp_elim. Qed.
Lemma affinely_plainly_intro' P Q : (■ P ⊢ Q) → ■ P ⊢ ■ Q.
Proof. intros <-. by rewrite plainly_affinely plainly_idemp. Qed.

Lemma affinely_plainly_emp : ■ emp ⊣⊢ emp.
Proof.
  by rewrite -plainly_True_emp plainly_pure affinely_True_emp affinely_emp.
Qed.
Lemma affinely_plainly_and P Q : ■ (P ∧ Q) ⊣⊢ ■ P ∧ ■ Q.
Proof. by rewrite plainly_and affinely_and. Qed.
Lemma affinely_plainly_or P Q : ■ (P ∨ Q) ⊣⊢ ■ P ∨ ■ Q.
Proof. by rewrite plainly_or affinely_or. Qed.
Lemma affinely_plainly_exist {A} (Φ : A → PROP) : ■ (∃ x, Φ x) ⊣⊢ ∃ x, ■ Φ x.
Proof. by rewrite plainly_exist affinely_exist. Qed.
Lemma affinely_plainly_sep_2 P Q : ■ P ∗ ■ Q ⊢ ■ (P ∗ Q).
Proof. by rewrite affinely_sep_2 plainly_sep_2. Qed.
Lemma affinely_plainly_sep `{PositiveBI PROP} P Q : ■ (P ∗ Q) ⊣⊢ ■ P ∗ ■ Q.
Proof. by rewrite -affinely_sep -plainly_sep. Qed.

Lemma affinely_plainly_idemp P : ■ ■ P ⊣⊢ ■ P.
Proof. by rewrite plainly_affinely plainly_idemp. Qed.

Lemma plainly_and_affinely_sep_l P Q : bi_plainly P ∧ Q ⊣⊢ ■ P ∗ Q.
Proof. by rewrite -(persistently_plainly P) persistently_and_affinely_sep_l. Qed.
Lemma plainly_and_affinely_sep_r P Q : P ∧ bi_plainly Q ⊣⊢ P ∗ ■ Q.
Proof. by rewrite !(comm _ P) plainly_and_affinely_sep_l. Qed.
Lemma and_sep_affinely_plainly P Q : ■ P ∧ ■ Q ⊣⊢ ■ P ∗ ■ Q.
Proof.
  by rewrite -plainly_and_affinely_sep_l -affinely_and affinely_and_r.
Qed.

Lemma affinely_plainly_sep_dup P : ■ P ⊣⊢ ■ P ∗ ■ P.
Proof.
  by rewrite -plainly_and_affinely_sep_l affinely_and_r affinely_and idemp.
Qed.

(* Conditional affinely modality *)
Global Instance affinely_if_ne p : NonExpansive (@bi_affinely_if PROP p).
Proof. solve_proper. Qed.
Global Instance affinely_if_proper p : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_affinely_if PROP p).
Proof. solve_proper. Qed.
Global Instance affinely_if_mono' p : Proper ((⊢) ==> (⊢)) (@bi_affinely_if PROP p).
Proof. solve_proper. Qed.
Global Instance affinely_if_flip_mono' p :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_affinely_if PROP p).
Proof. solve_proper. Qed.

Lemma affinely_if_mono p P Q : (P ⊢ Q) → bi_affinely_if p P ⊢ bi_affinely_if p Q.
Proof. by intros ->. Qed.

Lemma affinely_if_elim p P : bi_affinely_if p P ⊢ P.
Proof. destruct p; simpl; auto using affinely_elim. Qed.
Lemma affinely_affinely_if p P : bi_affinely P ⊢ bi_affinely_if p P.
Proof. destruct p; simpl; auto using affinely_elim. Qed.
Lemma affinely_if_intro' p P Q :
  (bi_affinely_if p P ⊢ Q) → bi_affinely_if p P ⊢ bi_affinely_if p Q.
Proof. destruct p; simpl; auto using affinely_intro'. Qed.

Lemma affinely_if_emp p : bi_affinely_if p emp ⊣⊢ emp.
Proof. destruct p; simpl; auto using affinely_emp. Qed.
Lemma affinely_if_and p P Q :
  bi_affinely_if p (P ∧ Q) ⊣⊢ bi_affinely_if p P ∧ bi_affinely_if p Q.
Proof. destruct p; simpl; auto using affinely_and. Qed.
Lemma affinely_if_or p P Q :
  bi_affinely_if p (P ∨ Q) ⊣⊢ bi_affinely_if p P ∨ bi_affinely_if p Q.
Proof. destruct p; simpl; auto using affinely_or. Qed.
Lemma affinely_if_exist {A} p (Ψ : A → PROP) :
  bi_affinely_if p (∃ a, Ψ a) ⊣⊢ ∃ a, bi_affinely_if p (Ψ a).
Proof. destruct p; simpl; auto using affinely_exist. Qed.
Lemma affinely_if_sep_2 p P Q :
  bi_affinely_if p P ∗ bi_affinely_if p Q ⊢ bi_affinely_if p (P ∗ Q).
Proof. destruct p; simpl; auto using affinely_sep_2. Qed.
Lemma affinely_if_sep `{PositiveBI PROP} p P Q :
  bi_affinely_if p (P ∗ Q) ⊣⊢ bi_affinely_if p P ∗ bi_affinely_if p Q.
Proof. destruct p; simpl; auto using affinely_sep. Qed.

Lemma affinely_if_idemp p P :
  bi_affinely_if p (bi_affinely_if p P) ⊣⊢ bi_affinely_if p P.
Proof. destruct p; simpl; auto using affinely_idemp. Qed.

(* Conditional persistently *)
Global Instance persistently_if_ne p : NonExpansive (@bi_persistently_if PROP p).
Proof. solve_proper. Qed.
Global Instance persistently_if_proper p :
  Proper ((⊣⊢) ==> (⊣⊢)) (@bi_persistently_if PROP p).
Proof. solve_proper. Qed.
Global Instance persistently_if_mono' p :
  Proper ((⊢) ==> (⊢)) (@bi_persistently_if PROP p).
Proof. solve_proper. Qed.
Global Instance persistently_if_flip_mono' p :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_persistently_if PROP p).
Proof. solve_proper. Qed.

Lemma persistently_if_mono p P Q :
  (P ⊢ Q) → bi_persistently_if p P ⊢ bi_persistently_if p Q.
Proof. by intros ->. Qed.

Lemma persistently_if_pure p φ : bi_persistently_if p ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof. destruct p; simpl; auto using persistently_pure. Qed.
Lemma persistently_if_and p P Q :
  bi_persistently_if p (P ∧ Q) ⊣⊢ bi_persistently_if p P ∧ bi_persistently_if p Q.
Proof. destruct p; simpl; auto using persistently_and. Qed.
Lemma persistently_if_or p P Q :
  bi_persistently_if p (P ∨ Q) ⊣⊢ bi_persistently_if p P ∨ bi_persistently_if p Q.
Proof. destruct p; simpl; auto using persistently_or. Qed.
Lemma persistently_if_exist {A} p (Ψ : A → PROP) :
  (bi_persistently_if p (∃ a, Ψ a)) ⊣⊢ ∃ a, bi_persistently_if p (Ψ a).
Proof. destruct p; simpl; auto using persistently_exist. Qed.
Lemma persistently_if_sep_2 p P Q :
  bi_persistently_if p P ∗ bi_persistently_if p Q ⊢ bi_persistently_if p (P ∗ Q).
Proof. destruct p; simpl; auto using persistently_sep_2. Qed.
Lemma persistently_if_sep `{PositiveBI PROP} p P Q :
  bi_persistently_if p (P ∗ Q) ⊣⊢ bi_persistently_if p P ∗ bi_persistently_if p Q.
Proof. destruct p; simpl; auto using persistently_sep. Qed.

Lemma persistently_if_idemp p P :
  bi_persistently_if p (bi_persistently_if p P) ⊣⊢ bi_persistently_if p P.
Proof. destruct p; simpl; auto using persistently_idemp. Qed.

(* Conditional affinely persistently *)
Lemma affinely_persistently_if_mono p P Q : (P ⊢ Q) → □?p P ⊢ □?p Q.
Proof. by intros ->. Qed.

Lemma affinely_persistently_if_elim p P : □?p P ⊢ P.
Proof. destruct p; simpl; auto using affinely_persistently_elim. Qed.
Lemma affinely_persistently_affinely_persistently_if p P : □ P ⊢ □?p P.
Proof. destruct p; simpl; auto using affinely_persistently_elim. Qed.
Lemma affinely_persistently_if_intro' p P Q : (□?p P ⊢ Q) → □?p P ⊢ □?p Q.
Proof. destruct p; simpl; auto using affinely_persistently_intro'. Qed.

Lemma affinely_persistently_if_emp p : □?p emp ⊣⊢ emp.
Proof. destruct p; simpl; auto using affinely_persistently_emp. Qed.
Lemma affinely_persistently_if_and p P Q : □?p (P ∧ Q) ⊣⊢ □?p P ∧ □?p Q.
Proof. destruct p; simpl; auto using affinely_persistently_and. Qed.
Lemma affinely_persistently_if_or p P Q : □?p (P ∨ Q) ⊣⊢ □?p P ∨ □?p Q.
Proof. destruct p; simpl; auto using affinely_persistently_or. Qed.
Lemma affinely_persistently_if_exist {A} p (Ψ : A → PROP) :
  (□?p ∃ a, Ψ a) ⊣⊢ ∃ a, □?p Ψ a.
Proof. destruct p; simpl; auto using affinely_persistently_exist. Qed.
Lemma affinely_persistently_if_sep_2 p P Q : □?p P ∗ □?p Q ⊢ □?p (P ∗ Q).
Proof. destruct p; simpl; auto using affinely_persistently_sep_2. Qed.
Lemma affinely_persistently_if_sep `{PositiveBI PROP} p P Q :
  □?p (P ∗ Q) ⊣⊢ □?p P ∗ □?p Q.
Proof. destruct p; simpl; auto using affinely_persistently_sep. Qed.

Lemma affinely_persistently_if_idemp p P : □?p □?p P ⊣⊢ □?p P.
Proof. destruct p; simpl; auto using affinely_persistently_idemp. Qed.

(* Conditional plainly *)
Global Instance plainly_if_ne p : NonExpansive (@bi_plainly_if PROP p).
Proof. solve_proper. Qed.
Global Instance plainly_if_proper p :
  Proper ((⊣⊢) ==> (⊣⊢)) (@bi_plainly_if PROP p).
Proof. solve_proper. Qed.
Global Instance plainly_if_mono' p :
  Proper ((⊢) ==> (⊢)) (@bi_plainly_if PROP p).
Proof. solve_proper. Qed.
Global Instance plainly_if_flip_mono' p :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_plainly_if PROP p).
Proof. solve_proper. Qed.

Lemma plainly_if_mono p P Q : (P ⊢ Q) → bi_plainly_if p P ⊢ bi_plainly_if p Q.
Proof. by intros ->. Qed.

Lemma plainly_if_pure p φ : bi_plainly_if p ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof. destruct p; simpl; auto using plainly_pure. Qed.
Lemma plainly_if_and p P Q : bi_plainly_if p (P ∧ Q) ⊣⊢ bi_plainly_if p P ∧ bi_plainly_if p Q.
Proof. destruct p; simpl; auto using plainly_and. Qed.
Lemma plainly_if_or p P Q : bi_plainly_if p (P ∨ Q) ⊣⊢ bi_plainly_if p P ∨ bi_plainly_if p Q.
Proof. destruct p; simpl; auto using plainly_or. Qed.
Lemma plainly_if_exist {A} p (Ψ : A → PROP) : (bi_plainly_if p (∃ a, Ψ a)) ⊣⊢ ∃ a, bi_plainly_if p (Ψ a).
Proof. destruct p; simpl; auto using plainly_exist. Qed.
Lemma plainly_if_sep `{PositiveBI PROP} p P Q :
  bi_plainly_if p (P ∗ Q) ⊣⊢ bi_plainly_if p P ∗ bi_plainly_if p Q.
Proof. destruct p; simpl; auto using plainly_sep. Qed.

Lemma plainly_if_idemp p P :
  bi_plainly_if p (bi_plainly_if p P) ⊣⊢ bi_plainly_if p P.
Proof. destruct p; simpl; auto using plainly_idemp. Qed.

(* Conditional affinely plainly *)
Lemma affinely_plainly_if_mono p P Q : (P ⊢ Q) → ■?p P ⊢ ■?p Q.
Proof. by intros ->. Qed.

Lemma affinely_plainly_if_elim p P : ■?p P ⊢ P.
Proof. destruct p; simpl; auto using affinely_plainly_elim. Qed.
Lemma affinely_plainly_affinely_plainly_if p P : ■ P ⊢ ■?p P.
Proof. destruct p; simpl; auto using affinely_plainly_elim. Qed.
Lemma affinely_plainly_if_intro' p P Q : (■?p P ⊢ Q) → ■?p P ⊢ ■?p Q.
Proof. destruct p; simpl; auto using affinely_plainly_intro'. Qed.

Lemma affinely_plainly_if_emp p : ■?p emp ⊣⊢ emp.
Proof. destruct p; simpl; auto using affinely_plainly_emp. Qed.
Lemma affinely_plainly_if_and p P Q : ■?p (P ∧ Q) ⊣⊢ ■?p P ∧ ■?p Q.
Proof. destruct p; simpl; auto using affinely_plainly_and. Qed.
Lemma affinely_plainly_if_or p P Q : ■?p (P ∨ Q) ⊣⊢ ■?p P ∨ ■?p Q.
Proof. destruct p; simpl; auto using affinely_plainly_or. Qed.
Lemma affinely_plainly_if_exist {A} p (Ψ : A → PROP) :
  (■?p ∃ a, Ψ a) ⊣⊢ ∃ a, ■?p Ψ a.
Proof. destruct p; simpl; auto using affinely_plainly_exist. Qed.
Lemma affinely_plainly_if_sep_2 p P Q : ■?p P ∗ ■?p Q ⊢ ■?p (P ∗ Q).
Proof. destruct p; simpl; auto using affinely_plainly_sep_2. Qed.
Lemma affinely_plainly_if_sep `{PositiveBI PROP} p P Q :
  ■?p (P ∗ Q) ⊣⊢ ■?p P ∗ ■?p Q.
Proof. destruct p; simpl; auto using affinely_plainly_sep. Qed.

Lemma affinely_plainly_if_idemp p P : ■?p ■?p P ⊣⊢ ■?p P.
Proof. destruct p; simpl; auto using affinely_plainly_idemp. Qed.

(* Properties of persistent propositions *)
Global Instance Persistent_proper : Proper ((≡) ==> iff) (@Persistent PROP).
Proof. solve_proper. Qed.

Lemma persistent_persistently_2 P `{!Persistent P} : P ⊢ bi_persistently P.
Proof. done. Qed.
Lemma persistent_persistently P `{!Persistent P, !Absorbing P} :
  bi_persistently P ⊣⊢ P.
Proof.
  apply (anti_symm _); auto using persistent_persistently_2, persistently_elim.
Qed.

Lemma persistently_intro P Q `{!Persistent P} : (P ⊢ Q) → P ⊢ bi_persistently Q.
Proof. intros HP. by rewrite (persistent P) HP. Qed.
Lemma persistent_and_affinely_sep_l_1 P Q `{!Persistent P} :
  P ∧ Q ⊢ bi_affinely P ∗ Q.
Proof.
  rewrite {1}(persistent_persistently_2 P) persistently_and_affinely_sep_l.
  by rewrite -affinely_idemp affinely_persistently_elim.
Qed.
Lemma persistent_and_affinely_sep_r_1 P Q `{!Persistent Q} :
  P ∧ Q ⊢ P ∗ bi_affinely Q.
Proof. by rewrite !(comm _ P) persistent_and_affinely_sep_l_1. Qed.

Lemma persistent_and_affinely_sep_l P Q `{!Persistent P, !Absorbing P} :
  P ∧ Q ⊣⊢ bi_affinely P ∗ Q.
Proof. by rewrite -(persistent_persistently P) persistently_and_affinely_sep_l. Qed.
Lemma persistent_and_affinely_sep_r P Q `{!Persistent Q, !Absorbing Q} :
  P ∧ Q ⊣⊢ P ∗ bi_affinely Q.
Proof. by rewrite -(persistent_persistently Q) persistently_and_affinely_sep_r. Qed.

Lemma persistent_and_sep_1 P Q `{HPQ : !TCOr (Persistent P) (Persistent Q)} :
  P ∧ Q ⊢ P ∗ Q.
Proof.
  destruct HPQ.
  - by rewrite persistent_and_affinely_sep_l_1 affinely_elim.
  - by rewrite persistent_and_affinely_sep_r_1 affinely_elim.
Qed.

Lemma persistent_sep_dup P `{!Persistent P, !Absorbing P} : P ⊣⊢ P ∗ P.
Proof. by rewrite -(persistent_persistently P) -persistently_sep_dup. Qed.

Lemma persistent_entails_l P Q `{!Persistent Q} : (P ⊢ Q) → P ⊢ Q ∗ P.
Proof. intros. rewrite -persistent_and_sep_1; auto. Qed.
Lemma persistent_entails_r P Q `{!Persistent Q} : (P ⊢ Q) → P ⊢ P ∗ Q.
Proof. intros. rewrite -persistent_and_sep_1; auto. Qed.

Lemma persistent_absorbingly_affinely P `{!Persistent P} :
  P ⊢ bi_absorbingly (bi_affinely P).
Proof.
  by rewrite {1}(persistent_persistently_2 P) -persistently_affinely
             persistently_elim_absorbingly.
Qed.

Lemma persistent_and_sep_assoc P `{!Persistent P, !Absorbing P} Q R :
  P ∧ (Q ∗ R) ⊣⊢ (P ∧ Q) ∗ R.
Proof. by rewrite -(persistent_persistently P) persistently_and_sep_assoc. Qed.

Lemma impl_wand_2 P `{!Persistent P} Q : (P -∗ Q) ⊢ P → Q.
Proof. apply impl_intro_l. by rewrite persistent_and_sep_1 wand_elim_r. Qed.

Section persistent_bi_absorbing.
  Context `{AffineBI PROP}.

  Lemma persistent_and_sep P Q `{HPQ : !TCOr (Persistent P) (Persistent Q)} :
    P ∧ Q ⊣⊢ P ∗ Q.
  Proof.
    destruct HPQ.
    - by rewrite -(persistent_persistently P) persistently_and_sep_l.
    - by rewrite -(persistent_persistently Q) persistently_and_sep_r.
  Qed.

  Lemma impl_wand P `{!Persistent P} Q : (P → Q) ⊣⊢ (P -∗ Q).
  Proof. apply (anti_symm _); auto using impl_wand_1, impl_wand_2. Qed.
End persistent_bi_absorbing.

(* Properties of plain propositions *)
Global Instance Plain_proper : Proper ((≡) ==> iff) (@Plain PROP).
Proof. solve_proper. Qed.

Lemma plain_plainly_2 P `{!Plain P} : P ⊢ bi_plainly P.
Proof. done. Qed.
Lemma plain_plainly P `{!Plain P, !Absorbing P} : bi_plainly P ⊣⊢ P.
Proof. apply (anti_symm _), plain_plainly_2, _. apply plainly_elim, _. Qed.
Lemma plainly_intro P Q `{!Plain P} : (P ⊢ Q) → P ⊢ bi_plainly Q.
Proof. by intros <-. Qed.
Lemma plainly_alt P : bi_plainly P ⊣⊢ P ≡ True.
Proof.
  apply (anti_symm (⊢)).
  - rewrite -prop_ext. apply plainly_mono, and_intro; apply impl_intro_r; auto.
  - rewrite internal_eq_sym (internal_eq_rewrite _ _ bi_plainly).
    by rewrite plainly_pure True_impl.
Qed.

(* Affine instances *)
Global Instance emp_affine_l : Affine (emp%I : PROP).
Proof. by rewrite /Affine. Qed.
Global Instance and_affine_l P Q : Affine P → Affine (P ∧ Q).
Proof. rewrite /Affine=> ->; auto. Qed.
Global Instance and_affine_r P Q : Affine Q → Affine (P ∧ Q).
Proof. rewrite /Affine=> ->; auto. Qed.
Global Instance or_affine P Q : Affine P → Affine Q → Affine (P ∨ Q).
Proof.  rewrite /Affine=> -> ->; auto. Qed.
Global Instance forall_affine `{Inhabited A} (Φ : A → PROP) :
  (∀ x, Affine (Φ x)) → Affine (∀ x, Φ x).
Proof. intros. rewrite /Affine (forall_elim inhabitant). apply: affine. Qed.
Global Instance exist_affine {A} (Φ : A → PROP) :
  (∀ x, Affine (Φ x)) → Affine (∃ x, Φ x).
Proof. rewrite /Affine=> H. apply exist_elim=> a. by rewrite H. Qed.

Global Instance sep_affine P Q : Affine P → Affine Q → Affine (P ∗ Q).
Proof. rewrite /Affine=>-> ->. by rewrite left_id. Qed.
Global Instance affinely_affine P : Affine (bi_affinely P).
Proof. rewrite /bi_affinely. apply _. Qed.

(* Absorbing instances *)
Global Instance pure_absorbing φ : Absorbing (⌜φ⌝%I : PROP).
Proof. by rewrite /Absorbing absorbingly_pure. Qed.
Global Instance and_absorbing P Q : Absorbing P → Absorbing Q → Absorbing (P ∧ Q).
Proof. intros. by rewrite /Absorbing absorbingly_and !absorbing. Qed.
Global Instance or_absorbing P Q : Absorbing P → Absorbing Q → Absorbing (P ∨ Q).
Proof. intros. by rewrite /Absorbing absorbingly_or !absorbing. Qed.
Global Instance forall_absorbing {A} (Φ : A → PROP) :
  (∀ x, Absorbing (Φ x)) → Absorbing (∀ x, Φ x).
Proof. rewrite /Absorbing=> ?. rewrite absorbingly_forall. auto using forall_mono. Qed.
Global Instance exist_absorbing {A} (Φ : A → PROP) :
  (∀ x, Absorbing (Φ x)) → Absorbing (∃ x, Φ x).
Proof. rewrite /Absorbing=> ?. rewrite absorbingly_exist. auto using exist_mono. Qed.

Global Instance internal_eq_absorbing {A : ofeT} (x y : A) :
  Absorbing (x ≡ y : PROP)%I.
Proof. by rewrite /Absorbing absorbingly_internal_eq. Qed.

Global Instance sep_absorbing_l P Q : Absorbing P → Absorbing (P ∗ Q).
Proof. intros. by rewrite /Absorbing -absorbingly_sep_l absorbing. Qed.
Global Instance sep_absorbing_r P Q : Absorbing Q → Absorbing (P ∗ Q).
Proof. intros. by rewrite /Absorbing -absorbingly_sep_r absorbing. Qed.

Global Instance wand_absorbing P Q : Absorbing Q → Absorbing (P -∗ Q).
Proof. intros. by rewrite /Absorbing absorbingly_wand !absorbing -absorbingly_intro. Qed.

Global Instance absorbingly_absorbing P : Absorbing (bi_absorbingly P).
Proof. rewrite /bi_absorbingly. apply _. Qed.
Global Instance plainly_absorbing P : Absorbing (bi_plainly P).
Proof. by rewrite /Absorbing /bi_absorbingly comm plainly_absorbing. Qed.
Global Instance persistently_absorbing P : Absorbing (bi_persistently P).
Proof. by rewrite /Absorbing absorbingly_persistently. Qed.

(* Persistence instances *)
(* Not an instance, see the bottom of this file *)
Lemma plain_persistent P : Plain P → Persistent P.
Proof. intros. by rewrite /Persistent -plainly_elim_persistently. Qed.

Global Instance pure_persistent φ : Persistent (⌜φ⌝%I : PROP).
Proof. by rewrite /Persistent persistently_pure. Qed.
Global Instance emp_persistent : Persistent (emp%I : PROP).
Proof. rewrite /Persistent. apply persistently_emp_intro. Qed.
Global Instance and_persistent P Q :
  Persistent P → Persistent Q → Persistent (P ∧ Q).
Proof. intros. by rewrite /Persistent persistently_and -!persistent. Qed.
Global Instance or_persistent P Q :
  Persistent P → Persistent Q → Persistent (P ∨ Q).
Proof. intros. by rewrite /Persistent persistently_or -!persistent. Qed.
Global Instance forall_persistent {A} (Ψ : A → PROP) :
  (∀ x, Persistent (Ψ x)) → Persistent (∀ x, Ψ x).
Proof.
  intros. rewrite /Persistent persistently_forall.
  apply forall_mono=> x. by rewrite -!persistent.
Qed.
Global Instance exist_persistent {A} (Ψ : A → PROP) :
  (∀ x, Persistent (Ψ x)) → Persistent (∃ x, Ψ x).
Proof.
  intros. rewrite /Persistent persistently_exist.
  apply exist_mono=> x. by rewrite -!persistent.
Qed.

Global Instance internal_eq_persistent {A : ofeT} (a b : A) :
  Persistent (a ≡ b : PROP)%I.
Proof. by intros; rewrite /Persistent persistently_internal_eq. Qed.

Global Instance impl_persistent P Q :
  Absorbing P → Plain P → Persistent Q → Persistent (P → Q).
Proof.
  intros. by rewrite /Persistent {2}(plain P) -persistently_impl_plainly
                     -(persistent Q) (plainly_elim_absorbingly P) absorbing.
Qed.
(* TODO : can we prove this lemma under positivity of the BI (or even
   weaker assumptions) ? *)
Global Instance wand_persistent `{AffineBI PROP} P Q :
  Plain P → Persistent Q → Persistent (P -∗ Q).
Proof.
 intros. by rewrite /Persistent {2}(plain P) wand_impl_plainly
   -persistently_impl_plainly -wand_impl_plainly -(persistent Q) (plainly_elim P).
Qed.
Global Instance pure_wand_persistent φ Q :
  Persistent Q → Absorbing Q → Persistent (⌜φ⌝ -∗ Q).
Proof. intros. rewrite pure_wand_forall. apply _. Qed.

Global Instance sep_persistent P Q :
  Persistent P → Persistent Q → Persistent (P ∗ Q).
Proof. intros. by rewrite /Persistent -persistently_sep_2 -!persistent. Qed.

Global Instance plainly_persistent P : Persistent (bi_plainly P).
Proof. by rewrite /Persistent persistently_plainly. Qed.
Global Instance persistently_persistent P : Persistent (bi_persistently P).
Proof. by rewrite /Persistent persistently_idemp. Qed.
Global Instance affinely_persistent P : Persistent P → Persistent (bi_affinely P).
Proof. rewrite /bi_affinely. apply _. Qed.
Global Instance absorbingly_persistent P : Persistent P → Persistent (bi_absorbingly P).
Proof. rewrite /bi_absorbingly. apply _. Qed.
Global Instance from_option_persistent {A} P (Ψ : A → PROP) (mx : option A) :
  (∀ x, Persistent (Ψ x)) → Persistent P → Persistent (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* Plainness instances *)
Global Instance pure_plain φ : Plain (⌜φ⌝%I : PROP).
Proof. by rewrite /Plain plainly_pure. Qed.
Global Instance emp_plain : Plain (emp%I : PROP).
Proof. apply plainly_emp_intro. Qed.
Global Instance and_plain P Q : Plain P → Plain Q → Plain (P ∧ Q).
Proof. intros. by rewrite /Plain plainly_and -!plain. Qed.
Global Instance or_plain P Q : Plain P → Plain Q → Plain (P ∨ Q).
Proof. intros. by rewrite /Plain plainly_or -!plain. Qed.
Global Instance forall_plain {A} (Ψ : A → PROP) :
  (∀ x, Plain (Ψ x)) → Plain (∀ x, Ψ x).
Proof.
  intros. rewrite /Plain plainly_forall. apply forall_mono=> x. by rewrite -plain.
Qed.
Global Instance exist_plain {A} (Ψ : A → PROP) :
  (∀ x, Plain (Ψ x)) → Plain (∃ x, Ψ x).
Proof.
  intros. rewrite /Plain plainly_exist. apply exist_mono=> x. by rewrite -plain.
Qed.

Global Instance internal_eq_plain {A : ofeT} (a b : A) :
  Plain (a ≡ b : PROP)%I.
Proof. by intros; rewrite /Plain plainly_internal_eq. Qed.

Global Instance impl_plain P Q :
  Absorbing P → Plain P → Plain Q → Plain (P → Q).
Proof.
  intros. by rewrite /Plain {2}(plain P) -plainly_impl_plainly -(plain Q)
                     (plainly_elim_absorbingly P) absorbing.
Qed.
(* TODO : can we prove this lemma under positivity of the BI (or even
   weaker assumptions) ? *)
Global Instance wand_plain `{AffineBI PROP} P Q :
  Plain P → Plain Q → Plain (P -∗ Q).
Proof.
  intros. rewrite /Plain {2}(plain P) wand_impl_plainly -plainly_impl_plainly.
  by rewrite -wand_impl_plainly -(plain Q) (plainly_elim P).
Qed.
Global Instance pure_wand_plain φ Q `{!Absorbing Q} : Plain Q → Plain (⌜φ⌝ -∗ Q).
Proof. intros ?. rewrite pure_wand_forall. apply _. Qed.
Global Instance sep_plain P Q : Plain P → Plain Q → Plain (P ∗ Q).
Proof. intros. by rewrite /Plain -plainly_sep_2 -!plain. Qed.

Global Instance plainly_plain P : Plain (bi_plainly P).
Proof. by rewrite /Plain plainly_idemp. Qed.
Global Instance persistently_plain P : Plain P → Plain (bi_persistently P).
Proof.
  rewrite /Plain=> HP. by rewrite {1}HP plainly_persistently persistently_plainly.
Qed.
Global Instance affinely_plain P : Plain P → Plain (bi_affinely P).
Proof. rewrite /bi_affinely. apply _. Qed.
Global Instance absorbingly_plain P : Plain P → Plain (bi_absorbingly P).
Proof. rewrite /bi_absorbingly. apply _. Qed.
Global Instance from_option_palin {A} P (Ψ : A → PROP) (mx : option A) :
  (∀ x, Plain (Ψ x)) → Plain P → Plain (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* For big ops *)
Global Instance bi_and_monoid : Monoid (@bi_and PROP) :=
  {| monoid_unit := True%I |}.
Global Instance bi_or_monoid : Monoid (@bi_or PROP) :=
  {| monoid_unit := False%I |}.
Global Instance bi_sep_monoid : Monoid (@bi_sep PROP) :=
  {| monoid_unit := emp%I |}.

Global Instance bi_plainly_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@bi_plainly PROP).
Proof.
  split; [split|]; try apply _. apply plainly_and. apply plainly_pure.
Qed.

Global Instance bi_plainly_or_homomorphism :
  MonoidHomomorphism bi_or bi_or (≡) (@bi_plainly PROP).
Proof.
  split; [split|]; try apply _. apply plainly_or. apply plainly_pure.
Qed.

Global Instance bi_plainly_sep_weak_homomorphism `{PositiveBI PROP} :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@bi_plainly PROP).
Proof. split; try apply _. apply plainly_sep. Qed.

Global Instance bi_plainly_sep_homomorphism `{AffineBI PROP} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@bi_plainly PROP).
Proof. split. apply _. apply plainly_emp. Qed.

Global Instance bi_plainly_sep_entails_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_plainly PROP).
Proof. split; try apply _. intros P Q; by rewrite plainly_sep_2. Qed.

Global Instance bi_plainly_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_plainly PROP).
Proof. split. apply _. simpl. apply plainly_emp_intro. Qed.

Global Instance bi_persistently_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@bi_persistently PROP).
Proof.
  split; [split|]; try apply _. apply persistently_and. apply persistently_pure.
Qed.

Global Instance bi_persistently_or_homomorphism :
  MonoidHomomorphism bi_or bi_or (≡) (@bi_persistently PROP).
Proof.
  split; [split|]; try apply _. apply persistently_or. apply persistently_pure.
Qed.

Global Instance bi_persistently_sep_weak_homomorphism `{PositiveBI PROP} :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@bi_persistently PROP).
Proof. split; try apply _. apply persistently_sep. Qed.

Global Instance bi_persistently_sep_homomorphism `{AffineBI PROP} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@bi_persistently PROP).
Proof. split. apply _. apply persistently_emp. Qed.

Global Instance bi_persistently_sep_entails_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_persistently PROP).
Proof. split; try apply _. intros P Q; by rewrite persistently_sep_2. Qed.

Global Instance bi_persistently_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_persistently PROP).
Proof. split. apply _. simpl. apply persistently_emp_intro. Qed.

(* Heterogeneous lists *)
Lemma hexist_exist {As B} (f : himpl As B) (Φ : B → PROP) :
  bi_hexist (hcompose Φ f) ⊣⊢ ∃ xs : hlist As, Φ (f xs).
Proof.
  apply (anti_symm _).
  - induction As as [|A As IH]; simpl.
    + by rewrite -(exist_intro hnil) .
    + apply exist_elim=> x; rewrite IH; apply exist_elim=> xs.
      by rewrite -(exist_intro (hcons x xs)).
  - apply exist_elim=> xs; induction xs as [|A As x xs IH]; simpl; auto.
    by rewrite -(exist_intro x) IH.
Qed.

Lemma hforall_forall {As B} (f : himpl As B) (Φ : B → PROP) :
  bi_hforall (hcompose Φ f) ⊣⊢ ∀ xs : hlist As, Φ (f xs).
Proof.
  apply (anti_symm _).
  - apply forall_intro=> xs; induction xs as [|A As x xs IH]; simpl; auto.
    by rewrite (forall_elim x) IH.
  - induction As as [|A As IH]; simpl.
    + by rewrite (forall_elim hnil) .
    + apply forall_intro=> x; rewrite -IH; apply forall_intro=> xs.
      by rewrite (forall_elim (hcons x xs)).
Qed.
End bi_derived.

Section sbi_derived.
Context {PROP : sbi}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.
Implicit Types Ps : list PROP.
Implicit Types A : Type.

(* Force implicit argument PROP *)
Notation "P ⊢ Q" := (@bi_entails PROP P%I Q%I).
Notation "P ⊣⊢ Q" := (equiv (A:=bi_car PROP) P%I Q%I).

Hint Resolve or_elim or_intro_l' or_intro_r' True_intro False_elim.
Hint Resolve and_elim_l' and_elim_r' and_intro forall_intro.

Global Instance later_proper :
  Proper ((⊣⊢) ==> (⊣⊢)) (@bi_later PROP) := ne_proper _.

(* Equality *)
Lemma internal_eq_rewrite_contractive {A : ofeT} a b (Ψ : A → PROP)
  {HΨ : Contractive Ψ} : ▷ (a ≡ b) ⊢ Ψ a → Ψ b.
Proof.
  rewrite later_eq_2. move: HΨ=>/contractive_alt [g [? HΨ]]. rewrite !HΨ.
  by apply internal_eq_rewrite.
Qed.
Lemma internal_eq_rewrite_contractive' {A : ofeT} a b (Ψ : A → PROP) P
  {HΨ : Contractive Ψ} : (P ⊢ ▷ (a ≡ b)) → (P ⊢ Ψ a) → P ⊢ Ψ b.
Proof.
  rewrite later_eq_2. move: HΨ=>/contractive_alt [g [? HΨ]]. rewrite !HΨ.
  by apply internal_eq_rewrite'.
Qed.

Lemma later_equivI {A : ofeT} (x y : A) : Next x ≡ Next y ⊣⊢ ▷ (x ≡ y).
Proof. apply (anti_symm _); auto using later_eq_1, later_eq_2. Qed.

(* Later derived *)
Hint Resolve later_mono.
Global Instance later_mono' : Proper ((⊢) ==> (⊢)) (@bi_later PROP).
Proof. intros P Q; apply later_mono. Qed.
Global Instance later_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_later PROP).
Proof. intros P Q; apply later_mono. Qed.

Lemma later_intro P : P ⊢ ▷ P.
Proof.
  rewrite -(and_elim_l (▷ P)%I P) -(löb (▷ P ∧ P)%I).
  apply impl_intro_l. by rewrite {1}(and_elim_r (▷ P)%I).
Qed.

Lemma later_True : ▷ True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using later_intro. Qed.
Lemma later_emp `{!AffineBI PROP} : ▷ emp ⊣⊢ emp.
Proof. by rewrite -True_emp later_True. Qed.
Lemma later_forall {A} (Φ : A → PROP) : (▷ ∀ a, Φ a) ⊣⊢ (∀ a, ▷ Φ a).
Proof.
  apply (anti_symm _); auto using later_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma later_exist_2 {A} (Φ : A → PROP) : (∃ a, ▷ Φ a) ⊢ ▷ (∃ a, Φ a).
Proof. apply exist_elim; eauto using exist_intro. Qed.
Lemma later_exist `{Inhabited A} (Φ : A → PROP) : ▷ (∃ a, Φ a) ⊣⊢ (∃ a, ▷ Φ a).
Proof.
  apply: anti_symm; [|apply later_exist_2].
  rewrite later_exist_false. apply or_elim; last done.
  rewrite -(exist_intro inhabitant); auto.
Qed.
Lemma later_and P Q : ▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q.
Proof. rewrite !and_alt later_forall. by apply forall_proper=> -[]. Qed.
Lemma later_or P Q : ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q.
Proof. rewrite !or_alt later_exist. by apply exist_proper=> -[]. Qed.
Lemma later_impl P Q : ▷ (P → Q) ⊢ ▷ P → ▷ Q.
Proof. apply impl_intro_l. by rewrite -later_and impl_elim_r. Qed.
Lemma later_sep P Q : ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q.
Proof. apply (anti_symm _); auto using later_sep_1, later_sep_2. Qed.
Lemma later_wand P Q : ▷ (P -∗ Q) ⊢ ▷ P -∗ ▷ Q.
Proof. apply wand_intro_l. by rewrite -later_sep wand_elim_r. Qed.
Lemma later_iff P Q : ▷ (P ↔ Q) ⊢ ▷ P ↔ ▷ Q.
Proof. by rewrite /bi_iff later_and !later_impl. Qed.
Lemma later_plainly P : ▷ bi_plainly P ⊣⊢ bi_plainly (▷ P).
Proof. apply (anti_symm _); auto using later_plainly_1, later_plainly_2. Qed.
Lemma later_persistently P : ▷ bi_persistently P ⊣⊢ bi_persistently (▷ P).
Proof. apply (anti_symm _); auto using later_persistently_1, later_persistently_2. Qed.
Lemma later_affinely_2 P : bi_affinely (▷ P) ⊢ ▷ bi_affinely P.
Proof. rewrite /bi_affinely later_and. auto using later_intro. Qed.
Lemma later_affinely_plainly_2 P : ■ ▷ P ⊢ ▷ ■ P.
Proof. by rewrite -later_plainly later_affinely_2. Qed.
Lemma later_affinely_persistently_2 P : □ ▷ P ⊢ ▷ □ P.
Proof. by rewrite -later_persistently later_affinely_2. Qed.
Lemma later_affinely_plainly_if_2 p P : ■?p ▷ P ⊢ ▷ ■?p P.
Proof. destruct p; simpl; auto using later_affinely_plainly_2. Qed.
Lemma later_affinely_persistently_if_2 p P : □?p ▷ P ⊢ ▷ □?p P.
Proof. destruct p; simpl; auto using later_affinely_persistently_2. Qed.
Lemma later_absorbingly P : ▷ bi_absorbingly P ⊣⊢ bi_absorbingly (▷ P).
Proof. by rewrite /bi_absorbingly later_sep later_True. Qed.

Global Instance later_plain P : Plain P → Plain (▷ P).
Proof. intros. by rewrite /Plain -later_plainly {1}(plain P). Qed.
Global Instance later_persistent P : Persistent P → Persistent (▷ P).
Proof. intros. by rewrite /Persistent -later_persistently {1}(persistent P). Qed.
Global Instance later_absorbing P : Absorbing P → Absorbing (▷ P).
Proof. intros ?. by rewrite /Absorbing -later_absorbingly absorbing. Qed.

(* Iterated later modality *)
Global Instance laterN_ne m : NonExpansive (@bi_laterN PROP m).
Proof. induction m; simpl. by intros ???. solve_proper. Qed.
Global Instance laterN_proper m :
  Proper ((⊣⊢) ==> (⊣⊢)) (@bi_laterN PROP m) := ne_proper _.

Lemma laterN_0 P : ▷^0 P ⊣⊢ P.
Proof. done. Qed.
Lemma later_laterN n P : ▷^(S n) P ⊣⊢ ▷ ▷^n P.
Proof. done. Qed.
Lemma laterN_later n P : ▷^(S n) P ⊣⊢ ▷^n ▷ P.
Proof. induction n; f_equiv/=; auto. Qed.
Lemma laterN_plus n1 n2 P : ▷^(n1 + n2) P ⊣⊢ ▷^n1 ▷^n2 P.
Proof. induction n1; f_equiv/=; auto. Qed.
Lemma laterN_le n1 n2 P : n1 ≤ n2 → ▷^n1 P ⊢ ▷^n2 P.
Proof. induction 1; simpl; by rewrite -?later_intro. Qed.

Lemma laterN_mono n P Q : (P ⊢ Q) → ▷^n P ⊢ ▷^n Q.
Proof. induction n; simpl; auto. Qed.
Global Instance laterN_mono' n : Proper ((⊢) ==> (⊢)) (@bi_laterN PROP n).
Proof. intros P Q; apply laterN_mono. Qed.
Global Instance laterN_flip_mono' n :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_laterN PROP n).
Proof. intros P Q; apply laterN_mono. Qed.

Lemma laterN_intro n P : P ⊢ ▷^n P.
Proof. induction n as [|n IH]; simpl; by rewrite -?later_intro. Qed.

Lemma laterN_True n : ▷^n True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using laterN_intro, True_intro. Qed.
Lemma laterN_emp `{!AffineBI PROP} n : ▷^n emp ⊣⊢ emp.
Proof. by rewrite -True_emp laterN_True. Qed.
Lemma laterN_forall {A} n (Φ : A → PROP) : (▷^n ∀ a, Φ a) ⊣⊢ (∀ a, ▷^n Φ a).
Proof. induction n as [|n IH]; simpl; rewrite -?later_forall ?IH; auto. Qed.
Lemma laterN_exist_2 {A} n (Φ : A → PROP) : (∃ a, ▷^n Φ a) ⊢ ▷^n (∃ a, Φ a).
Proof. apply exist_elim; eauto using exist_intro, laterN_mono. Qed.
Lemma laterN_exist `{Inhabited A} n (Φ : A → PROP) :
  (▷^n ∃ a, Φ a) ⊣⊢ ∃ a, ▷^n Φ a.
Proof. induction n as [|n IH]; simpl; rewrite -?later_exist ?IH; auto. Qed.
Lemma laterN_and n P Q : ▷^n (P ∧ Q) ⊣⊢ ▷^n P ∧ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_and ?IH; auto. Qed.
Lemma laterN_or n P Q : ▷^n (P ∨ Q) ⊣⊢ ▷^n P ∨ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_or ?IH; auto. Qed.
Lemma laterN_impl n P Q : ▷^n (P → Q) ⊢ ▷^n P → ▷^n Q.
Proof. apply impl_intro_l. by rewrite -laterN_and impl_elim_r. Qed.
Lemma laterN_sep n P Q : ▷^n (P ∗ Q) ⊣⊢ ▷^n P ∗ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_sep ?IH; auto. Qed.
Lemma laterN_wand n P Q : ▷^n (P -∗ Q) ⊢ ▷^n P -∗ ▷^n Q.
Proof. apply wand_intro_l. by rewrite -laterN_sep wand_elim_r. Qed.
Lemma laterN_iff n P Q : ▷^n (P ↔ Q) ⊢ ▷^n P ↔ ▷^n Q.
Proof. by rewrite /bi_iff laterN_and !laterN_impl. Qed.
Lemma laterN_plainly n P : ▷^n bi_plainly P ⊣⊢ bi_plainly (▷^n P).
Proof. induction n as [|n IH]; simpl; auto. by rewrite IH later_plainly. Qed.
Lemma laterN_persistently n P : ▷^n bi_persistently P ⊣⊢ bi_persistently (▷^n P).
Proof. induction n as [|n IH]; simpl; auto. by rewrite IH later_persistently. Qed.
Lemma laterN_affinely_2 n P : bi_affinely (▷^n P) ⊢ ▷^n bi_affinely P.
Proof. rewrite /bi_affinely laterN_and. auto using laterN_intro. Qed.
Lemma laterN_affinely_plainly_2 n P : ■ ▷^n P ⊢ ▷^n ■ P.
Proof. by rewrite -laterN_plainly laterN_affinely_2. Qed.
Lemma laterN_affinely_persistently_2 n P : □ ▷^n P ⊢ ▷^n □ P.
Proof. by rewrite -laterN_persistently laterN_affinely_2. Qed.
Lemma laterN_affinely_plainly_if_2 n p P : ■?p ▷^n P ⊢ ▷^n ■?p P.
Proof. destruct p; simpl; auto using laterN_affinely_plainly_2. Qed.
Lemma laterN_affinely_persistently_if_2 n p P : □?p ▷^n P ⊢ ▷^n □?p P.
Proof. destruct p; simpl; auto using laterN_affinely_persistently_2. Qed.
Lemma laterN_absorbingly n P : ▷^n (bi_absorbingly P) ⊣⊢ bi_absorbingly (▷^n P).
Proof. by rewrite /bi_absorbingly laterN_sep laterN_True. Qed.

Global Instance laterN_plain n P : Plain P → Plain (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance laterN_persistent n P : Persistent P → Persistent (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance laterN_absorbing n P : Absorbing P → Absorbing (▷^n P).
Proof. induction n; apply _. Qed.

(* Except-0 *)
Global Instance except_0_ne : NonExpansive (@bi_except_0 PROP).
Proof. solve_proper. Qed.
Global Instance except_0_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_except_0 PROP).
Proof. solve_proper. Qed.
Global Instance except_0_mono' : Proper ((⊢) ==> (⊢)) (@bi_except_0 PROP).
Proof. solve_proper. Qed.
Global Instance except_0_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_except_0 PROP).
Proof. solve_proper. Qed.

Lemma except_0_intro P : P ⊢ ◇ P.
Proof. rewrite /bi_except_0; auto. Qed.
Lemma except_0_mono P Q : (P ⊢ Q) → ◇ P ⊢ ◇ Q.
Proof. by intros ->. Qed.
Lemma except_0_idemp P : ◇ ◇ P ⊣⊢ ◇ P.
Proof. apply (anti_symm _); rewrite /bi_except_0; auto. Qed.

Lemma except_0_True : ◇ True ⊣⊢ True.
Proof. rewrite /bi_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_emp `{!AffineBI PROP} : ◇ emp ⊣⊢ emp.
Proof. by rewrite -True_emp except_0_True. Qed.
Lemma except_0_or P Q : ◇ (P ∨ Q) ⊣⊢ ◇ P ∨ ◇ Q.
Proof. rewrite /bi_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_and P Q : ◇ (P ∧ Q) ⊣⊢ ◇ P ∧ ◇ Q.
Proof. by rewrite /bi_except_0 or_and_l. Qed.
Lemma except_0_sep P Q : ◇ (P ∗ Q) ⊣⊢ ◇ P ∗ ◇ Q.
Proof.
  rewrite /bi_except_0. apply (anti_symm _).
  - apply or_elim; last by auto using sep_mono.
    by rewrite -!or_intro_l -persistently_pure -later_sep -persistently_sep_dup.
  - rewrite sep_or_r !sep_or_l {1}(later_intro P) {1}(later_intro Q).
    rewrite -!later_sep !left_absorb right_absorb. auto.
Qed.
Lemma except_0_forall {A} (Φ : A → PROP) : ◇ (∀ a, Φ a) ⊣⊢ ∀ a, ◇ Φ a.
Proof.
  apply (anti_symm _).
  { apply forall_intro=> a. by rewrite (forall_elim a). }
  trans (▷ (∀ a : A, Φ a) ∧ (∀ a : A, ◇ Φ a))%I.
  { apply and_intro, reflexivity. rewrite later_forall. apply forall_mono=> a.
    apply or_elim; auto using later_intro. }
  rewrite later_false_em and_or_r. apply or_elim.
  { rewrite and_elim_l. apply or_intro_l. }
  apply or_intro_r', forall_intro=> a. rewrite !(forall_elim a).
  by rewrite and_or_l impl_elim_l and_elim_r idemp.
Qed.
Lemma except_0_exist_2 {A} (Φ : A → PROP) : (∃ a, ◇ Φ a) ⊢ ◇ ∃ a, Φ a.
Proof. apply exist_elim=> a. by rewrite (exist_intro a). Qed.
Lemma except_0_exist `{Inhabited A} (Φ : A → PROP) :
  ◇ (∃ a, Φ a) ⊣⊢ (∃ a, ◇ Φ a).
Proof.
  apply (anti_symm _); [|by apply except_0_exist_2]. apply or_elim.
  - rewrite -(exist_intro inhabitant). by apply or_intro_l.
  - apply exist_mono=> a. apply except_0_intro.
Qed.
Lemma except_0_later P : ◇ ▷ P ⊢ ▷ P.
Proof. by rewrite /bi_except_0 -later_or False_or. Qed.
Lemma except_0_plainly P : ◇ bi_plainly P ⊣⊢ bi_plainly (◇ P).
Proof. by rewrite /bi_except_0 plainly_or -later_plainly plainly_pure. Qed.
Lemma except_0_persistently P : ◇ bi_persistently P ⊣⊢ bi_persistently (◇ P).
Proof.
  by rewrite /bi_except_0 persistently_or -later_persistently persistently_pure.
Qed.
Lemma except_0_affinely_2 P : bi_affinely (◇ P) ⊢ ◇ bi_affinely P.
Proof. rewrite /bi_affinely except_0_and. auto using except_0_intro. Qed.
Lemma except_0_affinely_plainly_2 P : ■ ◇ P ⊢ ◇ ■ P.
Proof. by rewrite -except_0_plainly except_0_affinely_2. Qed.
Lemma except_0_affinely_persistently_2 P : □ ◇ P ⊢ ◇ □ P.
Proof. by rewrite -except_0_persistently except_0_affinely_2. Qed.
Lemma except_0_affinely_plainly_if_2 p P : ■?p ◇ P ⊢ ◇ ■?p P.
Proof. destruct p; simpl; auto using except_0_affinely_plainly_2. Qed.
Lemma except_0_affinely_persistently_if_2 p P : □?p ◇ P ⊢ ◇ □?p P.
Proof. destruct p; simpl; auto using except_0_affinely_persistently_2. Qed.
Lemma except_0_absorbingly P : ◇ (bi_absorbingly P) ⊣⊢ bi_absorbingly (◇ P).
Proof. by rewrite /bi_absorbingly except_0_sep except_0_True. Qed.

Lemma except_0_frame_l P Q : P ∗ ◇ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro P) except_0_sep. Qed.
Lemma except_0_frame_r P Q : ◇ P ∗ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro Q) except_0_sep. Qed.

Lemma later_affinely_1 `{!Timeless (emp%I : PROP)} P :
  ▷ bi_affinely P ⊢ ◇ bi_affinely (▷ P).
Proof.
  rewrite /bi_affinely later_and (timeless emp%I) except_0_and.
  by apply and_mono, except_0_intro.
Qed.

Global Instance except_0_plain P : Plain P → Plain (◇ P).
Proof. rewrite /bi_except_0; apply _. Qed.
Global Instance except_0_persistent P : Persistent P → Persistent (◇ P).
Proof. rewrite /bi_except_0; apply _. Qed.
Global Instance except_0_absorbing P : Absorbing P → Absorbing (◇ P).
Proof. rewrite /bi_except_0; apply _. Qed.

(* Timeless instances *)
Global Instance Timeless_proper : Proper ((≡) ==> iff) (@Timeless PROP).
Proof. solve_proper. Qed.

Global Instance pure_timeless φ : Timeless (⌜φ⌝ : PROP)%I.
Proof.
  rewrite /Timeless /bi_except_0 pure_alt later_exist_false.
  apply or_elim, exist_elim; [auto|]=> Hφ. rewrite -(exist_intro Hφ). auto.
Qed.
Global Instance emp_timeless `{AffineBI PROP} : Timeless (emp : PROP)%I.
Proof. rewrite -True_emp. apply _. Qed.

Global Instance and_timeless P Q : Timeless P → Timeless Q → Timeless (P ∧ Q).
Proof. intros; rewrite /Timeless except_0_and later_and; auto. Qed.
Global Instance or_timeless P Q : Timeless P → Timeless Q → Timeless (P ∨ Q).
Proof. intros; rewrite /Timeless except_0_or later_or; auto. Qed.

Global Instance impl_timeless P Q : Timeless Q → Timeless (P → Q).
Proof.
  rewrite /Timeless=> HQ. rewrite later_false_em.
  apply or_mono, impl_intro_l; first done.
  rewrite -{2}(löb Q); apply impl_intro_l.
  rewrite HQ /bi_except_0 !and_or_r. apply or_elim; last auto.
  by rewrite assoc (comm _ _ P) -assoc !impl_elim_r.
Qed.
Global Instance sep_timeless P Q: Timeless P → Timeless Q → Timeless (P ∗ Q).
Proof.
  intros; rewrite /Timeless except_0_sep later_sep; auto using sep_mono.
Qed.

Global Instance wand_timeless P Q : Timeless Q → Timeless (P -∗ Q).
Proof.
  rewrite /Timeless=> HQ. rewrite later_false_em.
  apply or_mono, wand_intro_l; first done.
  rewrite -{2}(löb Q); apply impl_intro_l.
  rewrite HQ /bi_except_0 !and_or_r. apply or_elim; last auto.
  by rewrite (comm _ P) persistent_and_sep_assoc impl_elim_r wand_elim_l.
Qed.
Global Instance forall_timeless {A} (Ψ : A → PROP) :
  (∀ x, Timeless (Ψ x)) → Timeless (∀ x, Ψ x).
Proof.
  rewrite /Timeless=> HQ. rewrite except_0_forall later_forall.
  apply forall_mono; auto.
Qed.
Global Instance exist_timeless {A} (Ψ : A → PROP) :
  (∀ x, Timeless (Ψ x)) → Timeless (∃ x, Ψ x).
Proof.
  rewrite /Timeless=> ?. rewrite later_exist_false. apply or_elim.
  - rewrite /bi_except_0; auto.
  - apply exist_elim=> x. rewrite -(exist_intro x); auto.
Qed.
Global Instance plainly_timeless P : Timeless P → Timeless (bi_plainly P).
Proof.
  intros. rewrite /Timeless /bi_except_0 later_plainly_1.
  by rewrite (timeless P) /bi_except_0 plainly_or {1}plainly_elim.
Qed.
Global Instance persistently_timeless P : Timeless P → Timeless (bi_persistently P).
Proof.
  intros. rewrite /Timeless /bi_except_0 later_persistently_1.
  by rewrite (timeless P) /bi_except_0 persistently_or {1}persistently_elim.
Qed.

Global Instance affinely_timeless P :
  Timeless (emp%I : PROP) → Timeless P → Timeless (bi_affinely P).
Proof. rewrite /bi_affinely; apply _. Qed.
Global Instance absorbingly_timeless P : Timeless P → Timeless (bi_absorbingly P).
Proof. rewrite /bi_absorbingly; apply _. Qed.

Global Instance eq_timeless {A : ofeT} (a b : A) :
  Discrete a → Timeless (a ≡ b : PROP)%I.
Proof. intros. rewrite /Discrete !discrete_eq. apply (timeless _). Qed.
Global Instance from_option_timeless {A} P (Ψ : A → PROP) (mx : option A) :
  (∀ x, Timeless (Ψ x)) → Timeless P → Timeless (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* Big op stuff *)
Global Instance bi_later_monoid_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@bi_later PROP).
Proof. split; [split|]; try apply _. apply later_and. apply later_True. Qed.
Global Instance bi_laterN_and_homomorphism n :
  MonoidHomomorphism bi_and bi_and (≡) (@bi_laterN PROP n).
Proof. split; [split|]; try apply _. apply laterN_and. apply laterN_True. Qed.
Global Instance bi_except_0_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@bi_except_0 PROP).
Proof. split; [split|]; try apply _. apply except_0_and. apply except_0_True. Qed.

Global Instance bi_later_monoid_or_homomorphism :
  WeakMonoidHomomorphism bi_or bi_or (≡) (@bi_later PROP).
Proof. split; try apply _. apply later_or. Qed.
Global Instance bi_laterN_or_homomorphism n :
  WeakMonoidHomomorphism bi_or bi_or (≡) (@bi_laterN PROP n).
Proof. split; try apply _. apply laterN_or. Qed.
Global Instance bi_except_0_or_homomorphism :
  WeakMonoidHomomorphism bi_or bi_or (≡) (@bi_except_0 PROP).
Proof. split; try apply _. apply except_0_or. Qed.

Global Instance bi_later_monoid_sep_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@bi_later PROP).
Proof. split; try apply _. apply later_sep. Qed.
Global Instance bi_laterN_sep_weak_homomorphism n :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@bi_laterN PROP n).
Proof. split; try apply _. apply laterN_sep. Qed.
Global Instance bi_except_0_sep_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@bi_except_0 PROP).
Proof. split; try apply _. apply except_0_sep. Qed.

Global Instance bi_later_monoid_sep_homomorphism `{!AffineBI PROP} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@bi_later PROP).
Proof. split; try apply _. apply later_emp. Qed.
Global Instance bi_laterN_sep_homomorphism `{!AffineBI PROP} n :
  MonoidHomomorphism bi_sep bi_sep (≡) (@bi_laterN PROP n).
Proof. split; try apply _. apply laterN_emp. Qed.
Global Instance bi_except_0_sep_homomorphism `{!AffineBI PROP} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@bi_except_0 PROP).
Proof. split; try apply _. apply except_0_emp. Qed.

Global Instance bi_later_monoid_sep_entails_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_later PROP).
Proof. split; try apply _. intros P Q. by rewrite later_sep. Qed.
Global Instance bi_laterN_sep_entails_weak_homomorphism n :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_laterN PROP n).
Proof. split; try apply _. intros P Q. by rewrite laterN_sep. Qed.
Global Instance bi_except_0_sep_entails_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_except_0 PROP).
Proof. split; try apply _. intros P Q. by rewrite except_0_sep. Qed.

Global Instance bi_later_monoid_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_later PROP).
Proof. split; try apply _. apply later_intro. Qed.
Global Instance bi_laterN_sep_entails_homomorphism n :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_laterN PROP n).
Proof. split; try apply _. apply laterN_intro. Qed.
Global Instance bi_except_0_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_except_0 PROP).
Proof. split; try apply _. apply except_0_intro. Qed.
End sbi_derived.
End bi.

(* When declared as an actual instance, [plain_persistent] will cause
failing proof searches to take exponential time, as Coq will try to
apply it the instance at any node in the proof search tree.

To avoid that, we declare it using a [Hint Immediate], so that it will
only be used at the leaves of the proof search tree, i.e. when the
premise of the hint can be derived from just the current context. *)
Hint Immediate bi.plain_persistent : typeclass_instances.
