From iris.bi Require Import derived_laws.
From iris.algebra Require Import monoid.
Import interface.bi derived_laws.bi.

Class Plainly (A : Type) := plainly : A → A.
Hint Mode Plainly ! : typeclass_instances.
Instance: Params (@plainly) 2.
Notation "■ P" := (plainly P)%I
  (at level 20, right associativity) : bi_scope.

(* Mixins allow us to create instances easily without having to use Program *)
Record BiPlainlyMixin (PROP : sbi) `(Plainly PROP) := {
  bi_plainly_mixin_plainly_ne : NonExpansive plainly;

  bi_plainly_mixin_plainly_mono P Q : (P ⊢ Q) → ■ P ⊢ ■ Q;
  bi_plainly_mixin_plainly_elim_persistently P : ■ P ⊢ <pers> P;
  bi_plainly_mixin_plainly_idemp_2 P : ■ P ⊢ ■ ■ P;

  bi_plainly_mixin_plainly_forall_2 {A} (Ψ : A → PROP) :
    (∀ a, ■ (Ψ a)) ⊢ ■ (∀ a, Ψ a);

  (* The following two laws are very similar, and indeed they hold not just
     for persistently and plainly, but for any modality defined as `M P n x :=
     ∀ y, R x y → P n y`. *)
  bi_plainly_mixin_persistently_impl_plainly P Q :
    (■ P → <pers> Q) ⊢ <pers> (■ P → Q);
  bi_plainly_mixin_plainly_impl_plainly P Q : (■ P → ■ Q) ⊢ ■ (■ P → Q);

  bi_plainly_mixin_plainly_emp_intro P : P ⊢ ■ emp;
  bi_plainly_mixin_plainly_absorb P Q : ■ P ∗ Q ⊢ ■ P;

  bi_plainly_mixin_prop_ext P Q : ■ ((P -∗ Q) ∧ (Q -∗ P)) ⊢ P ≡ Q;

  bi_plainly_mixin_later_plainly_1 P : ▷ ■ P ⊢ ■ ▷ P;
  bi_plainly_mixin_later_plainly_2 P : ■ ▷ P ⊢ ▷ ■ P;
}.

Class BiPlainly (PROP : sbi) := {
  bi_plainly_plainly :> Plainly PROP;
  bi_plainly_mixin : BiPlainlyMixin PROP bi_plainly_plainly;
}.
Hint Mode BiPlainly ! : typeclass_instances.
Arguments bi_plainly_plainly : simpl never.

Class BiPlainlyExist `{!BiPlainly PROP} :=
  plainly_exist_1 A (Ψ : A → PROP) :
    ■ (∃ a, Ψ a) ⊢ ∃ a, ■ (Ψ a).
Arguments BiPlainlyExist : clear implicits.
Arguments BiPlainlyExist _ {_}.
Arguments plainly_exist_1 _ {_ _} _.
Hint Mode BiPlainlyExist ! - : typeclass_instances.

Section plainly_laws.
  Context `{BiPlainly PROP}.
  Implicit Types P Q : PROP.

  Global Instance plainly_ne : NonExpansive (@plainly PROP _).
  Proof. eapply bi_plainly_mixin_plainly_ne, bi_plainly_mixin. Qed.

  Lemma plainly_mono P Q : (P ⊢ Q) → ■ P ⊢ ■ Q.
  Proof. eapply bi_plainly_mixin_plainly_mono, bi_plainly_mixin. Qed.
  Lemma plainly_elim_persistently P : ■ P ⊢ <pers> P.
  Proof. eapply bi_plainly_mixin_plainly_elim_persistently, bi_plainly_mixin. Qed.
  Lemma plainly_idemp_2 P : ■ P ⊢ ■ ■ P.
  Proof. eapply bi_plainly_mixin_plainly_idemp_2, bi_plainly_mixin. Qed.
  Lemma plainly_forall_2 {A} (Ψ : A → PROP) : (∀ a, ■ (Ψ a)) ⊢ ■ (∀ a, Ψ a).
  Proof. eapply bi_plainly_mixin_plainly_forall_2, bi_plainly_mixin. Qed.
  Lemma persistently_impl_plainly P Q : (■ P → <pers> Q) ⊢ <pers> (■ P → Q).
  Proof. eapply bi_plainly_mixin_persistently_impl_plainly, bi_plainly_mixin. Qed.
  Lemma plainly_impl_plainly P Q : (■ P → ■ Q) ⊢ ■ (■ P → Q).
  Proof. eapply bi_plainly_mixin_plainly_impl_plainly, bi_plainly_mixin. Qed.
  Lemma plainly_absorb P Q : ■ P ∗ Q ⊢ ■ P.
  Proof. eapply bi_plainly_mixin_plainly_absorb, bi_plainly_mixin. Qed.
  Lemma plainly_emp_intro P : P ⊢ ■ emp.
  Proof. eapply bi_plainly_mixin_plainly_emp_intro, bi_plainly_mixin. Qed.

  Lemma prop_ext P Q : ■ ((P -∗ Q) ∧ (Q -∗ P)) ⊢ P ≡ Q.
  Proof. eapply bi_plainly_mixin_prop_ext, bi_plainly_mixin. Qed.

  Lemma later_plainly_1 P : ▷ ■ P ⊢ ■ (▷ P).
  Proof. eapply bi_plainly_mixin_later_plainly_1, bi_plainly_mixin. Qed.
  Lemma later_plainly_2 P : ■ ▷ P ⊢ ▷ ■ P.
  Proof. eapply bi_plainly_mixin_later_plainly_2, bi_plainly_mixin. Qed.
End plainly_laws.

(* Derived properties and connectives *)
Class Plain `{BiPlainly PROP} (P : PROP) := plain : P ⊢ ■ P.
Arguments Plain {_ _} _%I : simpl never.
Arguments plain {_ _} _%I {_}.
Hint Mode Plain + ! ! : typeclass_instances.
Instance: Params (@Plain) 1.

Definition plainly_if `{!BiPlainly PROP} (p : bool) (P : PROP) : PROP :=
  (if p then ■ P else P)%I.
Arguments plainly_if {_ _} !_ _%I /.
Instance: Params (@plainly_if) 2.
Typeclasses Opaque plainly_if.

Notation "■? p P" := (plainly_if p P)%I
  (at level 20, p at level 9, P at level 20,
   right associativity, format "■? p  P") : bi_scope.

(* Derived laws *)
Section plainly_derived.
Context `{BiPlainly PROP}.
Implicit Types P : PROP.

Hint Resolve pure_intro forall_intro.
Hint Resolve or_elim or_intro_l' or_intro_r'.
Hint Resolve and_intro and_elim_l' and_elim_r'.

Global Instance plainly_proper :
  Proper ((⊣⊢) ==> (⊣⊢)) (@plainly PROP _) := ne_proper _.

Global Instance plainly_mono' : Proper ((⊢) ==> (⊢)) (@plainly PROP _).
Proof. intros P Q; apply plainly_mono. Qed.
Global Instance plainly_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@plainly PROP _).
Proof. intros P Q; apply plainly_mono. Qed.

Lemma affinely_plainly_elim P : <affine> ■ P ⊢ P.
Proof. by rewrite plainly_elim_persistently /bi_affinely persistently_and_emp_elim. Qed.

Lemma persistently_plainly P : <pers> ■ P ⊣⊢ ■ P.
Proof.
  apply (anti_symm _).
  - by rewrite persistently_elim_absorbingly /bi_absorbingly comm plainly_absorb.
  - by rewrite {1}plainly_idemp_2 plainly_elim_persistently.
Qed.
Lemma persistently_if_plainly P p : <pers>?p ■ P ⊣⊢ ■ P.
Proof. destruct p; last done. exact: persistently_plainly. Qed.

Lemma plainly_persistently P : ■ <pers> P ⊣⊢ ■ P.
Proof.
  apply (anti_symm _).
  - rewrite -{1}(left_id True%I bi_and (■ _)%I) (plainly_emp_intro True%I).
    rewrite -{2}(persistently_and_emp_elim P).
    rewrite !and_alt -plainly_forall_2. by apply forall_mono=> -[].
  - by rewrite {1}plainly_idemp_2 (plainly_elim_persistently P).
Qed.

Lemma absorbingly_plainly P : <absorb> ■ P ⊣⊢ ■ P.
Proof. by rewrite -(persistently_plainly P) absorbingly_persistently. Qed.

Lemma plainly_and_sep_elim P Q : ■ P ∧ Q -∗ (emp ∧ P) ∗ Q.
Proof. by rewrite plainly_elim_persistently persistently_and_sep_elim_emp. Qed.
Lemma plainly_and_sep_assoc P Q R : ■ P ∧ (Q ∗ R) ⊣⊢ (■ P ∧ Q) ∗ R.
Proof. by rewrite -(persistently_plainly P) persistently_and_sep_assoc. Qed.
Lemma plainly_and_emp_elim P : emp ∧ ■ P ⊢ P.
Proof. by rewrite plainly_elim_persistently persistently_and_emp_elim. Qed.
Lemma plainly_elim_absorbingly P : ■ P ⊢ <absorb> P.
Proof. by rewrite plainly_elim_persistently persistently_elim_absorbingly. Qed.
Lemma plainly_elim P `{!Absorbing P} : ■ P ⊢ P.
Proof. by rewrite plainly_elim_persistently persistently_elim. Qed.

Lemma plainly_idemp_1 P : ■ ■ P ⊢ ■ P.
Proof. by rewrite plainly_elim_absorbingly absorbingly_plainly. Qed.
Lemma plainly_idemp P : ■ ■ P ⊣⊢ ■ P.
Proof. apply (anti_symm _); auto using plainly_idemp_1, plainly_idemp_2. Qed.

Lemma plainly_intro' P Q : (■ P ⊢ Q) → ■ P ⊢ ■ Q.
Proof. intros <-. apply plainly_idemp_2. Qed.

Lemma plainly_pure φ : ■ ⌜φ⌝ ⊣⊢ bi_pure (PROP:=PROP) φ.
Proof.
  apply (anti_symm _); auto.
  - by rewrite plainly_elim_persistently persistently_pure.
  - apply pure_elim'=> Hφ.
    trans (∀ x : False, ■ True : PROP)%I; [by apply forall_intro|].
    rewrite plainly_forall_2. by rewrite -(pure_intro _ φ).
Qed.
Lemma plainly_forall {A} (Ψ : A → PROP) : ■ (∀ a, Ψ a) ⊣⊢ ∀ a, ■ (Ψ a).
Proof.
  apply (anti_symm _); auto using plainly_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma plainly_exist_2 {A} (Ψ : A → PROP) : (∃ a, ■ (Ψ a)) ⊢ ■ (∃ a, Ψ a).
Proof. apply exist_elim=> x. by rewrite (exist_intro x). Qed.
Lemma plainly_exist `{!BiPlainlyExist PROP} {A} (Ψ : A → PROP) :
  ■ (∃ a, Ψ a) ⊣⊢ ∃ a, ■ (Ψ a).
Proof. apply (anti_symm _); auto using plainly_exist_1, plainly_exist_2. Qed.
Lemma plainly_and P Q : ■ (P ∧ Q) ⊣⊢ ■ P ∧ ■ Q.
Proof. rewrite !and_alt plainly_forall. by apply forall_proper=> -[]. Qed.
Lemma plainly_or_2 P Q : ■ P ∨ ■ Q ⊢ ■ (P ∨ Q).
Proof. rewrite !or_alt -plainly_exist_2. by apply exist_mono=> -[]. Qed.
Lemma plainly_or `{!BiPlainlyExist PROP} P Q : ■ (P ∨ Q) ⊣⊢ ■ P ∨ ■ Q.
Proof. rewrite !or_alt plainly_exist. by apply exist_proper=> -[]. Qed.
Lemma plainly_impl P Q : ■ (P → Q) ⊢ ■ P → ■ Q.
Proof.
  apply impl_intro_l; rewrite -plainly_and.
  apply plainly_mono, impl_elim with P; auto.
Qed.

Lemma plainly_sep_dup P : ■ P ⊣⊢ ■ P ∗ ■ P.
Proof.
  apply (anti_symm _).
  - rewrite -{1}(idemp bi_and (■ _)%I).
    by rewrite -{2}(left_id emp%I _ (■ _)%I) plainly_and_sep_assoc and_elim_l.
  - by rewrite plainly_absorb.
Qed.

Lemma plainly_and_sep_l_1 P Q : ■ P ∧ Q ⊢ ■ P ∗ Q.
Proof. by rewrite -{1}(left_id emp%I _ Q%I) plainly_and_sep_assoc and_elim_l. Qed.
Lemma plainly_and_sep_r_1 P Q : P ∧ ■ Q ⊢ P ∗ ■ Q.
Proof. by rewrite !(comm _ P) plainly_and_sep_l_1. Qed.

Lemma plainly_True_emp : ■ True ⊣⊢ ■ (@bi_emp PROP).
Proof. apply (anti_symm _); eauto using plainly_mono, plainly_emp_intro. Qed.
Lemma plainly_and_sep P Q : ■ (P ∧ Q) ⊢ ■ (P ∗ Q).
Proof.
  rewrite plainly_and.
  rewrite -{1}plainly_idemp -plainly_and -{1}(left_id emp%I _ Q%I).
  by rewrite plainly_and_sep_assoc (comm bi_and) plainly_and_emp_elim.
Qed.

Lemma plainly_affinely P : ■ <affine> P ⊣⊢ ■ P.
Proof. by rewrite /bi_affinely plainly_and -plainly_True_emp plainly_pure left_id. Qed.

Lemma intuitionistically_plainly_elim P : □ ■ P -∗ □ P.
Proof. rewrite intuitionistically_affinely plainly_elim_persistently //. Qed.
Lemma intuitionistically_plainly P : □ ■ P -∗ ■ □ P.
Proof.
  rewrite /bi_intuitionistically plainly_affinely affinely_elim.
  rewrite persistently_plainly plainly_persistently. done.
Qed.

Lemma and_sep_plainly P Q : ■ P ∧ ■ Q ⊣⊢ ■ P ∗ ■ Q.
Proof.
  apply (anti_symm _); auto using plainly_and_sep_l_1.
  apply and_intro.
  - by rewrite plainly_absorb.
  - by rewrite comm plainly_absorb.
Qed.
Lemma plainly_sep_2 P Q : ■ P ∗ ■ Q ⊢ ■ (P ∗ Q).
Proof. by rewrite -plainly_and_sep plainly_and -and_sep_plainly. Qed.
Lemma plainly_sep `{BiPositive PROP} P Q : ■ (P ∗ Q) ⊣⊢ ■ P ∗ ■ Q.
Proof.
  apply (anti_symm _); auto using plainly_sep_2.
  rewrite -(plainly_affinely (_ ∗ _)%I) affinely_sep -and_sep_plainly. apply and_intro.
  - by rewrite (affinely_elim_emp Q) right_id affinely_elim.
  - by rewrite (affinely_elim_emp P) left_id affinely_elim.
Qed.

Lemma plainly_wand P Q : ■ (P -∗ Q) ⊢ ■ P -∗ ■ Q.
Proof. apply wand_intro_r. by rewrite plainly_sep_2 wand_elim_l. Qed.

Lemma plainly_entails_l P Q : (P ⊢ ■ Q) → P ⊢ ■ Q ∗ P.
Proof. intros; rewrite -plainly_and_sep_l_1; auto. Qed.
Lemma plainly_entails_r P Q : (P ⊢ ■ Q) → P ⊢ P ∗ ■ Q.
Proof. intros; rewrite -plainly_and_sep_r_1; auto. Qed.

Lemma plainly_impl_wand_2 P Q : ■ (P -∗ Q) ⊢ ■ (P → Q).
Proof.
  apply plainly_intro', impl_intro_r.
  rewrite -{2}(left_id emp%I _ P%I) plainly_and_sep_assoc.
  by rewrite (comm bi_and) plainly_and_emp_elim wand_elim_l.
Qed.

Lemma impl_wand_plainly_2 P Q : (■ P -∗ Q) ⊢ (■ P → Q).
Proof. apply impl_intro_l. by rewrite plainly_and_sep_l_1 wand_elim_r. Qed.

Lemma impl_wand_affinely_plainly P Q : (■ P → Q) ⊣⊢ (<affine> ■ P -∗ Q).
Proof. by rewrite -(persistently_plainly P) impl_wand_intuitionistically. Qed.

Lemma persistently_wand_affinely_plainly P Q :
  (<affine> ■ P -∗ <pers> Q) ⊢ <pers> (<affine> ■ P -∗ Q).
Proof. rewrite -!impl_wand_affinely_plainly. apply persistently_impl_plainly. Qed.

Lemma plainly_wand_affinely_plainly P Q :
  (<affine> ■ P -∗ ■ Q) ⊢ ■ (<affine> ■ P -∗ Q).
Proof. rewrite -!impl_wand_affinely_plainly. apply plainly_impl_plainly. Qed.

Section plainly_affine_bi.
  Context `{BiAffine PROP}.

  Lemma plainly_emp : ■ emp ⊣⊢ bi_emp (PROP:=PROP).
  Proof. by rewrite -!True_emp plainly_pure. Qed.

  Lemma plainly_and_sep_l P Q : ■ P ∧ Q ⊣⊢ ■ P ∗ Q.
  Proof.
    apply (anti_symm (⊢));
      eauto using plainly_and_sep_l_1, sep_and with typeclass_instances.
  Qed.
  Lemma plainly_and_sep_r P Q : P ∧ ■ Q ⊣⊢ P ∗ ■ Q.
  Proof. by rewrite !(comm _ P) plainly_and_sep_l. Qed.

  Lemma plainly_impl_wand P Q : ■ (P → Q) ⊣⊢ ■ (P -∗ Q).
  Proof.
    apply (anti_symm (⊢)); auto using plainly_impl_wand_2.
    apply plainly_intro', wand_intro_l.
    by rewrite -plainly_and_sep_r plainly_elim impl_elim_r.
  Qed.

  Lemma impl_wand_plainly P Q : (■ P → Q) ⊣⊢ (■ P -∗ Q).
  Proof.
    apply (anti_symm (⊢)). by rewrite -impl_wand_1. by rewrite impl_wand_plainly_2.
  Qed. 
End plainly_affine_bi.

(* Conditional plainly *)
Global Instance plainly_if_ne p : NonExpansive (@plainly_if PROP _ p).
Proof. solve_proper. Qed.
Global Instance plainly_if_proper p : Proper ((⊣⊢) ==> (⊣⊢)) (@plainly_if PROP _ p).
Proof. solve_proper. Qed.
Global Instance plainly_if_mono' p : Proper ((⊢) ==> (⊢)) (@plainly_if PROP _ p).
Proof. solve_proper. Qed.
Global Instance plainly_if_flip_mono' p :
  Proper (flip (⊢) ==> flip (⊢)) (@plainly_if PROP _ p).
Proof. solve_proper. Qed.

Lemma plainly_if_mono p P Q : (P ⊢ Q) → ■?p P ⊢ ■?p Q.
Proof. by intros ->. Qed.

Lemma plainly_if_pure p φ : ■?p ⌜φ⌝ ⊣⊢ bi_pure (PROP:=PROP) φ.
Proof. destruct p; simpl; auto using plainly_pure. Qed.
Lemma plainly_if_and p P Q : ■?p (P ∧ Q) ⊣⊢ ■?p P ∧ ■?p Q.
Proof. destruct p; simpl; auto using plainly_and. Qed.
Lemma plainly_if_or_2 p P Q : ■?p P ∨ ■?p Q ⊢ ■?p (P ∨ Q).
Proof. destruct p; simpl; auto using plainly_or_2. Qed.
Lemma plainly_if_or `{!BiPlainlyExist PROP} p P Q : ■?p (P ∨ Q) ⊣⊢ ■?p P ∨ ■?p Q.
Proof. destruct p; simpl; auto using plainly_or. Qed.
Lemma plainly_if_exist_2 {A} p (Ψ : A → PROP) : (∃ a, ■?p (Ψ a)) ⊢ ■?p (∃ a, Ψ a).
Proof. destruct p; simpl; auto using plainly_exist_2. Qed.
Lemma plainly_if_exist `{!BiPlainlyExist PROP} {A} p (Ψ : A → PROP) :
  ■?p (∃ a, Ψ a) ⊣⊢ ∃ a, ■?p (Ψ a).
Proof. destruct p; simpl; auto using plainly_exist. Qed.
Lemma plainly_if_sep_2 `{!BiPositive PROP} p P Q : ■?p P ∗ ■?p Q  ⊢ ■?p (P ∗ Q).
Proof. destruct p; simpl; auto using plainly_sep_2. Qed.

Lemma plainly_if_idemp p P : ■?p ■?p P ⊣⊢ ■?p P.
Proof. destruct p; simpl; auto using plainly_idemp. Qed.

(* Properties of plain propositions *)
Global Instance Plain_proper : Proper ((≡) ==> iff) (@Plain PROP _).
Proof. solve_proper. Qed.

Lemma plain_plainly_2 P `{!Plain P} : P ⊢ ■ P.
Proof. done. Qed.
Lemma plain_plainly P `{!Plain P, !Absorbing P} : ■ P ⊣⊢ P.
Proof. apply (anti_symm _), plain_plainly_2, _. by apply plainly_elim. Qed.
Lemma plainly_intro P Q `{!Plain P} : (P ⊢ Q) → P ⊢ ■ Q.
Proof. by intros <-. Qed.

(* Typeclass instances *)
Global Instance plainly_absorbing P : Absorbing (■ P).
Proof. by rewrite /Absorbing /bi_absorbingly comm plainly_absorb. Qed.
Global Instance plainly_if_absorbing P p :
  Absorbing P → Absorbing (plainly_if p P).
Proof. intros; destruct p; simpl; apply _. Qed.

(* Not an instance, see the bottom of this file *)
Lemma plain_persistent P : Plain P → Persistent P.
Proof. intros. by rewrite /Persistent -plainly_elim_persistently. Qed.

(* Not an instance, see the bottom of this file *)
Lemma impl_persistent P Q :
  Absorbing P → Plain P → Persistent Q → Persistent (P → Q).
Proof.
  intros. by rewrite /Persistent {2}(plain P) -persistently_impl_plainly
                     -(persistent Q) (plainly_elim_absorbingly P) absorbing.
Qed.

Global Instance plainly_persistent P : Persistent (■ P).
Proof. by rewrite /Persistent persistently_plainly. Qed.

Global Instance wand_persistent P Q :
  Plain P → Persistent Q → Absorbing Q → Persistent (P -∗ Q).
Proof.
  intros. rewrite /Persistent {2}(plain P). trans (<pers> (■ P → Q))%I.
  - rewrite -persistently_impl_plainly impl_wand_affinely_plainly -(persistent Q).
    by rewrite affinely_plainly_elim.
  - apply persistently_mono, wand_intro_l. by rewrite sep_and impl_elim_r.
Qed.

(* Instances for big operators *)
Global Instance plainly_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@plainly PROP _).
Proof.
  split; [split|]; try apply _. apply plainly_and. apply plainly_pure.
Qed.

Global Instance plainly_or_homomorphism `{!BiPlainlyExist PROP} :
  MonoidHomomorphism bi_or bi_or (≡) (@plainly PROP _).
Proof.
  split; [split|]; try apply _. apply plainly_or. apply plainly_pure.
Qed.

Global Instance plainly_sep_weak_homomorphism `{!BiPositive PROP, !BiAffine PROP} :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@plainly PROP _).
Proof. split; try apply _. apply plainly_sep. Qed.

Global Instance plainly_sep_homomorphism `{BiAffine PROP} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@plainly PROP _).
Proof. split. apply _. apply plainly_emp. Qed.

Global Instance plainly_sep_entails_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@plainly PROP _).
Proof. split; try apply _. intros P Q; by rewrite plainly_sep_2. Qed.

Global Instance plainly_sep_entails_homomorphism `{!BiAffine PROP} :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@plainly PROP _).
Proof. split. apply _. simpl. rewrite plainly_emp. done. Qed.

Global Instance limit_preserving_Plain {A:ofeT} `{Cofe A} (Φ : A → PROP) :
  NonExpansive Φ → LimitPreserving (λ x, Plain (Φ x)).
Proof. intros. apply limit_preserving_entails; solve_proper. Qed.

(* Plainness instances *)
Global Instance pure_plain φ : Plain (⌜φ⌝%I : PROP).
Proof. by rewrite /Plain plainly_pure. Qed.
Global Instance emp_plain : Plain (PROP:=PROP) emp.
Proof. apply plainly_emp_intro. Qed.
Global Instance and_plain P Q : Plain P → Plain Q → Plain (P ∧ Q).
Proof. intros. by rewrite /Plain plainly_and -!plain. Qed.
Global Instance or_plain P Q : Plain P → Plain Q → Plain (P ∨ Q).
Proof. intros. by rewrite /Plain -plainly_or_2 -!plain. Qed.
Global Instance forall_plain {A} (Ψ : A → PROP) :
  (∀ x, Plain (Ψ x)) → Plain (∀ x, Ψ x).
Proof.
  intros. rewrite /Plain plainly_forall. apply forall_mono=> x. by rewrite -plain.
Qed.
Global Instance exist_plain {A} (Ψ : A → PROP) :
  (∀ x, Plain (Ψ x)) → Plain (∃ x, Ψ x).
Proof.
  intros. rewrite /Plain -plainly_exist_2. apply exist_mono=> x. by rewrite -plain.
Qed.

Global Instance impl_plain P Q : Absorbing P → Plain P → Plain Q → Plain (P → Q).
Proof.
  intros. by rewrite /Plain {2}(plain P) -plainly_impl_plainly -(plain Q)
                     (plainly_elim_absorbingly P) absorbing.
Qed.
Global Instance wand_plain P Q :
  Plain P → Plain Q → Absorbing Q → Plain (P -∗ Q).
Proof.
  intros. rewrite /Plain {2}(plain P). trans (■ (■ P → Q))%I.
  - rewrite -plainly_impl_plainly impl_wand_affinely_plainly -(plain Q).
    by rewrite affinely_plainly_elim.
  - apply plainly_mono, wand_intro_l. by rewrite sep_and impl_elim_r.
Qed.
Global Instance sep_plain P Q : Plain P → Plain Q → Plain (P ∗ Q).
Proof. intros. by rewrite /Plain -plainly_sep_2 -!plain. Qed.

Global Instance plainly_plain P : Plain (■ P).
Proof. by rewrite /Plain plainly_idemp. Qed.
Global Instance persistently_plain P : Plain P → Plain (<pers> P).
Proof.
  rewrite /Plain=> HP. rewrite {1}HP plainly_persistently persistently_plainly //.
Qed.
Global Instance affinely_plain P : Plain P → Plain (<affine> P).
Proof. rewrite /bi_affinely. apply _. Qed.
Global Instance intuitionistically_plain P : Plain P → Plain (□ P).
Proof. rewrite /bi_intuitionistically. apply _. Qed.
Global Instance absorbingly_plain P : Plain P → Plain (<absorb> P).
Proof. rewrite /bi_absorbingly. apply _. Qed.
Global Instance from_option_plain {A} P (Ψ : A → PROP) (mx : option A) :
  (∀ x, Plain (Ψ x)) → Plain P → Plain (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* Interaction with equality *)
Lemma plainly_internal_eq {A:ofeT} (a b : A) : plainly (A:=PROP) (a ≡ b) ⊣⊢ a ≡ b.
Proof.
  apply (anti_symm (⊢)).
  { by rewrite plainly_elim. }
  apply (internal_eq_rewrite' a b (λ  b, ■ (a ≡ b))%I); [solve_proper|done|].
  rewrite -(internal_eq_refl True%I a) plainly_pure; auto.
Qed.

Lemma plainly_alt P : ■ P ⊣⊢ <affine> P ≡ emp.
Proof.
  rewrite -plainly_affinely. apply (anti_symm (⊢)).
  - rewrite -prop_ext. apply plainly_mono, and_intro; apply wand_intro_l.
    + by rewrite affinely_elim_emp left_id.
    + by rewrite left_id.
  - rewrite internal_eq_sym (internal_eq_rewrite _ _ plainly).
    by rewrite -plainly_True_emp plainly_pure True_impl.
Qed.

Lemma plainly_alt_absorbing P `{!Absorbing P} : ■ P ⊣⊢ P ≡ True.
Proof.
  apply (anti_symm (⊢)).
  - rewrite -prop_ext. apply plainly_mono, and_intro; apply wand_intro_l; auto.
  - rewrite internal_eq_sym (internal_eq_rewrite _ _ plainly).
    by rewrite plainly_pure True_impl.
Qed.

Lemma plainly_True_alt P : ■ (True -∗ P) ⊣⊢ P ≡ True.
Proof.
  apply (anti_symm (⊢)).
  - rewrite -prop_ext. apply plainly_mono, and_intro; apply wand_intro_l; auto.
    by rewrite wand_elim_r.
  - rewrite internal_eq_sym (internal_eq_rewrite _ _
      (λ Q, ■ (True -∗ Q))%I ltac:(shelve)); last solve_proper.
    by rewrite -entails_wand // -(plainly_emp_intro True%I) True_impl.
Qed.

(* Interaction with ▷ *)
Lemma later_plainly P : ▷ ■ P ⊣⊢ ■ ▷ P.
Proof. apply (anti_symm _); auto using later_plainly_1, later_plainly_2. Qed.
Lemma laterN_plainly n P : ▷^n ■ P ⊣⊢ ■ ▷^n P.
Proof. induction n as [|n IH]; simpl; auto. by rewrite IH later_plainly. Qed.

Lemma later_plainly_if p P : ▷ ■?p P ⊣⊢ ■?p ▷ P.
Proof. destruct p; simpl; auto using later_plainly. Qed.
Lemma laterN_plainly_if n p P : ▷^n ■?p P ⊣⊢ ■?p (▷^n P).
Proof. destruct p; simpl; auto using laterN_plainly. Qed.

Lemma except_0_plainly_1 P : ◇ ■ P ⊢ ■ ◇ P.
Proof. by rewrite /sbi_except_0 -plainly_or_2 -later_plainly plainly_pure. Qed.
Lemma except_0_plainly `{!BiPlainlyExist PROP} P : ◇ ■ P ⊣⊢ ■ ◇ P.
Proof. by rewrite /sbi_except_0 plainly_or -later_plainly plainly_pure. Qed.

Global Instance internal_eq_plain {A : ofeT} (a b : A) :
  Plain (a ≡ b : PROP)%I.
Proof. by intros; rewrite /Plain plainly_internal_eq. Qed.

Global Instance later_plain P : Plain P → Plain (▷ P).
Proof. intros. by rewrite /Plain -later_plainly {1}(plain P). Qed.
Global Instance laterN_plain n P : Plain P → Plain (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance except_0_plain P : Plain P → Plain (◇ P).
Proof. rewrite /sbi_except_0; apply _. Qed.

Global Instance plainly_timeless P  `{!BiPlainlyExist PROP} :
  Timeless P → Timeless (■ P).
Proof.
  intros. rewrite /Timeless /sbi_except_0 later_plainly_1.
  by rewrite (timeless P) /sbi_except_0 plainly_or {1}plainly_elim.
Qed.
End plainly_derived.

(* When declared as an actual instance, [plain_persistent] will cause
failing proof searches to take exponential time, as Coq will try to
apply it the instance at any node in the proof search tree.

To avoid that, we declare it using a [Hint Immediate], so that it will
only be used at the leaves of the proof search tree, i.e. when the
premise of the hint can be derived from just the current context. *)
Hint Immediate plain_persistent : typeclass_instances.

(* Not defined using an ordinary [Instance] because the default
[class_apply @impl_persistent] shelves the [BiPlainly] premise, making proof
search for the other premises fail. See the proof of [coreP_persistent] for an
example where it would fail with a regular [Instance].*)
Hint Extern 4 (Persistent (_ → _)) => eapply @impl_persistent : typeclass_instances.
