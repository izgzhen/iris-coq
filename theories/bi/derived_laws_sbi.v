From iris.bi Require Export derived_laws_bi.
From iris.algebra Require Import monoid.
From stdpp Require Import hlist.

Module bi.
Import interface.bi.
Import derived_laws_bi.bi.
Section sbi_derived.
Context {PROP : sbi}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.
Implicit Types Ps : list PROP.
Implicit Types A : Type.

(* Force implicit argument PROP *)
Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

Hint Resolve or_elim or_intro_l' or_intro_r' True_intro False_elim.
Hint Resolve and_elim_l' and_elim_r' and_intro forall_intro.

Global Instance internal_eq_proper (A : ofeT) :
  Proper ((≡) ==> (≡) ==> (⊣⊢)) (@sbi_internal_eq PROP A) := ne_proper_2 _.
Global Instance later_proper :
  Proper ((⊣⊢) ==> (⊣⊢)) (@sbi_later PROP) := ne_proper _.

(* Equality *)
Hint Resolve internal_eq_refl.
Hint Extern 100 (NonExpansive _) => solve_proper.

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

Lemma pure_internal_eq {A : ofeT} (x y : A) : ⌜x ≡ y⌝ ⊢ x ≡ y.
Proof. apply pure_elim'=> ->. apply internal_eq_refl. Qed.
Lemma discrete_eq {A : ofeT} (a b : A) : Discrete a → a ≡ b ⊣⊢ ⌜a ≡ b⌝.
Proof.
  intros. apply (anti_symm _); auto using discrete_eq_1, pure_internal_eq.
Qed.

Lemma absorbingly_internal_eq {A : ofeT} (x y : A) : <absorb> (x ≡ y) ⊣⊢ x ≡ y.
Proof.
  apply (anti_symm _), absorbingly_intro.
  apply wand_elim_r', (internal_eq_rewrite' x y (λ y, True -∗ x ≡ y)%I); auto.
  apply wand_intro_l, internal_eq_refl.
Qed.
Lemma persistently_internal_eq {A : ofeT} (a b : A) : <pers> (a ≡ b) ⊣⊢ a ≡ b.
Proof.
  apply (anti_symm (⊢)).
  { by rewrite persistently_into_absorbingly absorbingly_internal_eq. }
  apply (internal_eq_rewrite' a b (λ b, <pers> (a ≡ b))%I); auto.
  rewrite -(internal_eq_refl emp%I a). apply persistently_emp_intro.
Qed.

Global Instance internal_eq_absorbing {A : ofeT} (x y : A) :
  Absorbing (PROP:=PROP) (x ≡ y).
Proof. by rewrite /Absorbing absorbingly_internal_eq. Qed.
Global Instance internal_eq_persistent {A : ofeT} (a b : A) :
  Persistent (PROP:=PROP) (a ≡ b).
Proof. by intros; rewrite /Persistent persistently_internal_eq. Qed.

(* Equality under a later. *)
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
Global Instance later_mono' : Proper ((⊢) ==> (⊢)) (@sbi_later PROP).
Proof. intros P Q; apply later_mono. Qed.
Global Instance later_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@sbi_later PROP).
Proof. intros P Q; apply later_mono. Qed.

Lemma later_True : ▷ True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using later_intro. Qed.
Lemma later_emp `{!BiAffine PROP} : ▷ emp ⊣⊢ emp.
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
Lemma later_persistently P : ▷ <pers> P ⊣⊢ <pers> ▷ P.
Proof. apply (anti_symm _); auto using later_persistently_1, later_persistently_2. Qed.
Lemma later_affinely_2 P : <affine> ▷ P ⊢ ▷ <affine> P.
Proof. rewrite /bi_affinely later_and. auto using later_intro. Qed.
Lemma later_intuitionistically_2 P : □ ▷ P ⊢ ▷ □ P.
Proof. by rewrite /bi_intuitionistically -later_persistently later_affinely_2. Qed.
Lemma later_intuitionistically_if_2 p P : □?p ▷ P ⊢ ▷ □?p P.
Proof. destruct p; simpl; auto using later_intuitionistically_2. Qed.
Lemma later_absorbingly P : ▷ <absorb> P ⊣⊢ <absorb> ▷ P.
Proof. by rewrite /bi_absorbingly later_sep later_True. Qed.

Global Instance later_persistent P : Persistent P → Persistent (▷ P).
Proof. intros. by rewrite /Persistent -later_persistently {1}(persistent P). Qed.
Global Instance later_absorbing P : Absorbing P → Absorbing (▷ P).
Proof. intros ?. by rewrite /Absorbing -later_absorbingly absorbing. Qed.

Section löb.
  (* Proof following https://en.wikipedia.org/wiki/L%C3%B6b's_theorem#Proof_of_L%C3%B6b's_theorem *)
  Definition flöb_pre (P Ψ : PROP) : PROP := (▷ Ψ → P)%I.

  Local Instance flöb_pre_contractive P : Contractive (flöb_pre P).
  Proof. solve_contractive. Qed.

  Context `{Cofe PROP}.

  Definition flöb (P : PROP) := fixpoint (flöb_pre P).

  Lemma weak_löb P : (▷ P ⊢ P) → (True ⊢ P).
  Proof.
    set (Ψ := flöb P). assert (Ψ ⊣⊢ (▷ Ψ → P)) as HΨ.
    { exact: fixpoint_unfold. }
    intros HP. rewrite -HP.
    assert (Ψ ⊢ (▷ Ψ → P)) as HΨ'%entails_impl_True by by rewrite -HΨ.
    rewrite ->(later_intro (Ψ → _))%I in HΨ'.
    rewrite ->later_impl in HΨ'.
    rewrite ->later_impl in HΨ'.
    assert (▷ Ψ ⊢ P) as HΨP.
    { rewrite -HP. rewrite -(idemp (∧) (▷ Ψ))%I {2}(later_intro (▷ Ψ))%I.
      apply impl_elim_l', entails_impl_True. done. }
    rewrite -HΨP HΨ -2!later_intro.
    apply (entails_impl_True _ P). done.
  Qed.

  Lemma löb P : (▷ P → P) ⊢ P.
  Proof.
    apply entails_impl_True, weak_löb. apply impl_intro_r.
    rewrite -{2}(idemp (∧) (▷ P → P))%I.
    rewrite {2}(later_intro (▷ P → P))%I.
    rewrite later_impl.
    rewrite assoc impl_elim_l.
    rewrite impl_elim_r. done.
  Qed.

End löb.

(* Iterated later modality *)
Global Instance laterN_ne m : NonExpansive (@sbi_laterN PROP m).
Proof. induction m; simpl. by intros ???. solve_proper. Qed.
Global Instance laterN_proper m :
  Proper ((⊣⊢) ==> (⊣⊢)) (@sbi_laterN PROP m) := ne_proper _.

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
Global Instance laterN_mono' n : Proper ((⊢) ==> (⊢)) (@sbi_laterN PROP n).
Proof. intros P Q; apply laterN_mono. Qed.
Global Instance laterN_flip_mono' n :
  Proper (flip (⊢) ==> flip (⊢)) (@sbi_laterN PROP n).
Proof. intros P Q; apply laterN_mono. Qed.

Lemma laterN_intro n P : P ⊢ ▷^n P.
Proof. induction n as [|n IH]; simpl; by rewrite -?later_intro. Qed.

Lemma laterN_True n : ▷^n True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using laterN_intro, True_intro. Qed.
Lemma laterN_emp `{!BiAffine PROP} n : ▷^n emp ⊣⊢ emp.
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
Lemma laterN_persistently n P : ▷^n <pers> P ⊣⊢ <pers> ▷^n P.
Proof. induction n as [|n IH]; simpl; auto. by rewrite IH later_persistently. Qed.
Lemma laterN_affinely_2 n P : <affine> ▷^n P ⊢ ▷^n <affine> P.
Proof. rewrite /bi_affinely laterN_and. auto using laterN_intro. Qed.
Lemma laterN_intuitionistically_2 n P : □ ▷^n P ⊢ ▷^n □ P.
Proof. by rewrite /bi_intuitionistically -laterN_persistently laterN_affinely_2. Qed.
Lemma laterN_intuitionistically_if_2 n p P : □?p ▷^n P ⊢ ▷^n □?p P.
Proof. destruct p; simpl; auto using laterN_intuitionistically_2. Qed.
Lemma laterN_absorbingly n P : ▷^n <absorb> P ⊣⊢ <absorb> ▷^n P.
Proof. by rewrite /bi_absorbingly laterN_sep laterN_True. Qed.

Global Instance laterN_persistent n P : Persistent P → Persistent (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance laterN_absorbing n P : Absorbing P → Absorbing (▷^n P).
Proof. induction n; apply _. Qed.

(* Except-0 *)
Global Instance except_0_ne : NonExpansive (@sbi_except_0 PROP).
Proof. solve_proper. Qed.
Global Instance except_0_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@sbi_except_0 PROP).
Proof. solve_proper. Qed.
Global Instance except_0_mono' : Proper ((⊢) ==> (⊢)) (@sbi_except_0 PROP).
Proof. solve_proper. Qed.
Global Instance except_0_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@sbi_except_0 PROP).
Proof. solve_proper. Qed.

Lemma except_0_intro P : P ⊢ ◇ P.
Proof. rewrite /sbi_except_0; auto. Qed.
Lemma except_0_mono P Q : (P ⊢ Q) → ◇ P ⊢ ◇ Q.
Proof. by intros ->. Qed.
Lemma except_0_idemp P : ◇ ◇ P ⊣⊢ ◇ P.
Proof. apply (anti_symm _); rewrite /sbi_except_0; auto. Qed.

Lemma except_0_True : ◇ True ⊣⊢ True.
Proof. rewrite /sbi_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_emp `{!BiAffine PROP} : ◇ emp ⊣⊢ emp.
Proof. by rewrite -True_emp except_0_True. Qed.
Lemma except_0_or P Q : ◇ (P ∨ Q) ⊣⊢ ◇ P ∨ ◇ Q.
Proof. rewrite /sbi_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_and P Q : ◇ (P ∧ Q) ⊣⊢ ◇ P ∧ ◇ Q.
Proof. by rewrite /sbi_except_0 or_and_l. Qed.
Lemma except_0_sep P Q : ◇ (P ∗ Q) ⊣⊢ ◇ P ∗ ◇ Q.
Proof.
  rewrite /sbi_except_0. apply (anti_symm _).
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
Proof. by rewrite /sbi_except_0 -later_or False_or. Qed.
Lemma except_0_persistently P : ◇ <pers> P ⊣⊢ <pers> ◇ P.
Proof.
  by rewrite /sbi_except_0 persistently_or -later_persistently persistently_pure.
Qed.
Lemma except_0_affinely_2 P : <affine> ◇ P ⊢ ◇ <affine> P.
Proof. rewrite /bi_affinely except_0_and. auto using except_0_intro. Qed.
Lemma except_0_intuitionistically_2 P : □ ◇ P ⊢ ◇ □ P.
Proof. by rewrite /bi_intuitionistically -except_0_persistently except_0_affinely_2. Qed.
Lemma except_0_intuitionistically_if_2 p P : □?p ◇ P ⊢ ◇ □?p P.
Proof. destruct p; simpl; auto using except_0_intuitionistically_2. Qed.
Lemma except_0_absorbingly P : ◇ <absorb> P ⊣⊢ <absorb> ◇ P.
Proof. by rewrite /bi_absorbingly except_0_sep except_0_True. Qed.

Lemma except_0_frame_l P Q : P ∗ ◇ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro P) except_0_sep. Qed.
Lemma except_0_frame_r P Q : ◇ P ∗ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro Q) except_0_sep. Qed.

Lemma later_affinely_1 `{!Timeless (PROP:=PROP) emp} P : ▷ <affine> P ⊢ ◇ <affine> ▷ P.
Proof.
  rewrite /bi_affinely later_and (timeless emp%I) except_0_and.
  by apply and_mono, except_0_intro.
Qed.

Global Instance except_0_persistent P : Persistent P → Persistent (◇ P).
Proof. rewrite /sbi_except_0; apply _. Qed.
Global Instance except_0_absorbing P : Absorbing P → Absorbing (◇ P).
Proof. rewrite /sbi_except_0; apply _. Qed.

(* Timeless instances *)
Global Instance Timeless_proper : Proper ((≡) ==> iff) (@Timeless PROP).
Proof. solve_proper. Qed.

Global Instance pure_timeless φ : Timeless (PROP:=PROP) ⌜φ⌝.
Proof.
  rewrite /Timeless /sbi_except_0 pure_alt later_exist_false.
  apply or_elim, exist_elim; [auto|]=> Hφ. rewrite -(exist_intro Hφ). auto.
Qed.
Global Instance emp_timeless `{BiAffine PROP} : Timeless (PROP:=PROP) emp.
Proof. rewrite -True_emp. apply _. Qed.

Global Instance and_timeless P Q : Timeless P → Timeless Q → Timeless (P ∧ Q).
Proof. intros; rewrite /Timeless except_0_and later_and; auto. Qed.
Global Instance or_timeless P Q : Timeless P → Timeless Q → Timeless (P ∨ Q).
Proof. intros; rewrite /Timeless except_0_or later_or; auto. Qed.

Global Instance impl_timeless `{Cofe PROP} P Q : Timeless Q → Timeless (P → Q).
Proof.
  rewrite /Timeless=> HQ. rewrite later_false_em.
  apply or_mono, impl_intro_l; first done.
  rewrite -{2}(löb Q); apply impl_intro_l.
  rewrite HQ /sbi_except_0 !and_or_r. apply or_elim; last auto.
  by rewrite assoc (comm _ _ P) -assoc !impl_elim_r.
Qed.
Global Instance sep_timeless P Q: Timeless P → Timeless Q → Timeless (P ∗ Q).
Proof.
  intros; rewrite /Timeless except_0_sep later_sep; auto using sep_mono.
Qed.

Global Instance wand_timeless `{Cofe PROP} P Q : Timeless Q → Timeless (P -∗ Q).
Proof.
  rewrite /Timeless=> HQ. rewrite later_false_em.
  apply or_mono, wand_intro_l; first done.
  rewrite -{2}(löb Q); apply impl_intro_l.
  rewrite HQ /sbi_except_0 !and_or_r. apply or_elim; last auto.
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
  - rewrite /sbi_except_0; auto.
  - apply exist_elim=> x. rewrite -(exist_intro x); auto.
Qed.
Global Instance persistently_timeless P : Timeless P → Timeless (<pers> P).
Proof.
  intros. rewrite /Timeless /sbi_except_0 later_persistently_1.
  by rewrite (timeless P) /sbi_except_0 persistently_or {1}persistently_elim.
Qed.

Global Instance affinely_timeless P :
  Timeless (PROP:=PROP) emp → Timeless P → Timeless (<affine> P).
Proof. rewrite /bi_affinely; apply _. Qed.
Global Instance absorbingly_timeless P : Timeless P → Timeless (<absorb> P).
Proof. rewrite /bi_absorbingly; apply _. Qed.

Global Instance eq_timeless {A : ofeT} (a b : A) :
  Discrete a → Timeless (PROP:=PROP) (a ≡ b).
Proof. intros. rewrite /Discrete !discrete_eq. apply (timeless _). Qed.
Global Instance from_option_timeless {A} P (Ψ : A → PROP) (mx : option A) :
  (∀ x, Timeless (Ψ x)) → Timeless P → Timeless (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* Big op stuff *)
Global Instance sbi_later_monoid_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@sbi_later PROP).
Proof. split; [split|]; try apply _. apply later_and. apply later_True. Qed.
Global Instance sbi_laterN_and_homomorphism n :
  MonoidHomomorphism bi_and bi_and (≡) (@sbi_laterN PROP n).
Proof. split; [split|]; try apply _. apply laterN_and. apply laterN_True. Qed.
Global Instance sbi_except_0_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@sbi_except_0 PROP).
Proof. split; [split|]; try apply _. apply except_0_and. apply except_0_True. Qed.

Global Instance sbi_later_monoid_or_homomorphism :
  WeakMonoidHomomorphism bi_or bi_or (≡) (@sbi_later PROP).
Proof. split; try apply _. apply later_or. Qed.
Global Instance sbi_laterN_or_homomorphism n :
  WeakMonoidHomomorphism bi_or bi_or (≡) (@sbi_laterN PROP n).
Proof. split; try apply _. apply laterN_or. Qed.
Global Instance sbi_except_0_or_homomorphism :
  WeakMonoidHomomorphism bi_or bi_or (≡) (@sbi_except_0 PROP).
Proof. split; try apply _. apply except_0_or. Qed.

Global Instance sbi_later_monoid_sep_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@sbi_later PROP).
Proof. split; try apply _. apply later_sep. Qed.
Global Instance sbi_laterN_sep_weak_homomorphism n :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@sbi_laterN PROP n).
Proof. split; try apply _. apply laterN_sep. Qed.
Global Instance sbi_except_0_sep_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@sbi_except_0 PROP).
Proof. split; try apply _. apply except_0_sep. Qed.

Global Instance sbi_later_monoid_sep_homomorphism `{!BiAffine PROP} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@sbi_later PROP).
Proof. split; try apply _. apply later_emp. Qed.
Global Instance sbi_laterN_sep_homomorphism `{!BiAffine PROP} n :
  MonoidHomomorphism bi_sep bi_sep (≡) (@sbi_laterN PROP n).
Proof. split; try apply _. apply laterN_emp. Qed.
Global Instance sbi_except_0_sep_homomorphism `{!BiAffine PROP} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@sbi_except_0 PROP).
Proof. split; try apply _. apply except_0_emp. Qed.

Global Instance sbi_later_monoid_sep_entails_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@sbi_later PROP).
Proof. split; try apply _. intros P Q. by rewrite later_sep. Qed.
Global Instance sbi_laterN_sep_entails_weak_homomorphism n :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@sbi_laterN PROP n).
Proof. split; try apply _. intros P Q. by rewrite laterN_sep. Qed.
Global Instance sbi_except_0_sep_entails_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@sbi_except_0 PROP).
Proof. split; try apply _. intros P Q. by rewrite except_0_sep. Qed.

Global Instance sbi_later_monoid_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@sbi_later PROP).
Proof. split; try apply _. apply later_intro. Qed.
Global Instance sbi_laterN_sep_entails_homomorphism n :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@sbi_laterN PROP n).
Proof. split; try apply _. apply laterN_intro. Qed.
Global Instance sbi_except_0_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@sbi_except_0 PROP).
Proof. split; try apply _. apply except_0_intro. Qed.
End sbi_derived.
End bi.
