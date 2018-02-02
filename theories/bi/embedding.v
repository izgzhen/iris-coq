From iris.algebra Require Import monoid.
From iris.bi Require Import interface derived_laws big_op.
From stdpp Require Import hlist.

(* Embeddings are often used to *define* the connectives of the
   domain BI. Hence we cannot ask it to verify the properties of
   embeddings. *)
Class BiEmbed (A B : Type) := bi_embed : A → B.
Arguments bi_embed {_ _ _} _%I : simpl never.
Notation "⎡ P ⎤" := (bi_embed P) : bi_scope.
Instance: Params (@bi_embed) 3.
Typeclasses Opaque bi_embed.

Hint Mode BiEmbed ! - : typeclass_instances.
Hint Mode BiEmbed - ! : typeclass_instances.

Class BiEmbedding (PROP1 PROP2 : bi) `{BiEmbed PROP1 PROP2} := {
  bi_embed_ne :> NonExpansive bi_embed;
  bi_embed_mono :> Proper ((⊢) ==> (⊢)) bi_embed;
  bi_embed_entails_inj :> Inj (⊢) (⊢) bi_embed;
  bi_embed_emp : ⎡emp⎤ ⊣⊢ emp;
  bi_embed_impl_2 P Q : (⎡P⎤ → ⎡Q⎤) ⊢ ⎡P → Q⎤;
  bi_embed_forall_2 A (Φ : A → PROP1) : (∀ x, ⎡Φ x⎤) ⊢ ⎡∀ x, Φ x⎤;
  bi_embed_exist_1 A (Φ : A → PROP1) : ⎡∃ x, Φ x⎤ ⊢ ∃ x, ⎡Φ x⎤;
  bi_embed_sep P Q : ⎡P ∗ Q⎤ ⊣⊢ ⎡P⎤ ∗ ⎡Q⎤;
  bi_embed_wand_2 P Q : (⎡P⎤ -∗ ⎡Q⎤) ⊢ ⎡P -∗ Q⎤;
  bi_embed_plainly P : ⎡bi_plainly P⎤ ⊣⊢ bi_plainly ⎡P⎤;
  bi_embed_persistently P : ⎡bi_persistently P⎤ ⊣⊢ bi_persistently ⎡P⎤
}.

Class SbiEmbedding (PROP1 PROP2 : sbi) `{BiEmbed PROP1 PROP2} := {
  sbi_embed_bi_embed :> BiEmbedding PROP1 PROP2;
  sbi_embed_internal_eq_1 (A : ofeT) (x y : A) : ⎡x ≡ y⎤ ⊢ x ≡ y;
  sbi_embed_later P : ⎡▷ P⎤ ⊣⊢ ▷ ⎡P⎤
}.

Section bi_embedding.
  Context `{BiEmbedding PROP1 PROP2}.
  Local Notation bi_embed := (bi_embed (A:=PROP1) (B:=PROP2)).
  Local Notation "⎡ P ⎤" := (bi_embed P) : bi_scope.
  Implicit Types P Q R : PROP1.

  Global Instance bi_embed_proper : Proper ((≡) ==> (≡)) bi_embed.
  Proof. apply (ne_proper _). Qed.
  Global Instance bi_embed_mono_flip : Proper (flip (⊢) ==> flip (⊢)) bi_embed.
  Proof. solve_proper. Qed.
  Global Instance bi_embed_inj : Inj (≡) (≡) bi_embed.
  Proof.
    intros P Q EQ. apply bi.equiv_spec, conj; apply (inj bi_embed);
    rewrite EQ //.
  Qed.

  Lemma bi_embed_valid (P : PROP1) : ⎡P⎤%I ↔ P.
  Proof.
    by rewrite /bi_valid -bi_embed_emp; split=>?; [apply (inj bi_embed)|f_equiv].
  Qed.

  Lemma bi_embed_forall A (Φ : A → PROP1) : ⎡∀ x, Φ x⎤ ⊣⊢ ∀ x, ⎡Φ x⎤.
  Proof.
    apply bi.equiv_spec; split; [|apply bi_embed_forall_2].
    apply bi.forall_intro=>?. by rewrite bi.forall_elim.
  Qed.
  Lemma bi_embed_exist A (Φ : A → PROP1) : ⎡∃ x, Φ x⎤ ⊣⊢ ∃ x, ⎡Φ x⎤.
  Proof.
    apply bi.equiv_spec; split; [apply bi_embed_exist_1|].
    apply bi.exist_elim=>?. by rewrite -bi.exist_intro.
  Qed.
  Lemma bi_embed_and P Q : ⎡P ∧ Q⎤ ⊣⊢ ⎡P⎤ ∧ ⎡Q⎤.
  Proof. rewrite !bi.and_alt bi_embed_forall. by f_equiv=>-[]. Qed.
  Lemma bi_embed_or P Q : ⎡P ∨ Q⎤ ⊣⊢ ⎡P⎤ ∨ ⎡Q⎤.
  Proof. rewrite !bi.or_alt bi_embed_exist. by f_equiv=>-[]. Qed.
  Lemma bi_embed_impl P Q : ⎡P → Q⎤ ⊣⊢ (⎡P⎤ → ⎡Q⎤).
  Proof.
    apply bi.equiv_spec; split; [|apply bi_embed_impl_2].
    apply bi.impl_intro_l. by rewrite -bi_embed_and bi.impl_elim_r.
  Qed.
  Lemma bi_embed_wand P Q : ⎡P -∗ Q⎤ ⊣⊢ (⎡P⎤ -∗ ⎡Q⎤).
  Proof.
    apply bi.equiv_spec; split; [|apply bi_embed_wand_2].
    apply bi.wand_intro_l. by rewrite -bi_embed_sep bi.wand_elim_r.
  Qed.
  Lemma bi_embed_pure φ : ⎡⌜φ⌝⎤ ⊣⊢ ⌜φ⌝.
  Proof.
    rewrite (@bi.pure_alt PROP1) (@bi.pure_alt PROP2) bi_embed_exist.
    do 2 f_equiv. apply bi.equiv_spec. split; [apply bi.True_intro|].
    rewrite -(_ : (emp → emp : PROP1) ⊢ True) ?bi_embed_impl;
      last apply bi.True_intro.
    apply bi.impl_intro_l. by rewrite right_id.
  Qed.
  Lemma bi_embed_iff P Q : ⎡P ↔ Q⎤ ⊣⊢ (⎡P⎤ ↔ ⎡Q⎤).
  Proof. by rewrite bi_embed_and !bi_embed_impl. Qed.
  Lemma bi_embed_wand_iff P Q : ⎡P ∗-∗ Q⎤ ⊣⊢ (⎡P⎤ ∗-∗ ⎡Q⎤).
  Proof. by rewrite bi_embed_and !bi_embed_wand. Qed.
  Lemma bi_embed_affinely P : ⎡bi_affinely P⎤ ⊣⊢ bi_affinely ⎡P⎤.
  Proof. by rewrite bi_embed_and bi_embed_emp. Qed.
  Lemma bi_embed_absorbingly P : ⎡bi_absorbingly P⎤ ⊣⊢ bi_absorbingly ⎡P⎤.
  Proof. by rewrite bi_embed_sep bi_embed_pure. Qed.
  Lemma bi_embed_plainly_if P b : ⎡bi_plainly_if b P⎤ ⊣⊢ bi_plainly_if b ⎡P⎤.
  Proof. destruct b; simpl; auto using bi_embed_plainly. Qed.
  Lemma bi_embed_persistently_if P b :
    ⎡bi_persistently_if b P⎤ ⊣⊢ bi_persistently_if b ⎡P⎤.
  Proof. destruct b; simpl; auto using bi_embed_persistently. Qed.
  Lemma bi_embed_affinely_if P b : ⎡bi_affinely_if b P⎤ ⊣⊢ bi_affinely_if b ⎡P⎤.
  Proof. destruct b; simpl; auto using bi_embed_affinely. Qed.
  Lemma bi_embed_hforall {As} (Φ : himpl As PROP1):
    ⎡bi_hforall Φ⎤ ⊣⊢ bi_hforall (hcompose bi_embed Φ).
  Proof. induction As=>//. rewrite /= bi_embed_forall. by do 2 f_equiv. Qed.
  Lemma bi_embed_hexist {As} (Φ : himpl As PROP1):
    ⎡bi_hexist Φ⎤ ⊣⊢ bi_hexist (hcompose bi_embed Φ).
  Proof. induction As=>//. rewrite /= bi_embed_exist. by do 2 f_equiv. Qed.

  Global Instance bi_embed_plain P : Plain P → Plain ⎡P⎤.
  Proof. intros ?. by rewrite /Plain -bi_embed_plainly -plain. Qed.
  Global Instance bi_embed_persistent P : Persistent P → Persistent ⎡P⎤.
  Proof. intros ?. by rewrite /Persistent -bi_embed_persistently -persistent. Qed.
  Global Instance bi_embed_affine P : Affine P → Affine ⎡P⎤.
  Proof. intros ?. by rewrite /Affine (affine P) bi_embed_emp. Qed.
  Global Instance bi_embed_absorbing P : Absorbing P → Absorbing ⎡P⎤.
  Proof. intros ?. by rewrite /Absorbing -bi_embed_absorbingly absorbing. Qed.

  Global Instance bi_embed_and_homomorphism :
    MonoidHomomorphism bi_and bi_and (≡) bi_embed.
  Proof.
    by split; [split|]; try apply _;
      [setoid_rewrite bi_embed_and|rewrite bi_embed_pure].
  Qed.
  Global Instance bi_embed_or_homomorphism :
    MonoidHomomorphism bi_or bi_or (≡) bi_embed.
  Proof.
    by split; [split|]; try apply _;
      [setoid_rewrite bi_embed_or|rewrite bi_embed_pure].
  Qed.
  Global Instance bi_embed_sep_homomorphism :
    MonoidHomomorphism bi_sep bi_sep (≡) bi_embed.
  Proof.
    by split; [split|]; try apply _;
      [setoid_rewrite bi_embed_sep|rewrite bi_embed_emp].
  Qed.

  Lemma bi_embed_big_sepL {A} (Φ : nat → A → PROP1) l :
    ⎡[∗ list] k↦x ∈ l, Φ k x⎤ ⊣⊢ [∗ list] k↦x ∈ l, ⎡Φ k x⎤.
  Proof. apply (big_opL_commute _). Qed.
  Lemma bi_embed_big_sepM `{Countable K} {A} (Φ : K → A → PROP1) (m : gmap K A) :
    ⎡[∗ map] k↦x ∈ m, Φ k x⎤ ⊣⊢ [∗ map] k↦x ∈ m, ⎡Φ k x⎤.
  Proof. apply (big_opM_commute _). Qed.
  Lemma bi_embed_big_sepS `{Countable A} (Φ : A → PROP1) (X : gset A) :
    ⎡[∗ set] y ∈ X, Φ y⎤ ⊣⊢ [∗ set] y ∈ X, ⎡Φ y⎤.
  Proof. apply (big_opS_commute _). Qed.
  Lemma bi_embed_big_sepMS `{Countable A} (Φ : A → PROP1) (X : gmultiset A) :
    ⎡[∗ mset] y ∈ X, Φ y⎤ ⊣⊢ [∗ mset] y ∈ X, ⎡Φ y⎤.
  Proof. apply (big_opMS_commute _). Qed.
End bi_embedding.

Section sbi_embedding.
  Context `{SbiEmbedding PROP1 PROP2}.
  Implicit Types P Q R : PROP1.

  Lemma sbi_embed_internal_eq (A : ofeT) (x y : A) : ⎡x ≡ y⎤ ⊣⊢ x ≡ y.
  Proof.
    apply bi.equiv_spec; split; [apply sbi_embed_internal_eq_1|].
    etrans; [apply (bi.internal_eq_rewrite x y (λ y, ⎡x ≡ y⎤%I)); solve_proper|].
    rewrite -(bi.internal_eq_refl True%I) bi_embed_pure.
    eapply bi.impl_elim; [done|]. apply bi.True_intro.
  Qed.
  Lemma sbi_embed_laterN n P : ⎡▷^n P⎤ ⊣⊢ ▷^n ⎡P⎤.
  Proof. induction n=>//=. rewrite sbi_embed_later. by f_equiv. Qed.
  Lemma sbi_embed_except_0 P : ⎡◇ P⎤ ⊣⊢ ◇ ⎡P⎤.
  Proof. by rewrite bi_embed_or sbi_embed_later bi_embed_pure. Qed.

  Global Instance sbi_embed_timeless P : Timeless P → Timeless ⎡P⎤.
  Proof.
    intros ?. by rewrite /Timeless -sbi_embed_except_0 -sbi_embed_later timeless.
  Qed.
End sbi_embedding.
