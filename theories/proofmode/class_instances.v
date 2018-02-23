From stdpp Require Import nat_cancel.
From iris.bi Require Import bi tactics.
From iris.proofmode Require Export classes.
Set Default Proof Using "Type".
Import bi.

Section always_modalities.
  Context {PROP : bi}.
  Lemma always_modality_persistently_mixin :
    always_modality_mixin (@bi_persistently PROP) AIEnvId AIEnvClear.
  Proof.
    split; eauto using equiv_entails_sym, persistently_intro, persistently_mono,
      persistently_and, persistently_sep_2 with typeclass_instances.
  Qed.
  Definition always_modality_persistently :=
    AlwaysModality _ always_modality_persistently_mixin.

  Lemma always_modality_affinely_mixin :
    always_modality_mixin (@bi_affinely PROP) AIEnvId (AIEnvForall Affine).
  Proof.
    split; eauto using equiv_entails_sym, affinely_intro, affinely_mono,
      affinely_and, affinely_sep_2 with typeclass_instances.
  Qed.
  Definition always_modality_affinely :=
    AlwaysModality _ always_modality_affinely_mixin.

  Lemma always_modality_affinely_persistently_mixin :
    always_modality_mixin (λ P : PROP, □ P)%I AIEnvId AIEnvIsEmpty.
  Proof.
    split; eauto using equiv_entails_sym, affinely_persistently_emp,
      affinely_mono, persistently_mono, affinely_persistently_idemp,
      affinely_persistently_and, affinely_persistently_sep_2 with typeclass_instances.
  Qed.
  Definition always_modality_affinely_persistently :=
    AlwaysModality _ always_modality_affinely_persistently_mixin.

  Lemma always_modality_plainly_mixin :
    always_modality_mixin (@bi_plainly PROP) (AIEnvForall Plain) AIEnvClear.
  Proof.
    split; eauto using equiv_entails_sym, plainly_intro, plainly_mono,
      plainly_and, plainly_sep_2 with typeclass_instances.
  Qed.
  Definition always_modality_plainly :=
    AlwaysModality _ always_modality_plainly_mixin.

  Lemma always_modality_affinely_plainly_mixin :
    always_modality_mixin (λ P : PROP, ■ P)%I (AIEnvForall Plain) AIEnvIsEmpty.
  Proof.
    split; eauto using equiv_entails_sym, affinely_plainly_emp, affinely_intro,
      plainly_intro, affinely_mono, plainly_mono, affinely_plainly_idemp,
      affinely_plainly_and, affinely_plainly_sep_2 with typeclass_instances.
  Qed.
  Definition always_modality_affinely_plainly :=
    AlwaysModality _ always_modality_affinely_plainly_mixin.
End always_modalities.

Section bi_instances.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

(* FromAffinely *)
Global Instance from_affinely_affine P : Affine P → FromAffinely P P.
Proof. intros. by rewrite /FromAffinely affinely_elim. Qed.
Global Instance from_affinely_default P : FromAffinely (bi_affinely P) P | 100.
Proof. by rewrite /FromAffinely. Qed.

(* IntoAbsorbingly *)
Global Instance into_absorbingly_True : @IntoAbsorbingly PROP True emp | 0.
Proof. by rewrite /IntoAbsorbingly -absorbingly_True_emp absorbingly_pure. Qed.
Global Instance into_absorbingly_absorbing P : Absorbing P → IntoAbsorbingly P P | 1.
Proof. intros. by rewrite /IntoAbsorbingly absorbing_absorbingly. Qed.
Global Instance into_absorbingly_default P : IntoAbsorbingly (bi_absorbingly P) P | 100.
Proof. by rewrite /IntoAbsorbingly. Qed.

(* FromAssumption *)
Global Instance from_assumption_exact p P : FromAssumption p P P | 0.
Proof. by rewrite /FromAssumption /= affinely_persistently_if_elim. Qed.

Global Instance from_assumption_persistently_r P Q :
  FromAssumption true P Q → FromAssumption true P (bi_persistently Q).
Proof.
  rewrite /FromAssumption /= =><-.
  by rewrite -{1}affinely_persistently_idemp affinely_elim.
Qed.
Global Instance from_assumption_affinely_r P Q :
  FromAssumption true P Q → FromAssumption true P (bi_affinely Q).
Proof. rewrite /FromAssumption /= =><-. by rewrite affinely_idemp. Qed.
Global Instance from_assumption_absorbingly_r p P Q :
  FromAssumption p P Q → FromAssumption p P (bi_absorbingly Q).
Proof. rewrite /FromAssumption /= =><-. apply absorbingly_intro. Qed.

Global Instance from_assumption_affinely_plainly_l p P Q :
  FromAssumption true P Q → FromAssumption p (■ P) Q.
Proof.
  rewrite /FromAssumption /= =><-.
  by rewrite affinely_persistently_if_elim plainly_elim_persistently.
Qed.
Global Instance from_assumption_plainly_l_true P Q :
  FromAssumption true P Q → FromAssumption true (bi_plainly P) Q.
Proof.
  rewrite /FromAssumption /= =><-.
  by rewrite persistently_elim plainly_elim_persistently.
Qed.
Global Instance from_assumption_plainly_l_false `{BiAffine PROP} P Q :
  FromAssumption true P Q → FromAssumption false (bi_plainly P) Q.
Proof.
  rewrite /FromAssumption /= =><-.
  by rewrite affine_affinely plainly_elim_persistently.
Qed.
Global Instance from_assumption_affinely_persistently_l p P Q :
  FromAssumption true P Q → FromAssumption p (□ P) Q.
Proof. rewrite /FromAssumption /= =><-. by rewrite affinely_persistently_if_elim. Qed.
Global Instance from_assumption_persistently_l_true P Q :
  FromAssumption true P Q → FromAssumption true (bi_persistently P) Q.
Proof. rewrite /FromAssumption /= =><-. by rewrite persistently_idemp. Qed.
Global Instance from_assumption_persistently_l_false `{BiAffine PROP} P Q :
  FromAssumption true P Q → FromAssumption false (bi_persistently P) Q.
Proof. rewrite /FromAssumption /= =><-. by rewrite affine_affinely. Qed.
Global Instance from_assumption_affinely_l_true p P Q :
  FromAssumption p P Q → FromAssumption p (bi_affinely P) Q.
Proof. rewrite /FromAssumption /= =><-. by rewrite affinely_elim. Qed.

Global Instance from_assumption_forall {A} p (Φ : A → PROP) Q x :
  FromAssumption p (Φ x) Q → FromAssumption p (∀ x, Φ x) Q.
Proof. rewrite /FromAssumption=> <-. by rewrite forall_elim. Qed.

(* IntoPure *)
Global Instance into_pure_pure φ : @IntoPure PROP ⌜φ⌝ φ.
Proof. by rewrite /IntoPure. Qed.

Global Instance into_pure_pure_and (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∧ P2) (φ1 ∧ φ2).
Proof. rewrite /IntoPure pure_and. by intros -> ->. Qed.
Global Instance into_pure_pure_or (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∨ P2) (φ1 ∨ φ2).
Proof. rewrite /IntoPure pure_or. by intros -> ->. Qed.
Global Instance into_pure_pure_impl (φ1 φ2 : Prop) P1 P2 :
  FromPure false P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 → P2) (φ1 → φ2).
Proof. rewrite /FromPure /IntoPure pure_impl=> <- -> //. Qed.

Global Instance into_pure_exist {A} (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, IntoPure (Φ x) (φ x)) → IntoPure (∃ x, Φ x) (∃ x, φ x).
Proof. rewrite /IntoPure=>Hx. rewrite pure_exist. by setoid_rewrite Hx. Qed.
Global Instance into_pure_forall {A} (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, IntoPure (Φ x) (φ x)) → IntoPure (∀ x, Φ x) (∀ x, φ x).
Proof. rewrite /IntoPure=>Hx. rewrite -pure_forall_2. by setoid_rewrite Hx. Qed.

Global Instance into_pure_pure_sep (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∗ P2) (φ1 ∧ φ2).
Proof. rewrite /IntoPure=> -> ->. by rewrite sep_and pure_and. Qed.
Global Instance into_pure_pure_wand (φ1 φ2 : Prop) P1 P2 :
  FromPure true P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 -∗ P2) (φ1 → φ2).
Proof.
  rewrite /FromPure /IntoPure=> <- -> /=.
  rewrite pure_impl -impl_wand_2. apply bi.wand_intro_l.
  rewrite {1}(persistent_absorbingly_affinely ⌜φ1⌝%I) absorbingly_sep_l
          bi.wand_elim_r absorbing //.
Qed.

Global Instance into_pure_affinely P φ :
  IntoPure P φ → IntoPure (bi_affinely P) φ.
Proof. rewrite /IntoPure=> ->. apply affinely_elim. Qed.
Global Instance into_pure_absorbingly P φ : IntoPure P φ → IntoPure (bi_absorbingly P) φ.
Proof. rewrite /IntoPure=> ->. by rewrite absorbingly_pure. Qed.
Global Instance into_pure_plainly P φ : IntoPure P φ → IntoPure (bi_plainly P) φ.
Proof. rewrite /IntoPure=> ->. apply: plainly_elim. Qed.
Global Instance into_pure_persistently P φ :
  IntoPure P φ → IntoPure (bi_persistently P) φ.
Proof. rewrite /IntoPure=> ->. apply: persistently_elim. Qed.
Global Instance into_pure_embed `{BiEmbedding PROP PROP'} P φ :
  IntoPure P φ → IntoPure ⎡P⎤ φ.
Proof. rewrite /IntoPure=> ->. by rewrite bi_embed_pure. Qed.

(* FromPure *)
Global Instance from_pure_pure a φ : @FromPure PROP a ⌜φ⌝ φ.
Proof. rewrite /FromPure. apply affinely_if_elim. Qed.
Global Instance from_pure_pure_and a (φ1 φ2 : Prop) P1 P2 :
  FromPure a P1 φ1 → FromPure a P2 φ2 → FromPure a (P1 ∧ P2) (φ1 ∧ φ2).
Proof. rewrite /FromPure pure_and=> <- <- /=. by rewrite affinely_if_and. Qed.
Global Instance from_pure_pure_or a (φ1 φ2 : Prop) P1 P2 :
  FromPure a P1 φ1 → FromPure a P2 φ2 → FromPure a (P1 ∨ P2) (φ1 ∨ φ2).
Proof. by rewrite /FromPure pure_or affinely_if_or=><- <-. Qed.
Global Instance from_pure_pure_impl a (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → FromPure a P2 φ2 → FromPure a (P1 → P2) (φ1 → φ2).
Proof.
  rewrite /FromPure /IntoPure pure_impl=> -> <-. destruct a=>//=.
  apply bi.impl_intro_l. by rewrite affinely_and_r bi.impl_elim_r.
Qed.

Global Instance from_pure_exist {A} a (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, FromPure a (Φ x) (φ x)) → FromPure a (∃ x, Φ x) (∃ x, φ x).
Proof.
  rewrite /FromPure=>Hx. rewrite pure_exist affinely_if_exist.
  by setoid_rewrite Hx.
Qed.
Global Instance from_pure_forall {A} a (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, FromPure a (Φ x) (φ x)) → FromPure a (∀ x, Φ x) (∀ x, φ x).
Proof.
  rewrite /FromPure=>Hx. rewrite pure_forall. setoid_rewrite <-Hx.
  destruct a=>//=. apply affinely_forall.
Qed.

Global Instance from_pure_pure_sep_true (φ1 φ2 : Prop) P1 P2 :
  FromPure true P1 φ1 → FromPure true P2 φ2 → FromPure true (P1 ∗ P2) (φ1 ∧ φ2).
Proof.
  rewrite /FromPure=> <- <- /=.
  by rewrite -persistent_and_affinely_sep_l affinely_and_r pure_and.
Qed.
Global Instance from_pure_pure_sep_false_l (φ1 φ2 : Prop) P1 P2 :
  FromPure false P1 φ1 → FromPure true P2 φ2 → FromPure false (P1 ∗ P2) (φ1 ∧ φ2).
Proof.
  rewrite /FromPure=> <- <- /=. by rewrite -persistent_and_affinely_sep_r pure_and.
Qed.
Global Instance from_pure_pure_sep_false_r (φ1 φ2 : Prop) P1 P2 :
  FromPure true P1 φ1 → FromPure false P2 φ2 → FromPure false (P1 ∗ P2) (φ1 ∧ φ2).
Proof.
  rewrite /FromPure=> <- <- /=. by rewrite -persistent_and_affinely_sep_l pure_and.
Qed.
Global Instance from_pure_pure_wand (φ1 φ2 : Prop) a P1 P2 :
  IntoPure P1 φ1 → FromPure false P2 φ2 → FromPure a (P1 -∗ P2) (φ1 → φ2).
Proof.
  rewrite /FromPure /IntoPure=> -> <- /=.
  by rewrite bi.affinely_if_elim pure_wand_forall pure_impl pure_impl_forall.
Qed.

Global Instance from_pure_plainly P φ :
  FromPure false P φ → FromPure false (bi_plainly P) φ.
Proof. rewrite /FromPure=> <-. by rewrite plainly_pure. Qed.
Global Instance from_pure_persistently P a φ :
  FromPure true P φ → FromPure a (bi_persistently P) φ.
Proof.
  rewrite /FromPure=> <- /=.
  by rewrite persistently_affinely affinely_if_elim persistently_pure.
Qed.
Global Instance from_pure_affinely_true P φ :
  FromPure true P φ → FromPure true (bi_affinely P) φ.
Proof. rewrite /FromPure=><- /=. by rewrite affinely_idemp. Qed.
Global Instance from_pure_affinely_false P φ `{!Affine P} :
  FromPure false P φ → FromPure false (bi_affinely P) φ.
Proof. rewrite /FromPure /= affine_affinely //. Qed.

Global Instance from_pure_absorbingly P φ :
  FromPure true P φ → FromPure false (bi_absorbingly P) φ.
Proof. rewrite /FromPure=> <- /=. apply persistent_absorbingly_affinely, _. Qed.
Global Instance from_pure_embed `{BiEmbedding PROP PROP'} a P φ :
  FromPure a P φ → FromPure a ⎡P⎤ φ.
Proof. rewrite /FromPure=> <-. by rewrite bi_embed_affinely_if bi_embed_pure. Qed.

(* IntoPersistent *)
Global Instance into_persistent_persistently p P Q :
  IntoPersistent true P Q → IntoPersistent p (bi_persistently P) Q | 0.
Proof.
  rewrite /IntoPersistent /= => ->.
  destruct p; simpl; auto using persistently_idemp_1.
Qed.
Global Instance into_persistent_affinely p P Q :
  IntoPersistent p P Q → IntoPersistent p (bi_affinely P) Q | 0.
Proof. rewrite /IntoPersistent /= => <-. by rewrite affinely_elim. Qed.
Global Instance into_persistent_embed `{BiEmbedding PROP PROP'} p P Q :
  IntoPersistent p P Q → IntoPersistent p ⎡P⎤ ⎡Q⎤ | 0.
Proof.
  rewrite /IntoPersistent -bi_embed_persistently -bi_embed_persistently_if=> -> //.
Qed.
Global Instance into_persistent_here P : IntoPersistent true P P | 1.
Proof. by rewrite /IntoPersistent. Qed.
Global Instance into_persistent_persistent P :
  Persistent P → IntoPersistent false P P | 100.
Proof. intros. by rewrite /IntoPersistent. Qed.

(* FromAlways *)
Global Instance from_always_affinely P :
  FromAlways always_modality_affinely (bi_affinely P) P | 2.
Proof. by rewrite /FromAlways. Qed.

Global Instance from_always_persistently P :
  FromAlways always_modality_persistently (bi_persistently P) P | 2.
Proof. by rewrite /FromAlways. Qed.
Global Instance from_always_affinely_persistently P :
  FromAlways always_modality_affinely_persistently (□ P) P | 1.
Proof. by rewrite /FromAlways. Qed.
Global Instance from_always_affinely_persistently_affine_bi P :
  BiAffine PROP → FromAlways always_modality_persistently (□ P) P | 0.
Proof. intros. by rewrite /FromAlways /= affine_affinely. Qed.

Global Instance from_always_plainly P :
  FromAlways always_modality_plainly (bi_plainly P) P | 2.
Proof. by rewrite /FromAlways. Qed.
Global Instance from_always_affinely_plainly P :
  FromAlways always_modality_affinely_plainly (■ P) P | 1.
Proof. by rewrite /FromAlways. Qed.
Global Instance from_always_affinely_plainly_affine_bi P :
  BiAffine PROP → FromAlways always_modality_plainly (■ P) P | 0.
Proof. intros. by rewrite /FromAlways /= affine_affinely. Qed.

Global Instance from_always_affinely_embed `{BiEmbedding PROP PROP'} P Q :
  FromAlways always_modality_affinely P Q →
  FromAlways always_modality_affinely ⎡P⎤ ⎡Q⎤.
Proof. rewrite /FromAlways /= =><-. by rewrite bi_embed_affinely. Qed.
Global Instance from_always_persistently_embed `{BiEmbedding PROP PROP'} P Q :
  FromAlways always_modality_persistently P Q →
  FromAlways always_modality_persistently ⎡P⎤ ⎡Q⎤.
Proof. rewrite /FromAlways /= =><-. by rewrite bi_embed_persistently. Qed.
Global Instance from_always_affinely_persistently_embed `{BiEmbedding PROP PROP'} P Q :
  FromAlways always_modality_affinely_persistently P Q →
  FromAlways always_modality_affinely_persistently ⎡P⎤ ⎡Q⎤.
Proof.
  rewrite /FromAlways /= =><-. by rewrite bi_embed_affinely bi_embed_persistently.
Qed.
Global Instance from_always_plainly_embed `{BiEmbedding PROP PROP'} P Q :
  FromAlways always_modality_plainly P Q →
  FromAlways always_modality_plainly ⎡P⎤ ⎡Q⎤.
Proof. rewrite /FromAlways /= =><-. by rewrite bi_embed_plainly. Qed.
Global Instance from_always_affinely_plainly_embed `{BiEmbedding PROP PROP'} P Q :
  FromAlways always_modality_affinely_plainly P Q →
  FromAlways always_modality_affinely_plainly ⎡P⎤ ⎡Q⎤.
Proof.
  rewrite /FromAlways /= =><-. by rewrite bi_embed_affinely bi_embed_plainly.
Qed.

(* IntoWand *)
Global Instance into_wand_wand p q P Q P' :
  FromAssumption q P P' → IntoWand p q (P' -∗ Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand=> HP. by rewrite HP affinely_persistently_if_elim.
Qed.
Global Instance into_wand_impl_false_false P Q P' :
  Absorbing P' → Absorbing (P' → Q) →
  FromAssumption false P P' → IntoWand false false (P' → Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand /= => ?? ->. apply wand_intro_r.
  by rewrite sep_and impl_elim_l.
Qed.
Global Instance into_wand_impl_false_true P Q P' :
  Absorbing P' → FromAssumption true P P' →
  IntoWand false true (P' → Q) P Q.
Proof.
  rewrite /IntoWand /FromAssumption /= => ? HP. apply wand_intro_l.
  rewrite -(affinely_persistently_idemp P) HP.
  by rewrite -persistently_and_affinely_sep_l persistently_elim impl_elim_r.
Qed.
Global Instance into_wand_impl_true_false P Q P' :
  Affine P' → FromAssumption false P P' →
  IntoWand true false (P' → Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand /= => ? HP. apply wand_intro_r.
  rewrite -persistently_and_affinely_sep_l HP -{2}(affine_affinely P') -affinely_and_lr.
  by rewrite affinely_persistently_elim impl_elim_l.
Qed.
Global Instance into_wand_impl_true_true P Q P' :
  FromAssumption true P P' → IntoWand true true (P' → Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand /= => <-. apply wand_intro_l.
  rewrite -{1}(affinely_persistently_idemp P) -and_sep_affinely_persistently.
  by rewrite -affinely_persistently_and impl_elim_r affinely_persistently_elim.
Qed.

Global Instance into_wand_and_l p q R1 R2 P' Q' :
  IntoWand p q R1 P' Q' → IntoWand p q (R1 ∧ R2) P' Q'.
Proof. rewrite /IntoWand=> ?. by rewrite /bi_wand_iff and_elim_l. Qed.
Global Instance into_wand_and_r p q R1 R2 P' Q' :
  IntoWand p q R2 Q' P' → IntoWand p q (R1 ∧ R2) Q' P'.
Proof. rewrite /IntoWand=> ?. by rewrite /bi_wand_iff and_elim_r. Qed.

Global Instance into_wand_forall_prop_true p (φ : Prop) P :
  IntoWand p true (∀ _ : φ, P) ⌜ φ ⌝ P.
Proof.
  rewrite /IntoWand (affinely_persistently_if_elim p) /=
          -impl_wand_affinely_persistently -pure_impl_forall
          bi.persistently_elim //.
Qed.
Global Instance into_wand_forall_prop_false p (φ : Prop) P :
  Absorbing P → IntoWand p false (∀ _ : φ, P) ⌜ φ ⌝ P.
Proof.
  intros ?.
  rewrite /IntoWand (affinely_persistently_if_elim p) /= pure_wand_forall //.
Qed.

Global Instance into_wand_forall {A} p q (Φ : A → PROP) P Q x :
  IntoWand p q (Φ x) P Q → IntoWand p q (∀ x, Φ x) P Q.
Proof. rewrite /IntoWand=> <-. by rewrite (forall_elim x). Qed.

Global Instance into_wand_affinely_plainly p q R P Q :
  IntoWand p q R P Q → IntoWand p q (■ R) P Q.
Proof. by rewrite /IntoWand affinely_plainly_elim. Qed.
Global Instance into_wand_plainly_true q R P Q :
  IntoWand true q R P Q → IntoWand true q (bi_plainly R) P Q.
Proof. by rewrite /IntoWand /= persistently_plainly plainly_elim_persistently. Qed.
Global Instance into_wand_plainly_false `{!BiAffine PROP} q R P Q :
  IntoWand false q R P Q → IntoWand false q (bi_plainly R) P Q.
Proof. by rewrite /IntoWand plainly_elim. Qed.

Global Instance into_wand_affinely_persistently p q R P Q :
  IntoWand p q R P Q → IntoWand p q (□ R) P Q.
Proof. by rewrite /IntoWand affinely_persistently_elim. Qed.
Global Instance into_wand_persistently_true q R P Q :
  IntoWand true q R P Q → IntoWand true q (bi_persistently R) P Q.
Proof. by rewrite /IntoWand /= persistently_idemp. Qed.
Global Instance into_wand_persistently_false `{!BiAffine PROP} q R P Q :
  IntoWand false q R P Q → IntoWand false q (bi_persistently R) P Q.
Proof. by rewrite /IntoWand persistently_elim. Qed.
Global Instance into_wand_embed `{BiEmbedding PROP PROP'} p q R P Q :
  IntoWand p q R P Q → IntoWand p q ⎡R⎤ ⎡P⎤ ⎡Q⎤.
Proof.
  rewrite /IntoWand -!bi_embed_persistently_if -!bi_embed_affinely_if
          -bi_embed_wand => -> //.
Qed.

(* FromWand *)
Global Instance from_wand_wand P1 P2 : FromWand (P1 -∗ P2) P1 P2.
Proof. by rewrite /FromWand. Qed.
Global Instance from_wand_embed `{BiEmbedding PROP PROP'} P Q1 Q2 :
  FromWand P Q1 Q2 → FromWand ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromWand -bi_embed_wand => <-. Qed.

(* FromImpl *)
Global Instance from_impl_impl P1 P2 : FromImpl (P1 → P2) P1 P2.
Proof. by rewrite /FromImpl. Qed.
Global Instance from_impl_embed `{BiEmbedding PROP PROP'} P Q1 Q2 :
  FromImpl P Q1 Q2 → FromImpl ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromImpl -bi_embed_impl => <-. Qed.

(* FromAnd *)
Global Instance from_and_and P1 P2 : FromAnd (P1 ∧ P2) P1 P2 | 100.
Proof. by rewrite /FromAnd. Qed.
Global Instance from_and_sep_persistent_l P1 P1' P2 :
  FromAffinely P1 P1' → Persistent P1' → FromAnd (P1 ∗ P2) P1' P2 | 9.
Proof.
  rewrite /FromAffinely /FromAnd=> <- ?. by rewrite persistent_and_affinely_sep_l_1.
Qed.
Global Instance from_and_sep_persistent_r P1 P2 P2' :
  FromAffinely P2 P2' → Persistent P2' → FromAnd (P1 ∗ P2) P1 P2' | 10.
Proof.
  rewrite /FromAffinely /FromAnd=> <- ?. by rewrite persistent_and_affinely_sep_r_1.
Qed.
Global Instance from_and_sep_persistent P1 P2 :
  Persistent P1 → Persistent P2 → FromAnd (P1 ∗ P2) P1 P2 | 11.
Proof.
  rewrite /FromAffinely /FromAnd. intros ??. by rewrite -persistent_and_sep_1.
Qed.

Global Instance from_and_pure φ ψ : @FromAnd PROP ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromAnd pure_and. Qed.

Global Instance from_and_plainly P Q1 Q2 :
  FromAnd P Q1 Q2 →
  FromAnd (bi_plainly P) (bi_plainly Q1) (bi_plainly Q2).
Proof. rewrite /FromAnd=> <-. by rewrite plainly_and. Qed.
Global Instance from_and_plainly_sep P Q1 Q2 :
  FromSep P Q1 Q2 →
  FromAnd (bi_plainly P) (bi_plainly Q1) (bi_plainly Q2) | 11.
Proof. rewrite /FromAnd=> <-. by rewrite -plainly_and plainly_and_sep. Qed.

Global Instance from_and_persistently P Q1 Q2 :
  FromAnd P Q1 Q2 →
  FromAnd (bi_persistently P) (bi_persistently Q1) (bi_persistently Q2).
Proof. rewrite /FromAnd=> <-. by rewrite persistently_and. Qed.
Global Instance from_and_persistently_sep P Q1 Q2 :
  FromSep P Q1 Q2 →
  FromAnd (bi_persistently P) (bi_persistently Q1) (bi_persistently Q2) | 11.
Proof. rewrite /FromAnd=> <-. by rewrite -persistently_and persistently_and_sep. Qed.

Global Instance from_and_embed `{BiEmbedding PROP PROP'} P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromAnd -bi_embed_and => <-. Qed.

Global Instance from_and_big_sepL_cons_persistent {A} (Φ : nat → A → PROP) x l :
  Persistent (Φ 0 x) →
  FromAnd ([∗ list] k ↦ y ∈ x :: l, Φ k y) (Φ 0 x) ([∗ list] k ↦ y ∈ l, Φ (S k) y).
Proof. intros. by rewrite /FromAnd big_opL_cons persistent_and_sep_1. Qed.
Global Instance from_and_big_sepL_app_persistent {A} (Φ : nat → A → PROP) l1 l2 :
  (∀ k y, Persistent (Φ k y)) →
  FromAnd ([∗ list] k ↦ y ∈ l1 ++ l2, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. intros. by rewrite /FromAnd big_opL_app persistent_and_sep_1. Qed.

(* FromSep *)
Global Instance from_sep_sep P1 P2 : FromSep (P1 ∗ P2) P1 P2 | 100.
Proof. by rewrite /FromSep. Qed.
Global Instance from_sep_and P1 P2 :
  TCOr (Affine P1) (Absorbing P2) → TCOr (Absorbing P1) (Affine P2) →
  FromSep (P1 ∧ P2) P1 P2 | 101.
Proof. intros. by rewrite /FromSep sep_and. Qed.

Global Instance from_sep_pure φ ψ : @FromSep PROP ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromSep pure_and sep_and. Qed.

Global Instance from_sep_affinely P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (bi_affinely P) (bi_affinely Q1) (bi_affinely Q2).
Proof. rewrite /FromSep=> <-. by rewrite affinely_sep_2. Qed.
Global Instance from_sep_absorbingly P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (bi_absorbingly P) (bi_absorbingly Q1) (bi_absorbingly Q2).
Proof. rewrite /FromSep=> <-. by rewrite absorbingly_sep. Qed.
Global Instance from_sep_plainly P Q1 Q2 :
  FromSep P Q1 Q2 →
  FromSep (bi_plainly P) (bi_plainly Q1) (bi_plainly Q2).
Proof. rewrite /FromSep=> <-. by rewrite plainly_sep_2. Qed.
Global Instance from_sep_persistently P Q1 Q2 :
  FromSep P Q1 Q2 →
  FromSep (bi_persistently P) (bi_persistently Q1) (bi_persistently Q2).
Proof. rewrite /FromSep=> <-. by rewrite persistently_sep_2. Qed.

Global Instance from_sep_embed `{BiEmbedding PROP PROP'} P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromSep -bi_embed_sep => <-. Qed.

Global Instance from_sep_big_sepL_cons {A} (Φ : nat → A → PROP) x l :
  FromSep ([∗ list] k ↦ y ∈ x :: l, Φ k y) (Φ 0 x) ([∗ list] k ↦ y ∈ l, Φ (S k) y).
Proof. by rewrite /FromSep big_sepL_cons. Qed.
Global Instance from_sep_big_sepL_app {A} (Φ : nat → A → PROP) l1 l2 :
  FromSep ([∗ list] k ↦ y ∈ l1 ++ l2, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. by rewrite /FromSep big_opL_app. Qed.

(* IntoAnd *)
Global Instance into_and_and p P Q : IntoAnd p (P ∧ Q) P Q | 10.
Proof. by rewrite /IntoAnd affinely_persistently_if_and. Qed.
Global Instance into_and_and_affine_l P Q Q' :
  Affine P → FromAffinely Q' Q → IntoAnd false (P ∧ Q) P Q'.
Proof.
  intros. rewrite /IntoAnd /=.
  by rewrite -(affine_affinely P) affinely_and_l affinely_and (from_affinely Q').
Qed.
Global Instance into_and_and_affine_r P P' Q :
  Affine Q → FromAffinely P' P → IntoAnd false (P ∧ Q) P' Q.
Proof.
  intros. rewrite /IntoAnd /=.
  by rewrite -(affine_affinely Q) affinely_and_r affinely_and (from_affinely P').
Qed.

Global Instance into_and_sep `{BiPositive PROP} P Q : IntoAnd true (P ∗ Q) P Q.
Proof.
  by rewrite /IntoAnd /= persistently_sep -and_sep_persistently persistently_and.
Qed.
Global Instance into_and_sep_affine P Q :
  TCOr (Affine P) (Absorbing Q) → TCOr (Absorbing P) (Affine Q) →
  IntoAnd true (P ∗ Q) P Q.
Proof. intros. by rewrite /IntoAnd /= sep_and. Qed.

Global Instance into_and_pure p φ ψ : @IntoAnd PROP p ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /IntoAnd pure_and affinely_persistently_if_and. Qed.

Global Instance into_and_affinely p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (bi_affinely P) (bi_affinely Q1) (bi_affinely Q2).
Proof.
  rewrite /IntoAnd. destruct p; simpl.
  - by rewrite -affinely_and !persistently_affinely.
  - intros ->. by rewrite affinely_and.
Qed.
Global Instance into_and_plainly p P Q1 Q2 :
  IntoAnd p P Q1 Q2 →
  IntoAnd p (bi_plainly P) (bi_plainly Q1) (bi_plainly Q2).
Proof.
  rewrite /IntoAnd /=. destruct p; simpl.
  - rewrite -plainly_and persistently_plainly -plainly_persistently
            -plainly_affinely => ->.
    by rewrite plainly_affinely plainly_persistently persistently_plainly.
  - intros ->. by rewrite plainly_and.
Qed.
Global Instance into_and_persistently p P Q1 Q2 :
  IntoAnd p P Q1 Q2 →
  IntoAnd p (bi_persistently P) (bi_persistently Q1) (bi_persistently Q2).
Proof.
  rewrite /IntoAnd /=. destruct p; simpl.
  - by rewrite -persistently_and !persistently_idemp.
  - intros ->. by rewrite persistently_and.
Qed.
Global Instance into_and_embed `{BiEmbedding PROP PROP'} p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof.
  rewrite /IntoAnd -bi_embed_and -!bi_embed_persistently_if
          -!bi_embed_affinely_if=> -> //.
Qed.

(* IntoSep *)
Global Instance into_sep_sep P Q : IntoSep (P ∗ Q) P Q.
Proof. by rewrite /IntoSep. Qed.

Inductive AndIntoSep : PROP → PROP → PROP → PROP → Prop :=
  | and_into_sep_affine P Q Q' : Affine P → FromAffinely Q' Q → AndIntoSep P P Q Q'
  | and_into_sep P Q : AndIntoSep P (bi_affinely P)%I Q Q.
Existing Class AndIntoSep.
Global Existing Instance and_into_sep_affine | 0.
Global Existing Instance and_into_sep | 2.

Global Instance into_sep_and_persistent_l P P' Q Q' :
  Persistent P → AndIntoSep P P' Q Q' → IntoSep (P ∧ Q) P' Q'.
Proof.
  destruct 2 as [P Q Q'|P Q]; rewrite /IntoSep.
  - rewrite -(from_affinely Q') -(affine_affinely P) affinely_and_lr.
    by rewrite persistent_and_affinely_sep_l_1.
  - by rewrite persistent_and_affinely_sep_l_1.
Qed.
Global Instance into_sep_and_persistent_r P P' Q Q' :
  Persistent Q → AndIntoSep Q Q' P P' → IntoSep (P ∧ Q) P' Q'.
Proof.
  destruct 2 as [Q P P'|Q P]; rewrite /IntoSep.
  - rewrite -(from_affinely P') -(affine_affinely Q) -affinely_and_lr.
    by rewrite persistent_and_affinely_sep_r_1.
  - by rewrite persistent_and_affinely_sep_r_1.
Qed.

Global Instance into_sep_pure φ ψ : @IntoSep PROP ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /IntoSep pure_and persistent_and_sep_1. Qed.

Global Instance into_sep_embed `{BiEmbedding PROP PROP'} P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. rewrite /IntoSep -bi_embed_sep=> -> //. Qed.

Global Instance into_sep_affinely `{BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (bi_affinely P) (bi_affinely Q1) (bi_affinely Q2) | 0.
Proof. rewrite /IntoSep /= => ->. by rewrite affinely_sep. Qed.
(* FIXME: This instance is kind of strange, it just gets rid of the bi_affinely.
Also, it overlaps with `into_sep_affinely_later`, and hence has lower
precedence. *)
Global Instance into_sep_affinely_trim P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (bi_affinely P) Q1 Q2 | 20.
Proof. rewrite /IntoSep /= => ->. by rewrite affinely_elim. Qed.

Global Instance into_sep_plainly `{BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (bi_plainly P) (bi_plainly Q1) (bi_plainly Q2).
Proof. rewrite /IntoSep /= => ->. by rewrite plainly_sep. Qed.
Global Instance into_sep_plainly_affine P Q1 Q2 :
  IntoSep P Q1 Q2 →
  TCOr (Affine Q1) (Absorbing Q2) → TCOr (Absorbing Q1) (Affine Q2) →
  IntoSep (bi_plainly P) (bi_plainly Q1) (bi_plainly Q2).
Proof.
  rewrite /IntoSep /= => -> ??. by rewrite sep_and plainly_and plainly_and_sep_l_1.
Qed.

Global Instance into_sep_persistently `{BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 →
  IntoSep (bi_persistently P) (bi_persistently Q1) (bi_persistently Q2).
Proof. rewrite /IntoSep /= => ->. by rewrite persistently_sep. Qed.
Global Instance into_sep_persistently_affine P Q1 Q2 :
  IntoSep P Q1 Q2 →
  TCOr (Affine Q1) (Absorbing Q2) → TCOr (Absorbing Q1) (Affine Q2) →
  IntoSep (bi_persistently P) (bi_persistently Q1) (bi_persistently Q2).
Proof.
  rewrite /IntoSep /= => -> ??.
  by rewrite sep_and persistently_and persistently_and_sep_l_1.
Qed.
Global Instance into_sep_affinely_persistently_affine P Q1 Q2 :
  IntoSep P Q1 Q2 →
  TCOr (Affine Q1) (Absorbing Q2) → TCOr (Absorbing Q1) (Affine Q2) →
  IntoSep (□ P) (□ Q1) (□ Q2).
Proof.
  rewrite /IntoSep /= => -> ??.
  by rewrite sep_and affinely_persistently_and and_sep_affinely_persistently.
Qed.

(* We use [IsCons] and [IsApp] to make sure that [frame_big_sepL_cons] and
[frame_big_sepL_app] cannot be applied repeatedly often when having
[ [∗ list] k ↦ x ∈ ?e, Φ k x] with [?e] an evar. *)
Global Instance into_sep_big_sepL_cons {A} (Φ : nat → A → PROP) l x l' :
  IsCons l x l' →
  IntoSep ([∗ list] k ↦ y ∈ l, Φ k y)
    (Φ 0 x) ([∗ list] k ↦ y ∈ l', Φ (S k) y).
Proof. rewrite /IsCons=>->. by rewrite /IntoSep big_sepL_cons. Qed.
Global Instance into_sep_big_sepL_app {A} (Φ : nat → A → PROP) l l1 l2 :
  IsApp l l1 l2 →
  IntoSep ([∗ list] k ↦ y ∈ l, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. rewrite /IsApp=>->. by rewrite /IntoSep big_sepL_app. Qed.

(* FromOr *)
Global Instance from_or_or P1 P2 : FromOr (P1 ∨ P2) P1 P2.
Proof. by rewrite /FromOr. Qed.
Global Instance from_or_pure φ ψ : @FromOr PROP ⌜φ ∨ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromOr pure_or. Qed.
Global Instance from_or_affinely P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (bi_affinely P) (bi_affinely Q1) (bi_affinely Q2).
Proof. rewrite /FromOr=> <-. by rewrite affinely_or. Qed.
Global Instance from_or_absorbingly P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (bi_absorbingly P) (bi_absorbingly Q1) (bi_absorbingly Q2).
Proof. rewrite /FromOr=> <-. by rewrite absorbingly_or. Qed.
Global Instance from_or_plainly P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (bi_plainly P) (bi_plainly Q1) (bi_plainly Q2).
Proof. rewrite /FromOr=> <-. by rewrite -plainly_or_2. Qed.
Global Instance from_or_persistently P Q1 Q2 :
  FromOr P Q1 Q2 →
  FromOr (bi_persistently P) (bi_persistently Q1) (bi_persistently Q2).
Proof. rewrite /FromOr=> <-. by rewrite persistently_or. Qed.
Global Instance from_or_embed `{BiEmbedding PROP PROP'} P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromOr -bi_embed_or => <-. Qed.

(* IntoOr *)
Global Instance into_or_or P Q : IntoOr (P ∨ Q) P Q.
Proof. by rewrite /IntoOr. Qed.
Global Instance into_or_pure φ ψ : @IntoOr PROP ⌜φ ∨ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /IntoOr pure_or. Qed.
Global Instance into_or_affinely P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (bi_affinely P) (bi_affinely Q1) (bi_affinely Q2).
Proof. rewrite /IntoOr=>->. by rewrite affinely_or. Qed.
Global Instance into_or_absorbingly P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (bi_absorbingly P) (bi_absorbingly Q1) (bi_absorbingly Q2).
Proof. rewrite /IntoOr=>->. by rewrite absorbingly_or. Qed.
Global Instance into_or_plainly `{BiPlainlyExist PROP} P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (bi_plainly P) (bi_plainly Q1) (bi_plainly Q2).
Proof. rewrite /IntoOr=>->. by rewrite plainly_or. Qed.
Global Instance into_or_persistently P Q1 Q2 :
  IntoOr P Q1 Q2 →
  IntoOr (bi_persistently P) (bi_persistently Q1) (bi_persistently Q2).
Proof. rewrite /IntoOr=>->. by rewrite persistently_or. Qed.
Global Instance into_or_embed `{BiEmbedding PROP PROP'} P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /IntoOr -bi_embed_or => <-. Qed.

(* FromExist *)
Global Instance from_exist_exist {A} (Φ : A → PROP): FromExist (∃ a, Φ a) Φ.
Proof. by rewrite /FromExist. Qed.
Global Instance from_exist_pure {A} (φ : A → Prop) :
  @FromExist PROP A ⌜∃ x, φ x⌝ (λ a, ⌜φ a⌝)%I.
Proof. by rewrite /FromExist pure_exist. Qed.
Global Instance from_exist_affinely {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (bi_affinely P) (λ a, bi_affinely (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite affinely_exist. Qed.
Global Instance from_exist_absorbingly {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (bi_absorbingly P) (λ a, bi_absorbingly (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite absorbingly_exist. Qed.
Global Instance from_exist_plainly {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (bi_plainly P) (λ a, bi_plainly (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite -plainly_exist_2. Qed.
Global Instance from_exist_persistently {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (bi_persistently P) (λ a, bi_persistently (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite persistently_exist. Qed.
Global Instance from_exist_embed `{BiEmbedding PROP PROP'} {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist ⎡P⎤ (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /FromExist -bi_embed_exist => <-. Qed.

(* IntoExist *)
Global Instance into_exist_exist {A} (Φ : A → PROP) : IntoExist (∃ a, Φ a) Φ.
Proof. by rewrite /IntoExist. Qed.
Global Instance into_exist_pure {A} (φ : A → Prop) :
  @IntoExist PROP A ⌜∃ x, φ x⌝ (λ a, ⌜φ a⌝)%I.
Proof. by rewrite /IntoExist pure_exist. Qed.
Global Instance into_exist_affinely {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (bi_affinely P) (λ a, bi_affinely (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP affinely_exist. Qed.
Global Instance into_exist_and_pure P Q φ :
  IntoPureT P φ → IntoExist (P ∧ Q) (λ _ : φ, Q).
Proof.
  intros (φ'&->&?). rewrite /IntoExist (into_pure P).
  apply pure_elim_l=> Hφ. by rewrite -(exist_intro Hφ).
Qed.
Global Instance into_exist_sep_pure P Q φ :
  TCOr (Affine P) (Absorbing Q) → IntoPureT P φ → IntoExist (P ∗ Q) (λ _ : φ, Q).
Proof.
  intros ? (φ'&->&?). rewrite /IntoExist.
  eapply (pure_elim φ'); [by rewrite (into_pure P); apply sep_elim_l, _|]=>?.
  rewrite -exist_intro //. apply sep_elim_r, _.
Qed.
Global Instance into_exist_absorbingly {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (bi_absorbingly P) (λ a, bi_absorbingly (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP absorbingly_exist. Qed.
Global Instance into_exist_plainly `{BiPlainlyExist PROP} {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (bi_plainly P) (λ a, bi_plainly (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP plainly_exist. Qed.
Global Instance into_exist_persistently {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (bi_persistently P) (λ a, bi_persistently (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP persistently_exist. Qed.
Global Instance into_exist_embed `{BiEmbedding PROP PROP'} {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist ⎡P⎤ (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /IntoExist -bi_embed_exist => <-. Qed.

(* IntoForall *)
Global Instance into_forall_forall {A} (Φ : A → PROP) : IntoForall (∀ a, Φ a) Φ.
Proof. by rewrite /IntoForall. Qed.
Global Instance into_forall_affinely {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (bi_affinely P) (λ a, bi_affinely (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP affinely_forall. Qed.
Global Instance into_forall_plainly {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (bi_plainly P) (λ a, bi_plainly (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP plainly_forall. Qed.
Global Instance into_forall_persistently {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (bi_persistently P) (λ a, bi_persistently (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP persistently_forall. Qed.
Global Instance into_forall_embed `{BiEmbedding PROP PROP'} {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall ⎡P⎤ (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /IntoForall -bi_embed_forall => <-. Qed.

(* FromForall *)
Global Instance from_forall_forall {A} (Φ : A → PROP) :
  FromForall (∀ x, Φ x)%I Φ.
Proof. by rewrite /FromForall. Qed.
Global Instance from_forall_pure {A} (φ : A → Prop) :
  @FromForall PROP A (⌜∀ a : A, φ a⌝)%I (λ a, ⌜ φ a ⌝)%I.
Proof. by rewrite /FromForall pure_forall. Qed.
Global Instance from_forall_pure_not (φ : Prop) :
  @FromForall PROP φ (⌜¬ φ⌝)%I (λ a : φ, False)%I.
Proof. by rewrite /FromForall pure_forall. Qed.
Global Instance from_forall_impl_pure P Q φ :
  IntoPureT P φ → FromForall (P → Q)%I (λ _ : φ, Q)%I.
Proof.
  intros (φ'&->&?). by rewrite /FromForall -pure_impl_forall (into_pure P).
Qed.
Global Instance from_forall_wand_pure P Q φ :
  TCOr (Affine P) (Absorbing Q) → IntoPureT P φ →
  FromForall (P -∗ Q)%I (λ _ : φ, Q)%I.
Proof.
  intros [|] (φ'&->&?); rewrite /FromForall; apply wand_intro_r.
  - rewrite -(affine_affinely P) (into_pure P) -persistent_and_affinely_sep_r.
    apply pure_elim_r=>?. by rewrite forall_elim.
  - by rewrite (into_pure P) -pure_wand_forall wand_elim_l.
Qed.

Global Instance from_forall_affinely `{BiAffine PROP} {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (bi_affinely P)%I (λ a, bi_affinely (Φ a))%I.
Proof.
  rewrite /FromForall=> <-. rewrite affine_affinely. by setoid_rewrite affinely_elim.
Qed.
Global Instance from_forall_plainly {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (bi_plainly P)%I (λ a, bi_plainly (Φ a))%I.
Proof. rewrite /FromForall=> <-. by rewrite plainly_forall. Qed.
Global Instance from_forall_persistently {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (bi_persistently P)%I (λ a, bi_persistently (Φ a))%I.
Proof. rewrite /FromForall=> <-. by rewrite persistently_forall. Qed.
Global Instance from_forall_embed `{BiEmbedding PROP PROP'} {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall ⎡P⎤%I (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /FromForall -bi_embed_forall => <-. Qed.

(* ElimModal *)
Global Instance elim_modal_wand φ P P' Q Q' R :
  ElimModal φ P P' Q Q' → ElimModal φ P P' (R -∗ Q) (R -∗ Q').
Proof.
  rewrite /ElimModal=> H Hφ. apply wand_intro_r.
  rewrite wand_curry -assoc (comm _ P') -wand_curry wand_elim_l; auto.
Qed.
Global Instance elim_modal_forall {A} φ P P' (Φ Ψ : A → PROP) :
  (∀ x, ElimModal φ P P' (Φ x) (Ψ x)) → ElimModal φ P P' (∀ x, Φ x) (∀ x, Ψ x).
Proof.
  rewrite /ElimModal=> H ?. apply forall_intro=> a. rewrite (forall_elim a); auto.
Qed.
Global Instance elim_modal_absorbingly_here P Q :
  Absorbing Q → ElimModal True (bi_absorbingly P) P Q Q.
Proof.
  rewrite /ElimModal=> H.
  by rewrite absorbingly_sep_l wand_elim_r absorbing_absorbingly.
Qed.

(* AddModal *)
Global Instance add_modal_wand P P' Q R :
  AddModal P P' Q → AddModal P P' (R -∗ Q).
Proof.
  rewrite /AddModal=> H. apply wand_intro_r.
  by rewrite wand_curry -assoc (comm _ P') -wand_curry wand_elim_l.
Qed.
Global Instance add_modal_forall {A} P P' (Φ : A → PROP) :
  (∀ x, AddModal P P' (Φ x)) → AddModal P P' (∀ x, Φ x).
Proof.
  rewrite /AddModal=> H. apply forall_intro=> a. by rewrite (forall_elim a).
Qed.

(* Frame *)
Global Instance frame_here_absorbing p R : Absorbing R → Frame p R R True | 0.
Proof. intros. by rewrite /Frame affinely_persistently_if_elim sep_elim_l. Qed.
Global Instance frame_here p R : Frame p R R emp | 1.
Proof. intros. by rewrite /Frame affinely_persistently_if_elim sep_elim_l. Qed.
Global Instance frame_affinely_here_absorbing p R :
  Absorbing R → Frame p (bi_affinely R) R True | 0.
Proof.
  intros. by rewrite /Frame affinely_persistently_if_elim affinely_elim sep_elim_l.
Qed.
Global Instance frame_affinely_here p R : Frame p (bi_affinely R) R emp | 1.
Proof.
  intros. by rewrite /Frame affinely_persistently_if_elim affinely_elim sep_elim_l.
Qed.

Global Instance frame_here_pure p φ Q : FromPure false Q φ → Frame p ⌜φ⌝ Q True.
Proof.
  rewrite /FromPure /Frame=> <-. by rewrite affinely_persistently_if_elim sep_elim_l.
Qed.

Class MakeEmbed `{BiEmbedding PROP PROP'} P (Q : PROP') :=
  make_embed : ⎡P⎤ ⊣⊢ Q.
Arguments MakeEmbed {_ _ _} _%I _%I.
Global Instance make_embed_pure `{BiEmbedding PROP PROP'} φ :
  MakeEmbed ⌜φ⌝ ⌜φ⌝.
Proof. by rewrite /MakeEmbed bi_embed_pure. Qed.
Global Instance make_embed_emp `{BiEmbedding PROP PROP'} :
  MakeEmbed emp emp.
Proof. by rewrite /MakeEmbed bi_embed_emp. Qed.
Global Instance make_embed_default `{BiEmbedding PROP PROP'} :
  MakeEmbed P ⎡P⎤ | 100.
Proof. by rewrite /MakeEmbed. Qed.

Global Instance frame_embed `{BiEmbedding PROP PROP'} p P Q (Q' : PROP') R :
  Frame p R P Q → MakeEmbed Q Q' → Frame p ⎡R⎤ ⎡P⎤ Q'.
Proof.
  rewrite /Frame /MakeEmbed => <- <-.
  rewrite bi_embed_sep bi_embed_affinely_if bi_embed_persistently_if => //.
Qed.
Global Instance frame_pure_embed `{BiEmbedding PROP PROP'} p P Q (Q' : PROP') φ :
  Frame p ⌜φ⌝ P Q → MakeEmbed Q Q' → Frame p ⌜φ⌝ ⎡P⎤ Q'.
Proof. rewrite /Frame /MakeEmbed -bi_embed_pure. apply (frame_embed p P Q). Qed.

Class MakeSep (P Q PQ : PROP) := make_sep : P ∗ Q ⊣⊢ PQ.
Arguments MakeSep _%I _%I _%I.
Global Instance make_sep_emp_l P : MakeSep emp P P.
Proof. by rewrite /MakeSep left_id. Qed.
Global Instance make_sep_emp_r P : MakeSep P emp P.
Proof. by rewrite /MakeSep right_id. Qed.
Global Instance make_sep_true_l P : Absorbing P → MakeSep True P P.
Proof. intros. by rewrite /MakeSep True_sep. Qed.
Global Instance make_and_emp_l_absorbingly P : MakeSep True P (bi_absorbingly P) | 10.
Proof. intros. by rewrite /MakeSep. Qed.
Global Instance make_sep_true_r P : Absorbing P → MakeSep P True P.
Proof. intros. by rewrite /MakeSep sep_True. Qed.
Global Instance make_and_emp_r_absorbingly P : MakeSep P True (bi_absorbingly P) | 10.
Proof. intros. by rewrite /MakeSep comm. Qed.
Global Instance make_sep_default P Q : MakeSep P Q (P ∗ Q) | 100.
Proof. by rewrite /MakeSep. Qed.

Global Instance frame_sep_persistent_l progress R P1 P2 Q1 Q2 Q' :
  Frame true R P1 Q1 → MaybeFrame true R P2 Q2 progress → MakeSep Q1 Q2 Q' →
  Frame true R (P1 ∗ P2) Q' | 9.
Proof.
  rewrite /Frame /MaybeFrame /MakeSep /= => <- <- <-.
  rewrite {1}(affinely_persistently_sep_dup R). solve_sep_entails.
Qed.
Global Instance frame_sep_l R P1 P2 Q Q' :
  Frame false R P1 Q → MakeSep Q P2 Q' → Frame false R (P1 ∗ P2) Q' | 9.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc. Qed.
Global Instance frame_sep_r p R P1 P2 Q Q' :
  Frame p R P2 Q → MakeSep P1 Q Q' → Frame p R (P1 ∗ P2) Q' | 10.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc -(comm _ P1) assoc. Qed.

Global Instance frame_big_sepL_cons {A} p (Φ : nat → A → PROP) R Q l x l' :
  IsCons l x l' →
  Frame p R (Φ 0 x ∗ [∗ list] k ↦ y ∈ l', Φ (S k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q.
Proof. rewrite /IsCons=>->. by rewrite /Frame big_sepL_cons. Qed.
Global Instance frame_big_sepL_app {A} p (Φ : nat → A → PROP) R Q l l1 l2 :
  IsApp l l1 l2 →
  Frame p R (([∗ list] k ↦ y ∈ l1, Φ k y) ∗
           [∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q.
Proof. rewrite /IsApp=>->. by rewrite /Frame big_opL_app. Qed.

Class MakeAnd (P Q PQ : PROP) := make_and : P ∧ Q ⊣⊢ PQ.
Arguments MakeAnd _%I _%I _%I.
Global Instance make_and_true_l P : MakeAnd True P P.
Proof. by rewrite /MakeAnd left_id. Qed.
Global Instance make_and_true_r P : MakeAnd P True P.
Proof. by rewrite /MakeAnd right_id. Qed.
Global Instance make_and_emp_l P : Affine P → MakeAnd emp P P.
Proof. intros. by rewrite /MakeAnd emp_and. Qed.
Global Instance make_and_emp_l_affinely P : MakeAnd emp P (bi_affinely P) | 10.
Proof. intros. by rewrite /MakeAnd. Qed.
Global Instance make_and_emp_r P : Affine P → MakeAnd P emp P.
Proof. intros. by rewrite /MakeAnd and_emp. Qed.
Global Instance make_and_emp_r_affinely P : MakeAnd P emp (bi_affinely P) | 10.
Proof. intros. by rewrite /MakeAnd comm. Qed.
Global Instance make_and_default P Q : MakeAnd P Q (P ∧ Q) | 100.
Proof. by rewrite /MakeAnd. Qed.

Global Instance frame_and p progress1 progress2 R P1 P2 Q1 Q2 Q' :
  MaybeFrame p R P1 Q1 progress1 →
  MaybeFrame p R P2 Q2 progress2 →
  TCEq (progress1 || progress2) true →
  MakeAnd Q1 Q2 Q' →
  Frame p R (P1 ∧ P2) Q' | 9.
Proof.
  rewrite /MaybeFrame /Frame /MakeAnd => <- <- _ <-. apply and_intro;
  [rewrite and_elim_l|rewrite and_elim_r]; done.
Qed.

Class MakeOr (P Q PQ : PROP) := make_or : P ∨ Q ⊣⊢ PQ.
Arguments MakeOr _%I _%I _%I.
Global Instance make_or_true_l P : MakeOr True P True.
Proof. by rewrite /MakeOr left_absorb. Qed.
Global Instance make_or_true_r P : MakeOr P True True.
Proof. by rewrite /MakeOr right_absorb. Qed.
Global Instance make_or_emp_l P : Affine P → MakeOr emp P emp.
Proof. intros. by rewrite /MakeOr emp_or. Qed.
Global Instance make_or_emp_r P : Affine P → MakeOr P emp emp.
Proof. intros. by rewrite /MakeOr or_emp. Qed.
Global Instance make_or_default P Q : MakeOr P Q (P ∨ Q) | 100.
Proof. by rewrite /MakeOr. Qed.

(* We could in principle write the instance [frame_or_spatial] by a bunch of
instances, i.e. (omitting the parameter [p = false]):

  Frame R P1 Q1 → Frame R P2 Q2 → Frame R (P1 ∨ P2) (Q1 ∨ Q2)
  Frame R P1 True → Frame R (P1 ∨ P2) P2
  Frame R P2 True → Frame R (P1 ∨ P2) P1

The problem here is that Coq will try to infer [Frame R P1 ?] and [Frame R P2 ?]
multiple times, whereas the current solution makes sure that said inference
appears at most once.

If Coq would memorize the results of type class resolution, the solution with
multiple instances would be preferred (and more Prolog-like). *)
Global Instance frame_or_spatial progress1 progress2 R P1 P2 Q1 Q2 Q :
  MaybeFrame false R P1 Q1 progress1 → MaybeFrame false R P2 Q2 progress2 →
  TCOr (TCEq (progress1 && progress2) true) (TCOr
    (TCAnd (TCEq progress1 true) (TCEq Q1 True%I))
    (TCAnd (TCEq progress2 true) (TCEq Q2 True%I))) →
  MakeOr Q1 Q2 Q →
  Frame false R (P1 ∨ P2) Q | 9.
Proof. rewrite /Frame /MakeOr => <- <- _ <-. by rewrite -sep_or_l. Qed.

Global Instance frame_or_persistent progress1 progress2 R P1 P2 Q1 Q2 Q :
  MaybeFrame true R P1 Q1 progress1 → MaybeFrame true R P2 Q2 progress2 →
  TCEq (progress1 || progress2) true →
  MakeOr Q1 Q2 Q → Frame true R (P1 ∨ P2) Q | 9.
Proof. rewrite /Frame /MakeOr => <- <- _ <-. by rewrite -sep_or_l. Qed.

Global Instance frame_wand p R P1 P2 Q2 :
  Frame p R P2 Q2 → Frame p R (P1 -∗ P2) (P1 -∗ Q2).
Proof.
  rewrite /Frame=> ?. apply wand_intro_l.
  by rewrite assoc (comm _ P1) -assoc wand_elim_r.
Qed.

Class MakeAffinely (P Q : PROP) := make_affinely : bi_affinely P ⊣⊢ Q.
Arguments MakeAffinely _%I _%I.
Global Instance make_affinely_True : MakeAffinely True emp | 0.
Proof. by rewrite /MakeAffinely affinely_True_emp affinely_emp. Qed.
Global Instance make_affinely_affine P : Affine P → MakeAffinely P P | 1.
Proof. intros. by rewrite /MakeAffinely affine_affinely. Qed.
Global Instance make_affinely_default P : MakeAffinely P (bi_affinely P) | 100.
Proof. by rewrite /MakeAffinely. Qed.

Global Instance frame_affinely R P Q Q' :
  Frame true R P Q → MakeAffinely Q Q' → Frame true R (bi_affinely P) Q'.
Proof.
  rewrite /Frame /MakeAffinely=> <- <- /=.
  by rewrite -{1}affinely_idemp affinely_sep_2.
Qed.

Class MakeAbsorbingly (P Q : PROP) := make_absorbingly : bi_absorbingly P ⊣⊢ Q.
Arguments MakeAbsorbingly _%I _%I.
Global Instance make_absorbingly_emp : MakeAbsorbingly emp True | 0.
Proof. by rewrite /MakeAbsorbingly -absorbingly_True_emp absorbingly_pure. Qed.
(* Note: there is no point in having an instance `Absorbing P → MakeAbsorbingly P P`
because framing will never turn a proposition that is not absorbing into
something that is absorbing. *)
Global Instance make_absorbingly_default P : MakeAbsorbingly P (bi_absorbingly P) | 100.
Proof. by rewrite /MakeAbsorbingly. Qed.

Global Instance frame_absorbingly p R P Q Q' :
  Frame p R P Q → MakeAbsorbingly Q Q' → Frame p R (bi_absorbingly P) Q'.
Proof. rewrite /Frame /MakeAbsorbingly=> <- <- /=. by rewrite absorbingly_sep_r. Qed.

Class MakePersistently (P Q : PROP) := make_persistently : bi_persistently P ⊣⊢ Q.
Arguments MakePersistently _%I _%I.
Global Instance make_persistently_true : MakePersistently True True.
Proof. by rewrite /MakePersistently persistently_pure. Qed.
Global Instance make_persistently_emp : MakePersistently emp True.
Proof. by rewrite /MakePersistently -persistently_True_emp persistently_pure. Qed.
Global Instance make_persistently_default P :
  MakePersistently P (bi_persistently P) | 100.
Proof. by rewrite /MakePersistently. Qed.

Global Instance frame_persistently R P Q Q' :
  Frame true R P Q → MakePersistently Q Q' → Frame true R (bi_persistently P) Q'.
Proof.
  rewrite /Frame /MakePersistently=> <- <- /=. rewrite -persistently_and_affinely_sep_l.
  by rewrite -persistently_sep_2 -persistently_and_sep_l_1 persistently_affinely
              persistently_idemp.
Qed.

Global Instance frame_exist {A} p R (Φ Ψ : A → PROP) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∃ x, Φ x) (∃ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_exist_l; apply exist_mono. Qed.
Global Instance frame_forall {A} p R (Φ Ψ : A → PROP) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_forall_l; apply forall_mono. Qed.

Global Instance frame_impl_persistent R P1 P2 Q2 :
  Frame true R P2 Q2 → Frame true R (P1 → P2) (P1 → Q2).
Proof.
  rewrite /Frame /= => ?. apply impl_intro_l.
  by rewrite -persistently_and_affinely_sep_l assoc (comm _ P1) -assoc impl_elim_r
             persistently_and_affinely_sep_l.
Qed.
Global Instance frame_impl R P1 P2 Q2 :
  Persistent P1 → Absorbing P1 →
  Frame false R P2 Q2 → Frame false R (P1 → P2) (P1 → Q2).
Proof.
  rewrite /Frame /==> ???. apply impl_intro_l.
  rewrite {1}(persistent P1) persistently_and_affinely_sep_l assoc.
  rewrite (comm _ (□ P1)%I) -assoc -persistently_and_affinely_sep_l.
  rewrite persistently_elim impl_elim_r //.
Qed.

(* FromModal *)
Global Instance from_modal_absorbingly P : FromModal (bi_absorbingly P) P.
Proof. apply absorbingly_intro. Qed.
Global Instance from_modal_embed `{BiEmbedding PROP PROP'} P Q :
  FromModal P Q → FromModal ⎡P⎤ ⎡Q⎤.
Proof. by rewrite /FromModal=> ->. Qed.

(* AsValid *)
Global Instance as_valid_valid {PROP : bi} (P : PROP) : AsValid0 (bi_valid P) P | 0.
Proof. by rewrite /AsValid. Qed.
Global Instance as_valid_entails {PROP : bi} (P Q : PROP) : AsValid0 (P ⊢ Q) (P -∗ Q).
Proof. split. apply bi.entails_wand. apply bi.wand_entails. Qed.
Global Instance as_valid_equiv {PROP : bi} (P Q : PROP) : AsValid0 (P ≡ Q) (P ∗-∗ Q).
Proof. split. apply bi.equiv_wand_iff. apply bi.wand_iff_equiv. Qed.

Global Instance as_valid_forall {A : Type} (φ : A → Prop) (P : A → PROP) :
  (∀ x, AsValid (φ x) (P x)) → AsValid (∀ x, φ x) (∀ x, P x).
Proof.
  rewrite /AsValid=>H1. split=>H2.
  - apply bi.forall_intro=>?. apply H1, H2.
  - intros x. apply H1. revert H2. by rewrite (bi.forall_elim x).
Qed.

Global Instance as_valid_embed `{BiEmbedding PROP PROP'} (φ : Prop) (P : PROP) :
  AsValid0 φ P → AsValid φ ⎡P⎤.
Proof. rewrite /AsValid0 /AsValid=> ->. rewrite bi_embed_valid //. Qed.
End bi_instances.

Section sbi_instances.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.

(* FromAssumption *)
Global Instance from_assumption_later p P Q :
  FromAssumption p P Q → FromAssumption p P (▷ Q)%I.
Proof. rewrite /FromAssumption=>->. apply later_intro. Qed.
Global Instance from_assumption_laterN n p P Q :
  FromAssumption p P Q → FromAssumption p P (▷^n Q)%I.
Proof. rewrite /FromAssumption=>->. apply laterN_intro. Qed.
Global Instance from_assumption_except_0 p P Q :
  FromAssumption p P Q → FromAssumption p P (◇ Q)%I.
Proof. rewrite /FromAssumption=>->. apply except_0_intro. Qed.

Global Instance from_assumption_bupd `{BUpdFacts PROP} p P Q :
  FromAssumption p P Q → FromAssumption p P (|==> Q).
Proof. rewrite /FromAssumption=>->. apply bupd_intro. Qed.
Global Instance from_assumption_fupd `{FUpdFacts PROP} E p P Q :
  FromAssumption p P (|==> Q) → FromAssumption p P (|={E}=> Q)%I.
Proof. rewrite /FromAssumption=>->. apply bupd_fupd. Qed.

(* FromPure *)
Global Instance from_pure_internal_eq af {A : ofeT} (a b : A) :
  @FromPure PROP af (a ≡ b) (a ≡ b).
Proof. by rewrite /FromPure pure_internal_eq affinely_if_elim. Qed.
Global Instance from_pure_later a P φ : FromPure a P φ → FromPure a (▷ P) φ.
Proof. rewrite /FromPure=> ->. apply later_intro. Qed.
Global Instance from_pure_laterN a n P φ : FromPure a P φ → FromPure a (▷^n P) φ.
Proof. rewrite /FromPure=> ->. apply laterN_intro. Qed.
Global Instance from_pure_except_0 a P φ : FromPure a P φ → FromPure a (◇ P) φ.
Proof. rewrite /FromPure=> ->. apply except_0_intro. Qed.

Global Instance from_pure_bupd `{BUpdFacts PROP} a P φ :
  FromPure a P φ → FromPure a (|==> P) φ.
Proof. rewrite /FromPure=> <-. apply bupd_intro. Qed.
Global Instance from_pure_fupd `{FUpdFacts PROP} a E P φ :
  FromPure a P φ → FromPure a (|={E}=> P) φ.
Proof. rewrite /FromPure. intros <-. apply fupd_intro. Qed.

(* IntoPure *)
Global Instance into_pure_eq {A : ofeT} (a b : A) :
  Discrete a → @IntoPure PROP (a ≡ b) (a ≡ b).
Proof. intros. by rewrite /IntoPure discrete_eq. Qed.

(* IntoWand *)
Global Instance into_wand_later p q R P Q :
  IntoWand p q R P Q → IntoWand p q (▷ R) (▷ P) (▷ Q).
Proof.
  rewrite /IntoWand /= => HR.
    by rewrite !later_affinely_persistently_if_2 -later_wand HR.
Qed.
Global Instance into_wand_later_args p q R P Q :
  IntoWand p q R P Q → IntoWand' p q R (▷ P) (▷ Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => HR.
  by rewrite !later_affinely_persistently_if_2
             (later_intro (□?p R)%I) -later_wand HR.
Qed.
Global Instance into_wand_laterN n p q R P Q :
  IntoWand p q R P Q → IntoWand p q (▷^n R) (▷^n P) (▷^n Q).
Proof.
  rewrite /IntoWand /= => HR.
    by rewrite !laterN_affinely_persistently_if_2 -laterN_wand HR.
Qed.
Global Instance into_wand_laterN_args n p q R P Q :
  IntoWand p q R P Q → IntoWand' p q R (▷^n P) (▷^n Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => HR.
  by rewrite !laterN_affinely_persistently_if_2
             (laterN_intro _ (□?p R)%I) -laterN_wand HR.
Qed.

Global Instance into_wand_bupd `{BUpdFacts PROP} p q R P Q :
  IntoWand false false R P Q → IntoWand p q (|==> R) (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !affinely_persistently_if_elim HR.
  apply wand_intro_l. by rewrite bupd_sep wand_elim_r.
Qed.
Global Instance into_wand_bupd_persistent `{BUpdFacts PROP} p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|==> R) P (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite affinely_persistently_if_elim HR.
  apply wand_intro_l. by rewrite bupd_frame_l wand_elim_r.
Qed.
Global Instance into_wand_bupd_args `{BUpdFacts PROP} p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite affinely_persistently_if_elim bupd_wand_r.
Qed.

Global Instance into_wand_fupd `{FUpdFacts PROP} E p q R P Q :
  IntoWand false false R P Q →
  IntoWand p q (|={E}=> R) (|={E}=> P) (|={E}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !affinely_persistently_if_elim HR.
  apply wand_intro_l. by rewrite fupd_sep wand_elim_r.
Qed.
Global Instance into_wand_fupd_persistent `{FUpdFacts PROP} E1 E2 p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|={E1,E2}=> R) P (|={E1,E2}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite affinely_persistently_if_elim HR.
  apply wand_intro_l. by rewrite fupd_frame_l wand_elim_r.
Qed.
Global Instance into_wand_fupd_args `{FUpdFacts PROP} E1 E2 p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|={E1,E2}=> P) (|={E1,E2}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite affinely_persistently_if_elim fupd_wand_r.
Qed.

(* FromAnd *)
Global Instance from_and_later P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite later_and. Qed.
Global Instance from_and_laterN n P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromAnd=> <-. by rewrite laterN_and. Qed.
Global Instance from_and_except_0 P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /FromAnd=><-. by rewrite except_0_and. Qed.

(* FromSep *)
Global Instance from_sep_later P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromSep=> <-. by rewrite later_sep. Qed.
Global Instance from_sep_laterN n P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromSep=> <-. by rewrite laterN_sep. Qed.
Global Instance from_sep_except_0 P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /FromSep=><-. by rewrite except_0_sep. Qed.

Global Instance from_sep_bupd `{BUpdFacts PROP} P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromSep=><-. apply bupd_sep. Qed.
Global Instance from_sep_fupd `{FUpdFacts PROP} E P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2).
Proof. rewrite /FromSep =><-. apply fupd_sep. Qed.

(* IntoAnd *)
Global Instance into_and_later p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷ P) (▷ Q1) (▷ Q2).
Proof.
  rewrite /IntoAnd=> HP. apply affinely_persistently_if_intro'.
  by rewrite later_affinely_persistently_if_2 HP
             affinely_persistently_if_elim later_and.
Qed.
Global Instance into_and_laterN n p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷^n P) (▷^n Q1) (▷^n Q2).
Proof.
  rewrite /IntoAnd=> HP. apply affinely_persistently_if_intro'.
  by rewrite laterN_affinely_persistently_if_2 HP
             affinely_persistently_if_elim laterN_and.
Qed.
Global Instance into_and_except_0 p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (◇ P) (◇ Q1) (◇ Q2).
Proof.
  rewrite /IntoAnd=> HP. apply affinely_persistently_if_intro'.
  by rewrite except_0_affinely_persistently_if_2 HP
             affinely_persistently_if_elim except_0_and.
Qed.

(* IntoSep *)
Global Instance into_sep_later P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /IntoSep=> ->. by rewrite later_sep. Qed.
Global Instance into_sep_laterN n P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /IntoSep=> ->. by rewrite laterN_sep. Qed.
Global Instance into_sep_except_0 P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /IntoSep=> ->. by rewrite except_0_sep. Qed.

(* FIXME: This instance is overly specific, generalize it. *)
Global Instance into_sep_affinely_later `{!Timeless (emp%I : PROP)} P Q1 Q2 :
  IntoSep P Q1 Q2 → Affine Q1 → Affine Q2 →
  IntoSep (bi_affinely (▷ P)) (bi_affinely (▷ Q1)) (bi_affinely (▷ Q2)).
Proof.
  rewrite /IntoSep /= => -> ??.
  rewrite -{1}(affine_affinely Q1) -{1}(affine_affinely Q2) later_sep !later_affinely_1.
  rewrite -except_0_sep /sbi_except_0 affinely_or. apply or_elim, affinely_elim.
  rewrite -(idemp bi_and (bi_affinely (▷ False))%I) persistent_and_sep_1.
  by rewrite -(False_elim Q1) -(False_elim Q2).
Qed.

(* FromOr *)
Global Instance from_or_later P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromOr=><-. by rewrite later_or. Qed.
Global Instance from_or_laterN n P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromOr=><-. by rewrite laterN_or. Qed.
Global Instance from_or_except_0 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /FromOr=><-. by rewrite except_0_or. Qed.

Global Instance from_or_bupd `{BUpdFacts PROP} P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|==> P) (|==> Q1) (|==> Q2).
Proof.
  rewrite /FromOr=><-.
  apply or_elim; apply bupd_mono; auto using or_intro_l, or_intro_r.
Qed.
Global Instance from_or_fupd `{FUpdFacts PROP} E1 E2 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
Proof.
  rewrite /FromOr=><-. apply or_elim; apply fupd_mono;
                         [apply bi.or_intro_l|apply bi.or_intro_r].
Qed.

(* IntoOr *)
Global Instance into_or_later P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /IntoOr=>->. by rewrite later_or. Qed.
Global Instance into_or_laterN n P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /IntoOr=>->. by rewrite laterN_or. Qed.
Global Instance into_or_except_0 P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /IntoOr=>->. by rewrite except_0_or. Qed.

(* FromExist *)
Global Instance from_exist_later {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (▷ P) (λ a, ▷ (Φ a))%I.
Proof.
  rewrite /FromExist=> <-. apply exist_elim=>x. apply later_mono, exist_intro.
Qed.
Global Instance from_exist_laterN {A} n P (Φ : A → PROP) :
  FromExist P Φ → FromExist (▷^n P) (λ a, ▷^n (Φ a))%I.
Proof.
  rewrite /FromExist=> <-. apply exist_elim=>x. apply laterN_mono, exist_intro.
Qed.
Global Instance from_exist_except_0 {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (◇ P) (λ a, ◇ (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite except_0_exist_2. Qed.

Global Instance from_exist_bupd `{BUpdFacts PROP} {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (|==> P) (λ a, |==> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.
Global Instance from_exist_fupd `{FUpdFacts PROP} {A} E1 E2 P (Φ : A → PROP) :
  FromExist P Φ → FromExist (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

(* IntoExist *)
Global Instance into_exist_later {A} P (Φ : A → PROP) :
  IntoExist P Φ → Inhabited A → IntoExist (▷ P) (λ a, ▷ (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP later_exist. Qed.
Global Instance into_exist_laterN {A} n P (Φ : A → PROP) :
  IntoExist P Φ → Inhabited A → IntoExist (▷^n P) (λ a, ▷^n (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP laterN_exist. Qed.
Global Instance into_exist_except_0 {A} P (Φ : A → PROP) :
  IntoExist P Φ → Inhabited A → IntoExist (◇ P) (λ a, ◇ (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP except_0_exist. Qed.

(* IntoForall *)
Global Instance into_forall_later {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (▷ P) (λ a, ▷ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP later_forall. Qed.
Global Instance into_forall_except_0 {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (◇ P) (λ a, ◇ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP except_0_forall. Qed.
Global Instance into_forall_impl_pure φ P Q :
  FromPureT false P φ → IntoForall (P → Q) (λ _ : φ, Q).
Proof.
  rewrite /FromPureT /FromPure /IntoForall=> -[φ' [-> <-]].
  by rewrite pure_impl_forall.
Qed.
Global Instance into_forall_wand_pure φ P Q :
  FromPureT true P φ → IntoForall (P -∗ Q) (λ _ : φ, Q).
Proof.
  rewrite /FromPureT /FromPure /IntoForall=> -[φ' [-> <-]] /=.
  apply forall_intro=>? /=.
  by rewrite -(pure_intro True%I) // /bi_affinely right_id emp_wand.
Qed.

(* FromForall *)
Global Instance from_forall_later {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (▷ P)%I (λ a, ▷ (Φ a))%I.
Proof. rewrite /FromForall=> <-. by rewrite later_forall. Qed.
Global Instance from_forall_except_0 {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (◇ P)%I (λ a, ◇ (Φ a))%I.
Proof. rewrite /FromForall=> <-. by rewrite except_0_forall. Qed.

(* IsExcept0 *)
Global Instance is_except_0_except_0 P : IsExcept0 (◇ P).
Proof. by rewrite /IsExcept0 except_0_idemp. Qed.
Global Instance is_except_0_later P : IsExcept0 (▷ P).
Proof. by rewrite /IsExcept0 except_0_later. Qed.
Global Instance is_except_0_embed `{SbiEmbedding PROP PROP'} P :
  IsExcept0 P → IsExcept0 ⎡P⎤.
Proof. by rewrite /IsExcept0 -sbi_embed_except_0=>->. Qed.
Global Instance is_except_0_bupd `{BUpdFacts PROP} P : IsExcept0 P → IsExcept0 (|==> P).
Proof.
  rewrite /IsExcept0=> HP.
  by rewrite -{2}HP -(except_0_idemp P) -except_0_bupd -(except_0_intro P).
Qed.
Global Instance is_except_0_fupd `{FUpdFacts PROP} E1 E2 P :
  IsExcept0 (|={E1,E2}=> P).
Proof. by rewrite /IsExcept0 except_0_fupd. Qed.

(* FromModal *)
Global Instance from_modal_later P : FromModal (▷ P) P.
Proof. apply later_intro. Qed.
Global Instance from_modal_except_0 P : FromModal (◇ P) P.
Proof. apply except_0_intro. Qed.

Global Instance from_modal_bupd `{BUpdFacts PROP} P : FromModal (|==> P) P.
Proof. apply bupd_intro. Qed.
Global Instance from_modal_fupd E P `{FUpdFacts PROP} : FromModal (|={E}=> P) P.
Proof. rewrite /FromModal. apply fupd_intro. Qed.

(* IntoInternalEq *)
Global Instance into_internal_eq_internal_eq {A : ofeT} (x y : A) :
  @IntoInternalEq PROP A (x ≡ y) x y.
Proof. by rewrite /IntoInternalEq. Qed.
Global Instance into_internal_eq_affinely {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (bi_affinely P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite affinely_elim. Qed.
Global Instance into_internal_eq_absorbingly {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (bi_absorbingly P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite absorbingly_internal_eq. Qed.
Global Instance into_internal_eq_plainly {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (bi_plainly P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite plainly_elim. Qed.
Global Instance into_internal_eq_persistently {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (bi_persistently P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite persistently_elim. Qed.
Global Instance into_internal_eq_embed
       `{SbiEmbedding PROP PROP'} {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq ⎡P⎤ x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite sbi_embed_internal_eq. Qed.

(* IntoExcept0 *)
Global Instance into_except_0_except_0 P : IntoExcept0 (◇ P) P.
Proof. by rewrite /IntoExcept0. Qed.
Global Instance into_except_0_later P : Timeless P → IntoExcept0 (▷ P) P.
Proof. by rewrite /IntoExcept0. Qed.
Global Instance into_except_0_later_if p P : Timeless P → IntoExcept0 (▷?p P) P.
Proof. rewrite /IntoExcept0. destruct p; auto using except_0_intro. Qed.

Global Instance into_except_0_affinely P Q :
  IntoExcept0 P Q → IntoExcept0 (bi_affinely P) (bi_affinely Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_affinely_2. Qed.
Global Instance into_except_0_absorbingly P Q :
  IntoExcept0 P Q → IntoExcept0 (bi_absorbingly P) (bi_absorbingly Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_absorbingly. Qed.
Global Instance into_except_0_plainly `{BiPlainlyExist PROP} P Q :
  IntoExcept0 P Q → IntoExcept0 (bi_plainly P) (bi_plainly Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_plainly. Qed.
Global Instance into_except_0_persistently P Q :
  IntoExcept0 P Q → IntoExcept0 (bi_persistently P) (bi_persistently Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_persistently. Qed.
Global Instance into_except_0_embed `{SbiEmbedding PROP PROP'} P Q :
  IntoExcept0 P Q → IntoExcept0 ⎡P⎤ ⎡Q⎤.
Proof. rewrite /IntoExcept0=> ->. by rewrite sbi_embed_except_0. Qed.

(* ElimModal *)
Global Instance elim_modal_timeless P Q :
  IntoExcept0 P P' → IsExcept0 Q → ElimModal True P P' Q Q.
Proof.
  intros. rewrite /ElimModal (except_0_intro (_ -∗ _)%I).
  by rewrite (into_except_0 P) -except_0_sep wand_elim_r.
Qed.
Global Instance elim_modal_bupd `{BUpdFacts PROP} P Q :
  ElimModal True (|==> P) P (|==> Q) (|==> Q).
Proof. by rewrite /ElimModal bupd_frame_r wand_elim_r bupd_trans. Qed.
Global Instance elim_modal_bupd_plain_goal `{BUpdFacts PROP} P Q :
  Plain Q → ElimModal True (|==> P) P Q Q.
Proof. intros. by rewrite /ElimModal bupd_frame_r wand_elim_r bupd_plain. Qed.
Global Instance elim_modal_bupd_plain `{BUpdFacts PROP} P Q :
  Plain P → ElimModal True (|==> P) P Q Q.
Proof. intros. by rewrite /ElimModal bupd_plain wand_elim_r. Qed.
Global Instance elim_modal_bupd_fupd `{FUpdFacts PROP} E1 E2 P Q :
  ElimModal True (|==> P) P (|={E1,E2}=> Q) (|={E1,E2}=> Q) | 10.
Proof.
  by rewrite /ElimModal (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_trans.
Qed.
Global Instance elim_modal_fupd_fupd `{FUpdFacts PROP} E1 E2 E3 P Q :
  ElimModal True (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).
Proof. by rewrite /ElimModal fupd_frame_r wand_elim_r fupd_trans. Qed.

(* AddModal *)
(* High priority to add a ▷ rather than a ◇ when P is timeless. *)
Global Instance add_modal_later_except_0 P Q :
  Timeless P → AddModal (▷ P) P (◇ Q) | 0.
Proof.
  intros. rewrite /AddModal (except_0_intro (_ -∗ _)%I) (timeless P).
  by rewrite -except_0_sep wand_elim_r except_0_idemp.
Qed.
Global Instance add_modal_later P Q :
  Timeless P → AddModal (▷ P) P (▷ Q) | 0.
Proof.
  intros. rewrite /AddModal (except_0_intro (_ -∗ _)%I) (timeless P).
  by rewrite -except_0_sep wand_elim_r except_0_later.
Qed.
Global Instance add_modal_except_0 P Q : AddModal (◇ P) P (◇ Q) | 1.
Proof.
  intros. rewrite /AddModal (except_0_intro (_ -∗ _)%I).
  by rewrite -except_0_sep wand_elim_r except_0_idemp.
Qed.
Global Instance add_modal_except_0_later P Q : AddModal (◇ P) P (▷ Q) | 1.
Proof.
  intros. rewrite /AddModal (except_0_intro (_ -∗ _)%I).
  by rewrite -except_0_sep wand_elim_r except_0_later.
Qed.

Global Instance add_modal_bupd `{BUpdFacts PROP} P Q : AddModal (|==> P) P (|==> Q).
Proof. by rewrite /AddModal bupd_frame_r wand_elim_r bupd_trans. Qed.
Global Instance add_modal_fupd `{FUpdFacts PROP} E1 E2 P Q :
  AddModal (|={E1}=> P) P (|={E1,E2}=> Q).
Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_trans. Qed.

(* Frame *)
Global Instance frame_eq_embed `{SbiEmbedding PROP PROP'} p P Q (Q' : PROP')
       {A : ofeT} (a b : A) :
  Frame p (a ≡ b) P Q → MakeEmbed Q Q' → Frame p (a ≡ b) ⎡P⎤ Q'.
Proof. rewrite /Frame /MakeEmbed -sbi_embed_internal_eq. apply (frame_embed p P Q). Qed.

Class MakeLaterN (n : nat) (P lP : PROP) := make_laterN : ▷^n P ⊣⊢ lP.
Arguments MakeLaterN _%nat _%I _%I.
Global Instance make_laterN_true n : MakeLaterN n True True | 0.
Proof. by rewrite /MakeLaterN laterN_True. Qed.
Global Instance make_laterN_0 P : MakeLaterN 0 P P | 0.
Proof. by rewrite /MakeLaterN. Qed.
Global Instance make_laterN_1 P : MakeLaterN 1 P (▷ P) | 2.
Proof. by rewrite /MakeLaterN. Qed.
Global Instance make_laterN_default P : MakeLaterN n P (▷^n P) | 100.
Proof. by rewrite /MakeLaterN. Qed.

Global Instance frame_later p R R' P Q Q' :
  NoBackTrack (MaybeIntoLaterN true 1 R' R) →
  Frame p R P Q → MakeLaterN 1 Q Q' → Frame p R' (▷ P) Q'.
Proof.
  rewrite /Frame /MakeLaterN /MaybeIntoLaterN=>-[->] <- <-.
  by rewrite later_affinely_persistently_if_2 later_sep.
Qed.
Global Instance frame_laterN p n R R' P Q Q' :
  NoBackTrack (MaybeIntoLaterN true n R' R) →
  Frame p R P Q → MakeLaterN n Q Q' → Frame p R' (▷^n P) Q'.
Proof.
  rewrite /Frame /MakeLaterN /MaybeIntoLaterN=>-[->] <- <-.
  by rewrite laterN_affinely_persistently_if_2 laterN_sep.
Qed.

Global Instance frame_bupd `{BUpdFacts PROP} p R P Q :
  Frame p R P Q → Frame p R (|==> P) (|==> Q).
Proof. rewrite /Frame=><-. by rewrite bupd_frame_l. Qed.
Global Instance frame_fupd `{FUpdFacts PROP} p E1 E2 R P Q :
  Frame p R P Q → Frame p R (|={E1,E2}=> P) (|={E1,E2}=> Q).
Proof. rewrite /Frame=><-. by rewrite fupd_frame_l. Qed.

Class MakeExcept0 (P Q : PROP) := make_except_0 : ◇ P ⊣⊢ Q.
Arguments MakeExcept0 _%I _%I.

Global Instance make_except_0_True : MakeExcept0 True True.
Proof. by rewrite /MakeExcept0 except_0_True. Qed.
Global Instance make_except_0_default P : MakeExcept0 P (◇ P) | 100.
Proof. by rewrite /MakeExcept0. Qed.

Global Instance frame_except_0 p R P Q Q' :
  Frame p R P Q → MakeExcept0 Q Q' → Frame p R (◇ P) Q'.
Proof.
  rewrite /Frame /MakeExcept0=><- <-.
  by rewrite except_0_sep -(except_0_intro (□?p R)%I).
Qed.

(* IntoLater *)
Global Instance into_laterN_0 only_head P : IntoLaterN only_head 0 P P.
Proof. by rewrite /IntoLaterN /MaybeIntoLaterN. Qed.
Global Instance into_laterN_later only_head n n' m' P Q lQ :
  NatCancel n 1 n' m' →
  (** If canceling has failed (i.e. [1 = m']), we should make progress deeper
  into [P], as such, we continue with the [IntoLaterN] class, which is required
  to make progress. If canceling has succeeded, we do not need to make further
  progress, but there may still be a left-over (i.e. [n']) to cancel more deeply
  into [P], as such, we continue with [MaybeIntoLaterN]. *)
  TCIf (TCEq 1 m') (IntoLaterN only_head n' P Q) (MaybeIntoLaterN only_head n' P Q) →
  MakeLaterN m' Q lQ →
  IntoLaterN only_head n (▷ P) lQ | 2.
Proof.
  rewrite /MakeLaterN /IntoLaterN /MaybeIntoLaterN /NatCancel.
  move=> Hn [_ ->|->] <-;
    by rewrite -later_laterN -laterN_plus -Hn Nat.add_comm.
Qed.
Global Instance into_laterN_laterN only_head n m n' m' P Q lQ :
  NatCancel n m n' m' →
  TCIf (TCEq m m') (IntoLaterN only_head n' P Q) (MaybeIntoLaterN only_head n' P Q) →
  MakeLaterN m' Q lQ →
  IntoLaterN only_head n (▷^m P) lQ | 1.
Proof.
  rewrite /MakeLaterN /IntoLaterN /MaybeIntoLaterN /NatCancel.
  move=> Hn [_ ->|->] <-; by rewrite -!laterN_plus -Hn Nat.add_comm.
Qed.

Global Instance into_laterN_and_l n P1 P2 Q1 Q2 :
  IntoLaterN false n P1 Q1 → MaybeIntoLaterN false n P2 Q2 →
  IntoLaterN false n (P1 ∧ P2) (Q1 ∧ Q2) | 10.
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> -> ->. by rewrite laterN_and. Qed.
Global Instance into_laterN_and_r n P P2 Q2 :
  IntoLaterN false n P2 Q2 → IntoLaterN false n (P ∧ P2) (P ∧ Q2) | 11.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_and -(laterN_intro _ P).
Qed.

Global Instance into_laterN_forall {A} n (Φ Ψ : A → PROP) :
  (∀ x, IntoLaterN false n (Φ x) (Ψ x)) →
  IntoLaterN false n (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN laterN_forall=> ?. by apply forall_mono. Qed.
Global Instance into_laterN_exist {A} n (Φ Ψ : A → PROP) :
  (∀ x, IntoLaterN false n (Φ x) (Ψ x)) →
  IntoLaterN false n (∃ x, Φ x) (∃ x, Ψ x).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN -laterN_exist_2=> ?. by apply exist_mono. Qed.

Global Instance into_laterN_or_l n P1 P2 Q1 Q2 :
  IntoLaterN false n P1 Q1 → MaybeIntoLaterN false n P2 Q2 →
  IntoLaterN false n (P1 ∨ P2) (Q1 ∨ Q2) | 10.
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> -> ->. by rewrite laterN_or. Qed.
Global Instance into_laterN_or_r n P P2 Q2 :
  IntoLaterN false n P2 Q2 →
  IntoLaterN false n (P ∨ P2) (P ∨ Q2) | 11.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_or -(laterN_intro _ P).
Qed.

Global Instance into_later_affinely n P Q :
  MaybeIntoLaterN false n P Q →
  MaybeIntoLaterN false n (bi_affinely P) (bi_affinely Q).
Proof. rewrite /MaybeIntoLaterN=> ->. by rewrite laterN_affinely_2. Qed.
Global Instance into_later_absorbingly n P Q :
  MaybeIntoLaterN false n P Q →
  MaybeIntoLaterN false n (bi_absorbingly P) (bi_absorbingly Q).
Proof. rewrite /MaybeIntoLaterN=> ->. by rewrite laterN_absorbingly. Qed.
Global Instance into_later_plainly n P Q :
  MaybeIntoLaterN false n P Q →
  MaybeIntoLaterN false n (bi_plainly P) (bi_plainly Q).
Proof. rewrite /MaybeIntoLaterN=> ->. by rewrite laterN_plainly. Qed.
Global Instance into_later_persistently n P Q :
  MaybeIntoLaterN false n P Q →
  MaybeIntoLaterN false n (bi_persistently P) (bi_persistently Q).
Proof. rewrite /MaybeIntoLaterN=> ->. by rewrite laterN_persistently. Qed.
Global Instance into_later_embed`{SbiEmbedding PROP PROP'} n P Q :
  MaybeIntoLaterN false n P Q → MaybeIntoLaterN false n ⎡P⎤ ⎡Q⎤.
Proof. rewrite /MaybeIntoLaterN=> ->. by rewrite sbi_embed_laterN. Qed.

Global Instance into_laterN_sep_l n P1 P2 Q1 Q2 :
  IntoLaterN false n P1 Q1 → MaybeIntoLaterN false n P2 Q2 →
  IntoLaterN false n (P1 ∗ P2) (Q1 ∗ Q2) | 10.
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> -> ->. by rewrite laterN_sep. Qed.
Global Instance into_laterN_sep_r n P P2 Q2 :
  IntoLaterN false n P2 Q2 →
  IntoLaterN false n (P ∗ P2) (P ∗ Q2) | 11.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_sep -(laterN_intro _ P).
Qed.

Global Instance into_laterN_big_sepL n {A} (Φ Ψ : nat → A → PROP) (l: list A) :
  (∀ x k, IntoLaterN false n (Φ k x) (Ψ k x)) →
  IntoLaterN false n ([∗ list] k ↦ x ∈ l, Φ k x) ([∗ list] k ↦ x ∈ l, Ψ k x).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ?.
  rewrite big_opL_commute. by apply big_sepL_mono.
Qed.
Global Instance into_laterN_big_sepM n `{Countable K} {A}
    (Φ Ψ : K → A → PROP) (m : gmap K A) :
  (∀ x k, IntoLaterN false n (Φ k x) (Ψ k x)) →
  IntoLaterN false n ([∗ map] k ↦ x ∈ m, Φ k x) ([∗ map] k ↦ x ∈ m, Ψ k x).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ?.
  rewrite big_opM_commute. by apply big_sepM_mono.
Qed.
Global Instance into_laterN_big_sepS n `{Countable A}
    (Φ Ψ : A → PROP) (X : gset A) :
  (∀ x, IntoLaterN false n (Φ x) (Ψ x)) →
  IntoLaterN false n ([∗ set] x ∈ X, Φ x) ([∗ set] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ?.
  rewrite big_opS_commute. by apply big_sepS_mono.
Qed.
Global Instance into_laterN_big_sepMS n `{Countable A}
    (Φ Ψ : A → PROP) (X : gmultiset A) :
  (∀ x, IntoLaterN false n (Φ x) (Ψ x)) →
  IntoLaterN false n ([∗ mset] x ∈ X, Φ x) ([∗ mset] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ?.
  rewrite big_opMS_commute. by apply big_sepMS_mono.
Qed.

(* FromLater *)
Global Instance from_laterN_later P : FromLaterN 1 (▷ P) P | 0.
Proof. by rewrite /FromLaterN. Qed.
Global Instance from_laterN_laterN n P : FromLaterN n (▷^n P) P | 0.
Proof. by rewrite /FromLaterN. Qed.

(* The instances below are used when stripping a specific number of laters, or
to balance laters in different branches of ∧, ∨ and ∗. *)
Global Instance from_laterN_0 P : FromLaterN 0 P P | 100. (* fallthrough *)
Proof. by rewrite /FromLaterN. Qed.
Global Instance from_laterN_later_S n P Q :
  FromLaterN n P Q → FromLaterN (S n) (▷ P) Q.
Proof. by rewrite /FromLaterN=><-. Qed.
Global Instance from_laterN_later_plus n m P Q :
  FromLaterN m P Q → FromLaterN (n + m) (▷^n P) Q.
Proof. rewrite /FromLaterN=><-. by rewrite laterN_plus. Qed.

Global Instance from_later_and n P1 P2 Q1 Q2 :
  FromLaterN n P1 Q1 → FromLaterN n P2 Q2 → FromLaterN n (P1 ∧ P2) (Q1 ∧ Q2).
Proof. intros ??; red. by rewrite laterN_and; apply and_mono. Qed.
Global Instance from_later_or n P1 P2 Q1 Q2 :
  FromLaterN n P1 Q1 → FromLaterN n P2 Q2 → FromLaterN n (P1 ∨ P2) (Q1 ∨ Q2).
Proof. intros ??; red. by rewrite laterN_or; apply or_mono. Qed.
Global Instance from_later_sep n P1 P2 Q1 Q2 :
  FromLaterN n P1 Q1 → FromLaterN n P2 Q2 → FromLaterN n (P1 ∗ P2) (Q1 ∗ Q2).
Proof. intros ??; red. by rewrite laterN_sep; apply sep_mono. Qed.

Global Instance from_later_affinely n P Q `{BiAffine PROP} :
  FromLaterN n P Q → FromLaterN n (bi_affinely P) (bi_affinely Q).
Proof. rewrite /FromLaterN=><-. by rewrite affinely_elim affine_affinely. Qed.
Global Instance from_later_plainly n P Q :
  FromLaterN n P Q → FromLaterN n (bi_plainly P) (bi_plainly Q).
Proof. by rewrite /FromLaterN laterN_plainly=> ->. Qed.
Global Instance from_later_persistently n P Q :
  FromLaterN n P Q → FromLaterN n (bi_persistently P) (bi_persistently Q).
Proof. by rewrite /FromLaterN laterN_persistently=> ->. Qed.
Global Instance from_later_absorbingly n P Q :
  FromLaterN n P Q → FromLaterN n (bi_absorbingly P) (bi_absorbingly Q).
Proof. by rewrite /FromLaterN laterN_absorbingly=> ->. Qed.
Global Instance from_later_embed`{SbiEmbedding PROP PROP'} n P Q :
  FromLaterN n P Q → FromLaterN n ⎡P⎤ ⎡Q⎤.
Proof. rewrite /FromLaterN=> <-. by rewrite sbi_embed_laterN. Qed.

Global Instance from_later_forall {A} n (Φ Ψ : A → PROP) :
  (∀ x, FromLaterN n (Φ x) (Ψ x)) → FromLaterN n (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /FromLaterN laterN_forall=> ?. by apply forall_mono. Qed.
Global Instance from_later_exist {A} n (Φ Ψ : A → PROP) :
  Inhabited A → (∀ x, FromLaterN n (Φ x) (Ψ x)) →
  FromLaterN n (∃ x, Φ x) (∃ x, Ψ x).
Proof. intros ?. rewrite /FromLaterN laterN_exist=> ?. by apply exist_mono. Qed.
End sbi_instances.
