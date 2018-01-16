From iris.proofmode Require Export classes.
From iris.bi Require Import bi tactics.
Set Default Proof Using "Type".
Import bi.

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

Global Instance into_pure_eq {A : ofeT} (a b : A) :
  Discrete a → @IntoPure M (a ≡ b) (a ≡ b).
Proof. intros. by rewrite /IntoPure discrete_eq. Qed.

Global Instance into_pure_pure_and (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∧ P2) (φ1 ∧ φ2).
Proof. rewrite /IntoPure pure_and. by intros -> ->. Qed.
Global Instance into_pure_pure_or (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∨ P2) (φ1 ∨ φ2).
Proof. rewrite /IntoPure pure_or. by intros -> ->. Qed.
Global Instance into_pure_pure_impl (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 → P2) (φ1 → φ2).
Proof. rewrite /FromPure /IntoPure pure_impl. by intros -> ->. Qed.

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
  FromPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 -∗ P2) (φ1 → φ2).
Proof. rewrite /FromPure /IntoPure=> <- ->. by rewrite pure_impl impl_wand_2. Qed.

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
Global Instance from_pure_pure φ : @FromPure PROP ⌜φ⌝ φ.
Proof. by rewrite /FromPure. Qed.
Global Instance from_pure_internal_eq {A : ofeT} (a b : A) :
  @FromPure PROP (a ≡ b) (a ≡ b).
Proof. by rewrite /FromPure pure_internal_eq. Qed.

Global Instance from_pure_pure_and (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 ∧ P2) (φ1 ∧ φ2).
Proof. rewrite /FromPure pure_and. by intros -> ->. Qed.
Global Instance from_pure_pure_or (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 ∨ P2) (φ1 ∨ φ2).
Proof. rewrite /FromPure pure_or. by intros -> ->. Qed.
Global Instance from_pure_pure_impl (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 → P2) (φ1 → φ2).
Proof. rewrite /FromPure /IntoPure pure_impl. by intros -> ->. Qed.

Global Instance from_pure_exist {A} (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, FromPure (Φ x) (φ x)) → FromPure (∃ x, Φ x) (∃ x, φ x).
Proof. rewrite /FromPure=>Hx. rewrite pure_exist. by setoid_rewrite Hx. Qed.
Global Instance from_pure_forall {A} (Φ : A → PROP) (φ : A → Prop) :
  (∀ x, FromPure (Φ x) (φ x)) → FromPure (∀ x, Φ x) (∀ x, φ x).
Proof. rewrite /FromPure=>Hx. rewrite pure_forall. by setoid_rewrite Hx. Qed.

Global Instance from_pure_pure_sep (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 ∗ P2) (φ1 ∧ φ2).
Proof. rewrite /FromPure=> <- <-. by rewrite pure_and persistent_and_sep_1. Qed.
Global Instance from_pure_pure_wand (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 -∗ P2) (φ1 → φ2).
Proof.
  rewrite /FromPure /IntoPure=> -> <-.
  by rewrite pure_wand_forall pure_impl pure_impl_forall.
Qed.

Global Instance from_pure_plainly P φ :
  FromPure P φ → FromPure (bi_plainly P) φ.
Proof. rewrite /FromPure=> <-. by rewrite plainly_pure. Qed.
Global Instance from_pure_persistently P φ :
  FromPure P φ → FromPure (bi_persistently P) φ.
Proof. rewrite /FromPure=> <-. by rewrite persistently_pure. Qed.
Global Instance from_pure_affinely P φ `{!Affine P} :
  FromPure P φ → FromPure (bi_affinely P) φ.
Proof. by rewrite /FromPure affine_affinely. Qed.
Global Instance from_pure_absorbingly P φ : FromPure P φ → FromPure (bi_absorbingly P) φ.
Proof. rewrite /FromPure=> <-. by rewrite absorbingly_pure. Qed.
Global Instance from_pure_embed `{BiEmbedding PROP PROP'} P φ :
  FromPure P φ → FromPure ⎡P⎤ φ.
Proof. rewrite /FromPure=> <-. by rewrite bi_embed_pure. Qed.

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
       `{BiEmbedding PROP PROP'} {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq ⎡P⎤ x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite bi_embed_internal_eq. Qed.

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
Global Instance from_always_here P : FromAlways false false false P P | 1.
Proof. by rewrite /FromAlways. Qed.
Global Instance from_always_plainly a pe pl P Q :
  FromAlways a pe pl P Q → FromAlways false true true (bi_plainly P) Q | 0.
Proof.
  rewrite /FromAlways /= => <-.
  destruct a, pe, pl; rewrite /= ?persistently_affinely ?plainly_affinely
       !persistently_plainly ?plainly_idemp ?plainly_persistently //.
Qed.
Global Instance from_always_persistently a pe pl P Q :
  FromAlways a pe pl P Q → FromAlways false true pl (bi_persistently P) Q | 0.
Proof.
  rewrite /FromAlways /= => <-.
  destruct a, pe; rewrite /= ?persistently_affinely ?persistently_idemp //.
Qed.
Global Instance from_always_affinely a pe pl P Q :
  FromAlways a pe pl P Q → FromAlways true pe pl (bi_affinely P) Q | 0.
Proof.
  rewrite /FromAlways /= => <-. destruct a; by rewrite /= ?affinely_idemp.
Qed.
Global Instance from_always_embed `{BiEmbedding PROP PROP'} a pe pl P Q :
  FromAlways a pe pl P Q → FromAlways a pe pl ⎡P⎤ ⎡Q⎤ | 0.
Proof.
  rewrite /FromAlways=><-.
  by rewrite bi_embed_affinely_if bi_embed_persistently_if bi_embed_plainly_if.
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
  TCOr (TCAnd (Affine P1) (Affine P2)) (TCAnd (Absorbing P1) (Absorbing P2)) →
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

(* FIXME: This instance is kind of strange, it just gets rid of the bi_affinely. Also, it
overlaps with `into_sep_affinely_later`, and hence has lower precedence. *)
Global Instance into_sep_affinely P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (bi_affinely P) Q1 Q2 | 20.
Proof. rewrite /IntoSep /= => ->. by rewrite affinely_elim. Qed.

Global Instance into_sep_plainly `{BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (bi_plainly P) (bi_plainly Q1) (bi_plainly Q2).
Proof. rewrite /IntoSep /= => ->. by rewrite plainly_sep. Qed.
Global Instance into_sep_persistently `{BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 →
  IntoSep (bi_persistently P) (bi_persistently Q1) (bi_persistently Q2).
Proof. rewrite /IntoSep /= => ->. by rewrite persistently_sep. Qed.

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
Global Instance elim_modal_wand P P' Q Q' R :
  ElimModal P P' Q Q' → ElimModal P P' (R -∗ Q) (R -∗ Q').
Proof.
  rewrite /ElimModal=> H. apply wand_intro_r.
  by rewrite wand_curry -assoc (comm _ P') -wand_curry wand_elim_l.
Qed.
Global Instance elim_modal_forall {A} P P' (Φ Ψ : A → PROP) :
  (∀ x, ElimModal P P' (Φ x) (Ψ x)) → ElimModal P P' (∀ x, Φ x) (∀ x, Ψ x).
Proof.
  rewrite /ElimModal=> H. apply forall_intro=> a. by rewrite (forall_elim a).
Qed.
Global Instance elim_modal_absorbingly P Q : Absorbing Q → ElimModal (bi_absorbingly P) P Q Q.
Proof.
  rewrite /ElimModal=> H. by rewrite absorbingly_sep_l wand_elim_r absorbing_absorbingly.
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

Global Instance frame_here_pure p φ Q : FromPure Q φ → Frame p ⌜φ⌝ Q True.
Proof.
  rewrite /FromPure /Frame=> <-. by rewrite affinely_persistently_if_elim sep_elim_l.
Qed.

Class MakeMorphism `{BiEmbedding PROP PROP'} P (Q : PROP') :=
  make_embed : ⎡P⎤ ⊣⊢ Q.
Arguments MakeMorphism {_ _ _} _%I _%I.
Global Instance make_embed_pure `{BiEmbedding PROP PROP'} φ :
  MakeMorphism ⌜φ⌝ ⌜φ⌝.
Proof. by rewrite /MakeMorphism bi_embed_pure. Qed.
Global Instance make_embed_emp `{BiEmbedding PROP PROP'} :
  MakeMorphism emp emp.
Proof. by rewrite /MakeMorphism bi_embed_emp. Qed.
Global Instance make_embed_default `{BiEmbedding PROP PROP'} :
  MakeMorphism P ⎡P⎤ | 100.
Proof. by rewrite /MakeMorphism. Qed.

Global Instance frame_embed `{BiEmbedding PROP PROP'} p P Q (Q' : PROP') R :
  Frame p R P Q → MakeMorphism Q Q' → Frame p ⎡R⎤ ⎡P⎤ Q'.
Proof.
  rewrite /Frame /MakeMorphism => <- <-.
  rewrite bi_embed_sep bi_embed_affinely_if bi_embed_persistently_if => //.
Qed.

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

Global Instance frame_sep_persistent_l R P1 P2 Q1 Q2 Q' :
  Frame true R P1 Q1 → MaybeFrame true R P2 Q2 → MakeSep Q1 Q2 Q' →
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

Global Instance frame_and_l p R P1 P2 Q1 Q2 Q :
  Frame p R P1 Q1 → MaybeFrame p R P2 Q2 →
  MakeAnd Q1 Q2 Q → Frame p R (P1 ∧ P2) Q | 9.
Proof.
  rewrite /Frame /MakeAnd => <- <- <- /=.
  auto using and_intro, and_elim_l, and_elim_r, sep_mono.
Qed.
Global Instance frame_and_persistent_r R P1 P2 Q2 Q :
  Frame true R P2 Q2 →
  MakeAnd P1 Q2 Q → Frame true R (P1 ∧ P2) Q | 10.
Proof.
  rewrite /Frame /MakeAnd => <- <- /=. rewrite -!persistently_and_affinely_sep_l.
  auto using and_intro, and_elim_l', and_elim_r'.
Qed.
Global Instance frame_and_r R P1 P2 Q2 Q :
  TCOr (Affine R) (Absorbing P1) →
  Frame false R P2 Q2 →
  MakeAnd P1 Q2 Q → Frame false R (P1 ∧ P2) Q | 10.
Proof.
  rewrite /Frame /MakeAnd=> ? <- <- /=. apply and_intro.
  - by rewrite and_elim_l sep_elim_r.
  - by rewrite and_elim_r.
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

Global Instance frame_or_persistent_l R P1 P2 Q1 Q2 Q :
  Frame true R P1 Q1 → MaybeFrame true R P2 Q2 → MakeOr Q1 Q2 Q →
  Frame true R (P1 ∨ P2) Q | 9.
Proof. rewrite /Frame /MakeOr => <- <- <-. by rewrite -sep_or_l. Qed.
Global Instance frame_or_persistent_r R P1 P2 Q1 Q2 Q :
  MaybeFrame true R P2 Q2 → MakeOr P1 Q2 Q →
  Frame true R (P1 ∨ P2) Q | 10.
Proof.
  rewrite /Frame /MaybeFrame /MakeOr => <- <- /=.
  by rewrite sep_or_l sep_elim_r.
Qed.
Global Instance frame_or R P1 P2 Q1 Q2 Q :
  Frame false R P1 Q1 → Frame false R P2 Q2 → MakeOr Q1 Q2 Q →
  Frame false R (P1 ∨ P2) Q.
Proof. rewrite /Frame /MakeOr => <- <- <-. by rewrite -sep_or_l. Qed.

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

(* FromModal *)
Global Instance from_modal_absorbingly P : FromModal (bi_absorbingly P) P.
Proof. apply absorbingly_intro. Qed.
Global Instance from_modal_embed `{BiEmbedding PROP PROP'} P Q :
  FromModal P Q → FromModal ⎡P⎤ ⎡Q⎤.
Proof. by rewrite /FromModal=> ->. Qed.
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

(* FromPure *)
Global Instance from_pure_later P φ : FromPure P φ → FromPure (▷ P) φ.
Proof. rewrite /FromPure=> ->. apply later_intro. Qed.
Global Instance from_pure_laterN n P φ : FromPure P φ → FromPure (▷^n P) φ.
Proof. rewrite /FromPure=> ->. apply laterN_intro. Qed.
Global Instance from_pure_except_0 P φ : FromPure P φ → FromPure (◇ P) φ.
Proof. rewrite /FromPure=> ->. apply except_0_intro. Qed.

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
  Affine Q1 → Affine Q2 → IntoSep P Q1 Q2 →
  IntoSep (bi_affinely (▷ P)) (bi_affinely (▷ Q1)) (bi_affinely (▷ Q2)).
Proof.
  rewrite /IntoSep /= => ?? ->.
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
  FromPureT P φ → IntoForall (P → Q) (λ _ : φ, Q).
Proof.
  rewrite /FromPureT /FromPure /IntoForall=> -[φ' [-> <-]].
  by rewrite pure_impl_forall.
Qed.
Global Instance into_forall_wand_pure φ P Q :
  Absorbing Q → FromPureT P φ → IntoForall (P -∗ Q) (λ _ : φ, Q).
Proof.
  rewrite /FromPureT /FromPure /IntoForall=> ? -[φ' [-> <-]].
  by rewrite pure_wand_forall.
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

(* FromModal *)
Global Instance from_modal_later P : FromModal (▷ P) P.
Proof. apply later_intro. Qed.
Global Instance from_modal_except_0 P : FromModal (◇ P) P.
Proof. apply except_0_intro. Qed.

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
  IntoExcept0 P P' → IsExcept0 Q → ElimModal P P' Q Q.
Proof.
  intros. rewrite /ElimModal (except_0_intro (_ -∗ _)%I).
  by rewrite (into_except_0 P) -except_0_sep wand_elim_r.
Qed.

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

(* Frame *)
Class MakeLater (P lP : PROP) := make_later : ▷ P ⊣⊢ lP.
Arguments MakeLater _%I _%I.

Global Instance make_later_true : MakeLater True True.
Proof. by rewrite /MakeLater later_True. Qed.
Global Instance make_later_default P : MakeLater P (▷ P) | 100.
Proof. by rewrite /MakeLater. Qed.

Global Instance frame_later p R R' P Q Q' :
  IntoLaterN 1 R' R → Frame p R P Q → MakeLater Q Q' → Frame p R' (▷ P) Q'.
Proof.
  rewrite /Frame /MakeLater /IntoLaterN=>-> <- <- /=.
  by rewrite later_affinely_persistently_if_2 later_sep.
Qed.

Class MakeLaterN (n : nat) (P lP : PROP) := make_laterN : ▷^n P ⊣⊢ lP.
Arguments MakeLaterN _%nat _%I _%I.

Global Instance make_laterN_true n : MakeLaterN n True True.
Proof. by rewrite /MakeLaterN laterN_True. Qed.
Global Instance make_laterN_default P : MakeLaterN n P (▷^n P) | 100.
Proof. by rewrite /MakeLaterN. Qed.

Global Instance frame_laterN p n R R' P Q Q' :
  IntoLaterN n R' R → Frame p R P Q → MakeLaterN n Q Q' → Frame p R' (▷^n P) Q'.
Proof.
  rewrite /Frame /MakeLaterN /IntoLaterN=>-> <- <-.
  by rewrite laterN_affinely_persistently_if_2 laterN_sep.
Qed.

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
Global Instance into_laterN_later n P Q :
  IntoLaterN n P Q → IntoLaterN' (S n) (▷ P) Q.
Proof. by rewrite /IntoLaterN' /IntoLaterN =>->. Qed.
Global Instance into_laterN_laterN n P : IntoLaterN' n (▷^n P) P.
Proof. by rewrite /IntoLaterN' /IntoLaterN. Qed.
Global Instance into_laterN_laterN_plus n m P Q :
  IntoLaterN m P Q → IntoLaterN' (n + m) (▷^n P) Q.
Proof. rewrite /IntoLaterN' /IntoLaterN=>->. by rewrite laterN_plus. Qed.

Global Instance into_laterN_and_l n P1 P2 Q1 Q2 :
  IntoLaterN' n P1 Q1 → IntoLaterN n P2 Q2 →
  IntoLaterN' n (P1 ∧ P2) (Q1 ∧ Q2) | 10.
Proof. rewrite /IntoLaterN' /IntoLaterN=> -> ->. by rewrite laterN_and. Qed.
Global Instance into_laterN_and_r n P P2 Q2 :
  IntoLaterN' n P2 Q2 → IntoLaterN' n (P ∧ P2) (P ∧ Q2) | 11.
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ->. by rewrite laterN_and -(laterN_intro _ P).
Qed.

Global Instance into_laterN_or_l n P1 P2 Q1 Q2 :
  IntoLaterN' n P1 Q1 → IntoLaterN n P2 Q2 →
  IntoLaterN' n (P1 ∨ P2) (Q1 ∨ Q2) | 10.
Proof. rewrite /IntoLaterN' /IntoLaterN=> -> ->. by rewrite laterN_or. Qed.
Global Instance into_laterN_or_r n P P2 Q2 :
  IntoLaterN' n P2 Q2 →
  IntoLaterN' n (P ∨ P2) (P ∨ Q2) | 11.
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ->. by rewrite laterN_or -(laterN_intro _ P).
Qed.

Global Instance into_laterN_forall {A} n (Φ Ψ : A → PROP) :
  (∀ x, IntoLaterN' n (Φ x) (Ψ x)) → IntoLaterN' n (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /IntoLaterN' /IntoLaterN laterN_forall=> ?. by apply forall_mono. Qed.
Global Instance into_laterN_exist {A} n (Φ Ψ : A → PROP) :
  (∀ x, IntoLaterN' n (Φ x) (Ψ x)) →
  IntoLaterN' n (∃ x, Φ x) (∃ x, Ψ x).
Proof. rewrite /IntoLaterN' /IntoLaterN -laterN_exist_2=> ?. by apply exist_mono. Qed.

Global Instance into_later_affinely n P Q :
  IntoLaterN n P Q → IntoLaterN n (bi_affinely P) (bi_affinely Q).
Proof. rewrite /IntoLaterN=> ->. by rewrite laterN_affinely_2. Qed.
Global Instance into_later_absorbingly n P Q :
  IntoLaterN n P Q → IntoLaterN n (bi_absorbingly P) (bi_absorbingly Q).
Proof. rewrite /IntoLaterN=> ->. by rewrite laterN_absorbingly. Qed.
Global Instance into_later_plainly n P Q :
  IntoLaterN n P Q → IntoLaterN n (bi_plainly P) (bi_plainly Q).
Proof. rewrite /IntoLaterN=> ->. by rewrite laterN_plainly. Qed.
Global Instance into_later_persistently n P Q :
  IntoLaterN n P Q → IntoLaterN n (bi_persistently P) (bi_persistently Q).
Proof. rewrite /IntoLaterN=> ->. by rewrite laterN_persistently. Qed.
Global Instance into_later_embed`{SbiEmbedding PROP PROP'} n P Q :
  IntoLaterN n P Q → IntoLaterN n ⎡P⎤ ⎡Q⎤.
Proof. rewrite /IntoLaterN=> ->. by rewrite sbi_embed_laterN. Qed.

Global Instance into_laterN_sep_l n P1 P2 Q1 Q2 :
  IntoLaterN' n P1 Q1 → IntoLaterN n P2 Q2 →
  IntoLaterN' n (P1 ∗ P2) (Q1 ∗ Q2) | 10.
Proof. rewrite /IntoLaterN' /IntoLaterN=> -> ->. by rewrite laterN_sep. Qed.
Global Instance into_laterN_sep_r n P P2 Q2 :
  IntoLaterN' n P2 Q2 →
  IntoLaterN' n (P ∗ P2) (P ∗ Q2) | 11.
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ->. by rewrite laterN_sep -(laterN_intro _ P).
Qed.

Global Instance into_laterN_big_sepL n {A} (Φ Ψ : nat → A → PROP) (l: list A) :
  (∀ x k, IntoLaterN' n (Φ k x) (Ψ k x)) →
  IntoLaterN' n ([∗ list] k ↦ x ∈ l, Φ k x) ([∗ list] k ↦ x ∈ l, Ψ k x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_opL_commute. by apply big_sepL_mono.
Qed.
Global Instance into_laterN_big_sepM n `{Countable K} {A}
    (Φ Ψ : K → A → PROP) (m : gmap K A) :
  (∀ x k, IntoLaterN' n (Φ k x) (Ψ k x)) →
  IntoLaterN' n ([∗ map] k ↦ x ∈ m, Φ k x) ([∗ map] k ↦ x ∈ m, Ψ k x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_opM_commute. by apply big_sepM_mono.
Qed.
Global Instance into_laterN_big_sepS n `{Countable A}
    (Φ Ψ : A → PROP) (X : gset A) :
  (∀ x, IntoLaterN' n (Φ x) (Ψ x)) →
  IntoLaterN' n ([∗ set] x ∈ X, Φ x) ([∗ set] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_opS_commute. by apply big_sepS_mono.
Qed.
Global Instance into_laterN_big_sepMS n `{Countable A}
    (Φ Ψ : A → PROP) (X : gmultiset A) :
  (∀ x, IntoLaterN' n (Φ x) (Ψ x)) →
  IntoLaterN' n ([∗ mset] x ∈ X, Φ x) ([∗ mset] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
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
