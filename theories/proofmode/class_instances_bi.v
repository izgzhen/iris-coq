From stdpp Require Import nat_cancel.
From iris.bi Require Import bi tactics telescopes.
From iris.proofmode Require Import base modality_instances classes ltac_tactics.
Set Default Proof Using "Type".
Import bi.

Section bi_instances.
Context {PROP : bi}.
Implicit Types P Q R : PROP.
Implicit Types mP : option PROP.

(** AsEmpValid *)
Global Instance as_emp_valid_emp_valid {PROP : bi} (P : PROP) : AsEmpValid0 (bi_emp_valid P) P | 0.
Proof. by rewrite /AsEmpValid. Qed.
Global Instance as_emp_valid_entails {PROP : bi} (P Q : PROP) : AsEmpValid0 (P ⊢ Q) (P -∗ Q).
Proof. split. apply bi.entails_wand. apply bi.wand_entails. Qed.
Global Instance as_emp_valid_equiv {PROP : bi} (P Q : PROP) : AsEmpValid0 (P ≡ Q) (P ∗-∗ Q).
Proof. split. apply bi.equiv_wand_iff. apply bi.wand_iff_equiv. Qed.

Global Instance as_emp_valid_forall {A : Type} (φ : A → Prop) (P : A → PROP) :
  (∀ x, AsEmpValid (φ x) (P x)) → AsEmpValid (∀ x, φ x) (∀ x, P x).
Proof.
  rewrite /AsEmpValid=>H1. split=>H2.
  - apply bi.forall_intro=>?. apply H1, H2.
  - intros x. apply H1. revert H2. by rewrite (bi.forall_elim x).
Qed.

(* We add a useless hypothesis [BiEmbed PROP PROP'] in order to make
   sure this instance is not used when there is no embedding between
   PROP and PROP'.
   The first [`{BiEmbed PROP PROP'}] is not considered as a premise by
   Coq TC search mechanism because the rest of the hypothesis is dependent
   on it. *)
Global Instance as_emp_valid_embed `{BiEmbed PROP PROP'} (φ : Prop) (P : PROP) :
  BiEmbed PROP PROP' →
  AsEmpValid0 φ P → AsEmpValid φ ⎡P⎤.
Proof. rewrite /AsEmpValid0 /AsEmpValid=> _ ->. rewrite embed_emp_valid //. Qed.

(** FromAffinely *)
Global Instance from_affinely_affine P : Affine P → FromAffinely P P.
Proof. intros. by rewrite /FromAffinely affinely_elim. Qed.
Global Instance from_affinely_default P : FromAffinely (<affine> P) P | 100.
Proof. by rewrite /FromAffinely. Qed.
Global Instance from_affinely_intuitionistically P :
  FromAffinely (□ P) (<pers> P) | 100.
Proof. by rewrite /FromAffinely. Qed.

(** IntoAbsorbingly *)
Global Instance into_absorbingly_True : @IntoAbsorbingly PROP True emp | 0.
Proof. by rewrite /IntoAbsorbingly -absorbingly_True_emp absorbingly_pure. Qed.
Global Instance into_absorbingly_absorbing P : Absorbing P → IntoAbsorbingly P P | 1.
Proof. intros. by rewrite /IntoAbsorbingly absorbing_absorbingly. Qed.
Global Instance into_absorbingly_intuitionistically P :
  IntoAbsorbingly (<pers> P) (□ P) | 2.
Proof.
  by rewrite /IntoAbsorbingly -absorbingly_intuitionistically_into_persistently.
Qed.
Global Instance into_absorbingly_default P : IntoAbsorbingly (<absorb> P) P | 100.
Proof. by rewrite /IntoAbsorbingly. Qed.

(** FromAssumption *)
Global Instance from_assumption_exact p P : FromAssumption p P P | 0.
Proof. by rewrite /FromAssumption /= intuitionistically_if_elim. Qed.

Global Instance from_assumption_persistently_r P Q :
  FromAssumption true P Q → KnownRFromAssumption true P (<pers> Q).
Proof.
  rewrite /KnownRFromAssumption /FromAssumption /= =><-.
  apply intuitionistically_persistent.
Qed.
Global Instance from_assumption_affinely_r P Q :
  FromAssumption true P Q → KnownRFromAssumption true P (<affine> Q).
Proof.
  rewrite /KnownRFromAssumption /FromAssumption /= =><-.
  by rewrite affinely_idemp.
Qed.
Global Instance from_assumption_intuitionistically_r P Q :
  FromAssumption true P Q → KnownRFromAssumption true P (□ Q).
Proof.
  rewrite /KnownRFromAssumption /FromAssumption /= =><-.
  by rewrite intuitionistically_idemp.
Qed.
Global Instance from_assumption_absorbingly_r p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (<absorb> Q).
Proof.
  rewrite /KnownRFromAssumption /FromAssumption /= =><-.
  apply absorbingly_intro.
Qed.

Global Instance from_assumption_intuitionistically_l p P Q :
  FromAssumption true P Q → KnownLFromAssumption p (□ P) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption /= =><-.
  by rewrite intuitionistically_if_elim.
Qed.
Global Instance from_assumption_persistently_l_true P Q :
  FromAssumption true P Q → KnownLFromAssumption true (<pers> P) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption /= =><-.
  rewrite intuitionistically_persistently_elim //.
Qed.
Global Instance from_assumption_persistently_l_false `{BiAffine PROP} P Q :
  FromAssumption true P Q → KnownLFromAssumption false (<pers> P) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption /= =><-.
  by rewrite intuitionistically_into_persistently.
Qed.
Global Instance from_assumption_affinely_l_true p P Q :
  FromAssumption p P Q → KnownLFromAssumption p (<affine> P) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption /= =><-.
  by rewrite affinely_elim.
Qed.
Global Instance from_assumption_intuitionistically_l_true p P Q :
  FromAssumption p P Q → KnownLFromAssumption p (□ P) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption /= =><-.
  by rewrite intuitionistically_elim.
Qed.

Global Instance from_assumption_forall {A} p (Φ : A → PROP) Q x :
  FromAssumption p (Φ x) Q → KnownLFromAssumption p (∀ x, Φ x) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption=> <-.
  by rewrite forall_elim.
Qed.

Global Instance from_assumption_bupd `{BiBUpd PROP} p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (|==> Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_intro. Qed.

(** IntoPure *)
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
  rewrite -{1}(persistent_absorbingly_affinely ⌜φ1⌝%I) absorbingly_sep_l
          bi.wand_elim_r absorbing //.
Qed.

Global Instance into_pure_affinely P φ : IntoPure P φ → IntoPure (<affine> P) φ.
Proof. rewrite /IntoPure=> ->. apply affinely_elim. Qed.
Global Instance into_pure_intuitionistically P φ :
  IntoPure P φ → IntoPure (□ P) φ.
Proof. rewrite /IntoPure=> ->. apply intuitionistically_elim. Qed.
Global Instance into_pure_absorbingly P φ : IntoPure P φ → IntoPure (<absorb> P) φ.
Proof. rewrite /IntoPure=> ->. by rewrite absorbingly_pure. Qed.
Global Instance into_pure_persistently P φ :
  IntoPure P φ → IntoPure (<pers> P) φ.
Proof. rewrite /IntoPure=> ->. apply: persistently_elim. Qed.
Global Instance into_pure_embed `{BiEmbed PROP PROP'} P φ :
  IntoPure P φ → IntoPure ⎡P⎤ φ.
Proof. rewrite /IntoPure=> ->. by rewrite embed_pure. Qed.

(** FromPure *)
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

Global Instance from_pure_persistently P a φ :
  FromPure true P φ → FromPure a (<pers> P) φ.
Proof.
  rewrite /FromPure=> <- /=.
  by rewrite persistently_affinely_elim affinely_if_elim persistently_pure.
Qed.
Global Instance from_pure_affinely_true P φ :
  FromPure true P φ → FromPure true (<affine> P) φ.
Proof. rewrite /FromPure=><- /=. by rewrite affinely_idemp. Qed.
Global Instance from_pure_affinely_false P φ `{!Affine P} :
  FromPure false P φ → FromPure false (<affine> P) φ.
Proof. rewrite /FromPure /= affine_affinely //. Qed.
Global Instance from_pure_intuitionistically_true P φ :
  FromPure true P φ → FromPure true (□ P) φ.
Proof.
  rewrite /FromPure=><- /=. rewrite intuitionistically_affinely_elim.
  rewrite {1}(persistent ⌜φ⌝%I) //.
Qed.

Global Instance from_pure_absorbingly P φ p :
  FromPure true P φ → FromPure p (<absorb> P) φ.
Proof.
  rewrite /FromPure=> <- /=.
  rewrite persistent_absorbingly_affinely affinely_if_elim //.
Qed.
Global Instance from_pure_embed `{BiEmbed PROP PROP'} a P φ :
  FromPure a P φ → FromPure a ⎡P⎤ φ.
Proof. rewrite /FromPure=> <-. by rewrite -embed_pure embed_affinely_if_2. Qed.

Global Instance from_pure_bupd `{BiBUpd PROP} a P φ :
  FromPure a P φ → FromPure a (|==> P) φ.
Proof. rewrite /FromPure=> <-. apply bupd_intro. Qed.

(** IntoPersistent *)
Global Instance into_persistent_persistently p P Q :
  IntoPersistent true P Q → IntoPersistent p (<pers> P) Q | 0.
Proof.
  rewrite /IntoPersistent /= => ->.
  destruct p; simpl; auto using persistently_idemp_1.
Qed.
Global Instance into_persistent_affinely p P Q :
  IntoPersistent p P Q → IntoPersistent p (<affine> P) Q | 0.
Proof. rewrite /IntoPersistent /= => <-. by rewrite affinely_elim. Qed.
Global Instance into_persistent_intuitionistically p P Q :
  IntoPersistent true P Q → IntoPersistent p (□ P) Q | 0.
Proof.
  rewrite /IntoPersistent /= =><-.
  destruct p; simpl;
    eauto using persistently_mono, intuitionistically_elim,
    intuitionistically_into_persistently_1.
Qed.
Global Instance into_persistent_embed `{BiEmbed PROP PROP'} p P Q :
  IntoPersistent p P Q → IntoPersistent p ⎡P⎤ ⎡Q⎤ | 0.
Proof.
  rewrite /IntoPersistent -embed_persistently -embed_persistently_if=> -> //.
Qed.
Global Instance into_persistent_here P : IntoPersistent true P P | 1.
Proof. by rewrite /IntoPersistent. Qed.
Global Instance into_persistent_persistent P :
  Persistent P → IntoPersistent false P P | 100.
Proof. intros. by rewrite /IntoPersistent. Qed.

(** FromModal *)
Global Instance from_modal_affinely P :
  FromModal modality_affinely (<affine> P) (<affine> P) P | 2.
Proof. by rewrite /FromModal. Qed.

Global Instance from_modal_persistently P :
  FromModal modality_persistently (<pers> P) (<pers> P) P | 2.
Proof. by rewrite /FromModal. Qed.
Global Instance from_modal_intuitionistically P :
  FromModal modality_intuitionistically (□ P) (□ P) P | 1.
Proof. by rewrite /FromModal. Qed.
Global Instance from_modal_intuitionistically_affine_bi P :
  BiAffine PROP → FromModal modality_persistently (□ P) (□ P) P | 0.
Proof.
  intros. by rewrite /FromModal /= intuitionistically_into_persistently.
Qed.

Global Instance from_modal_absorbingly P :
  FromModal modality_id (<absorb> P) (<absorb> P) P.
Proof. by rewrite /FromModal /= -absorbingly_intro. Qed.

(* When having a modality nested in an embedding, e.g. [ ⎡|==> P⎤ ], we prefer
the embedding over the modality. *)
Global Instance from_modal_embed `{BiEmbed PROP PROP'} (P : PROP) :
  FromModal (@modality_embed PROP PROP' _) ⎡P⎤ ⎡P⎤ P.
Proof. by rewrite /FromModal. Qed.

Global Instance from_modal_id_embed `{BiEmbed PROP PROP'} `(sel : A) P Q :
  FromModal modality_id sel P Q →
  FromModal modality_id sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. by rewrite /FromModal /= =><-. Qed.

Global Instance from_modal_affinely_embed `{BiEmbed PROP PROP'} `(sel : A) P Q :
  FromModal modality_affinely sel P Q →
  FromModal modality_affinely sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. rewrite /FromModal /= =><-. by rewrite embed_affinely_2. Qed.
Global Instance from_modal_persistently_embed `{BiEmbed PROP PROP'} `(sel : A) P Q :
  FromModal modality_persistently sel P Q →
  FromModal modality_persistently sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. rewrite /FromModal /= =><-. by rewrite embed_persistently. Qed.
Global Instance from_modal_intuitionistically_embed `{BiEmbed PROP PROP'} `(sel : A) P Q :
  FromModal modality_intuitionistically sel P Q →
  FromModal modality_intuitionistically sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. rewrite /FromModal /= =><-. by rewrite embed_intuitionistically_2. Qed.

Global Instance from_modal_bupd `{BiBUpd PROP} P :
  FromModal modality_id (|==> P) (|==> P) P.
Proof. by rewrite /FromModal /= -bupd_intro. Qed.

(** IntoWand *)
Global Instance into_wand_wand' p q (P Q P' Q' : PROP) :
  IntoWand' p q (P -∗ Q) P' Q' → IntoWand p q (P -∗ Q) P' Q' | 100.
Proof. done. Qed.
Global Instance into_wand_impl' p q (P Q P' Q' : PROP) :
  IntoWand' p q (P → Q) P' Q' → IntoWand p q (P → Q) P' Q' | 100.
Proof. done. Qed.
Global Instance into_wand_wandM' p q mP (Q P' Q' : PROP) :
  IntoWand' p q (mP -∗? Q) P' Q' → IntoWand p q (mP -∗? Q) P' Q' | 100.
Proof. done. Qed.

Global Instance into_wand_wand p q P Q P' :
  FromAssumption q P P' → IntoWand p q (P' -∗ Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand=> HP. by rewrite HP intuitionistically_if_elim.
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
  rewrite -(intuitionistically_idemp P) HP.
  by rewrite -persistently_and_intuitionistically_sep_l persistently_elim impl_elim_r.
Qed.
Global Instance into_wand_impl_true_false P Q P' :
  Affine P' → FromAssumption false P P' →
  IntoWand true false (P' → Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand /= => ? HP. apply wand_intro_r.
  rewrite HP sep_and intuitionistically_elim impl_elim_l //.
Qed.
Global Instance into_wand_impl_true_true P Q P' :
  FromAssumption true P P' → IntoWand true true (P' → Q) P Q.
Proof.
  rewrite /FromAssumption /IntoWand /= => <-. apply wand_intro_l.
  rewrite sep_and [(□ (_ → _))%I]intuitionistically_elim impl_elim_r //.
Qed.

Global Instance into_wand_wandM p q mP' P Q :
  FromAssumption q P (pm_default emp%I mP') → IntoWand p q (mP' -∗? Q) P Q.
Proof. rewrite /IntoWand wandM_sound. exact: into_wand_wand. Qed.

Global Instance into_wand_and_l p q R1 R2 P' Q' :
  IntoWand p q R1 P' Q' → IntoWand p q (R1 ∧ R2) P' Q'.
Proof. rewrite /IntoWand=> ?. by rewrite /bi_wand_iff and_elim_l. Qed.
Global Instance into_wand_and_r p q R1 R2 P' Q' :
  IntoWand p q R2 Q' P' → IntoWand p q (R1 ∧ R2) Q' P'.
Proof. rewrite /IntoWand=> ?. by rewrite /bi_wand_iff and_elim_r. Qed.

Global Instance into_wand_forall_prop_true p (φ : Prop) P :
  IntoWand p true (∀ _ : φ, P) ⌜ φ ⌝ P.
Proof.
  rewrite /IntoWand (intuitionistically_if_elim p) /=
          -impl_wand_intuitionistically -pure_impl_forall
          bi.persistently_elim //.
Qed.
Global Instance into_wand_forall_prop_false p (φ : Prop) P :
  Absorbing P → IntoWand p false (∀ _ : φ, P) ⌜ φ ⌝ P.
Proof.
  intros ?.
  rewrite /IntoWand (intuitionistically_if_elim p) /= pure_wand_forall //.
Qed.

Global Instance into_wand_forall {A} p q (Φ : A → PROP) P Q x :
  IntoWand p q (Φ x) P Q → IntoWand p q (∀ x, Φ x) P Q.
Proof. rewrite /IntoWand=> <-. by rewrite (forall_elim x). Qed.

Global Instance into_wand_tforall {A} p q (Φ : tele_arg A → PROP) P Q x :
  IntoWand p q (Φ x) P Q → IntoWand p q (∀.. x, Φ x) P Q.
Proof. rewrite /IntoWand=> <-. by rewrite bi_tforall_forall (forall_elim x). Qed.

Global Instance into_wand_affine p q R P Q :
  IntoWand p q R P Q → IntoWand p q (<affine> R) (<affine> P) (<affine> Q).
Proof.
  rewrite /IntoWand /= => HR. apply wand_intro_r. destruct p; simpl in *.
  - rewrite (affinely_elim R) -(affine_affinely (□ R)%I) HR. destruct q; simpl in *.
    + rewrite (affinely_elim P) -{2}(affine_affinely (□ P)%I).
      by rewrite affinely_sep_2 wand_elim_l.
    + by rewrite affinely_sep_2 wand_elim_l.
  - rewrite HR. destruct q; simpl in *.
    + rewrite (affinely_elim P) -{2}(affine_affinely (□ P)%I).
      by rewrite affinely_sep_2 wand_elim_l.
    + by rewrite affinely_sep_2 wand_elim_l.
Qed.
(* In case the argument is affine, but the wand resides in the spatial context,
we can only eliminate the affine modality in the argument. This would lead to
the following instance:

  IntoWand false q R P Q → IntoWand' false q R (<affine> P) Q.

This instance is redundant, however, since the elimination of the affine
modality is already covered by the [IntoAssumption] instances that are used at
the leaves of the instance search for [IntoWand]. *)
Global Instance into_wand_affine_args q R P Q :
  IntoWand true q R P Q → IntoWand' true q R (<affine> P) (<affine> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => HR. apply wand_intro_r.
  rewrite -(affine_affinely (□ R)%I) HR. destruct q; simpl.
  - rewrite (affinely_elim P) -{2}(affine_affinely (□ P)%I).
    by rewrite affinely_sep_2 wand_elim_l.
  - by rewrite affinely_sep_2 wand_elim_l.
Qed.

Global Instance into_wand_intuitionistically p q R P Q :
  IntoWand true q R P Q → IntoWand p q (□ R) P Q.
Proof. rewrite /IntoWand /= => ->. by rewrite {1}intuitionistically_if_elim. Qed.
Global Instance into_wand_persistently_true q R P Q :
  IntoWand true q R P Q → IntoWand true q (<pers> R) P Q.
Proof. by rewrite /IntoWand /= intuitionistically_persistently_elim. Qed.
Global Instance into_wand_persistently_false q R P Q :
  Absorbing R → IntoWand false q R P Q → IntoWand false q (<pers> R) P Q.
Proof. intros ?. by rewrite /IntoWand persistently_elim. Qed.

Global Instance into_wand_embed `{BiEmbed PROP PROP'} p q R P Q :
  IntoWand p q R P Q → IntoWand p q ⎡R⎤ ⎡P⎤ ⎡Q⎤.
Proof. by rewrite /IntoWand !embed_intuitionistically_if_2 -embed_wand=> ->. Qed.

(* There are two versions for [IntoWand ⎡RR⎤ ...] with the argument being
[<affine> ⎡PP⎤]. When the wand [⎡RR⎤] resides in the intuitionistic context
the result of wand elimination will have the affine modality. Otherwise, it
won't. Note that when the wand [⎡RR⎤] is under an affine modality, the instance
[into_wand_affine] would already have been used. *)
Global Instance into_wand_affine_embed_true `{BiEmbed PROP PROP'} q (PP QQ RR : PROP) :
  IntoWand true q RR PP QQ → IntoWand true q ⎡RR⎤ (<affine> ⎡PP⎤) (<affine> ⎡QQ⎤) | 100.
Proof.
  rewrite /IntoWand /=.
  rewrite -(intuitionistically_idemp ⎡ _ ⎤%I) embed_intuitionistically_2=> ->.
  apply bi.wand_intro_l. destruct q; simpl.
  - rewrite affinely_elim  -(intuitionistically_idemp ⎡ _ ⎤%I).
    rewrite embed_intuitionistically_2 intuitionistically_sep_2 -embed_sep.
    by rewrite wand_elim_r intuitionistically_affinely.
  - by rewrite intuitionistically_affinely affinely_sep_2 -embed_sep wand_elim_r.
Qed.
Global Instance into_wand_affine_embed_false `{BiEmbed PROP PROP'} q (PP QQ RR : PROP) :
  IntoWand false q RR (<affine> PP) QQ → IntoWand false q ⎡RR⎤ (<affine> ⎡PP⎤) ⎡QQ⎤ | 100.
Proof.
  rewrite /IntoWand /= => ->.
  by rewrite embed_affinely_2 embed_intuitionistically_if_2 embed_wand.
Qed.


Global Instance into_wand_bupd `{BiBUpd PROP} p q R P Q :
  IntoWand false false R P Q → IntoWand p q (|==> R) (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite bupd_sep wand_elim_r.
Qed.
Global Instance into_wand_bupd_persistent `{BiBUpd PROP} p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|==> R) P (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite bupd_frame_l wand_elim_r.
Qed.
Global Instance into_wand_bupd_args `{BiBUpd PROP} p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim bupd_wand_r.
Qed.

(** FromWand *)
Global Instance from_wand_wand P1 P2 : FromWand (P1 -∗ P2) P1 P2.
Proof. by rewrite /FromWand. Qed.
Global Instance from_wand_wandM mP1 P2 :
  FromWand (mP1 -∗? P2) (pm_default emp mP1)%I P2.
Proof. by rewrite /FromWand wandM_sound. Qed.
Global Instance from_wand_embed `{BiEmbed PROP PROP'} P Q1 Q2 :
  FromWand P Q1 Q2 → FromWand ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromWand -embed_wand => <-. Qed.

(** FromImpl *)
Global Instance from_impl_impl P1 P2 : FromImpl (P1 → P2) P1 P2.
Proof. by rewrite /FromImpl. Qed.
Global Instance from_impl_embed `{BiEmbed PROP PROP'} P Q1 Q2 :
  FromImpl P Q1 Q2 → FromImpl ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromImpl -embed_impl => <-. Qed.

(** FromAnd *)
Global Instance from_and_and P1 P2 : FromAnd (P1 ∧ P2) P1 P2 | 100.
Proof. by rewrite /FromAnd. Qed.
Global Instance from_and_sep_persistent_l P1 P1' P2 :
  Persistent P1 → IntoAbsorbingly P1' P1 → FromAnd (P1 ∗ P2) P1' P2 | 9.
Proof.
  rewrite /IntoAbsorbingly /FromAnd=> ? ->.
  rewrite persistent_and_affinely_sep_l_1 {1}(persistent_persistently_2 P1).
  by rewrite absorbingly_elim_persistently -{2}(intuitionistically_elim P1).
Qed.
Global Instance from_and_sep_persistent_r P1 P2 P2' :
  Persistent P2 → IntoAbsorbingly P2' P2 → FromAnd (P1 ∗ P2) P1 P2' | 10.
Proof.
  rewrite /IntoAbsorbingly /FromAnd=> ? ->.
  rewrite persistent_and_affinely_sep_r_1 {1}(persistent_persistently_2 P2).
  by rewrite absorbingly_elim_persistently -{2}(intuitionistically_elim P2).
Qed.

Global Instance from_and_pure φ ψ : @FromAnd PROP ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromAnd pure_and. Qed.

Global Instance from_and_persistently P Q1 Q2 :
  FromAnd P Q1 Q2 →
  FromAnd (<pers> P) (<pers> Q1) (<pers> Q2).
Proof. rewrite /FromAnd=> <-. by rewrite persistently_and. Qed.
Global Instance from_and_persistently_sep P Q1 Q2 :
  FromSep P Q1 Q2 →
  FromAnd (<pers> P) (<pers> Q1) (<pers> Q2) | 11.
Proof. rewrite /FromAnd=> <-. by rewrite -persistently_and persistently_and_sep. Qed.

Global Instance from_and_embed `{BiEmbed PROP PROP'} P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromAnd -embed_and => <-. Qed.

Global Instance from_and_big_sepL_cons_persistent {A} (Φ : nat → A → PROP) l x l' :
  IsCons l x l' →
  Persistent (Φ 0 x) →
  FromAnd ([∗ list] k ↦ y ∈ l, Φ k y) (Φ 0 x) ([∗ list] k ↦ y ∈ l', Φ (S k) y).
Proof. rewrite /IsCons=> -> ?. by rewrite /FromAnd big_sepL_cons persistent_and_sep_1. Qed.
Global Instance from_and_big_sepL_app_persistent {A} (Φ : nat → A → PROP) l l1 l2 :
  IsApp l l1 l2 →
  (∀ k y, Persistent (Φ k y)) →
  FromAnd ([∗ list] k ↦ y ∈ l, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. rewrite /IsApp=> -> ?. by rewrite /FromAnd big_sepL_app persistent_and_sep_1. Qed.

Global Instance from_and_big_sepL2_cons_persistent {A B}
    (Φ : nat → A → B → PROP) l1 x1 l1' l2 x2 l2' :
  IsCons l1 x1 l1' → IsCons l2 x2 l2' →
  Persistent (Φ 0 x1 x2) →
  FromAnd ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)
    (Φ 0 x1 x2) ([∗ list] k ↦ y1;y2 ∈ l1';l2', Φ (S k) y1 y2).
Proof.
  rewrite /IsCons=> -> -> ?.
  by rewrite /FromAnd big_sepL2_cons persistent_and_sep_1.
Qed.
Global Instance from_and_big_sepL2_app_persistent {A B}
    (Φ : nat → A → B → PROP) l1 l1' l1'' l2 l2' l2'' :
  IsApp l1 l1' l1'' → IsApp l2 l2' l2'' →
  (∀ k y1 y2, Persistent (Φ k y1 y2)) →
  FromAnd ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)
    ([∗ list] k ↦ y1;y2 ∈ l1';l2', Φ k y1 y2)
    ([∗ list] k ↦ y1;y2 ∈ l1'';l2'', Φ (length l1' + k) y1 y2).
Proof.
  rewrite /IsApp=> -> -> ?. rewrite /FromAnd persistent_and_sep_1.
  apply wand_elim_l', big_sepL2_app.
Qed.

(** FromSep *)
Global Instance from_sep_sep P1 P2 : FromSep (P1 ∗ P2) P1 P2 | 100.
Proof. by rewrite /FromSep. Qed.
Global Instance from_sep_and P1 P2 :
  TCOr (Affine P1) (Absorbing P2) → TCOr (Absorbing P1) (Affine P2) →
  FromSep (P1 ∧ P2) P1 P2 | 101.
Proof. intros. by rewrite /FromSep sep_and. Qed.

Global Instance from_sep_pure φ ψ : @FromSep PROP ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromSep pure_and sep_and. Qed.

Global Instance from_sep_affinely P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (<affine> P) (<affine> Q1) (<affine> Q2).
Proof. rewrite /FromSep=> <-. by rewrite affinely_sep_2. Qed.
Global Instance from_sep_intuitionistically P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromSep=> <-. by rewrite intuitionistically_sep_2. Qed.
Global Instance from_sep_absorbingly P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (<absorb> P) (<absorb> Q1) (<absorb> Q2).
Proof. rewrite /FromSep=> <-. by rewrite absorbingly_sep. Qed.
Global Instance from_sep_persistently P Q1 Q2 :
  FromSep P Q1 Q2 →
  FromSep (<pers> P) (<pers> Q1) (<pers> Q2).
Proof. rewrite /FromSep=> <-. by rewrite persistently_sep_2. Qed.

Global Instance from_sep_embed `{BiEmbed PROP PROP'} P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromSep -embed_sep => <-. Qed.

Global Instance from_sep_big_sepL_cons {A} (Φ : nat → A → PROP) l x l' :
  IsCons l x l' →
  FromSep ([∗ list] k ↦ y ∈ l, Φ k y) (Φ 0 x) ([∗ list] k ↦ y ∈ l', Φ (S k) y).
Proof. rewrite /IsCons=> ->. by rewrite /FromSep big_sepL_cons. Qed.
Global Instance from_sep_big_sepL_app {A} (Φ : nat → A → PROP) l l1 l2 :
  IsApp l l1 l2 →
  FromSep ([∗ list] k ↦ y ∈ l, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. rewrite /IsApp=> ->. by rewrite /FromSep big_opL_app. Qed.

Global Instance from_sep_big_sepL2_cons {A B} (Φ : nat → A → B → PROP)
    l1 x1 l1' l2 x2 l2' :
  IsCons l1 x1 l1' → IsCons l2 x2 l2' →
  FromSep ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)
    (Φ 0 x1 x2) ([∗ list] k ↦ y1;y2 ∈ l1';l2', Φ (S k) y1 y2).
Proof. rewrite /IsCons=> -> ->. by rewrite /FromSep big_sepL2_cons. Qed.
Global Instance from_sep_big_sepL2_app {A B} (Φ : nat → A → B → PROP)
    l1 l1' l1'' l2 l2' l2'' :
  IsApp l1 l1' l1'' → IsApp l2 l2' l2'' →
  FromSep ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)
    ([∗ list] k ↦ y1;y2 ∈ l1';l2', Φ k y1 y2)
    ([∗ list] k ↦ y1;y2 ∈ l1'';l2'', Φ (length l1' + k) y1 y2).
Proof. rewrite /IsApp=>-> ->. apply wand_elim_l', big_sepL2_app. Qed.

Global Instance from_sep_bupd `{BiBUpd PROP} P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromSep=><-. apply bupd_sep. Qed.

(** IntoAnd *)
Global Instance into_and_and p P Q : IntoAnd p (P ∧ Q) P Q | 10.
Proof. by rewrite /IntoAnd intuitionistically_if_and. Qed.
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
  rewrite /IntoAnd /= intuitionistically_sep -and_sep_intuitionistically intuitionistically_and //.
Qed.
Global Instance into_and_sep_affine P Q :
  TCOr (Affine P) (Absorbing Q) → TCOr (Absorbing P) (Affine Q) →
  IntoAnd true (P ∗ Q) P Q.
Proof. intros. by rewrite /IntoAnd /= sep_and. Qed.

Global Instance into_and_pure p φ ψ : @IntoAnd PROP p ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /IntoAnd pure_and intuitionistically_if_and. Qed.

Global Instance into_and_affinely p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (<affine> P) (<affine> Q1) (<affine> Q2).
Proof.
  rewrite /IntoAnd. destruct p; simpl.
  - rewrite -affinely_and !intuitionistically_affinely_elim //.
  - intros ->. by rewrite affinely_and.
Qed.
Global Instance into_and_intuitionistically p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (□ P) (□ Q1) (□ Q2).
Proof.
  rewrite /IntoAnd. destruct p; simpl.
  - rewrite -intuitionistically_and !intuitionistically_idemp //.
  - intros ->. by rewrite intuitionistically_and.
Qed.
Global Instance into_and_persistently p P Q1 Q2 :
  IntoAnd p P Q1 Q2 →
  IntoAnd p (<pers> P) (<pers> Q1) (<pers> Q2).
Proof.
  rewrite /IntoAnd /=. destruct p; simpl.
  - rewrite -persistently_and !intuitionistically_persistently_elim //.
  - intros ->. by rewrite persistently_and.
Qed.
Global Instance into_and_embed `{BiEmbed PROP PROP'} p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof.
  rewrite /IntoAnd -embed_and=> HP. apply intuitionistically_if_intro'.
  by rewrite embed_intuitionistically_if_2 HP intuitionistically_if_elim.
Qed.

(** IntoSep *)
Global Instance into_sep_sep P Q : IntoSep (P ∗ Q) P Q.
Proof. by rewrite /IntoSep. Qed.

Inductive AndIntoSep : PROP → PROP → PROP → PROP → Prop :=
  | and_into_sep_affine P Q Q' : Affine P → FromAffinely Q' Q → AndIntoSep P P Q Q'
  | and_into_sep P Q : AndIntoSep P (<affine> P)%I Q Q.
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

Global Instance into_sep_embed `{BiEmbed PROP PROP'} P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. rewrite /IntoSep -embed_sep=> -> //. Qed.

Global Instance into_sep_affinely `{BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (<affine> P) (<affine> Q1) (<affine> Q2) | 0.
Proof. rewrite /IntoSep /= => ->. by rewrite affinely_sep. Qed.
Global Instance into_sep_intuitionistically `{BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (□ P) (□ Q1) (□ Q2) | 0.
Proof. rewrite /IntoSep /= => ->. by rewrite intuitionistically_sep. Qed.
(* FIXME: This instance is kind of strange, it just gets rid of the bi_affinely.
Also, it overlaps with `into_sep_affinely_later`, and hence has lower
precedence. *)
Global Instance into_sep_affinely_trim P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (<affine> P) Q1 Q2 | 20.
Proof. rewrite /IntoSep /= => ->. by rewrite affinely_elim. Qed.

Global Instance into_sep_persistently `{BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 →
  IntoSep (<pers> P) (<pers> Q1) (<pers> Q2).
Proof. rewrite /IntoSep /= => ->. by rewrite persistently_sep. Qed.
Global Instance into_sep_persistently_affine P Q1 Q2 :
  IntoSep P Q1 Q2 →
  TCOr (Affine Q1) (Absorbing Q2) → TCOr (Absorbing Q1) (Affine Q2) →
  IntoSep (<pers> P) (<pers> Q1) (<pers> Q2).
Proof.
  rewrite /IntoSep /= => -> ??.
  by rewrite sep_and persistently_and persistently_and_sep_l_1.
Qed.
Global Instance into_sep_intuitionistically_affine P Q1 Q2 :
  IntoSep P Q1 Q2 →
  TCOr (Affine Q1) (Absorbing Q2) → TCOr (Absorbing Q1) (Affine Q2) →
  IntoSep (□ P) (□ Q1) (□ Q2).
Proof.
  rewrite /IntoSep /= => -> ??.
  by rewrite sep_and intuitionistically_and and_sep_intuitionistically.
Qed.

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

(* No instance for app, since that only works when the LHSs have the same length *)
Global Instance into_sep_big_sepL2_cons {A B}
    (Φ : nat → A → B → PROP) l1 x1 l1' l2 x2 l2' :
  IsCons l1 x1 l1' → IsCons l2 x2 l2' →
  IntoSep ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)
    (Φ 0 x1 x2) ([∗ list] k ↦ y1;y2 ∈ l1';l2', Φ (S k) y1 y2).
Proof. rewrite /IsCons=>-> ->. by rewrite /IntoSep big_sepL2_cons. Qed.

(** FromOr *)
Global Instance from_or_or P1 P2 : FromOr (P1 ∨ P2) P1 P2.
Proof. by rewrite /FromOr. Qed.
Global Instance from_or_pure φ ψ : @FromOr PROP ⌜φ ∨ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromOr pure_or. Qed.
Global Instance from_or_affinely P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (<affine> P) (<affine> Q1) (<affine> Q2).
Proof. rewrite /FromOr=> <-. by rewrite affinely_or. Qed.
Global Instance from_or_intuitionistically P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromOr=> <-. by rewrite intuitionistically_or. Qed.
Global Instance from_or_absorbingly P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (<absorb> P) (<absorb> Q1) (<absorb> Q2).
Proof. rewrite /FromOr=> <-. by rewrite absorbingly_or. Qed.
Global Instance from_or_persistently P Q1 Q2 :
  FromOr P Q1 Q2 →
  FromOr (<pers> P) (<pers> Q1) (<pers> Q2).
Proof. rewrite /FromOr=> <-. by rewrite persistently_or. Qed.
Global Instance from_or_embed `{BiEmbed PROP PROP'} P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromOr -embed_or => <-. Qed.

Global Instance from_or_bupd `{BiBUpd PROP} P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|==> P) (|==> Q1) (|==> Q2).
Proof.
  rewrite /FromOr=><-.
  apply or_elim; apply bupd_mono; auto using or_intro_l, or_intro_r.
Qed.

(** IntoOr *)
Global Instance into_or_or P Q : IntoOr (P ∨ Q) P Q.
Proof. by rewrite /IntoOr. Qed.
Global Instance into_or_pure φ ψ : @IntoOr PROP ⌜φ ∨ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /IntoOr pure_or. Qed.
Global Instance into_or_affinely P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (<affine> P) (<affine> Q1) (<affine> Q2).
Proof. rewrite /IntoOr=>->. by rewrite affinely_or. Qed.
Global Instance into_or_intuitionistically P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (□ P) (□ Q1) (□ Q2).
Proof. rewrite /IntoOr=>->. by rewrite intuitionistically_or. Qed.
Global Instance into_or_absorbingly P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (<absorb> P) (<absorb> Q1) (<absorb> Q2).
Proof. rewrite /IntoOr=>->. by rewrite absorbingly_or. Qed.
Global Instance into_or_persistently P Q1 Q2 :
  IntoOr P Q1 Q2 →
  IntoOr (<pers> P) (<pers> Q1) (<pers> Q2).
Proof. rewrite /IntoOr=>->. by rewrite persistently_or. Qed.
Global Instance into_or_embed `{BiEmbed PROP PROP'} P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /IntoOr -embed_or => <-. Qed.

(** FromExist *)
Global Instance from_exist_exist {A} (Φ : A → PROP) : FromExist (∃ a, Φ a) Φ.
Proof. by rewrite /FromExist. Qed.
Global Instance from_exist_texist {A} (Φ : tele_arg A → PROP) :
  FromExist (∃.. a, Φ a) Φ.
Proof. by rewrite /FromExist bi_texist_exist. Qed.
Global Instance from_exist_pure {A} (φ : A → Prop) :
  @FromExist PROP A ⌜∃ x, φ x⌝ (λ a, ⌜φ a⌝)%I.
Proof. by rewrite /FromExist pure_exist. Qed.
Global Instance from_exist_affinely {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (<affine> P) (λ a, <affine> (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite affinely_exist. Qed.
Global Instance from_exist_intuitionistically {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite intuitionistically_exist. Qed.
Global Instance from_exist_absorbingly {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (<absorb> P) (λ a, <absorb> (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite absorbingly_exist. Qed.
Global Instance from_exist_persistently {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (<pers> P) (λ a, <pers> (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite persistently_exist. Qed.
Global Instance from_exist_embed `{BiEmbed PROP PROP'} {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist ⎡P⎤ (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /FromExist -embed_exist => <-. Qed.

Global Instance from_exist_bupd `{BiBUpd PROP} {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (|==> P) (λ a, |==> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

(** IntoExist *)
Global Instance into_exist_exist {A} (Φ : A → PROP) : IntoExist (∃ a, Φ a) Φ.
Proof. by rewrite /IntoExist. Qed.
Global Instance into_exist_texist {A} (Φ : tele_arg A → PROP) :
  IntoExist (∃.. a, Φ a) Φ.
Proof. by rewrite /IntoExist bi_texist_exist. Qed.
Global Instance into_exist_pure {A} (φ : A → Prop) :
  @IntoExist PROP A ⌜∃ x, φ x⌝ (λ a, ⌜φ a⌝)%I.
Proof. by rewrite /IntoExist pure_exist. Qed.
Global Instance into_exist_affinely {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (<affine> P) (λ a, <affine> (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP affinely_exist. Qed.
Global Instance into_exist_intuitionistically {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP intuitionistically_exist. Qed.
Global Instance into_exist_and_pure P Q φ :
  IntoPureT P φ → IntoExist (P ∧ Q) (λ _ : φ, Q).
Proof.
  intros (φ'&->&?). rewrite /IntoExist (into_pure P).
  apply pure_elim_l=> Hφ. by rewrite -(exist_intro Hφ).
Qed.
Global Instance into_exist_sep_pure P Q φ :
  IntoPureT P φ → TCOr (Affine P) (Absorbing Q) → IntoExist (P ∗ Q) (λ _ : φ, Q).
Proof.
  intros (φ'&->&?) ?. rewrite /IntoExist.
  eapply (pure_elim φ'); [by rewrite (into_pure P); apply sep_elim_l, _|]=>?.
  rewrite -exist_intro //. apply sep_elim_r, _.
Qed.
Global Instance into_exist_absorbingly {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (<absorb> P) (λ a, <absorb> (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP absorbingly_exist. Qed.
Global Instance into_exist_persistently {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (<pers> P) (λ a, <pers> (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP persistently_exist. Qed.
Global Instance into_exist_embed `{BiEmbed PROP PROP'} {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist ⎡P⎤ (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /IntoExist -embed_exist => <-. Qed.

(** IntoForall *)
Global Instance into_forall_forall {A} (Φ : A → PROP) : IntoForall (∀ a, Φ a) Φ.
Proof. by rewrite /IntoForall. Qed.
Global Instance into_forall_tforall {A} (Φ : tele_arg A → PROP) : IntoForall (∀.. a, Φ a) Φ.
Proof. by rewrite /IntoForall bi_tforall_forall. Qed.
Global Instance into_forall_affinely {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (<affine> P) (λ a, <affine> (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP affinely_forall. Qed.
Global Instance into_forall_intuitionistically {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP intuitionistically_forall. Qed.
Global Instance into_forall_persistently {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (<pers> P) (λ a, <pers> (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP persistently_forall. Qed.
Global Instance into_forall_embed `{BiEmbed PROP PROP'} {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall ⎡P⎤ (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /IntoForall -embed_forall => <-. Qed.

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
  by rewrite -(pure_intro _ True%I) // /bi_affinely right_id emp_wand.
Qed.

(* These instances must be used only after [into_forall_wand_pure] and
[into_forall_wand_pure] above. *)
Global Instance into_forall_wand P Q :
  IntoForall (P -∗ Q) (λ _ : bi_emp_valid P, Q) | 10.
Proof. rewrite /IntoForall. apply forall_intro=><-. rewrite emp_wand //. Qed.
Global Instance into_forall_impl `{!BiAffine PROP} P Q :
  IntoForall (P → Q) (λ _ : bi_emp_valid P, Q) | 10.
Proof. rewrite /IntoForall. apply forall_intro=><-. rewrite -True_emp True_impl //. Qed.

(** FromForall *)
Global Instance from_forall_forall {A} (Φ : A → PROP) :
  FromForall (∀ x, Φ x)%I Φ.
Proof. by rewrite /FromForall. Qed.
Global Instance from_forall_tforall {A} (Φ : tele_arg A → PROP) :
  FromForall (∀.. x, Φ x)%I Φ.
Proof. by rewrite /FromForall bi_tforall_forall. Qed.
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
  IntoPureT P φ → TCOr (Affine P) (Absorbing Q) →
  FromForall (P -∗ Q)%I (λ _ : φ, Q)%I.
Proof.
  intros (φ'&->&?) [|]; rewrite /FromForall; apply wand_intro_r.
  - rewrite -(affine_affinely P) (into_pure P) -persistent_and_affinely_sep_r.
    apply pure_elim_r=>?. by rewrite forall_elim.
  - by rewrite (into_pure P) -pure_wand_forall wand_elim_l.
Qed.

Global Instance from_forall_intuitionistically `{BiAffine PROP} {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (□ P) (λ a, □ (Φ a))%I.
Proof.
  rewrite /FromForall=> <-. setoid_rewrite intuitionistically_into_persistently.
  by rewrite persistently_forall.
Qed.
Global Instance from_forall_persistently {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (<pers> P)%I (λ a, <pers> (Φ a))%I.
Proof. rewrite /FromForall=> <-. by rewrite persistently_forall. Qed.
Global Instance from_forall_embed `{BiEmbed PROP PROP'} {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall ⎡P⎤%I (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /FromForall -embed_forall => <-. Qed.

(** IntoInv *)
Global Instance into_inv_embed {PROP' : bi} `{BiEmbed PROP PROP'} P N :
  IntoInv P N → IntoInv ⎡P⎤ N.

(** ElimModal *)
Global Instance elim_modal_wand φ p p' P P' Q Q' R :
  ElimModal φ p p' P P' Q Q' → ElimModal φ p p' P P' (R -∗ Q) (R -∗ Q').
Proof.
  rewrite /ElimModal=> H Hφ. apply wand_intro_r.
  rewrite wand_curry -assoc (comm _ (□?p' _)%I) -wand_curry wand_elim_l; auto.
Qed.
Global Instance elim_modal_wandM φ p p' P P' Q Q' mR :
  ElimModal φ p p' P P' Q Q' →
  ElimModal φ p p' P P' (mR -∗? Q) (mR -∗? Q').
Proof. rewrite /ElimModal !wandM_sound. exact: elim_modal_wand. Qed.
Global Instance elim_modal_forall {A} φ p p' P P' (Φ Ψ : A → PROP) :
  (∀ x, ElimModal φ p p' P P' (Φ x) (Ψ x)) → ElimModal φ p p' P P' (∀ x, Φ x) (∀ x, Ψ x).
Proof.
  rewrite /ElimModal=> H ?. apply forall_intro=> a. rewrite (forall_elim a); auto.
Qed.
Global Instance elim_modal_absorbingly_here p P Q :
  Absorbing Q → ElimModal True p false (<absorb> P) P Q Q.
Proof.
  rewrite /ElimModal=> ? _. by rewrite intuitionistically_if_elim
    absorbingly_sep_l wand_elim_r absorbing_absorbingly.
Qed.

Global Instance elim_modal_bupd `{BiBUpd PROP} p P Q :
  ElimModal True p false (|==> P) P (|==> Q) (|==> Q).
Proof.
  by rewrite /ElimModal
    intuitionistically_if_elim bupd_frame_r wand_elim_r bupd_trans.
Qed.

Global Instance elim_modal_embed_bupd_goal `{BiEmbedBUpd PROP PROP'}
    p p' φ (P P' : PROP') (Q Q' : PROP) :
  ElimModal φ p p' P P' (|==> ⎡Q⎤)%I (|==> ⎡Q'⎤)%I →
  ElimModal φ p p' P P' ⎡|==> Q⎤ ⎡|==> Q'⎤.
Proof. by rewrite /ElimModal !embed_bupd. Qed.
Global Instance elim_modal_embed_bupd_hyp `{BiEmbedBUpd PROP PROP'}
    p p' φ (P : PROP) (P' Q Q' : PROP') :
  ElimModal φ p p' (|==> ⎡P⎤)%I P' Q Q' →
  ElimModal φ p p' ⎡|==> P⎤ P' Q Q'.
Proof. by rewrite /ElimModal !embed_bupd. Qed.

(** AddModal *)
Global Instance add_modal_wand P P' Q R :
  AddModal P P' Q → AddModal P P' (R -∗ Q).
Proof.
  rewrite /AddModal=> H. apply wand_intro_r.
  by rewrite wand_curry -assoc (comm _ P') -wand_curry wand_elim_l.
Qed.
Global Instance add_modal_wandM P P' Q mR :
  AddModal P P' Q → AddModal P P' (mR -∗? Q).
Proof. rewrite /AddModal wandM_sound. exact: add_modal_wand. Qed.
Global Instance add_modal_forall {A} P P' (Φ : A → PROP) :
  (∀ x, AddModal P P' (Φ x)) → AddModal P P' (∀ x, Φ x).
Proof.
  rewrite /AddModal=> H. apply forall_intro=> a. by rewrite (forall_elim a).
Qed.
Global Instance add_modal_embed_bupd_goal `{BiEmbedBUpd PROP PROP'}
       (P P' : PROP') (Q : PROP) :
  AddModal P P' (|==> ⎡Q⎤)%I → AddModal P P' ⎡|==> Q⎤.
Proof. by rewrite /AddModal !embed_bupd. Qed.

Global Instance add_modal_bupd `{BiBUpd PROP} P Q : AddModal (|==> P) P (|==> Q).
Proof. by rewrite /AddModal bupd_frame_r wand_elim_r bupd_trans. Qed.

(** ElimInv *)
Global Instance elim_inv_acc_without_close {X : Type}
       φ Pinv Pin
       M1 M2 α β mγ Q (Q' : X → PROP) :
  IntoAcc (X:=X) Pinv φ Pin M1 M2 α β mγ →
  ElimAcc (X:=X) M1 M2 α β mγ Q Q' →
  ElimInv φ Pinv Pin α None Q Q'.
Proof.
  rewrite /ElimAcc /IntoAcc /ElimInv.
  iIntros (Hacc Helim Hφ) "(Hinv & Hin & Hcont)".
  iApply (Helim with "[Hcont]").
  - iIntros (x) "Hα". iApply "Hcont". iSplitL; simpl; done.
  - iApply (Hacc with "Hinv Hin"). done.
Qed.

Global Instance elim_inv_acc_with_close {X : Type}
       φ1 φ2 Pinv Pin
       M1 M2 α β mγ Q Q' :
  IntoAcc Pinv φ1 Pin M1 M2 α β mγ →
  (∀ R, ElimModal φ2 false false (M1 R) R Q Q') →
  ElimInv (X:=X) (φ1 ∧ φ2) Pinv Pin
          α
          (Some (λ x, β x -∗ M2 (pm_default emp (mγ x))))%I
          Q (λ _, Q').
Proof.
  rewrite /ElimAcc /IntoAcc /ElimInv.
  iIntros (Hacc Helim [??]) "(Hinv & Hin & Hcont)".
  iMod (Hacc with "Hinv Hin") as (x) "[Hα Hclose]"; first done.
  iApply "Hcont". simpl. iSplitL "Hα"; done.
Qed.

(** IntoEmbed *)
Global Instance into_embed_embed {PROP' : bi} `{BiEmbed PROP PROP'} P :
  IntoEmbed ⎡P⎤ P.
Proof. by rewrite /IntoEmbed. Qed.
Global Instance into_embed_affinely `{BiEmbedBUpd PROP PROP'} (P : PROP') (Q : PROP) :
  IntoEmbed P Q → IntoEmbed (<affine> P) (<affine> Q).
Proof. rewrite /IntoEmbed=> ->. by rewrite embed_affinely_2. Qed.
End bi_instances.
