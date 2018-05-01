From stdpp Require Import nat_cancel.
From iris.bi Require Import bi tactics.
From iris.proofmode Require Import modality_instances classes class_instances_bi ltac_tactics.
Set Default Proof Using "Type".
Import bi.

Section sbi_instances.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.

(* FromAssumption *)
Global Instance from_assumption_later p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (▷ Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply later_intro. Qed.
Global Instance from_assumption_laterN n p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (▷^n Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply laterN_intro. Qed.
Global Instance from_assumption_except_0 p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (◇ Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply except_0_intro. Qed.

Global Instance from_assumption_bupd `{BiBUpd PROP} p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (|==> Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_intro. Qed.
Global Instance from_assumption_fupd `{BiBUpdFUpd PROP} E p P Q :
  FromAssumption p P (|==> Q) → KnownRFromAssumption p P (|={E}=> Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_fupd. Qed.

Global Instance from_assumption_plainly_l_true `{BiPlainly PROP} P Q :
  FromAssumption true P Q → KnownLFromAssumption true (■ P) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption /= =><-.
  rewrite intuitionistically_plainly_elim //.
Qed.
Global Instance from_assumption_plainly_l_false `{BiPlainly PROP, BiAffine PROP} P Q :
  FromAssumption true P Q → KnownLFromAssumption false (■ P) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption /= =><-.
  rewrite plainly_elim_persistently intuitionistically_into_persistently //.
Qed.

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

Global Instance from_pure_bupd `{BiBUpd PROP} a P φ :
  FromPure a P φ → FromPure a (|==> P) φ.
Proof. rewrite /FromPure=> <-. apply bupd_intro. Qed.
Global Instance from_pure_fupd `{BiFUpd PROP} a E P φ :
  FromPure a P φ → FromPure a (|={E}=> P) φ.
Proof. rewrite /FromPure. intros <-. apply fupd_intro. Qed.

Global Instance from_pure_plainly `{BiPlainly PROP} P φ :
  FromPure false P φ → FromPure false (■ P) φ.
Proof. rewrite /FromPure=> <-. by rewrite plainly_pure. Qed.

(* IntoPure *)
Global Instance into_pure_eq {A : ofeT} (a b : A) :
  Discrete a → @IntoPure PROP (a ≡ b) (a ≡ b).
Proof. intros. by rewrite /IntoPure discrete_eq. Qed.

Global Instance into_pure_plainly `{BiPlainly PROP} P φ :
  IntoPure P φ → IntoPure (■ P) φ.
Proof. rewrite /IntoPure=> ->. apply: plainly_elim. Qed.

(* IntoWand *)
Global Instance into_wand_later p q R P Q :
  IntoWand p q R P Q → IntoWand p q (▷ R) (▷ P) (▷ Q).
Proof.
  rewrite /IntoWand /= => HR.
  by rewrite !later_intuitionistically_if_2 -later_wand HR.
Qed.
Global Instance into_wand_later_args p q R P Q :
  IntoWand p q R P Q → IntoWand' p q R (▷ P) (▷ Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => HR.
  by rewrite !later_intuitionistically_if_2
             (later_intro (□?p R)%I) -later_wand HR.
Qed.
Global Instance into_wand_laterN n p q R P Q :
  IntoWand p q R P Q → IntoWand p q (▷^n R) (▷^n P) (▷^n Q).
Proof.
  rewrite /IntoWand /= => HR.
  by rewrite !laterN_intuitionistically_if_2 -laterN_wand HR.
Qed.
Global Instance into_wand_laterN_args n p q R P Q :
  IntoWand p q R P Q → IntoWand' p q R (▷^n P) (▷^n Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => HR.
  by rewrite !laterN_intuitionistically_if_2
             (laterN_intro _ (□?p R)%I) -laterN_wand HR.
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

Global Instance into_wand_fupd `{BiFUpd PROP} E p q R P Q :
  IntoWand false false R P Q →
  IntoWand p q (|={E}=> R) (|={E}=> P) (|={E}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_sep wand_elim_r.
Qed.
Global Instance into_wand_fupd_persistent `{BiFUpd PROP} E1 E2 p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|={E1,E2}=> R) P (|={E1,E2}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_frame_l wand_elim_r.
Qed.
Global Instance into_wand_fupd_args `{BiFUpd PROP} E1 E2 p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|={E1,E2}=> P) (|={E1,E2}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim fupd_wand_r.
Qed.

Global Instance into_wand_plainly_true `{BiPlainly PROP} q R P Q :
  IntoWand true q R P Q → IntoWand true q (■ R) P Q.
Proof. rewrite /IntoWand /= intuitionistically_plainly_elim //. Qed.
Global Instance into_wand_plainly_false `{BiPlainly PROP} q R P Q :
  Absorbing R → IntoWand false q R P Q → IntoWand false q (■ R) P Q.
Proof. intros ?. by rewrite /IntoWand plainly_elim. Qed.

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

Global Instance from_and_plainly `{BiPlainly PROP} P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (■ P) (■ Q1) (■ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite plainly_and. Qed.

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

Global Instance from_sep_bupd `{BiBUpd PROP} P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromSep=><-. apply bupd_sep. Qed.
Global Instance from_sep_fupd `{BiFUpd PROP} E P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2).
Proof. rewrite /FromSep =><-. apply fupd_sep. Qed.

Global Instance from_sep_plainly `{BiPlainly PROP} P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (■ P) (■ Q1) (■ Q2).
Proof. rewrite /FromSep=> <-. by rewrite plainly_sep_2. Qed.

(* IntoAnd *)
Global Instance into_and_later p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷ P) (▷ Q1) (▷ Q2).
Proof.
  rewrite /IntoAnd=> HP. apply intuitionistically_if_intro'.
  by rewrite later_intuitionistically_if_2 HP
             intuitionistically_if_elim later_and.
Qed.
Global Instance into_and_laterN n p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷^n P) (▷^n Q1) (▷^n Q2).
Proof.
  rewrite /IntoAnd=> HP. apply intuitionistically_if_intro'.
  by rewrite laterN_intuitionistically_if_2 HP
             intuitionistically_if_elim laterN_and.
Qed.
Global Instance into_and_except_0 p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (◇ P) (◇ Q1) (◇ Q2).
Proof.
  rewrite /IntoAnd=> HP. apply intuitionistically_if_intro'.
  by rewrite except_0_intuitionistically_if_2 HP
             intuitionistically_if_elim except_0_and.
Qed.

Global Instance into_and_plainly `{BiPlainly PROP} p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (■ P) (■ Q1) (■ Q2).
Proof.
  rewrite /IntoAnd /=. destruct p; simpl.
  - rewrite -plainly_and -[(□ ■ P)%I]intuitionistically_idemp intuitionistically_plainly =>->.
    rewrite [(□ (_ ∧ _))%I]intuitionistically_elim //.
  - intros ->. by rewrite plainly_and.
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
Global Instance into_sep_affinely_later `{!Timeless (PROP:=PROP) emp} P Q1 Q2 :
  IntoSep P Q1 Q2 → Affine Q1 → Affine Q2 →
  IntoSep (<affine> ▷ P) (<affine> ▷ Q1) (<affine> ▷ Q2).
Proof.
  rewrite /IntoSep /= => -> ??.
  rewrite -{1}(affine_affinely Q1) -{1}(affine_affinely Q2) later_sep !later_affinely_1.
  rewrite -except_0_sep /sbi_except_0 affinely_or. apply or_elim, affinely_elim.
  rewrite -(idemp bi_and (<affine> ▷ False)%I) persistent_and_sep_1.
  by rewrite -(False_elim Q1) -(False_elim Q2).
Qed.

Global Instance into_sep_plainly `{BiPlainly PROP, BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (■ P) (■ Q1) (■ Q2).
Proof. rewrite /IntoSep /= => ->. by rewrite plainly_sep. Qed.

Global Instance into_sep_plainly_affine `{BiPlainly PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 →
  TCOr (Affine Q1) (Absorbing Q2) → TCOr (Absorbing Q1) (Affine Q2) →
  IntoSep (■ P) (■ Q1) (■ Q2).
Proof.
  rewrite /IntoSep /= => -> ??. by rewrite sep_and plainly_and plainly_and_sep_l_1.
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

Global Instance from_or_bupd `{BiBUpd PROP} P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|==> P) (|==> Q1) (|==> Q2).
Proof.
  rewrite /FromOr=><-.
  apply or_elim; apply bupd_mono; auto using or_intro_l, or_intro_r.
Qed.
Global Instance from_or_fupd `{BiFUpd PROP} E1 E2 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
Proof.
  rewrite /FromOr=><-. apply or_elim; apply fupd_mono;
                         [apply bi.or_intro_l|apply bi.or_intro_r].
Qed.

Global Instance from_or_plainly `{BiPlainly PROP} P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (■ P) (■ Q1) (■ Q2).
Proof. rewrite /FromOr=> <-. by rewrite -plainly_or_2. Qed.

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

Global Instance into_or_plainly `{BiPlainly PROP, BiPlainlyExist PROP} P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (■ P) (■ Q1) (■ Q2).
Proof. rewrite /IntoOr=>->. by rewrite plainly_or. Qed.

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

Global Instance from_exist_bupd `{BiBUpd PROP} {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (|==> P) (λ a, |==> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.
Global Instance from_exist_fupd `{BiFUpd PROP} {A} E1 E2 P (Φ : A → PROP) :
  FromExist P Φ → FromExist (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

Global Instance from_exist_plainly `{BiPlainly PROP} {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (■ P) (λ a, ■ (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite -plainly_exist_2. Qed.

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

Global Instance into_exist_plainly `{BiPlainlyExist PROP} {A} P (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (■ P) (λ a, ■ (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP plainly_exist. Qed.

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

Global Instance into_forall_plainly `{BiPlainly PROP} {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (■ P) (λ a, ■ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP plainly_forall. Qed.

(* FromForall *)
Global Instance from_forall_later {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (▷ P)%I (λ a, ▷ (Φ a))%I.
Proof. rewrite /FromForall=> <-. by rewrite later_forall. Qed.
Global Instance from_forall_except_0 {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (◇ P)%I (λ a, ◇ (Φ a))%I.
Proof. rewrite /FromForall=> <-. by rewrite except_0_forall. Qed.

Global Instance from_forall_plainly `{BiPlainly PROP} {A} P (Φ : A → PROP) :
  FromForall P Φ → FromForall (■ P)%I (λ a, ■ (Φ a))%I.
Proof. rewrite /FromForall=> <-. by rewrite plainly_forall. Qed.

(* IsExcept0 *)
Global Instance is_except_0_except_0 P : IsExcept0 (◇ P).
Proof. by rewrite /IsExcept0 except_0_idemp. Qed.
Global Instance is_except_0_later P : IsExcept0 (▷ P).
Proof. by rewrite /IsExcept0 except_0_later. Qed.
Global Instance is_except_0_embed `{SbiEmbed PROP PROP'} P :
  IsExcept0 P → IsExcept0 ⎡P⎤.
Proof. by rewrite /IsExcept0 -embed_except_0=>->. Qed.
Global Instance is_except_0_bupd `{BiBUpd PROP} P : IsExcept0 P → IsExcept0 (|==> P).
Proof.
  rewrite /IsExcept0=> HP.
  by rewrite -{2}HP -(except_0_idemp P) -except_0_bupd -(except_0_intro P).
Qed.
Global Instance is_except_0_fupd `{BiFUpd PROP} E1 E2 P :
  IsExcept0 (|={E1,E2}=> P).
Proof. by rewrite /IsExcept0 except_0_fupd. Qed.

(* FromModal *)
Global Instance from_modal_later P :
  FromModal (modality_laterN 1) (▷^1 P) (▷ P) P.
Proof. by rewrite /FromModal. Qed.
Global Instance from_modal_laterN n P :
  FromModal (modality_laterN n) (▷^n P) (▷^n P) P.
Proof. by rewrite /FromModal. Qed.
Global Instance from_modal_except_0 P : FromModal modality_id (◇ P) (◇ P) P.
Proof. by rewrite /FromModal /= -except_0_intro. Qed.

Global Instance from_modal_bupd `{BiBUpd PROP} P :
  FromModal modality_id (|==> P) (|==> P) P.
Proof. by rewrite /FromModal /= -bupd_intro. Qed.
Global Instance from_modal_fupd E P `{BiFUpd PROP} :
  FromModal modality_id (|={E}=> P) (|={E}=> P) P.
Proof. by rewrite /FromModal /= -fupd_intro. Qed.

Global Instance from_modal_later_embed `{SbiEmbed PROP PROP'} `(sel : A) n P Q :
  FromModal (modality_laterN n) sel P Q →
  FromModal (modality_laterN n) sel ⎡P⎤ ⎡Q⎤.
Proof. rewrite /FromModal /= =><-. by rewrite embed_laterN. Qed.

Global Instance from_modal_plainly `{BiPlainly PROP} P :
  FromModal modality_plainly (■ P) (■ P) P | 2.
Proof. by rewrite /FromModal. Qed.

Global Instance from_modal_plainly_embed `{BiPlainly PROP, BiPlainly PROP',
    BiEmbedPlainly PROP PROP', !SbiEmbed PROP PROP'} `(sel : A) P Q :
  FromModal modality_plainly sel P Q →
  FromModal modality_plainly sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. rewrite /FromModal /= =><-. by rewrite embed_plainly. Qed.

(* IntoInternalEq *)
Global Instance into_internal_eq_internal_eq {A : ofeT} (x y : A) :
  @IntoInternalEq PROP A (x ≡ y) x y.
Proof. by rewrite /IntoInternalEq. Qed.
Global Instance into_internal_eq_affinely {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (<affine> P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite affinely_elim. Qed.
Global Instance into_internal_eq_intuitionistically {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (□ P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite intuitionistically_elim. Qed.
Global Instance into_internal_eq_absorbingly {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (<absorb> P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite absorbingly_internal_eq. Qed.
Global Instance into_internal_eq_plainly `{BiPlainly PROP} {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (■ P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite plainly_elim. Qed.
Global Instance into_internal_eq_persistently {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (<pers> P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite persistently_elim. Qed.
Global Instance into_internal_eq_embed
       `{SbiEmbed PROP PROP'} {A : ofeT} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq ⎡P⎤ x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite embed_internal_eq. Qed.

(* IntoExcept0 *)
Global Instance into_except_0_except_0 P : IntoExcept0 (◇ P) P.
Proof. by rewrite /IntoExcept0. Qed.
Global Instance into_except_0_later P : Timeless P → IntoExcept0 (▷ P) P.
Proof. by rewrite /IntoExcept0. Qed.
Global Instance into_except_0_later_if p P : Timeless P → IntoExcept0 (▷?p P) P.
Proof. rewrite /IntoExcept0. destruct p; auto using except_0_intro. Qed.

Global Instance into_except_0_affinely P Q :
  IntoExcept0 P Q → IntoExcept0 (<affine> P) (<affine> Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_affinely_2. Qed.
Global Instance into_except_0_intuitionistically P Q :
  IntoExcept0 P Q → IntoExcept0 (□ P) (□ Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_intuitionistically_2. Qed.
Global Instance into_except_0_absorbingly P Q :
  IntoExcept0 P Q → IntoExcept0 (<absorb> P) (<absorb> Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_absorbingly. Qed.
Global Instance into_except_0_plainly `{BiPlainly PROP, BiPlainlyExist PROP} P Q :
  IntoExcept0 P Q → IntoExcept0 (■ P) (■ Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_plainly. Qed.
Global Instance into_except_0_persistently P Q :
  IntoExcept0 P Q → IntoExcept0 (<pers> P) (<pers> Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_persistently. Qed.
Global Instance into_except_0_embed `{SbiEmbed PROP PROP'} P Q :
  IntoExcept0 P Q → IntoExcept0 ⎡P⎤ ⎡Q⎤.
Proof. rewrite /IntoExcept0=> ->. by rewrite embed_except_0. Qed.

(* ElimModal *)
Global Instance elim_modal_timeless p P Q :
  IntoExcept0 P P' → IsExcept0 Q → ElimModal True p p P P' Q Q.
Proof.
  intros. rewrite /ElimModal (except_0_intro (_ -∗ _)%I) (into_except_0 P).
  by rewrite except_0_intuitionistically_if_2 -except_0_sep wand_elim_r.
Qed.

Global Instance elim_modal_bupd_plain_goal `{BiBUpdPlainly PROP} p P Q :
  Plain Q → ElimModal True p false (|==> P) P Q Q.
Proof.
  intros. by rewrite /ElimModal intuitionistically_if_elim
    bupd_frame_r wand_elim_r bupd_plain.
Qed.
Global Instance elim_modal_bupd_plain `{BiBUpdPlainly PROP} p P Q :
  Plain P → ElimModal True p p (|==> P) P Q Q.
Proof. intros. by rewrite /ElimModal bupd_plain wand_elim_r. Qed.
Global Instance elim_modal_bupd_fupd `{BiBUpdFUpd PROP} p E1 E2 P Q :
  ElimModal True p false (|==> P) P (|={E1,E2}=> Q) (|={E1,E2}=> Q) | 10.
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_trans.
Qed.

Global Instance elim_modal_fupd_fupd `{BiFUpd PROP} p E1 E2 E3 P Q :
  ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    fupd_frame_r wand_elim_r fupd_trans.
Qed.

Global Instance elim_modal_embed_fupd_goal `{BiEmbedFUpd PROP PROP'}
    p p' φ E1 E2 E3 (P P' : PROP') (Q Q' : PROP) :
  ElimModal φ p p' P P' (|={E1,E3}=> ⎡Q⎤)%I (|={E2,E3}=> ⎡Q'⎤)%I →
  ElimModal φ p p' P P' ⎡|={E1,E3}=> Q⎤ ⎡|={E2,E3}=> Q'⎤.
Proof. by rewrite /ElimModal !embed_fupd. Qed.
Global Instance elim_modal_embed_fupd_hyp `{BiEmbedFUpd PROP PROP'}
    p p' φ E1 E2 (P : PROP) (P' Q Q' : PROP') :
  ElimModal φ p p' (|={E1,E2}=> ⎡P⎤)%I P' Q Q' →
  ElimModal φ p p' ⎡|={E1,E2}=> P⎤ P' Q Q'.
Proof. by rewrite /ElimModal embed_fupd. Qed.

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

Global Instance add_modal_bupd `{BiBUpd PROP} P Q : AddModal (|==> P) P (|==> Q).
Proof. by rewrite /AddModal bupd_frame_r wand_elim_r bupd_trans. Qed.
Global Instance add_modal_fupd `{BiFUpd PROP} E1 E2 P Q :
  AddModal (|={E1}=> P) P (|={E1,E2}=> Q).
Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_trans. Qed.

Global Instance add_modal_embed_fupd_goal `{BiEmbedFUpd PROP PROP'}
       E1 E2 (P P' : PROP') (Q : PROP) :
  AddModal P P' (|={E1,E2}=> ⎡Q⎤)%I → AddModal P P' ⎡|={E1,E2}=> Q⎤.
Proof. by rewrite /AddModal !embed_fupd. Qed.

(* ElimAcc *)
Global Instance elim_acc_vs `{BiFUpd PROP} {X} E1 E2 E α β γ Q :
  (* FIXME: Why %I? ElimAcc sets the right scopes! *)
  ElimAcc (X:=X) E1 E2 α β γ
          (|={E1,E}=> Q)
          (λ x, |={E2}=> (β x ∗ (coq_tactics.maybe_wand (γ x) (|={E1,E}=> Q))))%I.
Proof.
  rewrite /ElimAcc. setoid_rewrite coq_tactics.maybe_wand_sound.
  iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iMod ("Hinner" with "Hα") as "[Hβ Hfin]".
  iMod ("Hclose" with "Hβ") as "Hγ". by iApply "Hfin".
Qed.

(* IntoAcc *)
(* TODO: We could have instances from "unfolded" accessors with or without
   the first binder. *)

(* ElimInv *)
Global Instance elim_inv_acc_without_close `{BiFUpd PROP} {X : Type}
       φ Pinv Pin
       E1 E2 α β γ Q (Q' : X → PROP) :
  IntoAcc (X:=X) Pinv φ Pin E1 E2 α β γ →
  ElimAcc (X:=X) E1 E2 α β γ Q Q' →
  ElimInv φ Pinv Pin α None Q Q'.
Proof.
  rewrite /ElimAcc /IntoAcc /ElimInv.
  iIntros (Hacc Helim Hφ) "(Hinv & Hin & Hcont)".
  iApply (Helim with "[Hcont]").
  - iIntros (x) "Hα". iApply "Hcont". iSplitL; done.
  - iApply (Hacc with "Hinv Hin"). done.
Qed.

Global Instance elim_inv_acc_with_close `{BiFUpd PROP} {X : Type}
       φ Pinv Pin
       E1 E2 α β γ Q Q' :
  IntoAcc Pinv φ Pin E1 E2 α β γ →
  (∀ R, ElimModal True false false (|={E1,E2}=> R) R Q Q') →
  ElimInv (X:=X) φ Pinv Pin α (Some (λ x, β x ={E2,E1}=∗ default emp (γ x) id))%I
          Q (λ _, Q').
Proof.
  rewrite /ElimAcc /IntoAcc /ElimInv.
  iIntros (Hacc Helim Hφ) "(Hinv & Hin & Hcont)".
  iMod (Hacc with "Hinv Hin") as (x) "[Hα Hclose]"; first done.
  iApply "Hcont". simpl. iSplitL "Hα"; done.
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
  IntoLaterN false n P Q → IntoLaterN false n (<affine> P) (<affine> Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_affinely_2. Qed.
Global Instance into_later_intuitionistically n P Q :
  IntoLaterN false n P Q → IntoLaterN false n (□ P) (□ Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_intuitionistically_2. Qed.
Global Instance into_later_absorbingly n P Q :
  IntoLaterN false n P Q → IntoLaterN false n (<absorb> P) (<absorb> Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_absorbingly. Qed.
Global Instance into_later_plainly `{BiPlainly PROP} n P Q :
  IntoLaterN false n P Q → IntoLaterN false n (■ P) (■ Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_plainly. Qed.
Global Instance into_later_persistently n P Q :
  IntoLaterN false n P Q → IntoLaterN false n (<pers> P) (<pers> Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_persistently. Qed.
Global Instance into_later_embed`{SbiEmbed PROP PROP'} n P Q :
  IntoLaterN false n P Q → IntoLaterN false n ⎡P⎤ ⎡Q⎤.
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite embed_laterN. Qed.

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
End sbi_instances.
