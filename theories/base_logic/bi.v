From iris.bi Require Export derived_connectives updates plainly.
From iris.base_logic Require Export upred.
Import uPred_primitive.

(** BI instances for uPred, and re-stating the remaining primitive laws in terms
of the BI interface.  This file does *not* unseal. *)

Definition uPred_emp {M} : uPred M := uPred_pure True.

Local Existing Instance entails_po.

Lemma uPred_bi_mixin (M : ucmraT) :
  BiMixin
    uPred_entails uPred_emp uPred_pure uPred_and uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_wand
    uPred_persistently.
Proof.
  split.
  - exact: entails_po.
  - exact: equiv_spec.
  - exact: pure_ne.
  - exact: and_ne.
  - exact: or_ne.
  - exact: impl_ne.
  - exact: forall_ne.
  - exact: exist_ne.
  - exact: sep_ne.
  - exact: wand_ne.
  - exact: persistently_ne.
  - exact: pure_intro.
  - exact: pure_elim'.
  - exact: @pure_forall_2.
  - exact: and_elim_l.
  - exact: and_elim_r.
  - exact: and_intro.
  - exact: or_intro_l.
  - exact: or_intro_r.
  - exact: or_elim.
  - exact: impl_intro_r.
  - exact: impl_elim_l'.
  - exact: @forall_intro.
  - exact: @forall_elim.
  - exact: @exist_intro.
  - exact: @exist_elim.
  - exact: sep_mono.
  - exact: True_sep_1. 
  - exact: True_sep_2.
  - exact: sep_comm'.
  - exact: sep_assoc'.
  - exact: wand_intro_r.
  - exact: wand_elim_l'.
  - exact: persistently_mono.
  - exact: persistently_idemp_2.
  - (* emp ⊢ <pers> emp (ADMISSIBLE) *)
    trans (uPred_forall (M:=M) (λ _ : False, uPred_persistently uPred_emp)).
    + apply forall_intro=>[[]].
    + etrans; first exact: persistently_forall_2.
      apply persistently_mono. exact: pure_intro.
  - exact: @persistently_forall_2.
  - exact: @persistently_exist_1.
  - (* <pers> P ∗ Q ⊢ <pers> P (ADMISSIBLE) *)
    intros. etrans; first exact: sep_comm'.
    etrans; last exact: True_sep_2.
    apply sep_mono; last done.
    exact: pure_intro.
  - exact: persistently_and_sep_l_1.
Qed.

Lemma uPred_sbi_mixin (M : ucmraT) : SbiMixin
  uPred_entails uPred_pure uPred_or uPred_impl
  (@uPred_forall M) (@uPred_exist M) uPred_sep
  uPred_persistently (@uPred_internal_eq M) uPred_later.
Proof.
  split.
  - exact: later_contractive.
  - exact: internal_eq_ne.
  - exact: @internal_eq_refl.
  - exact: @internal_eq_rewrite.
  - exact: @fun_ext.
  - exact: @sig_eq.
  - exact: @discrete_eq_1.
  - exact: @later_eq_1.
  - exact: @later_eq_2.
  - exact: later_mono.
  - exact: later_intro.
  - exact: @later_forall_2.
  - exact: @later_exist_false.
  - exact: later_sep_1.
  - exact: later_sep_2.
  - exact: later_persistently_1.
  - exact: later_persistently_2.
  - exact: later_false_em.
Qed.

Canonical Structure uPredI (M : ucmraT) : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (uPred M); bi_bi_mixin := uPred_bi_mixin M |}.
Canonical Structure uPredSI (M : ucmraT) : sbi :=
  {| sbi_ofe_mixin := ofe_mixin_of (uPred M);
     sbi_bi_mixin := uPred_bi_mixin M; sbi_sbi_mixin := uPred_sbi_mixin M |}.

Coercion uPred_valid {M} : uPred M → Prop := bi_emp_valid.

Lemma uPred_plainly_mixin M : BiPlainlyMixin (uPredSI M) uPred_plainly.
Proof.
  split.
  - exact: plainly_ne.
  - exact: plainly_mono.
  - exact: plainly_elim_persistently.
  - exact: plainly_idemp_2.
  - exact: @plainly_forall_2.
  - exact: persistently_impl_plainly.
  - exact: plainly_impl_plainly.
  - (* P ⊢ ■ emp (ADMISSIBLE) *)
    intros P.
    trans (uPred_forall (M:=M) (λ _ : False , uPred_plainly uPred_emp)).
    + apply forall_intro=>[[]].
    + etrans; first exact: plainly_forall_2.
      apply plainly_mono. exact: pure_intro.
  - (* ■ P ∗ Q ⊢ ■ P (ADMISSIBLE) *)
    intros P Q. etrans; last exact: True_sep_2.
    etrans; first exact: sep_comm'.
    apply sep_mono; last done.
    exact: pure_intro.
  - exact: prop_ext.
  - exact: later_plainly_1.
  - exact: later_plainly_2.
Qed.
Global Instance uPred_plainlyC M : BiPlainly (uPredSI M) :=
  {| bi_plainly_mixin := uPred_plainly_mixin M |}.

Lemma uPred_bupd_mixin M : BiBUpdMixin (uPredI M) uPred_bupd.
Proof.
  split.
  - exact: bupd_ne.
  - exact: bupd_intro.
  - exact: bupd_mono.
  - exact: bupd_trans.
  - exact: bupd_frame_r.
Qed.
Global Instance uPred_bi_bupd M : BiBUpd (uPredI M) := {| bi_bupd_mixin := uPred_bupd_mixin M |}.

Global Instance uPred_bi_bupd_plainly M : BiBUpdPlainly (uPredSI M).
Proof. exact: bupd_plainly. Qed.

(** extra BI instances *)

Global Instance uPred_affine : BiAffine (uPredI M) | 0.
Proof. intros P Q. exact: pure_intro. Qed.
(* Also add this to the global hint database, otherwise [eauto] won't work for
many lemmas that have [BiAffine] as a premise. *)
Hint Immediate uPred_affine.

Global Instance uPred_plainly_exist_1 : BiPlainlyExist (uPredSI M).
Proof. exact: @plainly_exist_1. Qed.

(** Re-state/export lemmas about Iris-specific primitive connectives (own, valid) *)

Module uPred.

Section restate.
Context {M : ucmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

Global Existing Instance uPred_primitive.ownM_ne.
Global Existing Instance uPred_primitive.cmra_valid_ne.

(** Re-exporting primitive Own and valid lemmas *)
Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
Proof. exact: uPred_primitive.ownM_op. Qed.
Lemma persistently_ownM_core (a : M) : uPred_ownM a ⊢ <pers> uPred_ownM (core a).
Proof. exact: uPred_primitive.persistently_ownM_core. Qed.
Lemma ownM_unit P : P ⊢ (uPred_ownM ε).
Proof. exact: uPred_primitive.ownM_unit. Qed.
Lemma later_ownM a : ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ (a ≡ b).
Proof. exact: uPred_primitive.later_ownM. Qed.
Lemma bupd_ownM_updateP x (Φ : M → Prop) :
  x ~~>: Φ → uPred_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ uPred_ownM y.
Proof. exact: uPred_primitive.bupd_ownM_updateP. Qed.

Lemma ownM_valid (a : M) : uPred_ownM a ⊢ ✓ a.
Proof. exact: uPred_primitive.ownM_valid. Qed.
Lemma cmra_valid_intro {A : cmraT} P (a : A) : ✓ a → P ⊢ (✓ a).
Proof. exact: uPred_primitive.cmra_valid_intro. Qed.
Lemma cmra_valid_elim {A : cmraT} (a : A) : ¬ ✓{0} a → ✓ a ⊢ False.
Proof. exact: uPred_primitive.cmra_valid_elim. Qed.
Lemma plainly_cmra_valid_1 {A : cmraT} (a : A) : ✓ a ⊢ ■ ✓ a.
Proof. exact: uPred_primitive.plainly_cmra_valid_1. Qed.
Lemma cmra_valid_weaken {A : cmraT} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
Proof. exact: uPred_primitive.cmra_valid_weaken. Qed.
Lemma prod_validI {A B : cmraT} (x : A * B) : ✓ x ⊣⊢ ✓ x.1 ∧ ✓ x.2.
Proof. exact: uPred_primitive.prod_validI. Qed.
Lemma option_validI {A : cmraT} (mx : option A) :
  ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True : uPred M end.
Proof. exact: uPred_primitive.option_validI. Qed.
Lemma discrete_valid {A : cmraT} `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
Proof. exact: uPred_primitive.discrete_valid. Qed.
Lemma ofe_fun_validI `{B : A → ucmraT} (g : ofe_fun B) : ✓ g ⊣⊢ ∀ i, ✓ g i.
Proof. exact: uPred_primitive.ofe_fun_validI. Qed.

(** Consistency/soundness statement *)
Lemma soundness φ n : (▷^n ⌜ φ ⌝ : uPred M)%I → φ.
Proof. exact: uPred_primitive.soundness. Qed.

End restate.

(** New unseal tactic that also unfolds the BI layer.
    This is used by [base_logic.double_negation].
    TODO: Can we get rid of this? *)
Ltac unseal := (* Coq unfold is used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_emp; simpl; unfold sbi_emp; simpl;
  unfold uPred_emp, bupd, bi_bupd_bupd, bi_pure,
  bi_and, bi_or, bi_impl, bi_forall, bi_exist,
  bi_sep, bi_wand, bi_persistently, sbi_internal_eq, sbi_later; simpl;
  unfold sbi_emp, sbi_pure, sbi_and, sbi_or, sbi_impl, sbi_forall, sbi_exist,
  sbi_internal_eq, sbi_sep, sbi_wand, sbi_persistently; simpl;
  unfold plainly, bi_plainly_plainly; simpl;
  uPred_primitive.unseal.

End uPred.
