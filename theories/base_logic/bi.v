From iris.bi Require Export derived_connectives updates plainly.
From iris.base_logic Require Export upred.
Import uPred_primitive.

(** BI and other MoSeL instances for uPred.  This file does *not* unseal. *)

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
    trans (uPred_forall (M:=M) (fun _ : False => uPred_persistently uPred_emp)).
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
    trans (uPred_forall (M:=M) (fun _ : False => uPred_plainly uPred_emp)).
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
Instance uPred_plainlyC M : BiPlainly (uPredSI M) :=
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
Instance uPred_bi_bupd M : BiBUpd (uPredI M) := {| bi_bupd_mixin := uPred_bupd_mixin M |}.

Instance uPred_bi_bupd_plainly M : BiBUpdPlainly (uPredSI M).
Proof. exact: bupd_plainly. Qed.

(** extra BI instances *)

Global Instance uPred_affine : BiAffine (uPredI M) | 0.
Proof. intros P Q. exact: pure_intro. Qed.

Global Instance uPred_plainly_exist_1 : BiPlainlyExist (uPredSI M).
Proof. exact: @plainly_exist_1. Qed.
