From iris.bi Require Import bi.
From iris.proofmode Require Export classes.
Set Default Proof Using "Type".
Import bi.

Section bi_modalities.
  Context {PROP : bi}.

  Lemma modality_persistently_mixin :
    modality_mixin (@bi_persistently PROP) MIEnvId MIEnvClear.
  Proof.
    split; simpl; eauto using equiv_entails_sym, persistently_intro,
      persistently_mono, persistently_sep_2 with typeclass_instances.
  Qed.
  Definition modality_persistently :=
    Modality _ modality_persistently_mixin.

  Lemma modality_affinely_mixin :
    modality_mixin (@bi_affinely PROP) MIEnvId (MIEnvForall Affine).
  Proof.
    split; simpl; eauto using equiv_entails_sym, affinely_intro, affinely_mono,
      affinely_sep_2 with typeclass_instances.
  Qed.
  Definition modality_affinely :=
    Modality _ modality_affinely_mixin.

  Lemma modality_affinely_persistently_mixin :
    modality_mixin (λ P : PROP, □ P)%I MIEnvId MIEnvIsEmpty.
  Proof.
    split; simpl; eauto using equiv_entails_sym, affinely_persistently_emp,
      affinely_mono, persistently_mono, affinely_persistently_idemp,
      affinely_persistently_sep_2 with typeclass_instances.
  Qed.
  Definition modality_affinely_persistently :=
    Modality _ modality_affinely_persistently_mixin.

  Lemma modality_plainly_mixin :
    modality_mixin (@bi_plainly PROP) (MIEnvForall Plain) MIEnvClear.
  Proof.
    split; simpl; split_and?; eauto using equiv_entails_sym, plainly_intro,
      plainly_mono, plainly_and, plainly_sep_2 with typeclass_instances.
  Qed.
  Definition modality_plainly :=
    Modality _ modality_plainly_mixin.

  Lemma modality_affinely_plainly_mixin :
    modality_mixin (λ P : PROP, ■ P)%I (MIEnvForall Plain) MIEnvIsEmpty.
  Proof.
    split; simpl; split_and?; eauto using equiv_entails_sym,
      affinely_plainly_emp, affinely_intro,
      plainly_intro, affinely_mono, plainly_mono, affinely_plainly_idemp,
      affinely_plainly_and, affinely_plainly_sep_2 with typeclass_instances.
  Qed.
  Definition modality_affinely_plainly :=
    Modality _ modality_affinely_plainly_mixin.

  Lemma modality_embed_mixin `{BiEmbed PROP PROP'} :
    modality_mixin (@embed PROP PROP' _)
      (MIEnvTransform IntoEmbed) (MIEnvTransform IntoEmbed).
  Proof.
    split; simpl; split_and?;
      eauto using equiv_entails_sym, embed_emp, embed_sep, embed_and.
    - intros P Q. rewrite /IntoEmbed=> ->.
      by rewrite embed_affinely embed_persistently.
    - by intros P Q ->.
  Qed.
  Definition modality_embed `{BiEmbed PROP PROP'} :=
    Modality _ modality_embed_mixin.
End bi_modalities.

Section sbi_modalities.
  Context {PROP : sbi}.

  Lemma modality_laterN_mixin n :
    modality_mixin (@sbi_laterN PROP n)
      (MIEnvTransform (MaybeIntoLaterN false n)) (MIEnvTransform (MaybeIntoLaterN false n)).
  Proof.
    split; simpl; split_and?; eauto using equiv_entails_sym, laterN_intro,
      laterN_mono, laterN_and, laterN_sep with typeclass_instances.
    rewrite /MaybeIntoLaterN=> P Q ->. by rewrite laterN_affinely_persistently_2.
  Qed.
  Definition modality_laterN n :=
    Modality _ (modality_laterN_mixin n).
End sbi_modalities.
