From iris.bi Require Import bi.
From iris.proofmode Require Export classes.
Set Default Proof Using "Type".
Import bi.

Section bi_modalities.
  Context {SI} {PROP : bi SI}.

  Lemma modality_persistently_mixin :
    modality_mixin (@bi_persistently SI PROP) MIEnvId MIEnvClear.
  Proof.
    split; simpl; eauto using equiv_entails_sym, persistently_intro,
      persistently_mono, persistently_sep_2 with typeclass_instances.
  Qed.
  Definition modality_persistently :=
    Modality _ modality_persistently_mixin.

  Lemma modality_affinely_mixin :
    modality_mixin (@bi_affinely SI PROP) MIEnvId (MIEnvForall Affine).
  Proof.
    split; simpl; eauto using equiv_entails_sym, affinely_intro, affinely_mono,
      affinely_sep_2 with typeclass_instances.
  Qed.
  Definition modality_affinely :=
    Modality _ modality_affinely_mixin.

  Lemma modality_intuitionistically_mixin :
    modality_mixin (@bi_intuitionistically SI PROP) MIEnvId MIEnvIsEmpty.
  Proof.
    split; simpl; eauto using equiv_entails_sym, intuitionistically_emp,
      affinely_mono, persistently_mono, intuitionistically_idemp,
      intuitionistically_sep_2 with typeclass_instances.
  Qed.
  Definition modality_intuitionistically :=
    Modality _ modality_intuitionistically_mixin.

  Lemma modality_embed_mixin `{BiEmbed SI PROP PROP'} :
    modality_mixin (@embed PROP PROP' _)
      (MIEnvTransform IntoEmbed) (MIEnvTransform IntoEmbed).
  Proof.
    split; simpl; split_and?;
      eauto using equiv_entails_sym, embed_emp_2, embed_sep, embed_and.
    - intros P Q. rewrite /IntoEmbed=> ->. by rewrite embed_intuitionistically_2.
    - by intros P Q ->.
  Qed.
  Definition modality_embed `{BiEmbed SI PROP PROP'} :=
    Modality _ modality_embed_mixin.
End bi_modalities.

Section sbi_modalities.
  Context {SI} {PROP : sbi SI}.

  Lemma modality_plainly_mixin `{BiPlainly SI PROP} :
    modality_mixin (@plainly PROP _) (MIEnvForall Plain) MIEnvClear.
  Proof.
    split; simpl; split_and?; eauto using equiv_entails_sym, plainly_intro,
      plainly_mono, plainly_and, plainly_sep_2 with typeclass_instances.
  Qed.
  Definition modality_plainly `{BiPlainly SI PROP} :=
    Modality _ modality_plainly_mixin.

  Lemma modality_laterN_mixin n :
    modality_mixin (Nat.iter n (@sbi_later SI PROP))
      (MIEnvTransform (MaybeIntoLaterN false n)) (MIEnvTransform (MaybeIntoLaterN false n)).
  Proof.
    split; simpl; split_and?; eauto using equiv_entails_sym, laterN_intro,
      laterN_mono, laterN_and, laterN_sep_2 with typeclass_instances.
    rewrite /MaybeIntoLaterN=> P Q ->. by rewrite laterN_intuitionistically_2.
  Qed.
  Definition modality_laterN n :=
    Modality _ (modality_laterN_mixin n).
End sbi_modalities.
