From iris.bi Require Import
  derived_connectives derived_laws_bi
  derived_laws_sbi notation interface
  plainly updates.


Section satisfiable.
  Context {SI: indexT} {PROP: sbi SI} `{BiPlainly SI PROP} `{BUpd PROP}.


  Structure satisfiable_mixin (satisfiable: PROP → Prop) := {
    satisfiable_mixin_intro P: (True ⊢ P) → satisfiable P;
    satisfiable_mixin_mono P Q: satisfiable P → (P ⊢ Q) → satisfiable Q;
    satisfiable_mixin_elim  P: satisfiable P → Plain P → True ⊢ P;
    satisfiable_mixin_later P: satisfiable (▷ P)%I → satisfiable P;
    satisfiable_mixin_finite_exists `{FiniteExistential SI} (X: Type) P Q: satisfiable (∃ x: X, P x)%I → pred_finite Q → (∀ x, P x ⊢ ⌜Q x⌝) → ∃ x: X, satisfiable (P x);
    satisfiable_mixin_exists `{LargeIndex SI} (X: Type) P: satisfiable (∃ x: X, P x)%I → ∃ x: X, satisfiable (P x);
    satisfiable_mixin_bupd P: satisfiable (|==> P)%I → satisfiable P
  }.


  Class Satisfiable := {
    satisfiable: PROP → Prop;
    satisfiable_satisfiable_mixin: satisfiable_mixin satisfiable
  }.


  Section satisfiable_lemmas.
    Context `{Satisfiable}.

    Lemma satisfiable_intro P: (True ⊢ P) → satisfiable P.
    Proof. apply satisfiable_mixin_intro, satisfiable_satisfiable_mixin. Qed.

    Lemma satisfiable_mono P Q: satisfiable P → (P ⊢ Q) → satisfiable Q.
    Proof. apply satisfiable_mixin_mono, satisfiable_satisfiable_mixin. Qed.

    Lemma satisfiable_elim  P: satisfiable P → Plain P → True ⊢ P.
    Proof. apply satisfiable_mixin_elim, satisfiable_satisfiable_mixin. Qed.

    Lemma satisfiable_later P: satisfiable (▷ P)%I → satisfiable P.
    Proof. apply satisfiable_mixin_later, satisfiable_satisfiable_mixin. Qed.

    Lemma satisfiable_finite_exists `{FiniteExistential SI} (X: Type) P Q: satisfiable (∃ x: X, P x)%I → pred_finite Q → (∀ x, P x ⊢ ⌜Q x⌝) → ∃ x: X, satisfiable (P x).
    Proof. apply satisfiable_mixin_finite_exists; auto. apply satisfiable_satisfiable_mixin. Qed.

    Lemma satisfiable_exists `{LargeIndex SI} (X: Type) P: satisfiable (∃ x: X, P x)%I → ∃ x: X, satisfiable (P x).
    Proof. apply satisfiable_mixin_exists; auto. apply satisfiable_satisfiable_mixin. Qed.

    Lemma satisfiable_bupd P: satisfiable (|==> P)%I → satisfiable P.
    Proof. apply satisfiable_mixin_bupd; auto. apply satisfiable_satisfiable_mixin. Qed.

    Lemma satisfiable_forall {X} (x: X) P: satisfiable (∀ x, P x)%I → satisfiable (P x).
    Proof. intros Hs; eapply (satisfiable_mono _ _ Hs), bi.forall_elim. Qed.

    Lemma satisfiable_impl P Q: satisfiable (P → Q)%I → (True ⊢ P) → satisfiable Q.
    Proof.
      intros Hs Hent; apply (satisfiable_mono _ _ Hs).
      etrans; last apply derived_laws_bi.bi.impl_elim_r.
      apply bi.and_intro; last reflexivity.
      etrans; last apply Hent. by eapply bi.pure_intro.
    Qed.

    Lemma satisfiable_wand P Q: satisfiable (P -∗ Q)%I → (True ⊢ P) → satisfiable Q.
    Proof.
      intros Hs Hent; apply (satisfiable_mono _ _ Hs).
      erewrite derived_laws_bi.bi.True_sep_2.
      rewrite Hent. apply derived_laws_bi.bi.wand_elim_r.
    Qed.

    Lemma satisfiable_pers `{BiAffine SI PROP} P: satisfiable (<pers> P)%I → satisfiable P.
    Proof.
      intros Hs; apply (satisfiable_mono _ _ Hs).
      apply bi.persistently_elim. apply _.
    Qed.

    Lemma satisfiable_intuitionistically P: satisfiable (□ P)%I → satisfiable P.
    Proof.
      intros Hs; apply (satisfiable_mono _ _ Hs).
      apply bi.intuitionistically_elim.
    Qed.

    Lemma satisfiable_or `{FiniteExistential SI} P Q: satisfiable (P ∨ Q)%I → satisfiable P ∨ satisfiable Q.
    Proof.
      intros Hs. assert (satisfiable (∃ b: bool, if b then P else Q)%I) as Hex.
      - apply (satisfiable_mono _ _ Hs). by rewrite bi.or_alt.
      - apply satisfiable_finite_exists with (Q := λ b, True) in Hex as [[] Hex]; auto.
        + exists [true;false]; intros [] _; rewrite !elem_of_cons; eauto.
        + intros x. eapply bi.True_intro.
    Qed.

    Global Instance satisfiable_equiv: Proper (equiv ==> iff) satisfiable.
    Proof.
      intros P Q HPQ. split; intros H'; eapply satisfiable_mono; eauto; by rewrite HPQ.
    Qed.
  End satisfiable_lemmas.

End satisfiable.
Arguments Satisfiable {_} _ {_} {_}.

