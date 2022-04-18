From iris.base_logic Require Import bi.
From iris.bi Require Export satisfiable.


Section uPred_satisfiable.
  Context {SI: indexT} (M: ucmraT SI).

  Definition uPred_satisfiable (P: uPred M) := ∀ n, ∃ x, ✓{n} x ∧ P n x.

  Lemma uPred_satisfiable_intro P: (True ⊢ P) → uPred_satisfiable P.
  Proof.
    unfold uPred_satisfiable. intros [H]. revert H; uPred.unseal. intros H n. exists ε.
    simpl in *; split; eauto using ucmra_unit_validN.
    apply H; eauto using ucmra_unit_validN.
    constructor.
  Qed.

  Lemma uPred_satisfiable_mono P Q: uPred_satisfiable P → (P ⊢ Q) → uPred_satisfiable Q.
  Proof.
    unfold uPred_satisfiable. intros HP [PQ] n.
    destruct (HP n) as (x & Hv & HP'). exists x. split; eauto.
  Qed.

  Lemma uPred_satisfiable_elim P: uPred_satisfiable P → Plain P → True ⊢ P.
  Proof.
    unfold uPred_satisfiable, Plain. uPred.unseal. intros HP [H]. split=> n x Hv _.
    destruct (HP n) as (y & Hv' & HP').
    specialize (H n y Hv' HP').
    eapply uPred_mono; first apply H; auto.
    apply ucmra_unit_leastN.
  Qed.

  Lemma uPred_satisfiable_later P: uPred_satisfiable (▷ P) → uPred_satisfiable P.
  Proof.
    intros H n. destruct (H (stepindex.succ n)) as (x & Hv & HP).
    exists x. split.
    - eapply cmra_validN_le; eauto.
    - revert HP. uPred.unseal. intros HP. apply HP. eauto with index.
  Qed.

  Lemma uPred_satisfiable_update P: uPred_satisfiable (|==> P) → uPred_satisfiable P.
  Proof.
    unfold uPred_satisfiable. uPred.unseal. intros H.
    intros n. destruct (H n) as (y & Hv & Hupd).
    destruct (Hupd n ε) as (z & Hv' & HP); eauto; first by rewrite right_id.
    exists z; split; eauto. revert Hv'. by rewrite right_id.
  Qed.

  Lemma uPred_satisfiable_finite_exists `{FiniteExistential SI} A (P: A → uPred M) Q: uPred_satisfiable (∃ a, P a) → pred_finite Q → (∀ x, P x ⊢ ⌜Q x⌝) → ∃ a, uPred_satisfiable (P a).
  Proof.
    unfold uPred_satisfiable. intros Hexist Hfin Hent.
    eapply (can_commute_finite_exists _ (λ a n, ∃ x: M, ✓{n} x ∧ P a n x) Q); auto.
    - intros a m n Hmn (x & Hv & HP). exists x. split.
      + eapply cmra_validN_le; eauto.
      + eapply uPred_mono; eauto.
    - intros n. destruct (Hexist n) as (x & Hv & HP); eauto.
      revert HP Hent. uPred.unseal. intros [a ?] H'; eauto.
      exists a. split; eauto. specialize (H' a) as [H'].
      by eapply H'.
  Qed.

  Lemma uPred_satisfiable_exists `{LargeIndex SI} A (P: A → uPred M): uPred_satisfiable (∃ a, P a) → ∃ a, uPred_satisfiable (P a).
  Proof.
    unfold uPred_satisfiable.
    specialize (can_commute_exists _ (λ a n, ∃ x: M, ✓{n} x ∧ P a n x)) as Hcomm.
    intros Hexist. edestruct Hcomm as (a & HP).
    - intros a m n Hmn (x & Hv & HP). exists x. split.
      + eapply cmra_validN_le; eauto.
      + eapply uPred_mono; eauto.
    - intros n. destruct (Hexist n) as (x & Hv & HP); eauto.
      revert HP. uPred.unseal. intros [? ?]; eauto.
    - exists a. intros n. apply HP.
  Qed.


  Lemma uPred_satisfiable_mixin: satisfiable_mixin uPred_satisfiable.
  Proof.
    constructor.
    - apply uPred_satisfiable_intro.
    - apply uPred_satisfiable_mono.
    - apply uPred_satisfiable_elim.
    - apply uPred_satisfiable_later.
    - apply @uPred_satisfiable_finite_exists.
    - apply @uPred_satisfiable_exists.
    - apply uPred_satisfiable_update.
  Qed.

  Global Instance uPred_Satisfiable: Satisfiable (uPredSI M) :=
  {| satisfiable := uPred_satisfiable;
     satisfiable_satisfiable_mixin := uPred_satisfiable_mixin |}.


End uPred_satisfiable.







