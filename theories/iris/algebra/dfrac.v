(** Camera of discardable fractions.

    This is a generalisation of the fractional camera where elements can
    represent both ownership of a fraction (as in the fractional camera) and the
    knowledge that a fraction has been discarded.

    Ownership of a fraction is denoted [DfracOwn q] and behaves identically to
    [q] of the fractional camera.

    Knowledge that a fraction has been discarded is denoted [DfracDiscarded].
    This elements is its own core, making ownership persistent.

    One can make a frame preserving update from _owning_ a fraction to _knowing_
    that the fraction has been discarded.

    Crucially, ownership over 1 is an exclusive element just as it is in the
    fractional camera. Hence owning 1 implies that no fraction has been
    discarded. Conversely, knowing that a fraction has been discarded implies
    that no one can own 1. And, since discarding is an irreversible operation,
    it also implies that no one can own 1 in the future *)
From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes updates frac.

(** An element of dfrac denotes ownership of a fraction, knowledge that a
    fraction has been discarded, or both. Note that [DfracBoth] can be written
    as [DfracOwn q ⋅ DfracDiscarded]. This should be used instead
    of [DfracBoth] which is for internal use only. *)
Inductive dfrac :=
  | DfracOwn : Qp → dfrac
  | DfracDiscarded : dfrac
  | DfracBoth : Qp → dfrac.

Section dfrac.
Context {SI: indexT}.
  Canonical Structure dfracO := leibnizO SI dfrac.

  Implicit Types p q : Qp.
  Implicit Types dp dq : dfrac.

  Global Instance DfracOwn_inj : Inj (=) (=) DfracOwn.
  Proof. by injection 1. Qed.
  Global Instance DfracBoth_inj : Inj (=) (=) DfracBoth.
  Proof. by injection 1. Qed.

  (** An element is valid as long as the sum of its content is less than one. *)
  Instance dfrac_valid : Valid dfrac := λ dq,
    match dq with
    | DfracOwn q => q ≤ 1
    | DfracDiscarded => True
    | DfracBoth q => q < 1
    end%Qc.

  (** As in the fractional camera the core is undefined for elements denoting
     ownership of a fraction. For elements denoting the knowledge that a fraction has
     been discarded the core is the identity function. *)
  Instance dfrac_pcore : PCore dfrac := λ dq,
    match dq with
    | DfracOwn q => None
    | DfracDiscarded => Some DfracDiscarded
    | DfracBoth q => Some DfracDiscarded
    end.

  (** When elements are combined, ownership is added together and knowledge of
     discarded fractions is combined with the max operation. *)
  Instance dfrac_op : Op dfrac := λ dq dp,
    match dq, dp with
    | DfracOwn q, DfracOwn q' => DfracOwn (q + q')
    | DfracOwn q, DfracDiscarded => DfracBoth q
    | DfracOwn q, DfracBoth q' => DfracBoth (q + q')
    | DfracDiscarded, DfracOwn q' => DfracBoth q'
    | DfracDiscarded, DfracDiscarded => DfracDiscarded
    | DfracDiscarded, DfracBoth q' => DfracBoth q'
    | DfracBoth q, DfracOwn q' => DfracBoth (q + q')
    | DfracBoth q, DfracDiscarded => DfracBoth q
    | DfracBoth q, DfracBoth q' => DfracBoth (q + q')
    end.

  Lemma dfrac_op_own q p : DfracOwn p ⋅ DfracOwn q = DfracOwn (p + q).
  Proof. done. Qed.

  Lemma dfrac_op_discarded :
    DfracDiscarded ⋅ DfracDiscarded = DfracDiscarded.
  Proof. done. Qed.

  Lemma dfrac_own_included q p : DfracOwn q ≼ DfracOwn p ↔ (q < p)%Qp.
  Proof.
    rewrite Qp_lt_sum. split.
    - rewrite /included /op /dfrac_op. intros [[o| |?] [= ->]]. by exists o.
    - intros [o ->]. exists (DfracOwn o). by rewrite dfrac_op_own.
  Qed.

  (* [dfrac] does not have a unit so reflexivity is not for granted! *)
  Lemma dfrac_discarded_included :
    DfracDiscarded ≼ DfracDiscarded.
  Proof. exists DfracDiscarded. done. Qed.

  Definition dfrac_ra_mixin : RAMixin dfrac.
  Proof.
    split; try apply _.
    - intros [?| |?] ? dq <-; intros [= <-]; eexists _; done.
    - intros [?| |?] [?| |?] [?| |?];
        rewrite /op /dfrac_op 1?assoc_L 1?assoc_L; done.
    - intros [?| |?] [?| |?];
        rewrite /op /dfrac_op 1?(comm_L Qp_plus); done.
    - intros [?| |?] dq; rewrite /pcore /dfrac_pcore; intros [= <-];
        rewrite /op /dfrac_op; done.
    - intros [?| |?] ? [= <-]; done.
    - intros [?| |?] [?| |?] ? [[?| |?] [=]] [= <-]; eexists _; split; try done;
        apply dfrac_discarded_included.
    - intros [q| |q] [q'| |q']; rewrite /op /dfrac_op /valid /dfrac_valid //.
      + intros. trans (q + q')%Qp; [|done].
        apply Qclt_le_weak.
        apply Qp_lt_sum. eauto.
      + apply Qclt_le_weak.
      + intros. trans (q + q')%Qp; [|by apply Qclt_le_weak].
        apply Qclt_le_weak.
        apply Qp_lt_sum. eauto.
      + intros. trans (q + q')%Qp; [|by eauto].
        apply Qp_lt_sum. eauto.
      + intros. trans (q + q')%Qp; [|by eauto].
        apply Qp_lt_sum. eauto.
  Qed.
  Canonical Structure dfracR := discreteR SI dfrac dfrac_ra_mixin.

  Global Instance dfrac_cmra_discrete : CmraDiscrete dfracR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance dfrac_full_exclusive : Exclusive (DfracOwn 1).
  Proof.
    intros [q| |q];
      rewrite /op /cmra_op -cmra_discrete_valid_iff /valid /cmra_valid //=.
    - intros Hle.
      assert (Qp_car 1 < (1 + q)%Qp).
      { rewrite Qp_lt_sum. eexists. eauto. }
      eapply Qcle_ngt in Hle. eauto.
    - intros Hlt.
      assert (Qp_car 1 < (1 + q)%Qp).
      { rewrite Qp_lt_sum. eexists. eauto. }
      apply Qclt_le_weak in Hlt.
      eapply Qcle_ngt in Hlt. eauto.
  Qed.

  Lemma Qp_plus_id_free q p : q + p ≠ q.
  Proof.
    intro Heq.
      assert (Qp_car q < (q + p)%Qp).
      { rewrite Qp_lt_sum. eexists. eauto. }
      assert (q + p <= q)%Qp as Hle.
      { rewrite Heq. reflexivity. }
      eapply Qcle_ngt in Hle. eauto.
  Qed.

  Lemma Qp_to_Qc_inj_iff p q : Qp_car p = Qp_car q ↔ p = q.
  Proof.
    split; [|by intros ->].
    destruct p, q; intros; simplify_eq/=; f_equal; apply (proof_irrel _).
  Qed.
  Instance Qp_add_inj_r p : Inj (=) (=) (Qp_plus p).
  Proof.
    destruct p as [p ?].
    intros [q1 ?] [q2 ?]. rewrite <-!Qp_to_Qc_inj_iff; simpl. apply (inj (Qcplus p)).
  Qed.

  Global Instance dfrac_cancelable q : Cancelable (DfracOwn q).
  Proof.
    apply: discrete_cancelable.
    intros [q1| |q1][q2| |q2] _ [=]; try (simplify_eq/=; done).
    - f_equal. eapply (Qp_add_inj_r q); eauto.
      apply Qp_to_Qc_inj_iff => //=.
      rewrite /Qcplus/Q2Qc.
      apply Qc_decomp => //=.
    - destruct (Qp_plus_id_free q q2).
      transitivity (Qp_plus q q2); eauto.
      symmetry. apply Qp_to_Qc_inj_iff. apply H0.
    - destruct (Qp_plus_id_free q q1).
      transitivity (Qp_plus q q1); eauto.
      apply Qp_to_Qc_inj_iff. apply H0.
    - f_equal. eapply (Qp_add_inj_r q); eauto.
      apply Qp_to_Qc_inj_iff => //=.
      rewrite /Qcplus/Q2Qc.
      apply Qc_decomp => //=.
  Qed.
  Global Instance frac_id_free q : IdFree (DfracOwn q).
  Proof.
    intros [q'| |q'] _ [=].
    apply (Qp_plus_id_free q q').
    transitivity (Qp_plus q q'); eauto.
    apply Qp_to_Qc_inj_iff. apply H0.
  Qed.
  Global Instance dfrac_discarded_core_id : CoreId DfracDiscarded.
  Proof. by constructor. Qed.

  Lemma dfrac_valid_own p : ✓ DfracOwn p ↔ (p ≤ 1)%Qc.
  Proof. done. Qed.

  Lemma dfrac_valid_discarded p : ✓ DfracDiscarded.
  Proof. done. Qed.

  Lemma dfrac_valid_own_discarded q :
    ✓ (DfracOwn q ⋅ DfracDiscarded) ↔ (q < 1)%Qc.
  Proof. done. Qed.

  (** Discarding a fraction is a frame preserving update. *)
  Lemma dfrac_discard_update q : DfracOwn q ~~> DfracDiscarded.
  Proof.
    intros n [[q'| |q']|];
      rewrite /op /cmra_op -!cmra_discrete_valid_iff /valid /cmra_valid //=.
    - intros.
      apply Qclt_le_trans with (q + q')%Qp; [| done].
      apply Qp_lt_sum. eexists. rewrite (comm _ q q'). eauto.
    - intros.
      apply Qclt_trans with (q + q')%Qp; [| done].
      apply Qp_lt_sum. eexists. rewrite (comm _ q q'). eauto.
  Qed.

End dfrac.
