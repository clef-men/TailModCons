From iris.base_logic Require Export iprop satisfiable.
From iris.bi Require Export fixpoint.
From iris.proofmode Require Import tactics.


Section simulations.

  Context {SI} `{LargeIndex SI} {Σ: gFunctors SI}.


  (* We assume a source and a target language *)
  Variable (S T: Type) (src_step: S → S → Prop) (tgt_step: T → T → Prop).
  Variable (V: Type) (val_to_tgt: V → T) (φ: V → S → Prop).
  Variable (val_irred: ∀ v, ¬ ∃ t', tgt_step (val_to_tgt v) t') (val_inj: Inj eq eq val_to_tgt).


  (* refinements *)
  Definition gtpr (t: T) (s: S) :=
    (∀ v, rtc tgt_step t (val_to_tgt v) → ∃ s', rtc src_step s s' ∧ φ v s') ∧
    (ex_loop tgt_step t → ex_loop src_step s).


  Notation "S *d T" := (prodO (leibnizO SI T) (leibnizO SI S)) (at level 60).
  Definition gsim_pre (sim: ((S *d T) → iProp Σ)) : (S *d T) → iProp Σ :=
    (λ '(t, s),
      (∃ v, ⌜φ v s⌝ ∧ ⌜val_to_tgt v = t⌝) ∨
      (∃ t', ⌜tgt_step t t'⌝) ∧
      (∀ t', ⌜tgt_step t t'⌝ → sim (t', s) ∨ ∃ s', ⌜src_step s s'⌝ ∧ ▷ sim (t', s'))
    )%I.

  Instance gsim_pre_mono: BiMonoPred gsim_pre.
  Proof.
    split.
    - intros Φ Ψ. iIntros "#H" ([t s]).
      rewrite /gsim_pre.
      iIntros "[Hsim|Hsim]"; eauto.
      iRight. iDestruct "Hsim" as "[Hsteps Hsim]".
      iSplit; eauto.
      iIntros (t' Htgt). iDestruct ("Hsim" $! t' Htgt) as "[Hsim|Hsim]".
      + iLeft. by iApply "H".
      + iRight. iDestruct "Hsim" as (s' Hsrc) "Hsim".
        iExists s'. iSplit; eauto. iNext. by iApply "H".
    - intros Φ Hdist α [t s] [t' s'] [Heq1 Heq2]; simpl in *.
      repeat f_equiv; eauto.
  Qed.

  Definition gsim := bi_least_fixpoint gsim_pre.

  Lemma sim_unfold t s:
    (gsim (t, s) ⊣⊢ (∃ v, ⌜φ v s⌝ ∧ ⌜val_to_tgt v = t⌝) ∨
    (∃ t', ⌜tgt_step t t'⌝) ∧
    (∀ t', ⌜tgt_step t t'⌝ → gsim (t', s) ∨ ∃ s', ⌜src_step s s'⌝ ∧ ▷ gsim (t', s')))%I.
  Proof.
    fold (gsim_pre gsim (t, s)). iSplit.
    - iApply least_fixpoint_unfold_1.
    - iApply least_fixpoint_unfold_2.
  Qed.


  Lemma satisfiable_pure ψ: satisfiable (⌜ψ⌝: iProp Σ)%I → ψ.
  Proof.
    intros Hsat. apply satisfiable_elim in Hsat; last apply _.
    by apply uPred.pure_soundness in Hsat.
  Qed.

  (* result preserving *)
  Lemma gsim_execute_tgt_step t s t':
    tgt_step t t' → satisfiable (gsim (t, s)) → ∃ s', rtc src_step s s' ∧ satisfiable (gsim (t', s')).
  Proof.
    intros Hstep Hsat.
    eapply satisfiable_mono with (Q := (∃ s', ⌜rtc src_step s s'⌝ ∧ ▷ gsim (t', s'))%I) in Hsat.
    - eapply satisfiable_exists in Hsat as [s' Hsat].
      exists s'. split.
      + eapply satisfiable_pure, satisfiable_mono; eauto. iIntros "[$ _]".
      + eapply satisfiable_later, satisfiable_mono; eauto. iIntros "[_ $]".
    - iIntros "Hsim". rewrite sim_unfold. iDestruct "Hsim" as "[Hsim|[_ Hsim]]".
     + iDestruct "Hsim" as (v) "[_ <-]". exfalso. naive_solver.
     + iDestruct ("Hsim" $! t' Hstep) as "[Hsim|Hsim]".
       * iExists s. iSplit; first by iPureIntro. by iNext.
       * iDestruct "Hsim" as (s' Hstep') "Hsim". iExists s'. iSplit; eauto.
          iPureIntro. by eapply rtc_l.
   Qed.

  Lemma sim_execute_tgt t s t':
    rtc tgt_step t t' → satisfiable (gsim (t, s)) → ∃ s', rtc src_step s s' ∧ satisfiable (gsim (t', s')).
  Proof.
    induction 1 in s.
    - intros Hsim. exists s. by split.
    - intros Hsim. eapply gsim_execute_tgt_step in Hsim; last eauto.
      destruct Hsim as [s' [Hsrc Hsat]].
      destruct (IHrtc _ Hsat) as [s'' [Hsrc' Hsat']].
      exists s''. split; auto. by transitivity s'.
  Qed.


  (* termination preserving *)
  Lemma sim_execute_tgt_step t s:
    ex_loop tgt_step t → satisfiable (gsim (t, s)) →  ∃ t' s', src_step s s' ∧ ex_loop tgt_step t' ∧ satisfiable (gsim (t', s')).
  Proof.
    intros Hsteps Hsat.
    eapply satisfiable_mono with (Q := (∃ t' s', ⌜src_step s s'⌝ ∧ ⌜ex_loop tgt_step t'⌝ ∧ ▷ gsim (t', s'))%I) in Hsat; last first.
    iPoseProof (@least_fixpoint_strong_ind _ _ _ gsim_pre _ (λ '(t, s), ⌜ex_loop tgt_step t⌝ → ∃ (t' : T) (s' : S), ⌜src_step s s'⌝ ∧ ⌜ex_loop tgt_step t'⌝ ∧ ▷ gsim (t', s'))%I) as "Hind".
    { intros ? [t'' s''] [t' s'] [Heq1 Heq2]; repeat f_equiv; eauto. }
    - iIntros "Hsim". iRevert (Hsteps). iRevert "Hsim". iSpecialize ("Hind" with "[]"); last iApply ("Hind" $! (t, s)).
      clear Hsat t s. iModIntro. iIntros ([t s]). iIntros "Hsim" (Hloop).
      rewrite /gsim_pre. iDestruct "Hsim" as "[Hsim|Hsim]".
      + iDestruct "Hsim" as (v) "[_ %]".
        destruct Hloop as [t t']; subst t. naive_solver.
      + iDestruct "Hsim" as "[_ Hsim]".
        inversion Hloop as [t'' t' Hstep Hloop']; subst t''.
        iDestruct ("Hsim" $! t' Hstep) as "[Hsim|Hsim]".
        * iDestruct "Hsim" as "[Hsim _]". by iSpecialize ("Hsim" $! Hloop').
        * iDestruct "Hsim" as (s' Hstep') "Hsim".
          iExists t', s'. repeat iSplit; eauto.
          iNext. iDestruct "Hsim" as "[_ $]".
    - eapply satisfiable_exists in Hsat as [t' Hsat].
      eapply satisfiable_exists in Hsat as [s' Hsat].
      exists t', s'. repeat split.
      + eapply satisfiable_pure, satisfiable_mono; eauto. iIntros "($ & _ & _)".
      + eapply satisfiable_pure, satisfiable_mono; eauto. iIntros "(_ & $ & _)".
      + eapply satisfiable_later, satisfiable_mono; eauto. iIntros "(_ & _ & $)".
  Qed.

  Lemma sim_divergence t s:
    ex_loop tgt_step t → satisfiable (gsim (t, s)) → ex_loop src_step s.
  Proof.
    revert t s. cofix IH. intros t s Hloop Hsat.
    edestruct sim_execute_tgt_step as (t' & s' & Hsrc & Hloop' & Hsim); [eauto..|].
    econstructor; eauto.
  Qed.

  Lemma sim_is_tpr t s: (⊢ gsim (t, s)) → gtpr t s.
  Proof.
    intros Hsim. split.
    - apply satisfiable_intro in Hsim. intros v Hsteps.
      eapply sim_execute_tgt in Hsteps as [s' [Hsteps' Hsat]]; eauto.
      enough (φ v s') by eauto.
      eapply satisfiable_pure, satisfiable_mono; eauto.
      rewrite sim_unfold. iIntros "[H|[H _]]".
      + iDestruct "H" as (v')  "[% H]". by iDestruct "H" as %->%val_inj.
      + iDestruct "H" as (t') "%". exfalso. naive_solver.
    - intros Hloop. eapply sim_divergence; eauto.
      apply satisfiable_intro, Hsim.
  Qed.

End simulations.

