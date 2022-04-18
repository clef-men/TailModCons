From iris.base_logic Require Export iprop satisfiable.
From iris.bi Require Export fixpoint.
From iris.proofmode Require Import tactics.


Section simulations.

  Context {SI} `{LargeIndex SI} {Σ: gFunctors SI}.


  (* We assume a source and a target language *)
  Variable (S T: Type) (src_step: S → S → Prop) (tgt_step: T → T → Prop).
  Variable (V: Type) (val_to_src: V → S) (val_to_tgt: V → T).
  Variable (val_irred: ∀ v, ¬ ∃ t', tgt_step (val_to_tgt v) t') (val_inj: Inj eq eq val_to_tgt).


  (* refinements *)
  Definition rpr (t: T) (s: S) :=
    (∀ v, rtc tgt_step t (val_to_tgt v) → rtc src_step s (val_to_src v)).

  Definition tpr (t: T) (s: S) :=
    (∀ v, rtc tgt_step t (val_to_tgt v) → rtc src_step s (val_to_src v)) ∧
    (ex_loop tgt_step t → ex_loop src_step s).

  Definition sim_pre (sim: (T -d> S -d> iProp Σ)) : T -d> S -d> iProp Σ :=
    (λ t s,
      (∃ v, ⌜val_to_src v = s⌝ ∧ ⌜val_to_tgt v = t⌝) ∨
      (∃ t', ⌜tgt_step t t'⌝) ∧
      (∀ t', ⌜tgt_step t t'⌝ → ∃ s', ⌜src_step s s'⌝ ∧ ▷ sim t' s')
    )%I.

  Instance sim_pre_contr: Contractive sim_pre.
  Proof.
    intros a sim sim' Heq. unfold sim_pre.
    intros t s. do 8 f_equiv. apply bi.later_contractive.
    intros ??. by apply Heq.
  Qed.


  Definition sim := fixpoint sim_pre.

  Lemma sim_unfold':
    sim ≡ sim_pre sim.
  Proof. by rewrite {1}/sim fixpoint_unfold. Qed.

  Lemma sim_unfold t s:
    (sim t s ⊣⊢ ((∃ v, ⌜val_to_src v = s⌝ ∧ ⌜val_to_tgt v = t⌝) ∨
    (∃ t', ⌜tgt_step t t'⌝) ∧
    (∀ t', ⌜tgt_step t t'⌝ → ∃ s', ⌜src_step s s'⌝ ∧ ▷ sim t' s')))%I.
  Proof. apply sim_unfold'. Qed.

  Instance sim_plain t s: Plain (sim t s).
  Proof.
    unfold Plain. iRevert (t s). iLöb as "IH".
    iIntros (t s); rewrite sim_unfold.
    iIntros "[H1|[H1 H2]]".
    - iLeft. iApply (plain with "H1").
    - iRight. iSplit; first iApply (plain with "H1").
      iIntros (t' Hstep). iDestruct ("H2" $! t' Hstep) as (s' Hstep') "Hsim".
      iExists s'; iSplit; first (iApply plain; by iPureIntro).
      iApply later_plainly_1. iNext. by iApply "IH".
  Qed.

  Lemma sim_valid_satisfiable t s: satisfiable (sim t s) ↔ ⊢ sim t s.
  Proof.
    split.
    - intros ? % satisfiable_elim; eauto. apply _.
    - by intros ? % satisfiable_intro.
  Qed.


  Lemma satisfiable_pure φ: satisfiable (⌜φ⌝: iProp Σ)%I → φ.
  Proof.
    intros Hsat. apply satisfiable_elim in Hsat; last apply _.
    by apply uPred.pure_soundness in Hsat.
  Qed.

  (* result preserving *)
  Lemma sim_execute_tgt_step t s t':
    tgt_step t t' → satisfiable (sim t s) → ∃ s', src_step s s' ∧ satisfiable (sim t' s').
  Proof.
    intros Hstep Hsat.
    eapply satisfiable_mono with (Q := (∃ s', ⌜src_step s s'⌝ ∧ ▷ sim t' s')%I) in Hsat.
    - eapply satisfiable_exists in Hsat as [s' Hsat].
      exists s'. split.
      + eapply satisfiable_pure, satisfiable_mono; eauto. iIntros "[$ _]".
      + eapply satisfiable_later, satisfiable_mono; eauto. iIntros "[_ $]".
    - iIntros "Hsim". rewrite sim_unfold. iDestruct "Hsim" as "[Hsim|[_ Hsim]]".
     + iDestruct "Hsim" as (v) "[<- <-]". exfalso. naive_solver.
     + iApply ("Hsim" $! t' Hstep).
   Qed.

  Lemma sim_execute_tgt t s t':
    rtc tgt_step t t' → satisfiable (sim t s) 
    → ∃ s', rtc src_step s s' ∧ satisfiable (sim t' s').
  Proof.
    induction 1 in s.
    - intros Hsim. exists s. by split.
    - intros Hsim. eapply sim_execute_tgt_step in Hsim; eauto.
      destruct Hsim as [s' [Hsrc Hsat]].
      destruct (IHrtc _ Hsat) as [s'' [Hsrc' Hsat']].
      exists s''. split; auto. by eapply rtc_l.
  Qed.

  (* Lemma 2.1 *)
  Lemma sim_is_rpr t s: (⊢ sim t s) → rpr t s.
  Proof.
    intros Hsim % sim_valid_satisfiable v Hsteps.
    eapply sim_execute_tgt in Hsteps as [s' [Hsteps' Hsat]]; eauto.
    enough (s' = (val_to_src v)) as -> by eauto.
    eapply satisfiable_pure, satisfiable_mono; eauto.
    rewrite sim_unfold. iIntros "[H|[H _]]".
    - iDestruct "H" as (v')  "[<- H]". by iDestruct "H" as %->%val_inj.
    - iDestruct "H" as (t') "%". exfalso. naive_solver.
  Qed.


  (* Lemma 2.2 *)
  Lemma sim_is_tpr t s: (⊢ sim t s) → tpr t s.
  Proof.
    intros Hsim. split.
    - by apply sim_is_rpr.
    - apply sim_valid_satisfiable in Hsim. revert t s Hsim.
      cofix IH. intros t s Hsat. inversion 1 as [t'' t' Hstep Hloop]; subst t''.
      destruct (sim_execute_tgt_step _ _ _ Hstep Hsat) as [s' [Hstep' Hsat']].
      econstructor; eauto.
  Qed.
End simulations.

