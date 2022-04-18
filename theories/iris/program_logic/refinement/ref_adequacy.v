From iris.program_logic Require Export language.
From iris.bi Require Export weakestpre fixpoint.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import auth list.
From iris.base_logic Require Export satisfiable gen_heap.
From iris.base_logic.lib Require Export fancy_updates logical_step.
From iris.program_logic.refinement Require Export ref_source ref_weakestpre.
Set Default Proof Using "Type".



Lemma sn_not_ex_loop {A} `{Classical} (R : relation A) x :
  ¬ex_loop R x → sn R x.
Proof.
  intros Hex. destruct (excluded_middle (sn R x)) as [|Hsn]; [done|].
  destruct Hex. revert x Hsn. cofix IH; intros x Hsn.
  destruct (excluded_middle (∃ y, R x y ∧ ¬sn R y)) as [(y&?&?)|Hnot].
  - exists y; auto.
  - destruct Hsn. constructor. intros y Hxy.
    destruct (excluded_middle (sn R y)); naive_solver.
Qed.


Section refinements.
Context {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types a : A.
Implicit Types b : bool.

(** We first prove that termination is preserverd: if the source is strongly normalising, then also the target is strongly normalising *)

(* With rwp_tp, we lift the essential parts for termination preserving refinement of rwp to thread pools. *)
Definition rwp_tp_pre (rwp_tp: list (expr Λ) → iProp Σ) (t1: list (expr Λ)) : iProp Σ :=
  (∀ t2 σ σ' κ a n,
    ⌜step (t1, σ) κ (t2, σ')⌝
      -∗ source_interp a ∗ ref_state_interp σ n
          ={⊤, ∅}=∗ ∃ b,
            ▷?b |={∅, ⊤}=> ∃ m,
              ref_state_interp σ' m
              ∗ if b then ∃ a', ⌜a ↪⁺ a'⌝ ∗ rwp_tp t2 ∗ source_interp a'
                     else rwp_tp t2 ∗ source_interp a)%I.

(* Not every recursive occurrence is guarded by a later. We obtain a fixpoint of the defintion using a least fixpoint operator.*)
Definition rwp_tp (t : list (expr Λ)) : iProp Σ := bi_least_fixpoint rwp_tp_pre t.

Lemma rwp_tp_pre_mono (rwp_tp1 rwp_tp2 : list (expr Λ) → iProp Σ) :
  ⊢ (<pers> (∀ t, rwp_tp1 t -∗ rwp_tp2 t) →
    ∀ t, rwp_tp_pre rwp_tp1 t -∗ rwp_tp_pre rwp_tp2 t)%I.
Proof.
  iIntros "#H"; iIntros (t) "Hwp". rewrite /rwp_tp_pre.
  iIntros (t2 σ1 σ2 κ a n1) "Hstep Hσ".
  iMod ("Hwp" with "[$] [$]") as (b) "Hwp".
  iModIntro. iExists b. iNext. iMod "Hwp". iModIntro.
  iDestruct "Hwp" as (m) "(Hσ & Hwp)". iExists m. iFrame "Hσ".
  destruct b; eauto.
  - iDestruct "Hwp" as (a') "(Hstep & Hgn & Hsrc)".
    iExists a'. iFrame. by iApply "H".
  - iDestruct "Hwp" as "(Hgn & $)". by iApply "H".
Qed.

Local Instance rwp_tp_pre_mono' : BiMonoPred rwp_tp_pre.
Proof.
  constructor; first apply rwp_tp_pre_mono.
  intros wp Hwp n t1 t2 ?%(discrete_iff _ _)%leibniz_equiv; solve_proper.
Qed.


Lemma rwp_tp_unfold t : rwp_tp t ⊣⊢ rwp_tp_pre rwp_tp t.
Proof. by rewrite /rwp_tp least_fixpoint_unfold. Qed.

Lemma rwp_tp_ind Ψ :
  ⊢ ((□ ∀ t, rwp_tp_pre (λ t, Ψ t ∧ rwp_tp t) t -∗ Ψ t) → ∀ t, rwp_tp t -∗ Ψ t)%I.
Proof.
  iIntros "#IH" (t) "H".
  assert (NonExpansive Ψ).
  { by intros n ?? ->%(discrete_iff _ _)%leibniz_equiv. }
  iApply (least_fixpoint_strong_ind _ Ψ with "[] H").
  iIntros "!#" (t') "H". by iApply "IH".
Qed.

Instance rwp_tp_Permutation : Proper ((≡ₚ) ==> (⊢)) rwp_tp.
Proof.
  iIntros (t1 t1' Ht) "Ht1". iRevert (t1' Ht); iRevert (t1) "Ht1".
  iApply rwp_tp_ind; iIntros "!#" (t1) "IH"; iIntros (t1' Ht).
  rewrite rwp_tp_unfold /rwp_tp_pre. iIntros (t2 σ1 σ2 κ a n Hstep) "Hσ".
  destruct (step_Permutation t1' t1 t2 κ σ1 σ2) as (t2'&?&?); try done.
  iMod ("IH" with "[% //] Hσ") as (b) "IH". iModIntro. iExists b. iNext.
  iMod "IH" as (n2) "(Hσ & IH)".
  iModIntro. iExists n2. iFrame "Hσ".
  destruct b.
  - iDestruct "IH" as (a') "(Hstep & [IH _] & Hsrc)".
    iExists a'. iFrame. by iApply "IH".
  - iDestruct "IH" as "([IH _] & $)".
    by iApply "IH".
Qed.

Lemma rwp_tp_app t1 t2: rwp_tp t1 -∗ rwp_tp t2 -∗ rwp_tp (t1 ++ t2).
Proof.
  iIntros "H1". iRevert (t2). iRevert (t1) "H1".
  iApply rwp_tp_ind; iIntros "!#" (t1) "IH1". iIntros (t2) "H2".
  iRevert (t1) "IH1"; iRevert (t2) "H2".
  iApply rwp_tp_ind; iIntros "!#" (t2) "IH2". iIntros (t1) "IH1".
  rewrite rwp_tp_unfold {4}/rwp_tp_pre. iIntros (t1'' σ1 σ2 κ a n Hstep) "Hσ1".
  destruct Hstep as [e1 σ1' e2 σ2' efs' t1' t2' [=Ht ?] ? Hstep]; simplify_eq/=.
  apply app_eq_inv in Ht as [(t&?&?)|(t&?&?)]; subst.
  - destruct t as [|e1' ?]; simplify_eq/=.
    + iMod ("IH2" with "[%] Hσ1") as (b) "IH2".
      { by eapply step_atomic with (t1:=[]). }
      iModIntro. iExists b. iNext. iMod "IH2" as (n2) "[Hσ IH2]". iModIntro. iExists n2. iFrame "Hσ".
      rewrite -{2}(left_id_L [] (++) (e2 :: _)). destruct b.
      * iDestruct "IH2" as (a' Hsrc) "[[IH2 _] Hsrc]". iExists a'. iFrame "Hsrc".
        iSplit; first by iPureIntro. iApply "IH2".
        by rewrite (right_id_L [] (++)).
      * iDestruct "IH2" as "[[IH2 _] Hsrc]". iFrame "Hsrc". iApply "IH2".
        by rewrite (right_id_L [] (++)).
    +  iMod ("IH1" with "[%] Hσ1") as (b) "IH1".
      { by econstructor. }
      iModIntro. iExists b. iApply (bi.laterN_wand with "[IH2] IH1"). iNext.
      iIntros "IH1". iMod "IH1" as (n2) "(Hσ & IH1)". iModIntro.
      iExists n2. iFrame "Hσ".
      iAssert (rwp_tp t2) with "[IH2]" as "Ht2".
        { rewrite rwp_tp_unfold. iApply (rwp_tp_pre_mono with "[] IH2").
          iIntros "!# * [_ ?] //". }
      destruct b.
      * iDestruct "IH1" as (a' Hsrc) "[[IH1 _] Hsrc]".
        iExists a'. iFrame "Hsrc". iSplit; first by iPureIntro.
        rewrite -assoc_L (comm _ t2) !cons_middle !assoc_L. by iApply "IH1".
      * iDestruct "IH1" as  "[[IH1 _] Hsrc]".
        iFrame "Hsrc". rewrite -assoc_L (comm _ t2) !cons_middle !assoc_L. by iApply "IH1".
  - iMod ("IH2" with "[%] Hσ1") as (b) "IH2"; first by econstructor.
    iModIntro. iExists b. iApply (bi.laterN_wand with "[IH1] IH2"). iNext.
    iIntros "IH2". iMod "IH2" as (n2) "[Hσ IH2]". iModIntro. iExists n2.
    iFrame "Hσ". rewrite -assoc_L. destruct b.
    + iDestruct "IH2" as (a' Hsrc) "[[IH2 _] Hsrc]". iExists a'. iFrame "Hsrc".
      iSplit; first by iPureIntro. by iApply "IH2".
    + iDestruct "IH2" as "[[IH2 _] Hsrc]". iFrame "Hsrc". by iApply "IH2".
Qed.

(* rwp_tp subsumes rwp *)
Lemma rwp_rwp_tp s Φ e : RWP e @ s; ⊤ ⟨⟨ Φ ⟩⟩ -∗ rwp_tp [e].
Proof.
  iIntros "He". remember (⊤ : coPset) as E eqn:HE.
  iRevert (HE). iRevert (e E Φ) "He". iApply rwp_ind.
  iIntros "!#" (e E Φ). iIntros "IH" (->).
  rewrite /rwp_pre /rwp_step rwp_tp_unfold /rwp_tp_pre.
  iIntros (t' σ σ' κ a n Hstep).
  destruct Hstep as [e1 σ1 e2 σ2 efs [|? t1] t2 ?? Hstep];
    simplify_eq/=; try discriminate_list.
  destruct (to_val e1) as [v|] eqn:He1.
  { apply val_stuck in Hstep; naive_solver. }
  iIntros "[Ha Hσ]".
  iMod ("IH" with "[$Ha $Hσ]") as (b) "IH". iModIntro.
  iExists b. iApply (bi.laterN_wand with "[] IH"). iNext.
  iIntros "H". iMod "H" as "[_ IH]".
  iMod ("IH" with "[% //]") as "(Hsrc & Hσ & IH & IHs)".
  iModIntro. iExists (length efs + n). iFrame "Hσ".
  iAssert (rwp_tp (e2 :: efs))%I with "[IH IHs]" as "Hrwp_tp".
  { iApply (rwp_tp_app [_] with "(IH [//])").
    clear. iInduction efs as [|e efs] "IH"; simpl.
    { rewrite rwp_tp_unfold /rwp_tp_pre. iIntros (t2 σ1 κ σ2 a n1 Hstep).
      destruct Hstep; simplify_eq/=; discriminate_list. }
    iDestruct "IHs" as "[IH' IHfork]".
    iApply (rwp_tp_app [_] with "(IH' [//])"). by iApply "IH".
  }
  destruct b; iFrame.
Qed.


(* We unfold the refinement to a sequence of later operations interleaved with fancy updates. *)
Definition guarded_pre (grd: (A -d> iProp Σ -d> iProp Σ)) : A -d> iProp Σ -d> iProp Σ :=
  λ (a: A) (P: iProp Σ),
    (|={⊤,∅}=> (|={∅,⊤}=> P) ∨ (▷ |={∅,⊤}=> ∃ a', ⌜a ↪⁺ a'⌝ ∗ grd a' P))%I.

Global Instance guarded_pre_contractive: Contractive (guarded_pre).
Proof.
  intros α ev1 ev2 Heq. rewrite /guarded_pre; simpl.
  intros e_S P. do 2 f_equiv. f_contractive. intros ??.
  do 2 f_equiv. intros e_s'. f_equiv. by apply Heq.
Qed.

Definition guarded := fixpoint guarded_pre.

Lemma guarded_unfold a P: guarded a P ≡ (|={⊤,∅}=> (|={∅,⊤}=> P) ∨ (▷ |={∅,⊤}=> ∃ a', ⌜a ↪⁺a'⌝ ∗ guarded a' P))%I.
Proof. unfold guarded. apply (@fixpoint_unfold SI (A -d> iProp Σ -d> iProp Σ) _ guarded_pre _). Qed.

(* Guarded propositions eventually become true, if the source does not allow infinite loops. *)
Lemma guarded_satisfiable `{LargeIndex SI} a P:
  sn source_rel a
  → satisfiable_at ⊤ (guarded a P)
  → satisfiable_at ⊤ P.
Proof.
  intros Hsn % sn_tc. induction Hsn as [a Ha IH]. rewrite guarded_unfold.
  intros Hsat. apply satisfiable_at_fupd in Hsat.
  apply satisfiable_at_or in Hsat as [Hsat|Hsat].
  { by apply satisfiable_at_fupd in Hsat. }
  apply satisfiable_at_later in Hsat.
  apply satisfiable_at_fupd in Hsat.
  apply satisfiable_at_exists in Hsat as [b Hsat]; last apply _.
  apply satisfiable_at_sep in Hsat as [Hsat1 % satisfiable_at_pure Hsat2].
  by eapply IH.
Qed.



Lemma rwp_tp_guarded_false t:
  rwp_tp t ⊢ ∀ σ a n, ⌜ex_loop erased_step (t, σ)⌝
                      -∗ source_interp a
                      -∗ ref_state_interp σ n
                      -∗ guarded a False.
Proof.
  iApply (rwp_tp_ind (λ t, ∀ σ a n, ⌜ex_loop erased_step (t, σ)⌝ -∗ source_interp a -∗ ref_state_interp σ n -∗ guarded a False)%I with "[]"). clear t.
  iModIntro. iIntros (t). rewrite /rwp_tp_pre. iIntros "Hrwp_tp". iIntros (σ a n Hloop) "Hsrc Hσ".
  inversion Hloop as [x [t' σ'] [κ Hstep] Hloop']; subst x; clear Hloop.
  iSpecialize ("Hrwp_tp"  $! t' σ σ' κ a n with "[]"); eauto.
  iSpecialize ("Hrwp_tp" with "[$Hsrc $Hσ]"). iApply guarded_unfold.
  iMod "Hrwp_tp" as (b) "Hrwp_tp". destruct b.
  + iModIntro. iRight. iNext. iMod "Hrwp_tp" as (m) "(Hσ & Hev)".
    iModIntro. iDestruct "Hev" as (a' Hsrc) "[[Hev _] Hsrc]".
    iExists a'. iSplit; first by iPureIntro.
    iApply ("Hev" with "[] Hsrc Hσ"); eauto.
  + iMod "Hrwp_tp" as (m) "(Hσ & [Hev _] & Ha)".
    iSpecialize ("Hev" with "[//] Ha Hσ").
    by rewrite guarded_unfold.
Qed.

Lemma rwp_adequacy `{LargeIndex SI} Φ a e σ n s:
  sn source_rel a
  → ex_loop erased_step ([e], σ)
  → satisfiable_at ⊤ (source_interp a ∗ ref_state_interp σ n ∗ RWP e @ s; ⊤ ⟨⟨ Φ ⟩⟩)%I
  → False.
Proof.
  intros Hsn Hloop Hsat. eapply (satisfiable_at_mono _ _ (guarded a False)%I) in Hsat.
  - apply guarded_satisfiable in Hsat; eauto. by eapply satisfiable_at_pure.
  - iIntros "(Hsrc & Hσ & Hwp)".
    iApply (rwp_tp_guarded_false with "[Hwp] [//] Hsrc Hσ").
    by iApply rwp_rwp_tp.
Qed.

Lemma rwp_sn_preservation `{Classical} `{LargeIndex SI} Φ a e σ n s:
  sn source_rel a
  → satisfiable_at ⊤ (source_interp a ∗ ref_state_interp σ n ∗ RWP e @ s; ⊤ ⟨⟨ Φ ⟩⟩)%I
  → sn erased_step ([e], σ).
Proof.
    intros Hsn Hsat. eapply sn_not_ex_loop. intros Hloop.
    eapply rwp_adequacy; eauto.
Qed.


(** the following lemmas are completely independent from the preceding lemmas*)
(** they provide a general result which can be used to prove that the result of a computation refines a source computation
  -- however, the concrete shape of this strongly depends on the chosen source and state interpretations *)

(* we are ignoring any threads that are forked off *)
Lemma rwp_prim_step `{LargeIndex SI} F s κ a n e e' σ σ' Φ efs:
  prim_step e σ κ e' σ' efs →
  satisfiable_at ⊤ (source_interp a ∗ ref_state_interp σ n ∗ RWP e @ s; ⊤ ⟨⟨ Φ ⟩⟩ ∗ F)%I
  → ∃ a' m, rtc source_rel a a'
            ∧ satisfiable_at ⊤ (source_interp a' ∗ ref_state_interp σ' m ∗ RWP e' @ s; ⊤ ⟨⟨ Φ ⟩⟩
                                  ∗ ([∗ list] e ∈ efs, RWP e @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩) ∗ F)%I.
Proof.
  intros Hstep Hsat.
  eapply satisfiable_at_mono with (Q := (|={⊤, ∅}=> ▷ |={∅, ⊤}=> ∃ a' m, ⌜rtc source_rel a a'⌝ ∗ source_interp a' ∗ ref_state_interp σ' m ∗ RWP e' @ s; ⊤ ⟨⟨ Φ ⟩⟩ ∗ ([∗ list] e ∈ efs, RWP e @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩) ∗ F)%I)  in Hsat; last first.
  - rewrite rwp_unfold /rwp_pre /rwp_step.
    iIntros "(Hsrc & SI & Hwp & F)".
    erewrite val_stuck; eauto.
    iMod ("Hwp" $! σ n a with "[$Hsrc $SI]") as ([]) "Hwp"; simpl; iModIntro; iNext; iMod "Hwp" as "[_ Hwp]".
    + iMod ("Hwp" $! _ _ _ _ Hstep) as "(Hsrc & SI & RWP & Hfork)".
      iDestruct "Hsrc" as (a' Hsteps) "Hsrc".
      iModIntro. iExists a', _. iFrame. iPureIntro.
      by apply tc_rtc.
    + iMod ("Hwp" $! _ _ _ _ Hstep) as "(Hsrc & SI & RWP & Hfork)".
      iModIntro. iExists a, _. iFrame. by iPureIntro.
  - apply satisfiable_at_fupd in Hsat.
    apply satisfiable_at_later in Hsat.
    apply satisfiable_at_fupd in Hsat.
    apply satisfiable_at_exists in Hsat as [a' Hsat]; auto.
    apply satisfiable_at_exists in Hsat as [m Hsat]; auto.
    apply satisfiable_at_sep in Hsat as [Hsteps Hsat].
    apply satisfiable_at_pure in Hsteps.
    exists a', m. eauto.
Qed.


Definition thread_wps s Φ (es: list (expr Λ)) : iProp Σ :=
  ([∗ list] i ↦ e ∈ es, if i is 0 then RWP e @ s; ⊤ ⟨⟨ Φ ⟩⟩ else RWP e @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩)%I.

(* thread lifting *)
Lemma rwp_erased_step `{LargeIndex SI} s Φ a n ts ts' σ σ':
  erased_step (ts, σ) (ts', σ')
  → satisfiable_at ⊤ (source_interp a ∗ ref_state_interp σ n ∗ thread_wps s Φ ts)%I
  → ∃ a' m, rtc source_rel a a'
            ∧ satisfiable_at ⊤ (source_interp a' ∗ ref_state_interp σ' m ∗ thread_wps s Φ ts')%I.
Proof.
  intros [κ Hstep] Hsat. inversion Hstep as [e1 σ1 e2 σ2 efs t1 t2 Heq1 Heq2 Hstep'].
  injection Heq1 as -> ->. injection Heq2 as -> ->. revert Hsat.
  destruct t1; simpl in *; rewrite /thread_wps //=.
  -  intros Hsat. eapply rwp_prim_step in Hsat; eauto. rewrite /thread_wps //=.
    destruct Hsat as (a' & m & Hrtc & Hsat).
    exists a', m. split; auto.
    by rewrite big_sepL_app [(([∗ list] y ∈ t2, _) ∗ _)%I]bi.sep_comm.
  - rewrite big_sepL_app //=.
    intros Hsat; eapply satisfiable_at_mono with (Q := (_ ∗ _ ∗ _ ∗ _)%I)in Hsat; last first.
    { iIntros "(Hsrc & SI & Hrwp & Ht1 & He & Ht2)".
      iSplitL "Hsrc"; first iAssumption.
      iSplitL "SI"; first iAssumption.
      iSplitL "He"; first iAssumption.
      iCombine "Hrwp Ht1 Ht2" as "H"; iAssumption. }
    eapply rwp_prim_step in Hsat; eauto.
    destruct Hsat as (a' & m & Hrtc & Hsat).
    exists a', m. split; auto.
    eapply satisfiable_at_mono; first apply Hsat.
    iIntros "($ & $ & He2 & Hefs & $ & Ht1 & Ht2)".
    rewrite big_sepL_app //= big_sepL_app; iFrame.
Qed.


Lemma rwp_erased_steps `{LargeIndex SI} s Φ a n ts ts' σ σ':
  rtc erased_step (ts, σ) (ts', σ')
  → satisfiable_at ⊤ (source_interp a ∗ ref_state_interp σ n ∗ thread_wps s Φ ts)%I
  → ∃ a' m, rtc source_rel a a'
            ∧ satisfiable_at ⊤ (source_interp a' ∗ ref_state_interp σ' m ∗ thread_wps s Φ ts')%I.
Proof.
  intros Hsteps. remember (ts, σ) as c. remember (ts', σ') as c'.
  revert ts σ Heqc ts' σ' Heqc' n a.
  induction Hsteps as [|x [ts'' σ''] z Hstep]; intros ts σ Heqc ts' σ' Heqc' n a; subst.
  - injection Heqc' as -> ->. intros Hsteps. exists a, n; by split.
  - intros Hsat. eapply rwp_erased_step in Hsat as (a' & m & Hsteps' & Hsat); last eauto.
    edestruct IHHsteps as (a'' & m' & Hsteps'' & Hsat'); [done|done| |].
    + apply Hsat.
    + exists a'', m'; split; eauto. transitivity a'; eauto.
Qed.

Lemma rwp_result `{LargeIndex SI} Φ ts a n e v σ σ' s:
  rtc erased_step ([e], σ) (of_val v :: ts, σ')
  → satisfiable_at ⊤ (source_interp a ∗ ref_state_interp σ n ∗ RWP e @ s; ⊤ ⟨⟨ Φ ⟩⟩)%I
  → ∃ a' m, rtc source_rel a a'
            ∧ satisfiable_at ⊤ (source_interp a' ∗ ref_state_interp σ' m ∗ Φ v)%I.
Proof.
  intros Hsteps Hsat. eapply rwp_erased_steps in Hsteps; last first.
  { rewrite /thread_wps //=. eapply satisfiable_at_mono; first apply Hsat.
    by iIntros "($ & $ & $)". }
  destruct Hsteps as (a' & m & Hrtc & Hsat'). exists a', m; split; auto.
  eapply satisfiable_at_fupd, satisfiable_at_mono; first apply Hsat'.
  iIntros "(Hsrc & Href & Hthread)".
  rewrite /thread_wps. iDestruct "Hthread" as "[Hthread _]".
  rewrite rwp_unfold /rwp_pre to_of_val.
  by iMod ("Hthread" with "[$]") as "($&$&$)".
Qed.

End refinements.
