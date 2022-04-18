From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

From iris.program_logic.refinement Require Export ref_weakestpre.
(* TODO: move to the right place *)
Section step_fupdN.

  Context {SI} {PROP: sbi SI} `{FU: BiFUpd SI PROP}.

  Lemma step_fupdN_mask_comm n E1 E2 E3 E4 (P: PROP):
    E1 ⊆ E2 → E4 ⊆ E3 →
    ((|={E1, E2}=>|={E2, E3}▷=>^n P) ⊢ |={E1, E4}▷=>^n |={E1, E2}=> P)%I.
  Proof.
    iIntros (Hsub1 Hsub2) "H". iInduction n as [|n] "IH"; auto; simpl.
    iMod "H". iMod "H". iMod (fupd_intro_mask' E3 E4) as "Hclose"; auto.
    iModIntro. iNext. iMod "Hclose". iMod "H".
    iMod (fupd_intro_mask' E2 E1) as "Hclose'"; auto.
    iModIntro. iApply "IH". iMod "Hclose'". by iModIntro.
  Qed.

  Lemma step_fupdN_mask_comm' n E1 E2 (P: PROP):
    E2 ⊆ E1 →
    ((|={E1, E1}▷=>^n |={E1, E2}=> P) ⊢ |={E1, E2}=> |={E2, E2}▷=>^n P)%I.
  Proof.
    iIntros (Hsub) "H". iInduction n as [|n] "IH"; auto; simpl.
    iMod "H". iMod (fupd_intro_mask' E1 E2) as "Hclose"; auto.
    do 2 iModIntro. iNext. iMod "Hclose". iMod "H". by iApply "IH".
  Qed.


End step_fupdN.


Section lifting.
Context {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} `{Inhabited (expr Λ)}.
Implicit Types s : stuckness.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types a : A.
Implicit Types b : bool.

(* refinement weakest precondition *)
Hint Resolve reducible_no_obs_reducible : core.

Lemma rwp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 n a, source_interp a ∗ ref_state_interp σ1 n ={E,∅}=∗
  ∃ b, ▷? b |={∅}=> (⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
  ∀ e2 σ2 efs κ, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ |={∅,E}=>
    (if b then ∃ (a': A), ⌜a ↪⁺ a'⌝ ∗ source_interp a' else source_interp a) ∗
    ref_state_interp σ2 (length efs + n) ∗ RWP e2 @ s; E ⟨⟨ Φ ⟩⟩ ∗ [∗ list] i ↦ ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩))
  ⊢ RWP e1 @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  by rewrite rwp_unfold /rwp_pre /rwp_step=> ->.
Qed.

Lemma rwp_lift_atomic_step_fupd {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 n a, source_interp a ∗ ref_state_interp σ1 n ={E}=∗
    ∃ b, ▷? b |={E}=> ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs κ, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      (if b then ∃ (a': A), ⌜a ↪⁺ a'⌝ ∗ source_interp a' else source_interp a) ∗
      ref_state_interp σ2 (length efs + n) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩)
  ⊢ RWP e1 @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (?) "H".
  iApply (rwp_lift_step_fupd s E _ e1)=>//; iIntros (σ1 n a) "H'".
  iMod ("H" $! σ1 with "H'") as (b) "H". iExists b.
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro. iNext. iMod "Hclose" as "_". iMod "H" as "[$ H]".
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iIntros "!>" (e2 σ2 efs κ ?). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "($ & $ & H & $)"; [done|].
  iModIntro.
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply rwp_value; last done. by apply of_to_val.
Qed.

Lemma rwp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s E Φ e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → RWP e2 @ s; E ⟨⟨ Φ ⟩⟩)
  ⊢ RWP e1 @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hsafe Hstep) "H". iApply rwp_lift_step_fupd.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ1 n e_s) "Hσ".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first by set_solver.
  iExists false. iModIntro. iSplit.
  { iPureIntro. destruct s; done. }
  iIntros (e2 σ2 efs κ ?).
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iMod "Hclose" as "_". iModIntro.
  iDestruct ("H" with "[//]") as "H". simpl. iFrame.
Qed.

Lemma rwp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E Φ} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (RWP e2 @ s; E ⟨⟨ Φ ⟩⟩) ⊢ RWP e1 @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (? Hpuredet) "H". iApply (rwp_lift_pure_step_no_fork s E); try done.
  { naive_solver. }
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

Lemma rwp_pure_step `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  RWP e2 @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RWP e1 @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply rwp_lift_pure_det_step_no_fork.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - done.
  - by iApply "IH".
Qed.


(* step refinement weakest lemmas *)
Lemma rswp_lift_step_fupd k s E Φ e1 :
  (∀ σ1 n, ref_state_interp σ1 n ={E,∅}=∗
    |={∅,∅}▷=>^k ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
     ∀ e2 σ2 efs κ, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      ref_state_interp σ2 (length efs + n) ∗
      RWP e2 @ s; E ⟨⟨ Φ ⟩⟩ ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩)
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rswp_unfold /rswp_def /rswp_step. iIntros "H" (σ1 n ?) "(?&Hσ)".
  iMod ("H" with "Hσ") as "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "($&H)". iFrame. eauto.
Qed.

Lemma rswp_lift_step k s E Φ e1 :
  (∀ σ1 n, ref_state_interp σ1 n ={E,∅}=∗
    ▷^k (⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs κ, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      ref_state_interp σ2 (length efs + n) ∗
      RWP e2 @ s; E ⟨⟨ Φ ⟩⟩ ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩))
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_step_fupd. iIntros (??) "Hσ".
  iMod ("H" with "Hσ") as "H". iIntros "!>". by iApply step_fupdN_intro.
Qed.

Lemma rswp_lift_pure_step_no_fork k s E E' Φ e1 :
  (∀ σ1, s = NotStuck → reducible e1 σ1) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E}=>|={E,E'}▷=>^k ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → RWP e2 @ s; E ⟨⟨ Φ ⟩⟩)
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hsafe Hstep) "H". iApply rswp_lift_step_fupd.
  iIntros (σ1 n) "Hσ". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first by set_solver.
  iApply (step_fupdN_wand with "[Hclose H]").
  { iApply (step_fupdN_mask_comm _ _ E E'); first set_solver; first set_solver.
  iMod "Hclose". by iModIntro. }
  iIntros "H". iSplit.
  { iPureIntro. destruct s; eauto. }
  iIntros (e2 σ2 efs κ Hstep'). iMod "H"; iModIntro.
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iDestruct ("H" with "[//]") as "H". simpl. iFrame.
Qed.

Lemma rswp_lift_atomic_step_fupd {k s E1 Φ} e1 :
  (∀ σ1 n, ref_state_interp σ1 n ={E1}=∗
  |={E1,E1}▷=>^k ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs κ, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E1}=∗
      ref_state_interp σ2 (length efs + n) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩)
  ⊢ RSWP e1 at k @ s; E1 ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H".
  iApply (rswp_lift_step_fupd k s E1 _ e1)=>//; iIntros (σ1 n) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "H". iApply step_fupdN_mask_comm'; first set_solver.
  iApply (step_fupdN_wand with "H"); iIntros "[% H]".
  iMod (fupd_intro_mask' E1 ∅) as "Hclose"; first set_solver.
  iModIntro; iSplit; auto.
  iIntros (e2 σ2 efs κ Hstep). iMod "Hclose".
  iMod ("H" with "[//]") as "($ & H & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply rwp_value; last done. by apply of_to_val.
Qed.

Lemma rswp_lift_atomic_step {k s E Φ} e1 :
  (∀ σ1 n, ref_state_interp σ1 n ={E}=∗
    ▷^k (⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs κ, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ref_state_interp σ2 (length efs + n) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩))
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_atomic_step_fupd.
  iIntros (??) "?". iMod ("H" with "[$]") as "H".
  iIntros "!>". by iApply step_fupdN_intro; first done.
Qed.

Lemma rswp_lift_pure_det_step_no_fork {k s E E' Φ} e1 e2 :
  (∀ σ1, s = NotStuck → reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E,E'}▷=>^k RWP e2 @ s; E ⟨⟨ Φ ⟩⟩) ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (? Hpuredet) "H". iApply (rswp_lift_pure_step_no_fork k s E); try done.
  { naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.


(* RSWP lemmas are designed to be used with a single step only. The RSWP returns to RWP after a single step.*)
Lemma rswp_pure_step_fupd k s E E' e1 e2 φ Φ `{!Inhabited (state Λ)} :
  PureExec φ 1 e1 e2 →
  φ →
  (|={E,E'}▷=>^k RWP e2 @ s; E ⟨⟨ Φ ⟩⟩) ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  inversion Hexec as [|n' ? e1' ? Hstep Hrest]; subst.
  iApply rswp_lift_pure_det_step_no_fork.
  - intros σ; intros ->; eauto using pure_step_safe, reducible_no_obs_reducible, reducible_not_val.
  - eauto using pure_step_det.
  - inversion Hrest; subst; eauto.
Qed.

Lemma rswp_pure_step_later `{!Inhabited (state Λ)} k s E e1 e2 φ Φ :
  PureExec φ 1 e1 e2 →
  φ →
  ▷^k RWP e2 @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  intros Hexec ?. rewrite -rswp_pure_step_fupd //. iIntros "H".
  iApply step_fupdN_intro; eauto.
Qed.

End lifting.
