(** Some derived lemmas for ectx-based languages *)
From iris.program_logic Require Export ectx_language.

From iris.program_logic.refinement Require Export ref_weakestpre ref_lifting.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section rwp.
Context {SI} {Σ: gFunctors SI} {A} {Λ: ectxLanguage} `{Hsrc: !source Σ A} `{Hiris: !ref_irisG Λ Σ}  `{Hexp: Inhabited (expr Λ)} `{Hstate: Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types P Q : iProp Σ.
Implicit Types a : A.
Implicit Types b : bool.
Implicit Types Φ : val Λ → iProp Σ.
Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Hint Resolve (reducible_not_val _ inhabitant) : core.
Hint Resolve head_stuck_stuck : core.


(* refinement weakest precondition *)
Lemma rwp_lift_head_step_fupd {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 n (a: A), source_interp a ∗ ref_state_interp σ1 n ={E,∅}=∗
    ∃ b, ▷? b |={∅}=> ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs κ, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      (if b then ∃ a' : A, ⌜a ↪⁺ a'⌝ ∗ source_interp a' else source_interp a) ∗
      ref_state_interp σ2 (length efs + n) ∗
      RWP e2 @ s; E ⟨⟨ Φ ⟩⟩ ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩)
  ⊢ RWP e1 @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (?) "H". iApply rwp_lift_step_fupd=>//. iIntros (σ1 n a) "Hσ".
  iMod ("H" with "Hσ") as (b) "H"; iExists b. iModIntro. iNext. iMod "H" as "[% H]". iModIntro.
  iSplit; first by destruct s; eauto. iIntros (e2 σ2 efs κ ?).
  iApply "H"; eauto.
Qed.

Lemma rwp_lift_atomic_head_step_fupd {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 n a, source_interp a ∗ ref_state_interp σ1 n ={E}=∗
    ∃ b, ▷? b |={E}=> ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs κ, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      (if b then ∃ (a': A), ⌜a ↪⁺ a'⌝ ∗ source_interp a' else source_interp a) ∗
      ref_state_interp σ2 (length efs + n) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩)
  ⊢ RWP e1 @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (?) "H". iApply rwp_lift_atomic_step_fupd; [done|].
  iIntros (σ1 Qs a) "H'". iMod ("H" with "H'") as (b) "H'".
  iModIntro. iExists b. iNext. iMod "H'" as "[% H']". iModIntro.
  iSplit; first by destruct s; auto. iIntros (e2 σ2 efs κ Hstep).
  iMod ("H'" with "[]"); eauto.
Qed.

Lemma rwp_lift_pure_head_step_no_fork s E Φ e1 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ κ σ1 e2 σ2 efs, head_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (∀ κ e2 efs σ, ⌜head_step e1 σ κ e2 σ efs⌝ → RWP e2 @ s; E ⟨⟨ Φ ⟩⟩)%I
  ⊢ RWP e1 @ s; E ⟨⟨ Φ ⟩⟩.
Proof using A Hexp Hiris Hsrc Hstate SI Λ Σ.
  intros Hsafe Hstep.
  iIntros "H". iApply rwp_lift_head_step_fupd; auto.
  iIntros (σ1 n a) "[Ha Hσ]". iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro. iExists false. iModIntro; iSplit; auto.
  iIntros (e2 σ2 efs κ H'). destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iMod "Hclose" as "_". iModIntro.
  iDestruct ("H" with "[//]") as "H". simpl. iFrame.
Qed.

Lemma rwp_lift_pure_det_head_step_no_fork {s E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (RWP e2 @ s; E ⟨⟨ Φ ⟩⟩) ⊢ RWP e1 @ s; E ⟨⟨ Φ ⟩⟩.
Proof using A Hexp Hiris Hsrc Hstate SI Λ Σ.
  intros H2 Hstep Hpuredet.
  iIntros "H". iApply rwp_lift_pure_head_step_no_fork; auto.
  { naive_solver. }
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.


(* lemmas for the indexed version *)
Lemma rswp_lift_head_step_fupd {k s E Φ} e1 :
  (∀ σ1 n, ref_state_interp σ1 n ={E,∅}=∗
    |={∅, ∅}▷=>^k ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs κ, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      ref_state_interp σ2 (length efs + n) ∗
      RWP e2 @ s; E ⟨⟨ Φ ⟩⟩ ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩)
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_step_fupd=>//. iIntros (σ1 n) "Hσ".
  iMod ("H" with "Hσ") as "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "[% H]".
  iSplit; first by destruct s; eauto.
  iIntros (e2 σ2 efs κ ?).
  iApply "H"; eauto.
Qed.

Lemma rswp_lift_atomic_head_step_fupd {k s E Φ} e1 :
  (∀ σ1 n, ref_state_interp σ1 n ={E}=∗
    |={E,E}▷=>^k ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs κ, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ref_state_interp σ2 (length efs + n) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩)
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_atomic_step_fupd; eauto.
  iIntros (σ1 Qs) "Hσ1". iMod ("H" with "Hσ1") as "H"; iModIntro.
  iApply (step_fupdN_wand with "H"); iIntros "[% H]".
  iSplit; first by destruct s; auto. iIntros (e2 σ2 efs κ Hstep).
  iApply "H"; eauto.
Qed.

Lemma rswp_lift_atomic_head_step {k s E Φ} e1 :
  (∀ σ1 n, ref_state_interp σ1 n ={E}=∗
    ▷^k (⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs κ, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ref_state_interp σ2 (length efs + n) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, RWP ef @ s; ⊤ ⟨⟨ ref_fork_post ⟩⟩))
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_atomic_head_step_fupd; eauto.
  iIntros (σ1 Qs) "Hσ1". iMod ("H" with "Hσ1") as "H"; iModIntro.
  by iApply step_fupdN_intro.
Qed.

Lemma rswp_lift_atomic_head_step_no_fork_fupd {k s E Φ} e1 :
  (∀ σ1 n, ref_state_interp σ1 n ={E}=∗
    |={E,E}▷=>^k ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs κ, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ ref_state_interp σ2 n ∗ from_option Φ False (to_val e2))
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_atomic_head_step_fupd; eauto.
  iIntros (σ1 Qs) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "H"; iModIntro.
  iApply (step_fupdN_wand with "H"); iIntros "[$ H]" (v2 σ2 efs κ Hstep).
  iMod ("H" $! v2 σ2 efs with "[//]") as "(-> & ? & ?) /=". by iFrame.
Qed.

Lemma rswp_lift_atomic_head_step_no_fork {k s E Φ} e1 :
  (∀ σ1 n, ref_state_interp σ1 n ={E}=∗
    ▷^k (⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs κ, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ ref_state_interp σ2 n ∗ from_option Φ False (to_val e2)))
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_atomic_head_step_no_fork_fupd.
  iIntros (σ1 Qs) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "H"; iModIntro.
  by iApply step_fupdN_intro.
Qed.


Lemma rswp_lift_pure_head_step_no_fork_fupd k s E Φ e1 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ κ σ1 e2 σ2 efs, head_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E,E}▷=>^k ∀ κ e2 efs σ, ⌜head_step e1 σ κ e2 σ efs⌝ → RWP e2 @ s; E ⟨⟨ Φ ⟩⟩)%I
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof using A Hexp Hiris Hsrc Hstate SI Λ Σ.
  intros Hsafe Hstep.
  iIntros "H". iApply rswp_lift_pure_step_no_fork; eauto.
  iModIntro. iApply (step_fupdN_wand with "H"); iIntros "H" (κ e2 efs σ Hs).
  iApply "H"; eauto.
Qed.

Lemma rswp_lift_pure_head_step_no_fork k s E Φ e1 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ κ σ1 e2 σ2 efs, head_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (▷^k ∀ κ e2 efs σ, ⌜head_step e1 σ κ e2 σ efs⌝ → RWP e2 @ s; E ⟨⟨ Φ ⟩⟩)%I
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof using A Hexp Hiris Hsrc Hstate SI Λ Σ.
  iIntros (Hsafe Hstep) "H". iApply rswp_lift_pure_head_step_no_fork_fupd; eauto.
  by iApply step_fupdN_intro.
Qed.

Lemma rswp_lift_pure_det_head_step_no_fork_fupd {k s E Φ} e1 e2 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E,E}▷=>^k RWP e2 @ s; E ⟨⟨ Φ ⟩⟩) ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof using A Hexp Hiris Hsrc Hstate SI Λ Σ.
  iIntros (Hstep Hdet) "H". iApply rswp_lift_pure_head_step_no_fork_fupd; eauto.
  { naive_solver. }
  iApply (step_fupdN_wand with "H"); by iIntros "H" (κ e2' efs σ (_&_&->&->)%Hdet).
Qed.

Lemma rswp_lift_pure_det_head_step_no_fork {k s E Φ} e1 e2 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (▷^k RWP e2 @ s; E ⟨⟨ Φ ⟩⟩) ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof using A Hexp Hiris Hsrc Hstate SI Λ Σ.
  iIntros (Hsafe Hstep) "H". iApply rswp_lift_pure_det_head_step_no_fork_fupd; eauto.
  by iApply step_fupdN_intro.
Qed.
End rwp.
