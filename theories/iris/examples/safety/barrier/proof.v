From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Import invariants saved_prop.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth gset.
From iris.examples.safety.barrier Require Export barrier.
Set Default Proof Using "Type".

(** The CMRAs/functors we need. *)
Class barrierG {SI} (Σ : gFunctors SI) := BarrierG {
  barrier_inG :> inG Σ (authR (gset_disjUR gname));
  barrier_savedPropG :> savedPropG Σ;
}.
Definition barrierΣ {SI} : gFunctors SI :=
  #[ GFunctor (authRF (gset_disjUR gname)); savedPropΣ ].

Instance subG_barrierΣ `{Σ : gFunctors SI} : subG barrierΣ Σ → barrierG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{Σ : gFunctors SI} `{!heapG Σ, !barrierG Σ} (N : namespace).

(* P is the proposition that will be sent, R the one that will be received by the individual threads *)
Definition barrier_inv (l : loc) (γ : gname) (P : iProp Σ) : iProp Σ :=
  (∃ (b : bool) (γsps : gset gname) (oracle : gname -> iProp Σ),
    l ↦ #b ∗
    own γ (● (GSet γsps)) ∗
    ((if b then True else P) -∗ ▷ [∗ set] γsp ∈ γsps, oracle γsp) ∗
    ([∗ set] γsp ∈ γsps, saved_prop_own γsp (oracle γsp)))%I.

(*P is the proposition that will be sent, R' the one that will be received by this particular thread, and R the one we want to have *)
Definition recv (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ γ P R' γsp,
    inv N (barrier_inv l γ P) ∗
    ▷ (R' -∗ R) ∗
    own γ (◯ GSet {[ γsp ]}) ∗
    saved_prop_own γsp R')%I.

(* P is the prop that we need to send *)
Definition send (l : loc) (P : iProp Σ) : iProp Σ :=
  (∃ γ, inv N (barrier_inv l γ P))%I.

(** Setoids *)
Instance barrier_inv_ne l γ : NonExpansive (barrier_inv l γ).
Proof. solve_proper. Qed.
Global Instance send_ne l : NonExpansive (send l).
Proof. solve_proper. Qed.
Global Instance recv_ne l : NonExpansive (recv l).
Proof. solve_proper. Qed.

(** Actual proofs *)
Lemma newbarrier_spec (P : iProp Σ) :
  {{{ True }}} newbarrier #() {{{ l, RET #l; recv l P ∗ send l P }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_fupd. wp_lam. wp_alloc l as "Hl".
  iApply ("HΦ" with "[> -]").
  iMod (saved_prop_alloc P) as (γsp) "#Hsp".
  iMod (own_alloc (● GSet {[ γsp ]} ⋅ ◯ GSet {[ γsp ]})) as (γ) "[H● H◯]".
  { by apply auth_both_valid. }
  iMod (inv_alloc N _ (barrier_inv l γ P) with "[Hl H●]") as "#Hinv".
  { iExists false, {[ γsp ]}, (fun _ => P). iIntros "{$Hl $H●} !>".
    rewrite !big_sepS_singleton; eauto. }
  iModIntro; iSplitL "H◯".
  - iExists γ, P, P, γsp. iFrame; auto.
  - by iExists γ.
Qed.

Lemma signal_spec l P :
  {{{ send l P ∗ P }}} signal #l {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[Hs HP] HΦ".
  iDestruct "Hs" as (γ) "#Hinv". wp_lam.
  wp_swp. iInv "Hinv" as "H".
  swp_last_step. iNext; simpl.
  iDestruct "H" as ([] γsps oracle) "(Hl & H● & HRs & Hsaved)".
  { wp_store. iModIntro. iSplitR "HΦ"; last by iApply "HΦ".
    iExists true, γsps, oracle. iFrame. }
  wp_store. iDestruct ("HRs" with "HP") as "HRs".
  iModIntro. iSplitR "HΦ"; last by iApply "HΦ".
  iExists true, γsps, oracle. iFrame; eauto.
Qed.

Lemma wait_spec l P:
  {{{ recv l P }}} wait #l {{{ RET #(); P }}}.
Proof.
  rename P into R.
  iIntros (Φ) "HR HΦ".
  iDestruct "HR" as (γ P R' γsp) "(#Hinv & HR & H◯ & #Hsp)".
  iLöb as "IH". wp_rec. wp_bind (! _)%E.
  iInv "Hinv" as "H". wp_swp. swp_step. iNext; simpl.
  iDestruct "H" as ([] γsps oracle) "(Hl & H● & HRs & Hsaved)"; last first.
  { wp_load. iModIntro. iSplitL "Hl H● HRs Hsaved".
    { iExists false, γsps, oracle. iFrame. }
    by wp_apply ("IH" with "[$] [$]"). }
  iSpecialize ("HRs" with "[//]").
  swp_last_step. iNext. wp_load.
  iDestruct (own_valid_2 with "H● H◯")
    as %[Hvalid%gset_disj_included%elem_of_subseteq_singleton _]%auth_both_valid.
  iDestruct (big_sepS_delete with "HRs") as "[HR'' HRs]"; first done.
  iDestruct (big_sepS_delete with "Hsaved") as "[HRsaved Hsaved]"; first done.
  iDestruct (saved_prop_agree with "Hsp HRsaved") as "#Heq".
  iMod (own_update_2 with "H● H◯") as "H●".
  { apply (auth_update_dealloc _ _ (GSet (γsps ∖ {[ γsp ]}))).
    apply gset_disj_dealloc_local_update. }
  iIntros "!>". iSplitL "Hl H● HRs Hsaved".
  { iModIntro.
    iExists true, (γsps ∖ {[ γsp ]}), oracle. iFrame; eauto.
  }
  wp_if. iApply "HΦ". iApply "HR". by iRewrite "Heq".
Qed.

Lemma recv_split E l P1 P2 :
  ↑N ⊆ E → ⊢ (recv l (P1 ∗ P2) -∗ |={E, ∅}=> ▷ |={∅, E}=> recv l P1 ∗ recv l P2)%I.
Proof.
  rename P1 into R1; rename P2 into R2.
  iIntros (?). iDestruct 1 as (γ P R' γsp) "(#Hinv & HR & H◯ & #Hsp)".
  iInv N as "H" "Hclose".
  iMod (fupd_intro_mask' (E ∖ ↑N) ∅) as "H3". set_solver.
  iModIntro. iNext.
  iDestruct "H" as (b γsps oracle) "(Hl & H● & HRs & Hsaved)". (* as later does not commute with exists, this would fail without taking a step *)
  iDestruct (own_valid_2 with "H● H◯")
    as %[Hvalid%gset_disj_included%elem_of_subseteq_singleton _]%auth_both_valid.
  set (γsps' := γsps ∖ {[γsp]}).
  iMod (own_update_2 with "H● H◯") as "H●".
  { apply (auth_update_dealloc _ _ (GSet γsps')).
    apply gset_disj_dealloc_local_update. }
  iMod (saved_prop_alloc_cofinite γsps' R1) as (γsp1 Hγsp1) "#Hsp1".
  iMod (saved_prop_alloc_cofinite (γsps' ∪ {[ γsp1 ]}) R2)
    as (γsp2 [? ?%not_elem_of_singleton]%not_elem_of_union) "#Hsp2".
  iMod (own_update _ _ (● _ ⋅ (◯ GSet {[ γsp1 ]} ⋅ ◯ (GSet {[ γsp2 ]})))
    with "H●") as "(H● & H◯1 & H◯2)".
  { rewrite -auth_frag_op gset_disj_union; last set_solver.
    apply auth_update_alloc, (gset_disj_alloc_empty_local_update _ {[ γsp1; γsp2 ]}).
    set_solver. }
  iMod "H3" as "_".
  iMod ("Hclose" with "[HR Hl HRs Hsaved H●]") as "_".
  { iModIntro. iExists b, ({[γsp1; γsp2]} ∪ γsps'),
        (fun g => if (decide (g = γsp1)) then R1 else if (decide (g = γsp2)) then R2 else oracle g).
    iIntros "{$Hl $H●}".
    iDestruct (big_sepS_delete with "Hsaved") as "[HRsaved Hsaved]"; first done.
    iSplitL "HR HRs HRsaved".
    - iIntros "HP". iSpecialize ("HRs" with "HP").
      iDestruct (saved_prop_agree with "Hsp HRsaved") as "#Heq".
      iNext.
      iDestruct (big_sepS_delete with "HRs") as "[HR'' HRs]"; first done.
      iApply big_sepS_union; [set_solver|iSplitL "HR HR'' HRsaved"]; first last.
      {
        subst γsps'. iApply big_opS_forall. 2: iApply "HRs". cbn. intros γ' Hin.
        destruct (decide (γ' = γsp1)) as [-> |_]. 1: by destruct Hγsp1.
        destruct (decide (γ' = γsp2)) as [-> |_]. 1: by destruct H0.
        reflexivity.
      }
      iApply big_sepS_union; [set_solver|].
      iAssert (R')%I with "[HR'']" as "HR'"; [by iRewrite "Heq"|].
      iDestruct ("HR" with "HR'") as "[HR1 HR2]".
      iSplitL "HR1".
      + iApply big_sepS_singleton. rewrite decide_True; done.
      + iApply big_sepS_singleton. rewrite decide_False; [by rewrite decide_True | done].
    - iApply big_sepS_union; [set_solver| iSplitR "Hsaved"]; first last.
      {
        subst γsps'. iApply big_opS_forall. 2: iApply "Hsaved". cbn. intros γ' Hin.
        destruct (decide (γ' = γsp1)) as [-> | _]. by destruct Hγsp1.
        destruct (decide (γ' = γsp2)) as [-> | _]. by destruct H0.
        reflexivity.
      }
      iApply big_sepS_union; [set_solver|]; rewrite !big_sepS_singleton.
      iSplitL.
      + rewrite decide_True; done.
      + rewrite decide_False; [by rewrite decide_True | done].
  }
  iModIntro; iSplitL "H◯1".
  - iExists γ, P, R1, γsp1. iFrame; auto.
  - iExists γ, P, R2, γsp2. iFrame; auto.
Qed.

Lemma recv_weaken l P1 P2 : (P1 -∗ P2) -∗ recv l P1 -∗ recv l P2.
Proof.
  iIntros "HP". iDestruct 1 as (γ P R' i) "(#Hinv & HR & H◯)".
  iExists γ, P, R', i. iIntros "{$Hinv $H◯} !> HR'". iApply "HP". by iApply "HR".
Qed.

Lemma recv_mono l P1 P2 : (P1 ⊢ P2) → recv l P1 ⊢ recv l P2.
Proof. iIntros (HP) "H". iApply (recv_weaken with "[] H"). iApply HP. Qed.
End proof.

Typeclasses Opaque send recv.
