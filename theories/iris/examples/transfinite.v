From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import auth.
From iris.examples.safety Require Import lock.
Set Default Proof Using "Type".


Section how_to_handle_invariants.
  Context {SI} {Σ: gFunctors SI} `{!heapG Σ} (N : namespace).



  (* We compare how opening invariants worked previously and
     how it can be done in the transfinite setting. *)
  Lemma invariants_previously `{FiniteIndex SI} l Φ:
    {{{ inv N (∃ v, l ↦ v ∗ Φ v) }}} ! #l {{{ v, RET v; True }}}.
  Proof.
    iIntros (ϕ) "#I Post".
    iInv "I" as "H" "Hclose".
    iDestruct "H" as (v) "[Hl P]".
    wp_load. iMod ("Hclose" with "[Hl P]") as "_".
    { iNext. iExists v. iFrame. }
    iModIntro. by iApply "Post".
  Qed.


  Lemma invariants_transfinite l Φ:
    {{{ inv N (∃ v, l ↦ v ∗ Φ v) }}} ! #l {{{ v, RET v; True }}}.
  Proof.
    iIntros (ϕ) "#I Post".
    (* We move from the weakest pre to the stronger version which allows us to strip off laters.
       The argument is the number of laters we want to strip off. *)
    wp_swp 1%nat.
    (* SWP supports opening up invariants *)
    iInv "I" as "H" "Hclose".
    (* In general, we cannot commutate later with existential quantification *)
    Fail iDestruct "H" as (v) "[Hl P]".
    (* To access the contents of "H", we need to get rid of the later modality.
       We use the step property of SWP to add an additional later to our goal. *)
    swp_step. iNext; simpl.
    (* Afterwards the proof continues exactly the same as before. *)
    iDestruct "H" as (v) "[Hl P]".
    wp_load. iMod ("Hclose" with "[Hl P]") as "_".
    { iNext. iExists v. iFrame. }
    iModIntro. by iApply "Post".
  Qed.


  (* Using Coq EVars we leave the step counting to Coq: *)
  Lemma invariants_transfinite_evars l Φ:
    {{{ inv N (∃ v, l ↦ v ∗ Φ v) }}} ! #l {{{ v, RET v; True }}}.
  Proof.
    iIntros (ϕ) "#I Post".
    (* If no argument is provided to wp_swp, then the number of
       laters is instantiated with an evar (k in the following). *)
    wp_swp. iInv "I" as "H" "Hclose".
    (* In calling swp_step Coq creates a new evar, say k', and picks k := S k'.
       The user will usually only see k' from there on. *)
    swp_step.
    iNext; simpl.
    iDestruct "H" as (v) "[Hl P]".
    wp_load. iMod ("Hclose" with "[Hl P]") as "_".
    { iNext. iExists v. iFrame. }
    iModIntro. by iApply "Post".
    (* At the end we need to pick a value for the evar k'. Here 0 is always sufficient. *)
    Unshelve. exact 0%nat.
    (* Note that from k' := 0 automatically k := 1 follows *)
  Qed.

  (* Make the instantiation step explicit *)
  Lemma swp_finish E e s Φ : SWP e at 0%nat @ s; E {{ Φ }} ⊢ SWP e at 0%nat @ s; E {{ Φ }}.
  Proof. eauto. Qed.
  Ltac swp_finish := iApply swp_finish.
  Ltac swp_last_step := swp_step; swp_finish.


  (* Using Coq EVars we leave the step counting to Coq: *)
  Lemma invariants_transfinite_evars_inst l Φ:
    {{{ inv N (∃ v, l ↦ v ∗ Φ v) }}} ! #l {{{ v, RET v; True }}}.
  Proof.
    iIntros (ϕ) "#I Post".
    (* If no argument is provided to wp_swp, then the number of
       laters is instantiated with an evar (k in the following). *)
    wp_swp. iInv "I" as "H" "Hclose".
    (* do 5 swp_step. swp_finish. *)
    swp_last_step.
    iNext; simpl.
    iDestruct "H" as (v) "[Hl P]".
    wp_load. iMod ("Hclose" with "[Hl P]") as "_".
    { iNext. iExists v. iFrame. }
    iModIntro. by iApply "Post".
  Qed.

  (* Nested invariants *)
  (* We can nest invariants and open nested invariants in a single step of computation *)
  Section nested_invariants.
    Context `{inG SI Σ (authR (mnatUR SI))}.

    (* invariant asserting that the value stored at l is only increasing and already positive *)
    Definition Pos N l γ : iProp Σ := inv N (∃ n: mnat, l ↦ #n ∗ ⌜n > 0⌝ ∗ own γ (◯ n))%I.


    Definition L l1 γ : iProp Σ := inv (N .@ "L") (∃ m: mnat, l1 ↦ #m ∗ own γ (● m))%I.
    Definition R l2 γ : iProp Σ := inv (N .@ "R") (∃ l2': loc, l2 ↦ #l2' ∗ Pos (N .@ "I") l2' γ)%I.

    Lemma mnat_own (m n: mnat) γ:
      own γ (● m) -∗ own γ (◯ n) -∗ ⌜n ≤ m⌝%nat.
    Proof.
      iIntros "Hγ● Hγ◯". iDestruct (own_valid_2 with "Hγ● Hγ◯") as "H"; iRevert "H".
      iIntros (Hv). iPureIntro. eapply (mnat_included SI).
      apply auth_both_valid in Hv as [Hv _]; done.
    Qed.

    Lemma invariants_transfinite_nested  γ l1 l2:
      {{{ L l1 γ ∗ R l2 γ }}} !#l1 {{{ (m: nat), RET #m; ⌜m > 0⌝ }}}.
    Proof.
      iIntros (ϕ) "[#L #R] H".
      (* we need to open all invariants to ensure that the value stored at l1 is positive *)
      wp_swp 2%nat.
      iInv "L" as "HL" "CloseL".
      iInv "R" as "HR" "CloseR".
      swp_step. iNext; simpl.
      iDestruct "HL" as (m) "[Hl1 Hγ●]". iDestruct "HR" as (l2') "[Hl2 #I]".
      iInv "I" as "HI" "CloseI".
      swp_step. iNext; simpl.
      iDestruct "HI" as (n) "(Hl2' & % & #Hγ◯)".
      iPoseProof (mnat_own with "Hγ● Hγ◯") as "%".
      wp_load.
      iMod ("CloseI" with "[Hl2']") as "_".
      { iExists n; iNext; iFrame; by iSplit. }
      iModIntro. iMod ("CloseR" with "[Hl2]") as "_".
      { iExists l2'; iNext; by iFrame. } iModIntro.
      iMod ("CloseL" with "[Hl1 Hγ●]") as "_"; first (iNext; iExists m; iFrame).
      iModIntro. iApply "H". iPureIntro. lia.
    Qed.
  End nested_invariants.


  Lemma invariants_swp k e φ P `{!Atomic StronglyAtomic e}:
    (P ⊢ SWP e at k @ ⊤∖↑N  {{v, φ v ∗ P}}) → inv N P ⊢ SWP e at (S k) {{ v, φ v}}.
  Proof.
    iIntros (H) "I". iInv "I" as "P". swp_step. iNext.
    iPoseProof (H with "P") as "Q". iApply swp_wand_r.
    iFrame. iIntros (v) "($ & $)". by iModIntro.
  Qed.


End how_to_handle_invariants.
