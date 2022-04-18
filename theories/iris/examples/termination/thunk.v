From iris.program_logic.refinement Require Export seq_weakestpre.
From iris.base_logic.lib Require Export invariants na_invariants.
From iris.heap_lang Require Export lang lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation metatheory.
From iris.algebra Require Import auth.
From iris.algebra.ordinals Require Import arithmetic.
Set Default Proof Using "Type".



Definition thunk : val :=
  λ: "f", let: "r" := ref NONE in
  λ: <>, match: !"r" with
    SOME "v" => "v"
    | NONE => (let: "y" := "f" #() in "r" <- SOME "y";; "y")
  end.

Section thunk_proof.
  Context {SI} {Σ: gFunctors SI} `{Hheap: !heapG Σ} `{Htc: !tcG Σ} (N : namespace) `{Htok: !inG Σ (authR (unitUR SI))}.

  Implicit Types (α β: ord_stepindex.Ord).

  (* simplest spec - one to one correspondence *)
  Lemma thunk_partial_spec (f: val) Φ:
    WP f #() {{ Φ }} -∗ WP (thunk f) {{ g, WP g #() {{ Φ }} }}.
  Proof.
    iIntros "Hf". unfold thunk. wp_pures. wp_bind (ref _)%E.
    wp_alloc r as "Hr"; wp_pures.
    wp_pures. wp_load. wp_pures.
    wp_apply (wp_wand with "Hf [Hr]").
    iIntros (v) "Hv"; wp_pures.
    by wp_store.
  Qed.

  Lemma thunk_spec (f: val) Φ:
    WP f #() [{ Φ }] -∗ WP (thunk f) [{ g, WP g #() [{ Φ }] }].
  Proof.
    iIntros "Hf". unfold thunk. wp_pures. wp_bind (ref _)%E.
    wp_alloc r as "Hr"; wp_pures.
    wp_pures. wp_load. wp_pures.
    wp_apply (rwp_wand with "Hf [Hr]").
    iIntros (v) "Hv"; wp_pures.
    by wp_store.
  Qed.


  Definition thunk_inv `{!seqG Σ} r (f: val) Φ : iProp Σ :=
    (r ↦ NONEV ∗ SEQ  (f #()) @ (⊤ ∖ ↑N) ⟨⟨ v, Φ v ⟩⟩ ∨ (∃ v, r ↦ SOMEV v ∗ Φ v))%I.

  Lemma thunk_sequential_spec `{!seqG Σ} `{FiniteBoundedExistential SI} (f: val) Φ:
    (∀ x, Persistent (Φ x)) →
    SEQ (f #()) @ (⊤ ∖ ↑N) ⟨⟨ v, Φ v ⟩⟩ -∗
    SEQ (thunk f) ⟨⟨ g, □ $one -∗ SEQ (g #()) ⟨⟨ v, Φ v⟩⟩⟩⟩.
  Proof.
    iIntros (HΦ) "Hf". rewrite /thunk. iIntros "Hna".
    wp_pures. wp_bind (ref _)%E.
    wp_alloc r as "Hr".
    iMod (na_inv_alloc seqG_name _ N (thunk_inv r f Φ) with "[Hr Hf]") as "#I".
    { iNext. iLeft. by iFrame. }
    wp_pures. iFrame. iModIntro.
    iIntros "Hc Hna". wp_pures.
    wp_bind (! _)%E.
    iMod (na_inv_acc_open with "I Hna") as "P"; eauto.
    iApply (tcwp_burn_credit with "Hc"); auto. iNext.
    iDestruct "P" as "([H|H] & Hna & Hclose)".
    - iDestruct "H" as "(Hr & Hwp)".
      wp_load. wp_pures. iSpecialize ("Hwp" with "Hna").
      wp_bind (f #()). iApply (rwp_wand with "Hwp [Hr Hclose]").
      iIntros (v) "[Hna #HΦ]". wp_pures.
      wp_bind (#r <- _)%E. wp_store.
      iMod ("Hclose" with "[Hr $Hna]") as "Hna".
      { iNext. iRight. iExists v. by iFrame. }
      wp_pures. by iFrame.
    - iDestruct "H" as (v) "[Hr #HΦ]".
      wp_load. iMod ("Hclose" with "[Hr $Hna]") as "Hna".
      { iNext. iRight. iExists v. by iFrame. }
      wp_pures. by iFrame.
  Qed.


  (* the timeless portion *)
  Definition prepaid_inv_tl `{!seqG Σ} γ r Φ : iProp Σ :=
    ((r ↦ NONEV ∗ $ one ∗ own γ (● ())) ∨ (∃ v, r ↦ SOMEV v ∗ Φ v))%I.

  Global Instance prepaid_inv_tl_timeless `{!seqG Σ} α γ Φ r: (∀ v, Timeless (Φ v)) → Timeless (prepaid_inv_tl γ r Φ).
  Proof.
    intros. rewrite /prepaid_inv_tl. apply _.
  Qed.

  Definition prepaid_inv_re `{!seqG Σ} γ (f: val) Φ : iProp Σ :=
    (SEQ  (f #())  @ (⊤ ∖ ↑N.@"tl" ∖ ↑N.@"re") ⟨⟨ v, Φ v ⟩⟩ ∨ own γ (● ()))%I.


  Lemma thunk_sequential_prepaid_spec `{!seqG Σ} `{FiniteBoundedExistential SI} (f: val) Φ:
    (∀ x, Persistent (Φ x)) → (∀ x, Timeless (Φ x)) →
    SEQ (f #()) @  (⊤ ∖ ↑N.@"tl" ∖ ↑N.@"re") ⟨⟨v, Φ v⟩⟩ -∗ $one -∗ SEQ (thunk f) ⟨⟨ g, □ SEQ (g #()) ⟨⟨ v, Φ v⟩⟩⟩⟩.
  Proof using Hheap Htc Htok N SI Σ.
    iIntros (??) "Hf Hone". rewrite /thunk. iIntros "Hna".
    wp_pures.
    iMod (own_alloc (● ())) as (γ) "H●"; first by apply auth_auth_valid.
    wp_bind (ref _)%E.
    wp_alloc r as "Hr".
    iMod (na_inv_alloc seqG_name _ (N .@ "tl") (prepaid_inv_tl γ r Φ) with "[Hr Hone H●]") as "#Itl".
    { iNext. iLeft. by iFrame. }
    iMod (na_inv_alloc seqG_name _ (N .@ "re") (prepaid_inv_re γ f Φ) with "[$Hf]") as "#Ire".
    wp_pures. iFrame. iModIntro.
    iIntros "Hna". wp_pures.
    wp_bind (! _)%E.
    iMod (na_inv_acc_open_timeless with "Itl Hna") as "([H|H] & Hna & Hclose)"; eauto.
    - iDestruct "H" as "(Hr & Hone & H●)".
      iMod (na_inv_acc_open with "Ire Hna") as "P"; eauto; first solve_ndisj.
      iApply (tcwp_burn_credit with "Hone"); auto.
      iNext. iDestruct "P" as "(Hre & Hna & Hclose')".
      wp_load. wp_pures.
      wp_bind (f #()). rewrite /prepaid_inv_re.
      iDestruct "Hre" as "[Hwp|H●']".
      + iSpecialize ("Hwp" with "Hna").
        iApply (rwp_wand with "Hwp [Hr Hclose Hclose' H●]").
        iIntros (v) "[Hna #HΦ]". wp_pures.
        wp_bind (#r <- _)%E. wp_store.
        iMod ("Hclose'" with "[$Hna $H●]") as "Hna".
        iMod ("Hclose" with "[Hr $Hna]") as "Hna".
        { iNext. iRight. iExists v. by iFrame. }
        wp_pures. by iFrame.
      + iCombine "H● H●'" as "H".
        iPoseProof (own_valid with "H") as "H".
        rewrite uPred.discrete_valid.
        iDestruct "H" as "%".
        apply ->(@auth_auth_frac_valid SI) in H2.
        destruct H2 as [H2 _]. rewrite frac_op' in H2.
        apply ->(@frac_valid' SI) in H2.
        exfalso. by eapply Qp_not_plus_q_ge_1.
    - iDestruct "H" as (v) "[Hr #HΦ]".
      wp_load. iMod ("Hclose" with "[Hr $Hna]") as "Hna".
      { iNext. iRight. iExists v. by iFrame. }
      wp_pures. by iFrame.
  Qed.
End thunk_proof.
