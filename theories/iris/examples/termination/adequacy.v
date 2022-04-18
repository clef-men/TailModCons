From iris.program_logic.refinement Require Export ref_weakestpre ref_source seq_weakestpre.
From iris.base_logic.lib Require Export invariants na_invariants.
From iris.heap_lang Require Export lang lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation metatheory.
From iris.algebra Require Import auth gmap excl frac agree.
From iris.program_logic Require Import ref_adequacy.
From iris.examples Require Import refinement.
Set Default Proof Using "Type".


(* Adequacy Theorem *)
Section adequacy.
  Context {SI} `{C: Classical}  {Σ: gFunctors SI} {Hlarge: LargeIndex SI}. 
  Context `{Hpre: !heapPreG Σ} `{Hna: !na_invG Σ} `{Htc: !inG Σ (authR (ordA SI))}.

  Theorem heap_lang_ref_adequacy (e: expr) σ:
    (∀ `{heapG SI Σ} `{!seqG Σ} `{!auth_sourceG Σ (ordA SI)},
      True ⊢ (∃ α, $α -∗ SEQ e ⟨⟨ v, True ⟩⟩)%I
    ) →
    sn erased_step ([e], σ).
  Proof using C Hlarge Σ Hpre Hna Htc.
    intros Hobj.
    (* allocate the heap *)
    edestruct (satisfiable_at_gen_heap nil σ) as [Hheap Hsat].
    (* allocate sequential invariants *)
    eapply satisfiable_update_alloc in Hsat as [seqG_name Hsat]; last apply na_alloc.
    pose (seq := {| seqG_na_invG := _; seqG_name := seqG_name |}).
    (* allocte stuttering credits *)
    eapply (satisfiable_at_alloc (● zero ⋅ ◯ zero)) in Hsat as [authG_name Hsat]; last first.
    { apply auth_both_valid; by split. }
    pose (stutter := {| sourceG_inG := _; sourceG_name := authG_name |}).
    specialize (Hobj Hheap seq stutter).
    eapply satisfiable_at_mono with (Q := (∃ α: Ord, _)%I) in Hsat; last first.
    { iIntros "H". iPoseProof (Hobj with "[//]") as (α) "Hwp".
      iExists α. iCombine "H Hwp" as "H". iExact "H". }
    eapply satisfiable_at_exists in Hsat as [α Hsat]; last apply _.
    eapply satisfiable_at_mono with (Q := (|={⊤}=> _)%I) in Hsat; last first.
    - iIntros "[[[[SI _] Hna] [Hc Hc']] Hwp]".
      iMod (own_update_2 _ _  _ (● α ⋅ ◯ α) with "Hc Hc'") as "[Hc Hc']".
      { rewrite -[α]natural_addition_zero_left_id natural_addition_comm -ord_op_plus.
        eapply auth_update, op_local_update_discrete; done. }
      iSpecialize ("Hwp" with "Hc' Hna").
      iCombine "Hc SI Hwp" as "G". iExact "G".
    - eapply satisfiable_at_fupd in Hsat as Hsat.
      eapply (rwp_sn_preservation _ (α) _ _ 0); first apply index_lt_wf.
      eapply satisfiable_at_mono; first apply Hsat.
      iIntros "($ & $ & $)".
    Qed.

End adequacy.

Section adequacy_ord. 
  (* result for the ordinal step-index type *)
  Context `{C: Classical}  {Σ: gFunctors ordI}.
  Context `{Hpre: !heapPreG Σ} `{Hna: !na_invG Σ} `{Htc: !inG Σ (authR (ordA ordI))}.
  Theorem heap_lang_ref_adequacy_ord (e: expr) σ:
    (∀ `{heapG ordI Σ} `{!seqG Σ} `{!auth_sourceG Σ (ordA ordI)},
      True ⊢ (∃ α, $α -∗ SEQ e ⟨⟨ v, True ⟩⟩)%I
    ) →
    sn erased_step ([e], σ).
  Proof using C Σ Hpre Hna Htc.
    apply heap_lang_ref_adequacy.
  Qed.
  Print Assumptions heap_lang_ref_adequacy_ord. 

End adequacy_ord.
