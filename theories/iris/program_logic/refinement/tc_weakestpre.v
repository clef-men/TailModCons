From iris.program_logic Require Export language.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import auth.
From iris.algebra.ordinals Require Export ord_stepindex arithmetic.
From iris.program_logic.refinement Require Import ref_adequacy ref_source ref_weakestpre.
Set Default Proof Using "Type".


(* time credits weakest precondition, using notation of total weakest-pre  *)
Notation tcG Σ := (auth_sourceG Σ (ordA _)).

Global Program Instance tcwp {SI} {Σ: gFunctors SI} `{!tcG Σ} `{!ref_irisG Λ Σ} : Twp Λ (iProp Σ) stuckness := rwp.

Section lemmas.
  Context {SI} {Σ: gFunctors SI} {Λ} `{!ref_irisG Λ Σ} `{!tcG Σ}.

  Definition one := (succ zero).

  Lemma tc_split α β: $ (α ⊕ β) ≡ ($α ∗ $β)%I.
  Proof.
    by rewrite -ord_op_plus /srcF auth_frag_op own_op.
  Qed.

  Lemma tc_succ α: $ succ α ≡ ($ α ∗ $ one)%I.
  Proof.
    by rewrite -tc_split /one natural_addition_comm natural_addition_succ natural_addition_zero_left_id.
  Qed.

  Lemma tcwp_rwp e E s Φ:
    twp s E e Φ ≡ rwp s E e Φ.
  Proof. reflexivity. Qed.

  Lemma tcwp_burn_credit e E s (Φ: val Λ → iProp Σ):
    to_val e = None →
    ⊢ ($ one -∗ (▷ RSWP e at 0 @ s; E ⟨⟨ v, Φ v ⟩⟩) -∗ WP e @ s; E [{ v, Φ v }])%I.
  Proof.
    iIntros (?) "Hone Hwp". rewrite tcwp_rwp.
    iApply (rwp_take_step  with "[Hwp] [Hone]"); first done.
    - iIntros "_". iApply rswp_do_step. by iNext.
    - iApply (@auth_src_update _ _ (ordA SI) with "Hone").
      eapply succ_greater.
  Qed.

  Lemma tc_weaken (α β: Ord) e s E Φ:
    to_val e = None
    → β ⪯ α
    → ($β -∗ WP e @ s; E [{ Φ }]) ∗ $ α ⊢ WP e @ s; E [{ Φ }].
  Proof.
    intros He [->|]; iIntros "[Hwp Hc]".
    - by iApply "Hwp".
    - iApply (rwp_weaken with "[Hwp] [Hc]"); first done.
      + iExact "Hwp".
      + by iApply (@auth_src_update _ _ (ordA SI) with "Hc").
  Qed.

  Lemma tc_alloc_zero s E e Φ: ($ zero -∗ WP e @ s; E [{ Φ }]) ⊢ WP e @ s; E [{ Φ }].
  Proof.
    iIntros "H".
    iMod (@own_unit _ _ _ sourceG_inG sourceG_name) as "Hz".
    replace (ε: @authR SI (auth_sourceUR SI (ordA SI)))
      with (◯ zero: @authR SI (auth_sourceUR SI (ordA SI))) by reflexivity.
    by iSpecialize ("H" with "Hz").
  Qed.

  Global Instance tc_timeless α : Timeless ($ α).
  Proof. apply _. Qed.

  Global Instance zero_persistent : Persistent ($ zero).
  Proof.
    apply own_core_persistent, auth_frag_core_id.
    replace zero with (core zero) by reflexivity.
    apply cmra_core_core_id.
  Qed.

  Global Instance tcwp_elim_wand p e s E Φ Ψ :
    ElimModal True p false (twp s E e Φ) emp (twp s E e Ψ) (∀ v, Φ v ={E}=∗ Ψ v).
  Proof.
    iIntros (_) "(P & HPQ)". iPoseProof (bi.intuitionistically_if_elim with "P") as "P".
    iApply (rwp_strong_mono with "P"); auto. iIntros (v) "HΦ". by iApply ("HPQ" with "[] HΦ").
  Qed.
End lemmas.



(* adequacy lemmas *)
Lemma tcwp_adequacy {SI} {Σ: gFunctors SI} {Λ} `{!ref_irisG Λ Σ} `{!tcG Σ} `{LargeIndex SI} Φ (e: expr Λ) σ (n: nat) (α: Ord):
  satisfiable_at ⊤ (●$ α ∗ ref_state_interp σ n ∗ (WP e [{ v, Φ v}]))%I
  → ex_loop erased_step ([e], σ)
  → False.
Proof.
  specialize (@rwp_adequacy SI Σ Ord Λ _ _ _ Φ α e σ n NotStuck).
  simpl; rewrite /srcA. intros Had Hsat Hloop. eapply Had; auto.
  by apply wf_ord_lt.
Qed.

(* instantiation with the ordinal index to be sure *)
Lemma tcwp_adequacy' {Λ} {Σ: gFunctors ordI} `{!ref_irisG Λ Σ} `{!tcG Σ} Φ e (n: nat) σ (α: Ord):
  satisfiable_at ⊤ (●$ α ∗ ref_state_interp σ n ∗ (WP e [{ v, Φ v}]))%I
  → ex_loop erased_step ([e], σ)
  → False.
Proof.
  apply tcwp_adequacy.
Qed.
