From iris.program_logic Require Export language.
From iris.bi Require Export fixpoint weakestpre.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import auth list.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export fancy_updates logical_step.
From iris.program_logic.refinement Require Export ref_source.
Set Default Proof Using "Type".

From iris.program_logic Require Import weakestpre.

Class ref_irisG (Λ : language) {SI} (Σ : gFunctors SI) := IrisG {
  ref_iris_invG :> invG Σ;
  (** The state interpretation is an invariant that should hold in between each
  step of reduction. Here [Λstate] is the global state and [nat] is the number of forked-off threads
  (not the total number of threads, which is one higher because there is always
  a main thread). *)
  ref_state_interp : state Λ → nat → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  ref_fork_post : val Λ → iProp Σ;
}.

(* we first define the core of the WP for the case that e1 is not a value.
  Φ is the prop that needs to hold for the expression (and forked-off threads) that we step to. *)
Definition rwp_step {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} E s (e1: expr Λ) (φ: expr Λ → list (expr Λ) → iProp Σ) : iProp Σ :=
  (∀ σ1 n (a: A), source_interp a ∗ ref_state_interp σ1 n ={E,∅}=∗
  ∃ b, ▷? b |={∅}=> (⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
  ∀ e2 σ2 efs κ, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ |={∅,E}=> (
    (if b then ∃ (a': A), ⌜a ↪⁺ a'⌝ ∗ source_interp a' else source_interp a) ∗
    ref_state_interp σ2 (length efs + n) ∗ φ e2 efs)))%I.

(* a "stronger" version: we cannot take a source step, but have to prove that the target
  can take a step under k laters *)
Definition rswp_step {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} (k: nat) E s (e1: expr Λ) (φ: expr Λ → list (expr Λ) → iProp Σ) : iProp Σ :=
  (∀ σ1 n a, source_interp a ∗ ref_state_interp σ1 n ={E,∅}=∗
  |={∅, ∅}▷=>^k (⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
  ∀ e2 σ2 efs κ, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ |={∅,E}=> (
      source_interp a ∗
      ref_state_interp σ2 (length efs + n) ∗ φ e2 efs)))%I.

(* pre-definition of rwp of which we will take a fixpoint. *)
Definition rwp_pre {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} (s: stuckness)
    (rwp : coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ) :
    coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => ∀ σ n a, source_interp a ∗ ref_state_interp σ n ={E}=∗ source_interp a ∗ ref_state_interp σ n ∗ Φ v
  | None => rwp_step E s e1 (λ e2 efs, (rwp E e2 Φ) ∗ [∗ list] i ↦ ef ∈ efs, rwp ⊤ ef ref_fork_post)
  end%I.

Lemma rwp_pre_mono {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ}  s (wp1 wp2 : coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ) :
  ⊢ ((□ ∀ E e Φ, wp1 E e Φ -∗ wp2 E e Φ) →
      ∀ E e Φ, rwp_pre s wp1 E e Φ -∗ rwp_pre s wp2 E e Φ)%I.
Proof.
iIntros "#H"; iIntros (E e1 Φ) "Hwp". rewrite /rwp_pre /rwp_step.
destruct (to_val e1) as [v|]; first done.
iIntros (σ1 n e_s) "Hσ". iMod ("Hwp" with "Hσ") as (b) "Hwp"; iModIntro.
iExists b. iApply (bi.laterN_wand with "[] Hwp"). iNext. iIntros "Hwp". iMod "Hwp" as "($ & Hwp)". iModIntro.
iIntros (e2 σ2 efs κ) "Hstep"; iMod ("Hwp" with "Hstep") as "(Hsrc & Hσ & Hwp & Hfork)".
iModIntro; iFrame "Hsrc Hσ". iSplitL "Hwp"; first by iApply "H".
iApply (@big_sepL_impl with "Hfork"); iIntros "!#" (k e _) "Hwp".
  by iApply "H".
Qed.

(* Uncurry [rwp_pre] and equip its type with an OFE structure *)
Definition rwp_pre' {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} (s : stuckness) :
(prodO (prodO (leibnizO SI coPset) (exprO SI Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
prodO (prodO (leibnizO SI coPset) (exprO SI Λ)) (val Λ -d> iProp Σ) → iProp Σ
:= curry3 ∘ rwp_pre s ∘ uncurry3.

Local Instance rwp_pre_mono' {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} s :
  BiMonoPred (rwp_pre' s).
Proof.
constructor.
- iIntros (wp1 wp2) "#H"; iIntros ([[E e1] Φ]); iRevert (E e1 Φ).
  iApply rwp_pre_mono. iIntros "!#" (E e Φ). iApply ("H" $! (E,e,Φ)).
- intros wp Hwp n [[E1 e1] Φ1] [[E2 e2] Φ2]
    [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=.
  rewrite /uncurry3 /rwp_pre /rwp_step. do 28 (f_equiv || done).
  by apply pair_ne.
Qed.

(* take the least fixpoint of the above definition *)
Definition rwp_def {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} (s : stuckness) (E : coPset)
  (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ
  := bi_least_fixpoint (rwp_pre' s) (E,e,Φ).
Definition rwp_aux {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} : seal (@rwp_def SI Σ A Λ _ _). by eexists. Qed.
Instance rwp' {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} : Rwp Λ (iProp Σ) stuckness := rwp_aux.(unseal).
Definition rwp_eq {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} : rwp = @rwp_def SI Σ A Λ _ _ := rwp_aux.(seal_eq).

(* take a rswp_step and afterwards, we prove an rwp *)
Definition rswp_def {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} (k: nat) (s : stuckness) (E : coPset) (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ
  := rswp_step k E s e (λ e2 efs, (rwp s E e2 Φ)
                        ∗ [∗ list] i ↦ ef ∈ efs, rwp s ⊤ ef ref_fork_post)%I.
Definition rswp_aux {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} : seal (@rswp_def SI Σ A Λ _ _). by eexists. Qed.
Instance rswp' {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} : Rswp Λ (iProp Σ) stuckness := rswp_aux.(unseal).
Definition rswp_eq {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ} : rswp = @rswp_def SI Σ A Λ _ _ := rswp_aux.(seal_eq).



Section rwp.
Context {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types a : A.
Implicit Types b : bool.

(* Weakest pre *)
Lemma rwp_unfold s E e Φ :
  RWP e @ s; E ⟨⟨ Φ ⟩⟩ ⊣⊢ rwp_pre s (rwp (PROP:=iProp Σ) s) E e Φ.
Proof. by rewrite rwp_eq /rwp_def least_fixpoint_unfold. Qed.


Lemma rwp_strong_ind s Ψ :
  (∀ n E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ E e))
  → ⊢ (□ (∀ e E Φ, rwp_pre s (λ E e Φ, Ψ E e Φ ∧ RWP e @ s; E ⟨⟨ Φ ⟩⟩) E e Φ -∗ Ψ E e Φ)
       → ∀ e E Φ, RWP e @ s; E ⟨⟨ Φ ⟩⟩ -∗ Ψ E e Φ)%I.
Proof.
  iIntros (HΨ). iIntros "#IH" (e E Φ) "H". rewrite rwp_eq.
  set (Ψ' := curry3 Ψ :
    prodO (prodO (leibnizO SI coPset) (exprO SI Λ)) (val Λ -d> iProp Σ) → iProp Σ).
  assert (NonExpansive Ψ').
  { intros n [[E1 e1] Φ1] [[E2 e2] Φ2]
      [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=. by apply HΨ. }
  iApply (least_fixpoint_strong_ind _ Ψ' with "[] H").
  iIntros "!#" ([[??] ?]) "H". by iApply "IH".
Qed.

Lemma rwp_ind s Ψ :
  (∀ n E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ E e))
  → ⊢ (□ (∀ e E Φ, rwp_pre s (λ E e Φ, Ψ E e Φ) E e Φ -∗ Ψ E e Φ)
       → ∀ e E Φ, RWP e @ s; E ⟨⟨ Φ ⟩⟩ -∗ Ψ E e Φ)%I.
Proof.
  iIntros (HΨ) "#H". iApply rwp_strong_ind. iIntros "!>" (e E Φ) "Hrwp".
  iApply "H". iApply (rwp_pre_mono with "[] Hrwp"). clear.
  iIntros "!>" (E e Φ) "[$ _]".
Qed.

Global Instance rwp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (rwp (PROP:=iProp Σ) s E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !rwp_eq. by apply (least_fixpoint_ne _), pair_ne, HΦ.
Qed.

Global Instance rwp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (rwp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply rwp_ne=>v; apply equiv_dist.
Qed.

Lemma rwp_value' s E Φ v : Φ v ⊢ RWP of_val v @ s; E ⟨⟨ Φ ⟩⟩.
Proof. iIntros "HΦ". rewrite rwp_unfold /rwp_pre to_of_val. iIntros (???) "($&$)". auto. Qed.
(*
Lemma rwp_value_inv' s E Φ v : RWP of_val v @ s; E ⟨⟨ Φ ⟩⟩ ={E}=∗ Φ v.
Proof. by rewrite rwp_unfold /rwp_pre to_of_val. Qed.
*)


Lemma rwp_strong_mono' s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  RWP e @ s1; E1 ⟨⟨ Φ ⟩⟩ -∗
  (∀ σ n a v, source_interp a ∗ ref_state_interp σ n ∗ Φ v ={E2}=∗
              source_interp a ∗ ref_state_interp σ n ∗ Ψ v) -∗
  RWP e @ s2; E2 ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (? HE) "H HΦ". iRevert (E2 Ψ HE) "HΦ"; iRevert (e E1 Φ) "H".
  iApply rwp_ind; first solve_proper.
  iIntros "!#" (e E1 Φ) "IH"; iIntros (E2 Ψ HE) "HΦ".
  rewrite !rwp_unfold /rwp_pre /rwp_step.
  destruct (to_val e) as [v|] eqn:?.
  { iIntros (???) "H".
    iSpecialize ("IH" with "[$]").
    iMod (fupd_mask_mono with "IH") as "(H1&H2&H)"; auto.
    by iApply ("HΦ" with "[$]"). }
  iIntros (σ1 n e_s) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod ("IH" with "[$]") as "IH". iModIntro. iDestruct "IH" as (b) "IH". iExists b.
  iNext. iMod "IH" as "[? IH]"; iModIntro.
  iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs κ Hstep).
  iSpecialize ("IH" with "[//]"). iMod "IH". iMod "Hclose" as "_". iModIntro.
  iDestruct "IH" as "($ & $ & IH & Hefs)". iSplitR "Hefs".
  - iApply ("IH" with "[//] HΦ").
  - iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
    iIntros "IH". iApply ("IH" with "[]"); auto.
Qed.

Lemma rwp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  RWP e @ s1; E1 ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ RWP e @ s2; E2 ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (??) "Hrwp H". iApply (rwp_strong_mono' with "[$]"); auto.
  iIntros (????) "($&$&HΦ)". by iApply "H".
Qed.

Lemma fupd_rwp s E e Φ : (|={E}=> RWP e @ s; E ⟨⟨ Φ ⟩⟩) ⊢ RWP e @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rwp_unfold /rwp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 n e_s) "HS". iMod "H". by iApply "H".
Qed.
Lemma fupd_rwp' s E e Φ : (∀ σ1 n a, source_interp a ∗ ref_state_interp σ1 n ={E}=∗
                                     source_interp a ∗ ref_state_interp σ1 n ∗
                                     RWP e @ s; E ⟨⟨ Φ ⟩⟩) ⊢ RWP e @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H".
  iEval (rewrite rwp_unfold /rwp_pre). destruct (to_val e) as [v|] eqn:Heq.
  { iIntros. iSpecialize ("H" with "[$]"). rewrite rwp_unfold /rwp_pre Heq.
    iMod "H" as "(H1&H2&Hwand)". by iMod ("Hwand" with "[$]") as "$". }
  iIntros (σ1 n e_s) "HS".
  iSpecialize ("H" with "[$]"). rewrite rwp_unfold /rwp_pre Heq.
  iMod "H" as "(H1&H2&Hwand)". by iMod ("Hwand" with "[$]") as "$".
Qed.
Lemma rwp_fupd s E e Φ : RWP e @ s; E ⟨⟨ v, |={E}=> Φ v ⟩⟩ ⊢ RWP e @ s; E ⟨⟨ Φ ⟩⟩.
Proof. iIntros "H". iApply (rwp_strong_mono s s E with "H"); auto. Qed.

Lemma rwp_fupd' s E e Φ : RWP e @ s; E ⟨⟨ v, ∀ σ1 n a, source_interp a ∗ ref_state_interp σ1 n ={E}=∗
                                                        source_interp a ∗ ref_state_interp σ1 n ∗ Φ v⟩⟩
                          ⊢ RWP e @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply (rwp_strong_mono' s s E with "H"); auto. iIntros (????) "(?&?&H)".
  by iMod ("H" with "[$]").
Qed.


(* TODO: We do not need StronglyAtomic for the definition with a single later but for the definition with a logical step. *)
Lemma rwp_atomic E1 E2 e s Φ `{!Atomic StronglyAtomic e} :
  (|={E1,E2}=> RWP e @ s; E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩) ⊢ RWP e @ s; E1 ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". rewrite !rwp_unfold /rwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iIntros. iMod ("H"). iMod ("H" with "[$]") as "($&$&$)". }
  iIntros (σ1 n e_s) "Hσ". iMod "H".
  iMod ("H" $! σ1 with "Hσ") as "H". iModIntro.
  iDestruct "H" as (b) "H". iExists b. iNext. iMod "H" as "[$ H]"; iModIntro.
  iIntros (e2 σ2 efs κ Hstep). iSpecialize ("H" with "[//]"). iMod "H".
  iDestruct "H" as "(Hsrc & Hσ & H & Hefs)".
  rewrite rwp_unfold /rwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
  - rewrite rwp_unfold /rwp_pre He2.
    destruct b.
    * iDestruct "Hsrc" as (??) "H'". iMod ("H" with "[$]") as "(Hsrc&$&H)".
      iFrame. iMod "H". iIntros "!>".
      iSplitL "Hsrc"; first eauto.
      iIntros (???) "(?&?) !>". iFrame.
    * iMod ("H" with "[$]") as "(Hsrc&$&H)".
      iFrame. iMod "H". iIntros "!>".
      iIntros (???) "(?&?) !>". iFrame.
  - specialize (atomic _ _ _ _ _ Hstep) as []; congruence.
Qed.

Lemma rwp_bind K `{!LanguageCtx K} s E e Φ :
  RWP e @ s; E ⟨⟨ v, RWP K (of_val v) @ s; E ⟨⟨ Φ ⟩⟩ ⟩⟩ ⊢ RWP K e @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  revert Φ. cut (∀ Φ', RWP e @ s; E ⟨⟨ Φ' ⟩⟩ -∗ ∀ Φ,
  (∀ v, Φ' v -∗ RWP K (of_val v) @ s; E ⟨⟨ Φ ⟩⟩) -∗ RWP K e @ s; E ⟨⟨ Φ ⟩⟩).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (e E Φ') "H". iApply rwp_strong_ind; first solve_proper.
  iIntros "!#" (e E1 Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /rwp_pre /rwp_step.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply fupd_rwp'.
    iIntros. iMod ("IH" with "[$]") as "($&$&H)".
      by iApply "HΦ". }
  rewrite rwp_unfold /rwp_pre /rwp_step fill_not_val //.
  iIntros (σ1 n a) "H". iMod ("IH" with "H") as "IH". iModIntro.
  iDestruct "IH" as (b) "IH". iExists b. iNext.
  iMod "IH" as "[% IH]"; iModIntro. iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 efs κ Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("IH" $! e2' σ2 efs with "[//]") as "($ & $ & IH & IHfork)". iIntros "!>".
  iSplitL "IH HΦ".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite bi.and_elim_r.
Qed.


Lemma rwp_bind_inv K `{!LanguageCtx K} s E e Φ :
  RWP K e @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ s; E ⟨⟨ v, RWP K (of_val v) @ s; E ⟨⟨ Φ ⟩⟩ ⟩⟩.
Proof.
  iIntros "H". remember (K e) as e' eqn:He'.
  iRevert (e He'). iRevert (e' E Φ) "H". iApply rwp_strong_ind; first solve_proper.
  iIntros "!#" (e' E1 Φ) "IH". iIntros (e ->).
  rewrite !rwp_unfold {2}/rwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iIntros (???) "($&$)". iModIntro. apply of_to_val in He as <-. rewrite !rwp_unfold.
    iApply (rwp_pre_mono with "[] IH"). by iIntros "!#" (E e Φ') "[_ ?]". }
  rewrite /rwp_pre fill_not_val //.
  iIntros (σ1 κs n) "Hσ". iMod ("IH" with "[$]") as (b) "IH". iModIntro.
  iExists b. iNext. iMod "IH" as "[% IH]"; iModIntro. iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs κ Hstep).
  iMod ("IH" $! (K e2) σ2 efs κ with "[]") as "(Hsrc & Hσ & IH & IHefs)"; eauto using fill_step.
  iModIntro. iFrame "Hsrc Hσ". iSplitR "IHefs".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite bi.and_elim_r.
Qed.

(** * Derived rules *)
Lemma rwp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → RWP e @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ s; E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (HΦ) "H"; iApply (rwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma rwp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → RWP e @ s1; E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ s2; E ⟨⟨ Φ ⟩⟩.
Proof. iIntros (?) "H". iApply (rwp_strong_mono with "H"); auto. Qed.
Lemma rwp_stuck_weaken s E e Φ :
  RWP e @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ E ?⟨⟨ Φ ⟩⟩.
Proof. apply rwp_stuck_mono. by destruct s. Qed.
Lemma rwp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → RWP e @ s; E1 ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ s; E2 ⟨⟨ Φ ⟩⟩.
Proof. iIntros (?) "H"; iApply (rwp_strong_mono with "H"); auto. Qed.
Global Instance rwp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (rwp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply rwp_mono. Qed.

Lemma rwp_value s E Φ e v : IntoVal e v → Φ v ⊢ RWP e @ s; E ⟨⟨ Φ ⟩⟩.
Proof. intros <-. by apply rwp_value'. Qed.
Lemma rwp_value_fupd' s E Φ v : (|={E}=> Φ v) ⊢ RWP of_val v @ s; E ⟨⟨ Φ ⟩⟩.
Proof. intros. by rewrite -rwp_fupd -rwp_value'. Qed.
Lemma rwp_value_fupd s E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ RWP e @ s; E ⟨⟨ Φ ⟩⟩.
Proof. intros. rewrite -rwp_fupd -rwp_value //. Qed.
(*
Lemma rwp_value_inv s E Φ e v : IntoVal e v → RWP e @ s; E ⟨⟨ Φ ⟩⟩ ={E}=∗ Φ v.
Proof. intros <-. by apply rwp_value_inv'. Qed.
*)

Lemma rwp_frame_l s E e Φ R : R ∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ s; E ⟨⟨ v, R ∗ Φ v ⟩⟩.
Proof. iIntros "[? H]". iApply (rwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma rwp_frame_r s E e Φ R : RWP e @ s; E ⟨⟨ Φ ⟩⟩ ∗ R ⊢ RWP e @ s; E ⟨⟨ v, Φ v ∗ R ⟩⟩.
Proof. iIntros "[H ?]". iApply (rwp_strong_mono with "H"); auto with iFrame. Qed.

Lemma rwp_wand s E e Φ Ψ :
  RWP e @ s; E ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v -∗ Ψ v) -∗ RWP e @ s; E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros "Hwp H". iApply (rwp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma rwp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ s; E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[H Hwp]". iApply (rwp_wand with "Hwp H"). Qed.
Lemma rwp_wand_r s E e Φ Ψ :
  RWP e @ s; E ⟨⟨ Φ ⟩⟩ ∗ (∀ v, Φ v -∗ Ψ v) ⊢ RWP e @ s; E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[Hwp H]". iApply (rwp_wand with "Hwp H"). Qed.
Lemma rwp_frame_wand_l s E e Q Φ :
  Q ∗ RWP e @ s; E ⟨⟨ v, Q -∗ Φ v ⟩⟩ -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "[HQ HRWP]". iApply (rwp_wand with "HRWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End rwp.


Section rswp.
Context {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types a : A.
Implicit Types b : bool.
Implicit Types k : nat.

(* Weakest pre *)
Lemma rswp_unfold k s E e Φ :
  RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ ⊣⊢ rswp_def k s E e Φ.
Proof. by rewrite rswp_eq. Qed.


Global Instance rswp_ne k s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (rswp (PROP:=iProp Σ) k s E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !rswp_eq /rswp_def /rswp_step.
  do 20 f_equiv. by rewrite HΦ.
Qed.

Global Instance rswp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (rwp (PROP:=iProp Σ) s E e).
Proof.
  apply _.
Qed.

Lemma rswp_strong_mono k s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  RSWP e at k @ s1; E1 ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ RSWP e at k @ s2; E2 ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (? HE); rewrite !rswp_eq /rswp_def /rswp_step.
  iIntros "H HΦ" (σ1 n a) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "[H' H]". iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs κ Hstep).
  iSpecialize ("H" with "[//]"). iMod "H". iMod "Hclose" as "_". iModIntro.
  iDestruct "H" as "($ & $ & H & Hefs)". iSplitR "Hefs".
  - iApply (rwp_strong_mono with "H"); auto.
  - iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k' ef _).
    iIntros "H"; iApply (rwp_strong_mono with "H"); auto.
Qed.


Lemma fupd_rswp k s E e Φ : (|={E}=> RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) ⊢ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rswp_eq /rswp_def /rswp_step. iIntros "H".
  iIntros (σ1 n a) "HS". iMod "H". by iApply "H".
Qed.
Lemma rswp_fupd k s E e Φ : RSWP e at k @ s; E ⟨⟨ v, |={E}=> Φ v ⟩⟩ ⊢ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof. iIntros "H". iApply (rswp_strong_mono k s s E with "H"); auto. Qed.


(* do not take a source step, end up with an rswp with no later budget *)
Lemma rwp_no_step E e s Φ:
  to_val e = None →
  (RSWP e at 0 @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RWP e @ s; E ⟨⟨ Φ ⟩⟩)%I.
Proof.
  rewrite rswp_eq rwp_unfold /rswp_def /rwp_pre /rswp_step /rwp_step.
  iIntros (He) "Hswp". rewrite He. iIntros (σ1 n a) "[Ha Hσ]".
  iMod ("Hswp" with "[$]") as "[$ Hswp]". iModIntro.
  iExists false. iModIntro. iIntros (e2 σ2 efs κ Hstep).
  by iMod ("Hswp" with "[//]") as "($ & $ & $)".
Qed.

(* take a source step, end up with an rswp with a budget of one later *)
Lemma rwp_take_step P E e s Φ:
  to_val e = None
  → ⊢ ((P -∗ RSWP e at 1 @ s; E ⟨⟨ Φ ⟩⟩) -∗ src_update E P -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩)%I.
Proof.
  rewrite rswp_eq rwp_unfold /rswp_def /rwp_pre /rswp_step /rwp_step.
  iIntros (He) "Hswp Hsrc". rewrite He. iIntros (σ1 n a) "[Ha Hσ]". rewrite /src_update.
  iMod ("Hsrc" with "Ha") as (a' Ha) "(Hsource_interp & P)". iMod ("Hswp" with "P [$]") as "Hswp".
  iMod "Hswp". iModIntro. iExists true. iNext. iMod "Hswp" as "[$ Hswp]"; iModIntro.
  iIntros (e2 σ2 efs κ Hstep'). iMod ("Hswp" with "[//]") as "(Hsrc & $ & Hrwp & $)".
  iModIntro; iFrame. iExists a'; iSplit; eauto.
Qed.

Lemma rwp_weaken' P E e s Φ:
  to_val e = None
  → ⊢ ((P -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩) -∗ weak_src_update E P -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩)%I.
Proof.
  rewrite rwp_unfold /rwp_pre /rwp_step.
  iIntros (He) "Hwp Hsrc". rewrite He. iIntros (σ1 n a) "[Ha Hσ]". rewrite /src_update.
  iMod ("Hsrc" with "Ha") as (a' Ha) "(Hsource_interp & P)". iMod ("Hwp" with "P [$Hsource_interp $Hσ]") as (b) "Hwp".
  iModIntro. destruct Ha as [a|].
  { iExists b. iFrame. }
  iExists true. destruct b; iNext.
  - iMod "Hwp" as "[$ Hwp]"; iModIntro.
    iIntros (e2 σ2 efs κ Hstep'); iMod ("Hwp" with "[//]") as "(Hstep & $ & $)"; iModIntro.
    iDestruct "Hstep" as (a' Hsteps) "S". iExists a'. iFrame. iPureIntro.
    eapply tc_l, tc_rtc_l; eauto.
  - iMod "Hwp" as "[$ Hwp]"; iModIntro.
    iIntros (e2 σ2 efs κ Hstep'); iMod ("Hwp" with "[//]") as "(Hstep & $ & $)"; iModIntro.
    iExists z. iFrame. iPureIntro.
    eapply tc_rtc_r; eauto. by apply tc_once.
Qed.

Lemma rwp_weaken P E e s Φ:
  to_val e = None
  → ⊢ ((P -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩) -∗ src_update E P -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩)%I.
Proof.
  intros H. rewrite src_update_weak_src_update. by apply rwp_weaken'.
Qed.

Lemma rswp_do_step k E e s Φ:
  ▷ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at (S k) @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rswp_eq /rswp_def /rswp_step.
  iIntros "H". iIntros (σ1 n a) "Hσ". iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
  simpl; do 2 iModIntro. iNext. iSpecialize ("H" with "Hσ"). by iMod "Hclose".
Qed.

(* TODO: We do not need StronglyAtomic for the definition with a single later but for the definition with a logical step. *)
Lemma rswp_atomic k E1 E2 e s Φ `{!Atomic StronglyAtomic e} :
  (|={E1,E2}=> RSWP e at k @ s; E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩) ⊢ RSWP e at k @ s; E1 ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". rewrite !rswp_eq /rswp_def /rswp_step.
  iIntros (σ1 n a) "Hσ". iMod "H".
  iMod ("H" $! σ1 with "Hσ") as "H". iModIntro.
  iApply (step_fupdN_wand with "H"); iIntros "[$ H]".
  iIntros (e2 σ2 efs κ Hstep). iSpecialize ("H" with "[//]"). iMod "H".
  iDestruct "H" as "(? & Hσ & H & Hefs)".
  rewrite rwp_unfold /rwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
  - rewrite rwp_unfold /rwp_pre He2. iDestruct ("H" with "[$]") as ">($&$&>$)". iFrame. eauto.
  - specialize (atomic _ _ _ _ _ Hstep) as []; congruence.
Qed.

Lemma rswp_bind K `{!LanguageCtx K} k s E e Φ :
  to_val e = None →
  RSWP e at k @ s; E ⟨⟨ v, RWP K (of_val v) @ s; E ⟨⟨ Φ ⟩⟩ ⟩⟩ ⊢ RSWP K e at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (He) "H". rewrite !rswp_eq /rswp_def /rswp_step.
  iIntros (σ1 n a) "Hσ". iMod ("H" with "Hσ") as "H".
  iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "[% H]". iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 efs κ Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//]") as "($ & $ & H & $)". iIntros "!>".
  by iApply rwp_bind.
Qed.


Lemma rswp_bind_inv K `{!LanguageCtx K} k s E e Φ :
  to_val e = None →
  RSWP K e at k @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ s; E ⟨⟨ v, RWP K (of_val v) @ s; E ⟨⟨ Φ ⟩⟩ ⟩⟩.
Proof.
  iIntros (He) "H". rewrite !rswp_eq /rswp_def /rswp_step.
  iIntros (σ1 n a) "Hσ". iMod ("H" with "Hσ") as "H".
  iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "[% H]". iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs κ Hstep).
  iMod ("H" $! (K e2) σ2 efs κ with "[]") as "($ & $ & H & $)"; eauto using fill_step.
  iModIntro. by iApply rwp_bind_inv.
Qed.

(** * Derived rules *)
Lemma rswp_mono k s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ s; E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros (HΦ) "H". iApply (rswp_strong_mono with "[H] []"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma rswp_stuck_mono k s1 s2 E e Φ :
  s1 ⊑ s2 → RSWP e at k @ s1; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ s2; E ⟨⟨ Φ ⟩⟩.
Proof. iIntros (?) "H". iApply (rswp_strong_mono with "H"); auto. Qed.
Lemma rswp_stuck_weaken k s E e Φ :
  RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ E ?⟨⟨ Φ ⟩⟩.
Proof. apply rswp_stuck_mono. by destruct s. Qed.
Lemma rswp_mask_mono k s E1 E2 e Φ : E1 ⊆ E2 → RSWP e at k @ s; E1 ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ s; E2 ⟨⟨ Φ ⟩⟩.
Proof. iIntros (?) "H"; iApply (rswp_strong_mono with "H"); auto. Qed.
Global Instance rswp_mono' k s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (rswp (PROP:=iProp Σ) k s E e).
Proof. by intros Φ Φ' ?; apply rswp_mono. Qed.

Lemma rswp_frame_l k s E e Φ R : R ∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ s; E ⟨⟨ v, R ∗ Φ v ⟩⟩.
Proof. iIntros "[? H]". iApply (rswp_strong_mono with "H"); auto with iFrame. Qed.
Lemma rswp_frame_r k s E e Φ R : RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ ∗ R ⊢ RSWP e at k @ s; E ⟨⟨ v, Φ v ∗ R ⟩⟩.
Proof. iIntros "[H ?]". iApply (rswp_strong_mono with "H"); auto with iFrame. Qed.

Lemma rswp_wand k s E e Φ Ψ :
  RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ -∗ (∀ v, Φ v -∗ Ψ v) -∗ RSWP e at k @ s; E ⟨⟨ Ψ ⟩⟩.
Proof.
  iIntros "Hwp H". iApply (rswp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma rswp_wand_l k s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ ⊢ RSWP e at k @ s; E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[H Hwp]". iApply (rswp_wand with "Hwp H"). Qed.
Lemma rswp_wand_r k s E e Φ Ψ :
  RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩ ∗ (∀ v, Φ v -∗ Ψ v) ⊢ RSWP e at k @ s; E ⟨⟨ Ψ ⟩⟩.
Proof. iIntros "[Hwp H]". iApply (rswp_wand with "Hwp H"). Qed.
Lemma rswp_frame_wand_l k s E e Q Φ :
  Q ∗ RSWP e at k @ s; E ⟨⟨ v, Q -∗ Φ v ⟩⟩ -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "[HQ HWP]". iApply (rswp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End rswp.


(** Proofmode class instances *)
Section proofmode_classes.
  Context {SI} {Σ: gFunctors SI} {A Λ} `{!source Σ A} `{!ref_irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_rwp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (RWP e @ s; E ⟨⟨ Φ ⟩⟩) (RWP e @ s; E ⟨⟨ Ψ ⟩⟩).
  Proof. rewrite /Frame=> HR. rewrite rwp_frame_l. apply rwp_mono, HR. Qed.

  Global Instance frame_rswp k p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) (RSWP e at k @ s; E ⟨⟨ Ψ ⟩⟩).
  Proof. rewrite /Frame=> HR. rewrite rswp_frame_l. apply rswp_mono, HR. Qed.

  Global Instance is_except_0_rwp s E e Φ : IsExcept0 (RWP e @ s; E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /IsExcept0 -{2}fupd_rwp -except_0_fupd -fupd_intro. Qed.

  Global Instance is_except_0_rswp k s E e Φ : IsExcept0 (RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /IsExcept0 -{2}fupd_rswp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_rwp p s E e P Φ :
    ElimModal True p false (|==> P) P (RWP e @ s; E ⟨⟨ Φ ⟩⟩) (RWP e @ s; E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_rwp.
  Qed.

   Global Instance elim_modal_bupd_rswp k p s E e P Φ :
    ElimModal True p false (|==> P) P (RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) (RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_rswp.
  Qed.

  Global Instance elim_modal_fupd_rwp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (RWP e @ s; E ⟨⟨ Φ ⟩⟩) (RWP e @ s; E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_rwp.
  Qed.

  Global Instance elim_modal_fupd_rswp k p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) (RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_rswp.
  Qed.

  Global Instance elim_modal_fupd_rwp_atomic s p E1 E2 e P Φ :
    Atomic StronglyAtomic e →
    ElimModal True p false (|={E1,E2}=> P) P
            (RWP e @ s; E1 ⟨⟨ Φ ⟩⟩) (RWP e @ s; E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩)%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r rwp_atomic.
  Qed.

  Global Instance elim_modal_fupd_rswp_atomic k s p E1 E2 e P Φ :
    Atomic StronglyAtomic e →
    ElimModal True p false (|={E1,E2}=> P) P
            (RSWP e at k @ s; E1 ⟨⟨ Φ ⟩⟩) (RSWP e at k @ s; E2 ⟨⟨ v, |={E2,E1}=> Φ v ⟩⟩)%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r rswp_atomic.
  Qed.


  Global Instance add_modal_fupd_rwp s E e P Φ :
    AddModal (|={E}=> P) P (RWP e @ s; E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_rwp. Qed.

  Global Instance add_modal_fupd_rswp k s E e P Φ :
    AddModal (|={E}=> P) P (RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_rswp. Qed.


  Global Instance elim_acc_wp {X} s E1 E2 α β γ e Φ :
    Atomic StronglyAtomic e →
    ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1)
            α β γ (RWP e @ s; E1 ⟨⟨ Φ ⟩⟩)
            (λ x, RWP e @ s; E2 ⟨⟨ v, |={E2}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (rwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_rswp {X} k s E1 E2 α β γ e Φ :
    Atomic StronglyAtomic e →
    ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1)
            α β γ (RSWP e at k @ s; E1 ⟨⟨ Φ ⟩⟩)
            (λ x, RSWP e at k @ s; E2 ⟨⟨ v, |={E2}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (rswp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) (fupd E E) (fupd E E)
            α β γ (RWP e @ s; E ⟨⟨ Φ ⟩⟩)
            (λ x, RWP e @ s; E ⟨⟨ v, |={E}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I.
  Proof.
    rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply rwp_fupd.
    iApply (rwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_swp_nonatomic {X} k E α β γ e s Φ :
    ElimAcc (X:=X) (fupd E E) (fupd E E)
            α β γ (RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩)
            (λ x, RSWP e at k @ s; E ⟨⟨ v, |={E}=> β x ∗ (γ x -∗? Φ v) ⟩⟩)%I.
  Proof.
    rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply rswp_fupd.
    iApply (rswp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
