From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export logical_step.
From iris.program_logic Require Export language.
From iris.bi Require Export weakestpre.
From iris.proofmode Require Import base tactics classes.
Set Default Proof Using "Type".
Import uPred.

Section eventually.

  Context {SI} {PROP: sbi SI} `{FU: BiFUpd SI PROP}.


  Global Instance big_later_elim p (P Q: PROP):
    ElimModal True p false (⧍ P) P (⧍ Q) Q.
  Proof.
    iIntros (_) "(P & HPQ)". iPoseProof (intuitionistically_if_elim with "P") as "P".
    iDestruct "P" as (n) "P". iExists n. iNext. by iApply "HPQ".
  Qed.

  Global Instance plain_big_later `{BP: BiPlainly SI PROP} (P: PROP): Plain P → Plain (⧍ P).
  Proof. apply _. Qed.

  Global Instance plain_big_laterN `{BP: BiPlainly SI PROP} (P: PROP) n: Plain P → Plain (⧍^n P).
  Proof. intros HP. induction n; simpl; apply _. Qed.

  Lemma eventuallyN_plain `{BP: BiPlainly SI PROP} `{@BiFUpdPlainly SI PROP FU BP} (P : PROP) n E:
    Plain P → (<E>_n P) ⊢ |={E}=> ▷^(S n) P.
  Proof.
    iIntros (HP) "H". iInduction n as [ | n] "IH".
    - iMod "H". by iModIntro.
    - simpl. iSpecialize ("IH" with "H").
      iMod "IH".
      iPoseProof (fupd_trans with "IH") as "IH".
      iPoseProof (fupd_plain_later with "IH") as "IH".
      iMod "IH". iModIntro.
      iNext. by iApply except_0_later.
  Qed.

  Lemma eventually_plain `{BP: BiPlainly SI PROP} `{@BiFUpdPlainly SI PROP FU BP} (P : PROP) E:
    Plain P → (<E> P) ⊢ |={E}=> ⧍ P.
  Proof.
    intros HP. iIntros "H".
    unfold eventually. iMod "H". iDestruct "H" as (n) "H".
    iDestruct (eventuallyN_plain _ with "H") as "H".
    iMod "H". iModIntro. eauto.
  Qed.

  Existing Instance elim_eventuallyN.
  Lemma lstep_fupd_plain `{BP: BiPlainly SI PROP} `{@BiFUpdPlainly SI PROP FU BP} (P : PROP):
    Plain P → ((>={⊤}=={⊤}=> P) ⊢ |={⊤}=> ⧍ P)%I.
  Proof.
    iIntros (HP) "H".
    iApply (fupd_plain_mask _ ∅). iMod "H".
    iApply eventually_plain.
    iApply eventually_fupd_right.
    iMod "H" as (n) "H". iApply (eventuallyN_eventually (n)).  iMod "H".
    by iApply (fupd_plain_mask _ ⊤).
  Qed.

  Lemma lstep_fupdN_plain `{BP: BiPlainly SI PROP} `{@BiFUpdPlainly SI PROP FU BP} (P : PROP) n:
    Plain P → ((>={⊤}=={⊤}=>^n P) ⊢ |={⊤}=> ⧍^n P)%I.
  Proof.
    intros HP. iIntros "H". iInduction n as [|n] "IH"; simpl.
    - by iModIntro.
    - iAssert (>={⊤}=={⊤}=> ⧍^n P)%I with "[H]" as "H".
      { do 2 iMod "H". iModIntro. iDestruct "H" as (n') "H".
        iApply (eventuallyN_eventually (n' )). iMod "H".
        iMod "H". by iSpecialize ("IH" with "H").
      }
      iApply (lstep_fupd_plain with "H").
  Qed.
End eventually.


Class irisG (Λ : language) {SI} (Σ : gFunctors SI) := IrisG {
  iris_invG :> invG Σ;

  (** The state interpretation is an invariant that should hold in between each
  step of reduction. Here [Λstate] is the global state, [list Λobservation] are
  the remaining observations, and [nat] is the number of forked-off threads
  (not the total number of threads, which is one higher because there is always
  a main thread). *)
  state_interp : state Λ → list (observation Λ) → nat → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val Λ → iProp Σ;
}.
Global Opaque iris_invG.

Definition wp_pre {SI} {Σ: gFunctors SI} `{!irisG Λ Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iProp Σ) -d> iProp Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iProp Σ) -d> iProp Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 κ κs n,
    state_interp σ1 (κ ++ κs) n -∗ >={E}=={∅}=> (
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ |={∅,∅,E}▷=> (
         state_interp σ2 κs (length efs + n) ∗
         wp E e2 Φ ∗
         [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post))
  end%I.

Local Instance wp_pre_contractive {SI} {Σ: gFunctors SI} `{!irisG Λ Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
  do 20 f_equiv. f_contractive. intros β Hβ. do 3 f_equiv. apply (Hwp β Hβ).
  do 3 f_equiv. apply (Hwp β Hβ).
Qed.

Definition wp_def {SI} {Σ: gFunctors SI} `{!irisG Λ Σ} (s : stuckness) :
  coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ := fixpoint (wp_pre s).
Definition wp_aux {SI} {Σ: gFunctors SI} `{!irisG Λ Σ} : seal (@wp_def SI Σ Λ _). by eexists. Qed.
Instance wp' {SI} {Σ: gFunctors SI} `{!irisG Λ Σ} : Wp Λ (iProp Σ) stuckness := wp_aux.(unseal).
Definition wp_eq {SI} {Σ: gFunctors SI}  `{!irisG Λ Σ} : wp = @wp_def SI Σ Λ  _ := wp_aux.(seal_eq).

Definition swp_def {SI} {Σ: gFunctors SI} `{!irisG Λ Σ} (k: nat) (s : stuckness) (E: coPset)  (e1: expr Λ) (Φ: val Λ → iProp Σ) : iProp Σ :=
  (∀ σ1 κ κs n,
    state_interp σ1 (κ ++ κs) n -∗ >={E}=={∅}=>_k (
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ |={∅,∅,E}▷=> (
         state_interp σ2 κs (length efs + n) ∗
         WP e2 @ s; E {{ v, Φ v }} ∗
         [∗ list] i ↦ ef ∈ efs, WP ef @ s; ⊤ {{ v, fork_post v }})))%I.
Definition swp_aux {SI} {Σ: gFunctors SI} `{!irisG Λ Σ} : seal (@swp_def SI Σ Λ _). by eexists. Qed.
Instance swp' {SI} {Σ: gFunctors SI} `{!irisG Λ Σ} : Swp Λ (iProp Σ) stuckness := swp_aux.(unseal).
Definition swp_eq {SI} {Σ: gFunctors SI}  `{!irisG Λ Σ} : swp = @swp_def SI Σ Λ  _ :=
  swp_aux.(seal_eq).

Section wp.
Context {SI} {Σ: gFunctors SI}  `{!irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre s (wp (PROP:=iProp Σ)  s) E e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre s)). Qed.

Lemma swp_unfold k s E e Φ :
  SWP e at k @ s; E {{ Φ }} ⊣⊢ swp_def k s E e Φ.
Proof. by rewrite swp_eq. Qed.


Global Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (index_lt_wf SI n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 20 f_equiv. f_contractive. intros β Hβ.
  do 3 f_equiv. eapply IH; eauto.
  intros v. eapply dist_le; eauto.
Qed.
Global Instance wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Global Instance swp_ne k s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (swp (PROP:=iProp Σ) k s E e).
Proof.
  intros Φ Ψ HΦ. rewrite !swp_unfold /swp_def.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 19 f_equiv. f_contractive. intros β Hβ.
  do 3 f_equiv. eapply wp_ne.
  intros v. eapply dist_le; eauto.
Qed.
Global Instance swp_proper k s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (swp k (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply swp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value' s E Φ v : Φ v ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre to_of_val. auto. Qed.
Lemma wp_value_inv' s E Φ v : WP of_val v @ s; E {{ Φ }} ={E}=∗ Φ v.
Proof. by rewrite wp_unfold /wp_pre to_of_val. Qed.

Section gstep.
Local Existing Instance elim_gstep.
Lemma wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 κ κs n) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[? H]".
  iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
  iSpecialize ("H" with "[//]"). iMod "H". iModIntro. iNext. iMod "H". iMod "Hclose" as "_".
  iModIntro.
  iDestruct "H" as "(Hσ & H & Hefs)". iFrame "Hσ". iSplitR "Hefs".
  - iApply ("IH" with "[//] H HΦ").
  - iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
    iIntros "H". iApply ("IH" with "[] H"); auto.
Qed.

Lemma fupd_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 κ κs n) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.


Lemma wp_atomic E1 E2 e s Φ `{!Atomic StronglyAtomic e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 κ κs n) "Hσ". iMod "H".
  iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iIntros (e2 σ2 efs Hstep). iSpecialize ("H" with "[//]"). iMod "H". iModIntro. iNext.
  iMod "H" as "(Hσ & H & Hefs)".
  + rewrite wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    * rewrite wp_unfold /wp_pre He2. iDestruct "H" as ">> $". by iFrame.
    * specialize (atomic _ _ _ _ _ Hstep) as []; congruence.
Qed.


Local Existing Instance elim_gstepN.
Lemma swp_strong_mono k1 k2 s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 → k1 ≤ k2 →
  SWP e at k1 @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ SWP e at k2 @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE Hk) "H HΦ". rewrite !swp_unfold /swp_def.
  iIntros (σ1 κ κs n) "S". iMod (fupd_intro_mask' E2 E1) as "E"; eauto.
  iSpecialize ("H" with "S"). iApply (gstepN_mono _ _ _ _ _ _ Hk).
  iMod ("H") as "[? H]".
  iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
  iSpecialize ("H" with "[//]"). iMod "H". iModIntro. iNext. iMod "H". iMod "E" as "_".
  iModIntro.
  iDestruct "H" as "(Hσ & H & Hefs)". iFrame "Hσ". iSplitR "Hefs".
  - iApply (wp_strong_mono with "H"); eauto.
  - iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
    iIntros "H". iApply (wp_strong_mono with "H"); eauto.
Qed.

Lemma fupd_swp k s E e Φ : (|={E}=> SWP e at k @ s; E {{ Φ }})%I ⊢ SWP e at k @ s; E {{ Φ }}.
Proof.
  rewrite swp_unfold /swp_def. iIntros "SWP".
  iIntros (σ1 κ κs n) "S". iMod "SWP".
  iApply "SWP"; iFrame.
Qed.

Lemma swp_fupd k s E e Φ : SWP e at k @ s; E {{ v, |={E}=> Φ v}} ⊢ SWP e at k @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (swp_strong_mono k k s s E with "H"); auto. Qed.


Lemma swp_atomic k E1 E2 e s Φ `{!Atomic StronglyAtomic e} :
  (|={E1, E2}=> SWP e at k @ s; E2 {{ v, |={E2, E1}=> Φ v}})%I ⊢ SWP e at k @ s; E1 {{ Φ }}.
Proof.
  rewrite !swp_unfold /swp_def. iIntros "SWP". iIntros (σ1 κ κs n) "S".
  iMod "SWP". iMod ("SWP" with "S") as "[$ SWP]".
  iIntros (e2 σ2 efs Hstep). iMod ("SWP" with "[//]") as "SWP". iModIntro. iNext.
  iMod "SWP" as "($& SWP & $)". destruct (atomic _ _ _ _ _ Hstep) as [v Hv].
  rewrite !wp_unfold /wp_pre Hv. do 2 iMod "SWP". by do 2 iModIntro.
Qed.

Lemma swp_wp k s E e Φ : to_val e = None →
   SWP e at k @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ }}%I.
Proof.
  intros H; rewrite swp_unfold wp_unfold /swp_def /wp_pre H.
  iIntros "SWP". iIntros (σ1 κ κs n) "S".
  iApply gstepN_gstep. iMod ("SWP" with "S") as "$".
Qed.

Lemma swp_step k E e s Φ : ▷ SWP e at k @ s; E {{ Φ }} ⊢ SWP e at S k @ s; E {{ Φ }}.
Proof.
  rewrite !swp_unfold /swp_def. iIntros "SWP". iIntros (σ1 κ κs n) "S".
  iMod (fupd_intro_mask') as "M". apply empty_subseteq.
  do 3 iModIntro. iMod "M" as "_".
  iMod ("SWP" with "S") as "$".
Qed.


Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val //.
  iIntros (σ1 κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]"; iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//]") as "H". iIntros "!> !>".
  iMod "H" as "(Hσ & H & Hefs)".
  iModIntro. iFrame "Hσ Hefs". by iApply "IH".
Qed.

Lemma swp_bind k K `{!LanguageCtx K} s E e Φ : to_val e = None →
  SWP e at k @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ SWP K e at k @ s; E {{ Φ }}.
Proof.
  iIntros (H) "H". rewrite !swp_unfold /swp_def.
  iIntros (σ1 κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]"; iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//]") as "H". iIntros "!> !>".
  iMod "H" as "(Hσ & H & Hefs)".
  iModIntro. iFrame "Hσ Hefs". by iApply wp_bind.
Qed.


Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1 κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]"; iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! (K e2) σ2 efs with "[]") as "H"; [by eauto using fill_step|].
  iIntros "!> !>". iMod "H" as "(Hσ & H & Hefs)".
  iModIntro. iFrame "Hσ Hefs". by iApply "IH".
Qed.

Lemma swp_bind_inv K `{!LanguageCtx K} k s E e Φ : to_val e = None →
  SWP K e at k @ s; E {{ Φ }} ⊢ SWP e at k @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros (H) "H". rewrite !swp_unfold /swp_def.
  iIntros (σ1 κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]"; iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! (K e2) σ2 efs with "[]") as "H"; [by eauto using fill_step|].
  iIntros "!> !>". iMod "H" as "(Hσ & H & Hefs)".
  iModIntro. iFrame "Hσ Hefs". by iApply wp_bind_inv.
Qed.

(** * Derived rules *)
Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. by apply wp_value'. Qed.
Lemma wp_value_fupd' s E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd s E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.
Lemma wp_value_inv s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ={E}=∗ Φ v.
Proof. intros <-. by apply wp_value_inv'. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

End gstep.

Existing Instance elim_eventuallyN.
Lemma wp_step_fupd s E1 E2 e P Φ :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 κ κs n) "Hσ". iMod "HR".
  iMod ("H" with "[$]") as ">H". iDestruct "H" as (n1) "H".
  iApply (gstepN_gstep _ _ _ (S n1)). iApply gstepN_later; first eauto. iNext.
  iModIntro. iMod "H". iMod "H" as "[$ H]". iModIntro.
  iIntros(e2 σ2 efs Hstep).
  iSpecialize ("H" $! e2 σ2 efs with "[% //]"). iMod "H". iModIntro. iNext.
  iMod "H" as "(Hσ & H & Hefs)".
  iMod "HR". iModIntro. iFrame "Hσ Hefs".
  iApply (wp_strong_mono s s E2 with "H"); [done..|].
  iIntros (v) "H". by iApply "H".
Qed.


Lemma wp_step_gstep s E e P Φ :
  to_val e = None →
  (>={E}=={E}=> P) -∗ WP e @ s; ∅ {{ v, P ={E}=∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (->) "HR H".
  iIntros (σ1 κ κs n) "Hσ". iMod "HR". iMod "HR". iDestruct "HR" as (n1) "HR".
  iMod ("H" with "[$]") as ">H". iDestruct "H" as (n2) "H".
  iApply (gstepN_gstep _ _ _ (n1 + n2)).
  iModIntro. iApply eventuallyN_compose.
  iMod "HR". iMod "H". iMod "H" as "[$ H]". iMod "HR".
  iMod (fupd_intro_mask' _ ∅) as "Hcnt"; first set_solver.
  iModIntro. iIntros(e2 σ2 efs Hstep).
  iSpecialize ("H" $! e2 σ2 efs with "[% //]"). iMod "H". iModIntro. iNext.
  iMod "H" as "($ & H & $)". iMod "Hcnt". iModIntro.
  iApply (wp_strong_mono s s ∅ with "H"); [done | set_solver|].
  iIntros (v) "Hv". iApply ("Hv" with "HR").
Qed.

Lemma swp_step_fupd k s E1 E2 e P Φ :
  E2 ⊆ E1 →
  (|={E1,E2}▷=> P) -∗ SWP e at k @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ SWP e at k @ s; E1 {{ Φ }}.
Proof.
  rewrite !swp_unfold /swp_def. iIntros (?) "HR H".
  iIntros (σ1 κ κs n) "Hσ". iMod "HR". iMod ("H" with "[$]") as "H". iModIntro.
  iMod "H". iMod "H" as "[$ H]". iModIntro. iIntros(e2 σ2 efs Hstep).
  iSpecialize ("H" $! e2 σ2 efs with "[% //]"). iMod "H". iModIntro. iNext.
  iMod "H" as "(Hσ & H & Hefs)".
  iMod "HR". iModIntro. iFrame "Hσ Hefs".
  iApply (wp_strong_mono s s E2 with "H"); [done..|].
  iIntros (v) "H". by iApply "H".
Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1,E2}▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  to_val e = None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  to_val e = None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand_l s E e Q Φ :
  Q ∗ WP e @ s; E {{ v, Q -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

(* we can pull out a logical step from a WP when switching to the SWP *)
Local Existing Instance elim_fupd_step.
Instance elim_fupd_stepN b E P Q n:
  ElimModal True b false (|={E, E}▷=>^n P)%I P (|={E, E}▷=>^n Q)%I Q.
Proof.
  iIntros (_) "(P & HPQ)". iPoseProof (intuitionistically_if_elim with "P") as "P".
  iInduction n as [ |n] "IH"; cbn.
  - by iApply "HPQ".
  - iMod "P". fold Nat.iter. by iApply ("IH" with "HPQ").
Qed.
Lemma fupd_fupd_step E P n :
 (|={E}=> |={E, E}▷=>^n P)%I -∗ |={E, E}▷=>^n (|={E}=> P)%I.
Proof.
  iIntros "H". iInduction n as [ | n] "IH"; cbn.
  iApply "H".
  iMod "H".
  iApply "IH". iMod "H". iModIntro. iApply "H".
Qed.

Lemma fupd_step_fupd E P n :
 (|={E, E}▷=>^n |={E}=> P)%I -∗ (|={E}=> |={E, E}▷=>^n P)%I .
Proof.
  iIntros "H". iInduction n as [ | n] "IH". cbn.
  iApply "H". iApply "IH". iModIntro.
  iMod "H". iModIntro. iNext. iApply fupd_fupd_step.
  iMod "H". iApply "IH". iApply "H".
Qed.

Lemma swp_wp_lstep k2 s E e Φ : to_val e = None →
  (>={E}=={E}=> SWP e at k2 @ s ; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}%I.
Proof.
  intros H; rewrite wp_unfold swp_unfold /wp_pre /swp_def H.
  iIntros "WP". iIntros (σ1 κ κs n) "S".
  do 2 iMod "WP". iDestruct ("WP") as (k1) "WP".
  iApply (lstepN_lstep _ _ (k1 + (1 + k2))). iModIntro. iApply eventuallyN_compose.
  iMod ("WP"). iApply eventuallyN_compose. iMod "WP".
  iMod ("WP" with "S") as "WP".
  do 4 iModIntro. do 2 iMod "WP". iModIntro.
  iApply "WP".
Qed.
End wp.


Section swp.
  Context {SI} {Σ: gFunctors SI}  `{!irisG Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Variable (k: nat).

  Lemma swp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → SWP e at k @ s; E {{ Φ }} ⊢ SWP e at k @ s; E {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (swp_strong_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.
  Lemma swp_stuck_mono s1 s2 E e Φ :
    s1 ⊑ s2 → SWP e at k @ s1; E {{ Φ }} ⊢ SWP e at k @ s2; E {{ Φ }}.
  Proof. iIntros (?) "H". iApply (swp_strong_mono with "H"); auto. Qed.
  Lemma swp_stuck_weaken s E e Φ :
    SWP e at k @ s; E {{ Φ }} ⊢ SWP e at k @ E ?{{ Φ }}.
  Proof. apply swp_stuck_mono. by destruct s. Qed.
  Lemma swp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → SWP e at k @ s; E1 {{ Φ }} ⊢ SWP e at k @ s; E2 {{ Φ }}.
  Proof. iIntros (?) "H"; iApply (swp_strong_mono with "H"); auto. Qed.
  Global Instance swp_mono' s E e :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (swp (PROP:=iProp Σ) k s E e).
  Proof. by intros Φ Φ' ?; apply swp_mono. Qed.

  Lemma swp_frame_l s E e Φ R : R ∗ SWP e at k @ s; E {{ Φ }} ⊢ SWP e at k @ s; E {{ v, R ∗ Φ v }}.
  Proof. iIntros "[? H]". iApply (swp_strong_mono with "H"); auto with iFrame. Qed.
  Lemma swp_frame_r s E e Φ R : SWP e at k @ s; E {{ Φ }} ∗ R ⊢ SWP e at k @ s; E {{ v, Φ v ∗ R }}.
  Proof. iIntros "[H ?]". iApply (swp_strong_mono with "H"); auto with iFrame. Qed.

  Lemma swp_frame_step_l s E1 E2 e Φ R :
    to_val e = None → E2 ⊆ E1 →
    (|={E1,E2}▷=> R) ∗ SWP e at k @ s; E2 {{ Φ }} ⊢ SWP e at k @ s; E1 {{ v, R ∗ Φ v }}.
  Proof.
    iIntros (??) "[Hu Hwp]". iApply (swp_step_fupd with "Hu"); try done.
    iApply (swp_mono with "Hwp"). by iIntros (?) "$$".
  Qed.
  Lemma swp_frame_step_r s E1 E2 e Φ R :
    to_val e = None → E2 ⊆ E1 →
    SWP e at k @ s; E2 {{ Φ }} ∗ (|={E1,E2}▷=> R) ⊢ SWP e at k @ s; E1 {{ v, Φ v ∗ R }}.
  Proof.
    rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply swp_frame_step_l.
  Qed.
  Lemma swp_frame_step_l' s E e Φ R :
    to_val e = None → ▷ R ∗ SWP e at k @ s; E {{ Φ }} ⊢ SWP e at k @ s; E {{ v, R ∗ Φ v }}.
  Proof. iIntros (?) "[??]". iApply (swp_frame_step_l s E E); try iFrame; eauto. Qed.
  Lemma swp_frame_step_r' s E e Φ R :
    to_val e = None → SWP e at k @ s; E {{ Φ }} ∗ ▷ R ⊢ SWP e at k @ s; E {{ v, Φ v ∗ R }}.
  Proof. iIntros (?) "[??]". iApply (swp_frame_step_r s E E); try iFrame; eauto. Qed.

  Lemma swp_wand s E e Φ Ψ :
    SWP e at k @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ SWP e at k @ s; E {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (swp_strong_mono with "Hwp"); auto.
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma swp_wand_l s E e Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ SWP e at k @ s; E {{ Φ }} ⊢ SWP e at k @ s; E {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (swp_wand with "Hwp H"). Qed.
  Lemma swp_wand_r s E e Φ Ψ :
    SWP e at k @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ SWP e at k @ s; E {{ Ψ }}.
  Proof. iIntros "[Hwp H]". iApply (swp_wand with "Hwp H"). Qed.
  Lemma swp_frame_wand_l s E e Q Φ :
    Q ∗ SWP e at k @ s; E {{ v, Q -∗ Φ v }} -∗ SWP e at k @ s; E {{ Φ }}.
  Proof.
    iIntros "[HQ HWP]". iApply (swp_wand with "HWP").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

  Lemma swp_finish E e s Φ : SWP e at 0%nat @ s; E {{ Φ }} ⊢ SWP e at 0%nat @ s; E {{ Φ }}.
  Proof. eauto. Qed.
End swp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context {SI} {Σ: gFunctors SI} `{!irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance frame_swp k p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (SWP e at k @ s; E {{ Φ }}) (SWP e at k @ s; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite swp_frame_l. apply swp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance is_except_0_swp k s E e Φ : IsExcept0 (SWP e at k @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_swp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

   Global Instance elim_modal_bupd_swp k p s E e P Φ :
    ElimModal True p false (|==> P) P (SWP e at k @ s; E {{ Φ }}) (SWP e at k @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_swp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_swp k p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (SWP e at k @ s; E {{ Φ }}) (SWP e at k @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_swp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic s p E1 E2 e P Φ :
    Atomic StronglyAtomic e →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r wp_atomic.
  Qed.

  Global Instance elim_modal_fupd_swp_atomic k s p E1 E2 e P Φ :
    Atomic StronglyAtomic e →
    ElimModal True p false (|={E1,E2}=> P) P
            (SWP e at k @ s; E1 {{ Φ }}) (SWP e at k @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r swp_atomic.
  Qed.


  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance add_modal_fupd_swp k s E e P Φ :
    AddModal (|={E}=> P) P (SWP e at k @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_swp. Qed.


  Global Instance elim_acc_wp {X} s E1 E2 α β γ e Φ :
    Atomic StronglyAtomic e →
    ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_swp {X} k s E1 E2 α β γ e Φ :
    Atomic StronglyAtomic e →
    ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1)
            α β γ (SWP e at k @ s; E1 {{ Φ }})
            (λ x, SWP e at k @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (swp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_swp_nonatomic {X} k E α β γ e s Φ :
    ElimAcc (X:=X) (fupd E E) (fupd E E)
            α β γ (SWP e at k @ s; E {{ Φ }})
            (λ x, SWP e at k @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply swp_fupd.
    iApply (swp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.

