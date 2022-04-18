From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(** This file contains the adequacy statements of the Iris program logic. First we prove a number of auxilary results. *)

Lemma lstep_fupd_soundness {SI} {Σ: gFunctors SI} `{TransfiniteIndex SI} `{!invPreG Σ} φ n:
  (∀ Hinv : invG Σ, @sbi_emp_valid SI (iPropSI Σ) (>={⊤}=={⊤}=>^n ⌜φ⌝)%I) → φ.
Proof.
  intros Hiter. assert ((True ⊢ ⧍^n ⌜φ⌝ : iProp Σ)%I → φ) as Hlater;
                  last (apply Hlater).
  { intros H1. 
    eapply pure_soundness, uPred_primitive.big_laterN_soundness, H1. 
  }
  apply (fupd_plain_soundness ⊤ ⊤ _)=> Hinv.
  iPoseProof (Hiter Hinv) as "H". by iApply lstep_fupdN_plain.
Qed.

Section adequacy.
Context {SI} {Σ: gFunctors SI} `{!irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).



Notation wptp s t := ([∗ list] ef ∈ t, WP ef @ s; ⊤ {{ fork_post }})%I.

Existing Instance elim_eventuallyN.
Existing Instance elim_gstep. 
Lemma wp_step s e1 σ1 κ κs e2 σ2 efs m Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 (κ ++ κs) m -∗ WP e1 @ s; ⊤ {{ Φ }} -∗ >={⊤}=={⊤}=>
  (state_interp σ2 κs (length efs + m) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s efs).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 with "Hσ") as "H". iMod "H". 
  iDestruct "H" as (n) "H". 
  iApply (gstepN_gstep _ _ _ (S n)). iModIntro. 
  replace (S n) with (n + 1) by lia. iApply eventuallyN_compose. iMod "H". 
  iMod "H" as "[% H]". iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  by iIntros "!> !> !> !>".
Qed.

Lemma wptp_step s e1 t1 t2 κ κs σ1 σ2 Φ :
  step (e1 :: t1,σ1) κ (t2, σ2) →
  state_interp σ1 (κ ++ κs) (length t1) -∗ WP e1 @ s; ⊤ {{ Φ }} -∗ wptp s t1 -∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  >={⊤}=={⊤}=> (state_interp σ2 κs (pred (length t2)) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2').
Proof.
  iIntros (Hstep) "Hσ He Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iSplitR; first by eauto.
    iMod (wp_step with "Hσ He") as "(Hσ & He2 & Hefs)"; first done.
    rewrite Nat.add_comm app_length. iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iMod (wp_step with "Hσ He1") as "(Hσ & He2 & Hefs)"; first done.
    rewrite !app_length /= !app_length.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by omega. iFrame.
Qed.

Lemma wptp_steps s n e1 t1 κs κs' t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗ WP e1 @ s; ⊤ {{ Φ }} -∗ wptp s t1
  -∗ (>={⊤}=={⊤}=>^n
  (∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 κs' (pred (length t2)) ∗
    WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2')). 
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "???"; iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "Hσ He Ht". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iPoseProof (wptp_step with "Hσ He Ht")  as (e1' t1'' ?) ">(Hσ & He & Ht)"; first eauto. 
  simplify_eq. by iApply (IH with "Hσ He Ht").
Qed.

Lemma wp_safe κs m e σ Φ :
  state_interp σ κs m -∗
  WP e {{ Φ }} ={⊤}=∗ ⧍ ⌜is_Some (to_val e) ∨ reducible e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ [] κs with "Hσ").
  iAssert (|={⊤,∅}=> ⧍ ⌜reducible e σ⌝)%I with "[H]" as "H".
  { iMod "H". iMod (eventually_plain with "[H]") as "H"; last by iModIntro. apply _.
    iMod "H" as (n) "H". iModIntro. iExists (S n). replace (S n) with (n + 1)by lia. iApply eventuallyN_compose. 
    iMod "H". by iMod "H" as "[$ _]". } 
  iMod (fupd_plain_mask with "H") as "H"; eauto.
  iModIntro. iMod "H" as "%". by iRight.
Qed.

Lemma list_big_later {X} (L: list X) (P: X → iProp Σ): ([∗ list] x ∈ L, ⧍ P x) ⊢ ⧍ [∗ list] x ∈ L, P x.
Proof.
  iInduction L as [|L] "IH"; simpl.
  - iIntros "_". by iExists 0.
  - iIntros "[H1 H2]". iSpecialize ("IH" with "H2").
    iDestruct "H1" as (n1) "H1". iDestruct "IH" as (n2) "IH".
    iExists (n1 + n2). iNext. iFrame.
Qed.

Lemma big_later_eventually P E: ⧍ P -∗ <E> P.
Proof.
  iDestruct 1 as (n) "H". iExists n. 
  iModIntro. iInduction n as [ | n] "IH"; simpl; eauto. 
  iModIntro. iNext. iModIntro. by iApply "IH". 
Qed.

Existing Instance elim_gstep_N. 
Lemma wptp_strong_adequacy Φ κs' s n e1 t1 κs e2 t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WP e1 @ s; ⊤ {{ Φ }} -∗
  wptp s t1 -∗ >={⊤}=={⊤}=>^(S n) ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v).
Proof.
  iIntros (Hstep) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht") as "Hwp"; first done.
  iMod "Hwp". iDestruct "Hwp" as (e2' t2' ?) "(Hσ & Hwp & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ( ⌜s = NotStuck⌝ → [∗ list] e2 ∈ (e2' :: t2'),  ⧍ ⌜(is_Some (to_val e2) ∨ reducible e2 σ2) ⌝)%I
    (state_interp σ2 κs' (length t2') ∗ WP e2' @ s; ⊤ {{ v, Φ v }} ∗ wptp s t2')%I
    with "[$Hσ $Hwp $Ht]") as "(Hsafe&Hσ&Hwp&Hvs)".
  { iIntros "(Hσ & Hwp & Ht)" (->); simpl.
    iMod (fupd_plain_keep_l ⊤ (⧍ ⌜is_Some (to_val e2') ∨ reducible e2' σ2⌝)%I
                            (state_interp σ2 κs' (length t2') ∗ WP e2' @ ⊤ {{ v, Φ v }})%I
            with "[$Hσ $Hwp]") as "($ & Hσ & _)".
    { iIntros "[H1 H2]". iApply (wp_safe with "H1 H2"). }
    clear Hstep. generalize (length t2') as l. intros l. iInduction t2' as [| e3 t3] "IH"; simpl.
    - by iModIntro.
    - iDestruct "Ht" as "[Hwp Ht]".
      iMod (fupd_plain_keep_l ⊤ (⧍ ⌜is_Some (to_val e3) ∨ reducible e3 σ2⌝)%I
                            (state_interp σ2 κs' l ∗ WP e3 {{ v, fork_post v }})%I
            with "[$Hσ $Hwp]") as "($ & Hσ & _)".
      { iIntros "[H1 H2]". iApply (wp_safe with "H1 H2"). }
      iMod ("IH" with "Ht Hσ") as "$". by iModIntro. }
  iAssert (⧍ ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝)%I with "[Hsafe]" as "Hsafe".
  { destruct s; last (iExists 0; iIntros (? H); discriminate). iSpecialize ("Hsafe" with "[]"); eauto.
    iMod (list_big_later with "Hsafe") as "Hsafe". iIntros (e) "_ %".
      by iApply (big_sepL_elem_of with "Hsafe"). }
  iMod (fupd_intro_mask') as "Hclose". apply empty_subseteq. iModIntro.
  iApply big_later_eventually. iMod "Hsafe". iMod "Hclose" as "_".
  iExists _, _. iSplitL ""; first done. iFrame "Hsafe Hσ".
  iSplitL "Hwp".
  - destruct (to_val e2') as [v2|] eqn:He2'; last done.
    apply of_to_val in He2' as <-. iApply (wp_value_inv' with "Hwp").
  - clear Hstep. iInduction t2' as [|e t2'] "IH"; csimpl; first by iFrame.
    iDestruct "Hvs" as "[Hv Hvs]". destruct (to_val e) as [v|] eqn:He.
    + apply of_to_val in He as <-. iMod (wp_value_inv' with "Hv") as "$".
      by iApply "IH".
    + by iApply "IH".
Qed.
End adequacy.

Existing Instance elim_gstep_N. 
(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy {SI} `{TransfiniteIndex SI} (Σ: gFunctors SI) Λ `{!invPreG Σ} e1 σ1 n κs t2 σ2 φ :
  (∀ `{Hinv : !invG Σ},
       ⊢ (|={⊤}=> ∃
         (s: stuckness)
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (Φ fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI fork_post in
       stateI σ1 κs 0 ∗
       WP e1 @ s; ⊤ {{ Φ }} ∗
       (∀ e2 t2',
         (* e2 is the final state of the main thread, t2' the rest *)
         ⌜ t2 = e2 :: t2' ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are either done (a value) or reducible *)
         ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 [] (length t2') -∗
         (* If the main thread is done, its post-condition [Φ] holds *)
         from_option Φ True (to_val e2) -∗
         (* For all threads that are done, their postcondition [fork_post] holds. *)
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_intro_mask'] or [fupd_mask_weaken] to introduce the
         fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝))%I) →
  nsteps n ([e1], σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  eapply (@lstep_fupd_soundness _ Σ _ _ _ (S (S n) + 1))=> Hinv.
  rewrite Nat_iter_add Nat_iter_S.
  iMod Hwp as (s stateI Φ fork_post) "(Hσ & Hwp & Hφ)".
  iApply lstep_intro. iModIntro. 
  iPoseProof (@wptp_strong_adequacy _ _ _ (IrisG _ _ _ Hinv stateI fork_post) _ []
  with "[Hσ] Hwp") as "Hpost". 1-3:eauto. by rewrite right_id_L. iSpecialize ("Hpost" with "[$]").
  iMod "Hpost". iDestruct "Hpost" as (e2 t2' ->) "(? & ? & ? & ?)".
  iApply lstep_intro. 
  iApply fupd_plain_mask_empty.
  iMod ("Hφ" with "[% //] [$] [$] [$] [$]"). done.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are moreover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)).
Proof. split. intros []; naive_solver. constructor; naive_solver. Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.

Corollary wp_adequacy {SI} `{TransfiniteIndex SI} {Σ: gFunctors SI} Λ `{!invPreG Σ} s e σ φ :
  (∀ `{Hinv : !invG Σ} κs,
     sbi_emp_valid (|={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv (λ σ κs _, stateI σ κs) fork_post in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }})%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists s, (λ σ κs _, stateI σ κs), (λ v, ⌜φ v⌝%I), fork_post.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ?) "_ H _".
  iApply fupd_mask_weaken; [done|]. iSplit; [|done].
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Corollary wp_invariance {SI} `{TransfiniteIndex SI} {Σ: gFunctors SI} Λ `{!invPreG Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invG Σ} κs,
     sbi_emp_valid (|={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI fork_post in
       stateI σ1 κs 0 ∗ WP e1 @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝))%I) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists s, stateI, (λ _, True)%I, fork_post.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _) "Hσ _ _ /=".
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_weaken; first set_solver.
Qed.
