From iris.base_logic.lib Require Export own.
From stdpp Require Export coPset.
From iris.base_logic.lib Require Import wsat.
From iris.base_logic Require Import satisfiable.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Export invG.
Import uPred.

Definition uPred_fupd_def {SI} {Σ: gFunctors SI} `{!invG Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  (wsat ∗ ownE E1 ==∗ ◇ (wsat ∗ ownE E2 ∗ P))%I.
Definition uPred_fupd_aux {SI} {Σ: gFunctors SI} `{!invG Σ} : seal uPred_fupd_def. by eexists. Qed.
Definition uPred_fupd {SI} {Σ: gFunctors SI} `{!invG Σ} : FUpd (iProp Σ):= uPred_fupd_aux.(unseal).
Definition uPred_fupd_eq {SI} {Σ: gFunctors SI} `{!invG Σ} : @fupd _ uPred_fupd = uPred_fupd_def :=
  uPred_fupd_aux.(seal_eq).

Lemma uPred_fupd_mixin {SI} {Σ: gFunctors SI}  `{!invG Σ} : BiFUpdMixin (uPredSI (iResUR Σ)) uPred_fupd.
Proof.
  split.
  - rewrite uPred_fupd_eq. solve_proper.
  - intros E1 E2 P (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //.
    by iIntros "$ ($ & $ & HE) !> !> [$ $] !> !>" .
  - rewrite uPred_fupd_eq. iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite uPred_fupd_eq. iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite uPred_fupd_eq. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //.
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
    iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". by iApply "HP".
  - rewrite uPred_fupd_eq /uPred_fupd_def. by iIntros (????) "[HwP $]".
Qed.
Instance uPred_bi_fupd {SI} {Σ: gFunctors SI} `{!invG Σ} : BiFUpd (uPredSI (iResUR Σ)) :=
  {| bi_fupd_mixin := uPred_fupd_mixin |}.

Instance uPred_bi_bupd_fupd {SI} {Σ: gFunctors SI} `{!invG Σ} : BiBUpdFUpd (uPredSI (iResUR Σ)).
Proof. rewrite /BiBUpdFUpd uPred_fupd_eq. by iIntros (E P) ">? [$ $] !> !>". Qed.

Instance uPred_bi_fupd_plainly {SI} {Σ: gFunctors SI} `{!invG Σ} : BiFUpdPlainly (uPredSI (iResUR Σ)).
Proof.
  split.
  - rewrite uPred_fupd_eq /uPred_fupd_def. iIntros (E P) "H [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    by iFrame.
  - rewrite uPred_fupd_eq /uPred_fupd_def. iIntros (E P Q) "[H HQ] [Hw HE]".
    iAssert (◇ ■ P)%I as "#>HP".
    { by iMod ("H" with "HQ [$]") as "(_ & _ & HP)". }
    by iFrame.
  - rewrite uPred_fupd_eq /uPred_fupd_def. iIntros (E P) "H [Hw HE]".
    iAssert (▷ ◇ ■ P)%I as "#HP".
    { iNext. by iMod ("H" with "[$]") as "(_ & _ & HP)". }
    iFrame. iIntros "!> !> !>". by iMod "HP".
  - rewrite uPred_fupd_eq /uPred_fupd_def. iIntros (E A Φ) "HΦ [Hw HE]".
    iAssert (◇ ■ ∀ x : A, Φ x)%I as "#>HP".
    { iIntros (x). by iMod ("HΦ" with "[$Hw $HE]") as "(_&_&?)". }
    by iFrame.
Qed.

Lemma fupd_plain_soundness {SI} {Σ: gFunctors SI}  `{!invPreG Σ} E1 E2 (P: iProp Σ) `{!Plain P}:
  (∀ `{Hinv: !invG Σ}, bi_emp_valid (|={E1,E2}=> P)) → bi_emp_valid P.
Proof.
  iIntros (Hfupd). apply later_soundness. iMod wsat_alloc as (Hinv) "[Hw HE]".
  iAssert (|={⊤,E2}=> P)%I as "H".
  { iMod fupd_intro_mask'; last iApply Hfupd. done. }
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("H" with "[$]") as "[Hw [HE >H']]"; iFrame.
Qed.

Lemma step_fupdN_soundness {SI} {Σ: gFunctors SI}  `{!invPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ}, bi_emp_valid (|={⊤,∅}▷=>^n |={⊤,∅}=> ⌜ φ ⌝ : iProp Σ)%I) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (S n)); simpl.
  apply (fupd_plain_soundness ⊤ ⊤ _)=> Hinv.
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  destruct n as [|n].
  - iApply fupd_plainly_mask_empty. iMod "H" as %?; auto.
  - iDestruct (step_fupdN_wand _ _ _ _ (|={⊤}=> ⌜φ⌝)%I with "H []") as "H'".
    { by iApply fupd_plain_mask_empty. }
    rewrite -step_fupdN_S_fupd.
    iMod (step_fupdN_plain with "H'") as "Hφ". iModIntro. iNext.
    simpl; rewrite -later_laterN laterN_later.
    iNext. by iMod "Hφ".
Qed.

Lemma step_fupdN_soundness' {SI} {Σ: gFunctors SI}  `{!invPreG Σ} φ n :
  (∀ `{Hinv: !invG Σ}, bi_emp_valid (|={⊤,∅}▷=>^n ⌜ φ ⌝ : iProp Σ)%I)  →
  φ.
Proof.
  iIntros (Hiter). eapply (step_fupdN_soundness _ n).
  iIntros (Hinv). iPoseProof (Hiter Hinv) as "Hiter".
  iApply (step_fupdN_wand with "Hiter"). by iApply (fupd_mask_weaken _ _ _).
Qed.


Section satisfiable_at.
  Context {SI} {Σ: gFunctors SI} `{invG SI Σ}.

  Definition satisfiable_at E P := satisfiable (wsat ∗ ownE E ∗ P)%I.

  Lemma satisfiable_at_fupd E1 E2 P:
    satisfiable_at E1 (|={E1, E2}=> P)%I → satisfiable_at E2 P.
  Proof.
    intros Hs. apply satisfiable_later, satisfiable_bupd.
    apply (satisfiable_mono _ _ Hs).
    iIntros "(W & O & P)". rewrite uPred_fupd_eq /uPred_fupd_def.
    iSpecialize ("P" with "[W O]"); first by iFrame.
    iMod "P". iModIntro. iApply except_0_later.
    iMod "P". iModIntro. by iNext.
  Qed.

  (* TODO: satisfiable_at is almost an instance of Satisfiable.
    By redesigning Satisfiable, we could get away without proving the following lemmas. *)
  Section satisfiable_at_lifting.

    Lemma satisfiable_at_mono E P Q: satisfiable_at E P → (P ⊢ Q) → satisfiable_at E Q.
    Proof. intros Hs HPQ. apply (satisfiable_mono _ _ Hs). by rewrite HPQ. Qed.

    Lemma satisfiable_at_elim E P: satisfiable_at E P → Plain P → True ⊢ P.
    Proof.
      intros Hs HP; apply satisfiable_elim; auto.
      apply (satisfiable_mono _ _ Hs); iIntros "(_ & _ & $)".
    Qed.

    Lemma satisfiable_at_later E P: satisfiable_at E (▷ P)%I → satisfiable_at E P.
    Proof.
      intros Hs; apply satisfiable_later, (satisfiable_mono _ _ Hs).
      iIntros "($ & $ & $)".
    Qed.

    Lemma satisfiable_at_finite_exists E `{FiniteExistential SI} (X: Type) P Q: satisfiable_at E (∃ x: X, P x)%I → pred_finite Q → (∀ x, P x ⊢ ⌜Q x⌝) → ∃ x: X, satisfiable_at E (P x).
    Proof.
      intros Hs ??; eapply satisfiable_finite_exists; eauto.
      - apply (satisfiable_mono _ _ Hs).
        iIntros "($ & $ & $)".
      - iIntros (x) "(_ & _ & P)". by iApply H2.
    Qed.

    Lemma satisfiable_at_exists E `{LargeIndex SI} (X: Type) P: satisfiable_at E (∃ x: X, P x)%I → ∃ x: X, satisfiable_at E (P x).
    Proof.
      intros Hs; apply satisfiable_exists, (satisfiable_mono _ _ Hs).
      iIntros "($ & $ & $)".
    Qed.

    Lemma satisfiable_at_bupd E P: satisfiable_at E (|==> P)%I → satisfiable_at E P.
    Proof.
      intros Hs; apply satisfiable_bupd, (satisfiable_mono _ _ Hs).
      iIntros "($ & $ & $)".
    Qed.

    Lemma satisfiable_at_forall E {X} (x: X) P: satisfiable_at E (∀ x, P x)%I → satisfiable_at E (P x).
    Proof.
      intros Hs; apply (satisfiable_mono _ _ Hs).
      iIntros "($ & $ & H)"; auto.
    Qed.

    Lemma satisfiable_at_impl E P Q: satisfiable_at E (P → Q)%I → (True ⊢ P) → satisfiable_at E Q.
    Proof.
      intros Hs Hent; apply (satisfiable_mono _ _ Hs).
      iIntros "($ & $ & PQ)". iApply "PQ". by iApply Hent.
    Qed.

    Lemma satisfiable_at_wand E P Q: satisfiable_at E (P -∗ Q)%I → (True ⊢ P) → satisfiable_at E Q.
    Proof.
      intros Hs Hent; apply (satisfiable_mono _ _ Hs).
      iIntros "($ & $ & PQ)". iApply "PQ". by iApply Hent.
    Qed.

    Lemma satisfiable_at_pers E P: satisfiable_at E (<pers> P)%I → satisfiable_at E P.
    Proof.
      intros Hs; apply (satisfiable_mono _ _ Hs).
      iIntros "($ & $ & P)". iApply "P".
    Qed.

    Lemma satisfiable_at_intuitionistically E P: satisfiable_at E (□ P)%I → satisfiable_at E P.
    Proof.
      intros Hs; apply (satisfiable_mono _ _ Hs).
      iIntros "($ & $ & P)". iApply "P".
    Qed.

    Lemma satisfiable_at_or `{FiniteExistential SI} E P Q: satisfiable_at E (P ∨ Q)%I → satisfiable_at E P ∨ satisfiable_at E Q.
    Proof.
      intros Hs; apply satisfiable_or, (satisfiable_mono _ _ Hs).
      iIntros "($ & $ & $)".
    Qed.

    (* TODO: add this for satisfiable. *)
    Lemma satisfiable_at_sep P Q E: satisfiable_at E (P ∗ Q)%I → satisfiable_at E P ∧ satisfiable_at E Q.
    Proof.
      intros Hsat; split; apply (satisfiable_at_mono _ _ _ Hsat).
      all: iIntros "[? ?]"; iFrame.
    Qed.

    Global Instance satisfiable_at_equiv E: Proper (equiv ==> iff) (satisfiable_at E).
    Proof.
      intros P Q HPQ; unfold satisfiable_at; by rewrite HPQ.
    Qed.

  End satisfiable_at_lifting.

  Lemma satisfiable_at_pure E φ: satisfiable_at E (⌜φ⌝)%I → φ.
  Proof.
    intros Hsat. apply satisfiable_at_elim in Hsat; last apply _.
    by apply uPred.pure_soundness in Hsat.
  Qed.
End satisfiable_at.

Lemma satisfiable_at_intro {SI} `{LargeIndex SI} {Σ: gFunctors SI} `{!invPreG Σ}:
  ∃ Hinv: invG Σ, satisfiable_at ⊤ True%I.
Proof.
  specialize wsat_alloc_strong.
  intros HC % satisfiable_intro % satisfiable_bupd.
  apply satisfiable_exists in HC. destruct HC as [γI HC].
  apply satisfiable_exists in HC. destruct HC as [γE HC].
  apply satisfiable_exists in HC. destruct HC as [γD HC].
  exists (WsatG _ _ _ _ _ γI γE γD).
  apply (satisfiable_mono _ _ HC).
  by iIntros "($ & $)".
Qed.
