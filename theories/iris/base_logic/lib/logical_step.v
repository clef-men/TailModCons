From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import base tactics classes.
Set Default Proof Using "Type".
Import uPred.


Section eventually.

  Context {SI} {PROP: sbi SI} `{FU: BiFUpd SI PROP}.
  Global Instance elim_fupd_step p E (P Q: PROP):
    ElimModal True p false (|={E}▷=> P) P (|={E}▷=> Q) Q.
  Proof.
    iIntros (_) "(P & HPQ)". iPoseProof (intuitionistically_if_elim with "P") as "P".
    iMod "P". iModIntro. iNext;simpl. iMod "P". iModIntro. by iApply "HPQ".
  Qed.

  Fixpoint eventuallyN n E P : PROP :=
    match n with
    | 0 => (|={E}=> P)%I
    | S n => (|={E}=> ▷ |={E}=> eventuallyN n E P)%I
    end.

  Definition eventually E P : PROP := (|={E}=> ∃ n, eventuallyN n E P)%I.

  Notation "< E > P" := (eventually E P) (at level 99, E at level 50, P at level 200, format "< E >  P").
  Notation "< E >_ n P" := (eventuallyN n E P) (at level 99, E at level 50, n at level 9, P at level 200, format "< E >_ n  P").

  Global Instance eventuallyN_ne n E: NonExpansive (eventuallyN n E).
  Proof.
    intros α P Q EQ.
    induction n as [|n IH]; simpl; f_equiv; eauto; by rewrite IH.
  Qed.

  Global Instance eventually_ne E: NonExpansive (eventually E).
  Proof.
    intros α P Q EQ. unfold eventually. f_equiv. f_equiv. intros ?. by apply eventuallyN_ne.
  Qed.

  Lemma eventuallyN_intro P E: P ⊢ <E>_0 P.
  Proof.
    iIntros "P". by iModIntro.
  Qed.

  Lemma eventuallyN_eventually n E P: (<E>_n P)%I ⊢ (<E> P)%I.
  Proof. iIntros "H". iModIntro. by iExists n. Qed.

  Lemma eventuallyN_fupd_left n E P: (|={E}=> <E>_n P)%I ⊢ (<E>_n P)%I.
  Proof.
    iIntros "H". destruct n as [|n]; simpl.
    - by iMod "H".
    - by do 2 iMod "H".
  Qed.

  Lemma eventuallyN_fupd_right n E P: (<E>_n |={E}=> P)%I ⊢ (<E>_n P)%I.
  Proof.
    iIntros "H". iInduction n as [|n] "IH"; simpl.
    - by iMod "H".
    - iMod "H". by iApply "IH".
  Qed.

  Lemma eventuallyN_step_left n E P: (▷ <E>_n P)%I ⊢ (<E>_(S n) P)%I.
  Proof.
    iIntros "H"; simpl. iModIntro. iNext;simpl. by iModIntro.
  Qed.

  Lemma eventuallyN_intro_n n E P : P ⊢ (<E>_n P).
  Proof.
    iIntros "H". iInduction n as [ | n] "IH"; simpl.
    - iModIntro. iApply "H".
    - iApply eventuallyN_step_left. iNext. by iApply "IH".
  Qed.

  Lemma eventuallyN_mono P E n1 n2 : n1 ≤ n2 → (<E>_n1 P) ⊢ <E>_n2 P.
  Proof.
    iIntros (H) "P". iRevert (n2 H). iInduction n1 as [ | n1] "IH"; iIntros ([ | n2] H).
    - iApply "P".
    - iMod "P". iApply eventuallyN_intro_n. iModIntro. iNext. iModIntro. iApply "P".
    - lia.
    - simpl. iMod "P". iApply ("IH" with "P [%]"). lia.
  Qed.

  Lemma eventuallyN_step_right n E P: (<E>_n ▷ P)%I ⊢ (<E>_(S n) P)%I.
  Proof.
  iIntros "H"; simpl. iInduction n as [|n] "IH"; simpl.
  - iMod "H". iModIntro. iNext;simpl. by do 2 iModIntro.
  - iMod "H". by iApply "IH".
  Qed.

  Lemma eventually_fupd_left E P: (|={E}=> <E> P)%I ⊢ (<E> P)%I.
  Proof.
    iIntros "H". by iMod "H".
  Qed.

  Lemma eventually_fupd_right E P: (<E> |={E}=> P)%I ⊢ (<E> P)%I.
  Proof.
    iIntros "H". iMod "H". iDestruct "H" as (n) "H". iModIntro.
    iExists n. by iApply eventuallyN_fupd_right.
  Qed.

  Lemma eventually_step_right E P: (<E> ▷ P)%I ⊢ (<E> P)%I.
  Proof.
    iIntros "H"; simpl. iMod "H". iModIntro. iDestruct "H" as (n) "H".
    iExists (S n). by iApply eventuallyN_step_right.
  Qed.

  Lemma eventuallyN_mask_mono E1 E2 P n: E1 ⊆ E2 → (<E1>_n P) ⊢ <E2>_n P.
  Proof.
    iIntros (Hsub) "P". iInduction n as [|n] "IH"; simpl.
    - by iApply fupd_mask_mono.
    - iApply fupd_mask_mono; eauto. iMod "P". iModIntro. iNext; simpl.
      iApply fupd_mask_mono; eauto.
    iMod (fupd_intro_mask') as "H'"; eauto.
    iMod "P". iMod "H'" as "_". iModIntro. by iApply "IH".
  Qed.


  Lemma eventually_mask_mono E1 E2 P: E1 ⊆ E2 → (<E1> P) ⊢ <E2> P.
  Proof.
    iIntros (Hsub) "P". iApply fupd_mask_mono; eauto.
    iMod "P". iModIntro. iDestruct "P" as (n) "P".
    iExists n. by iApply eventuallyN_mask_mono.
  Qed.

  Lemma eventuallyN_compose E n m P : (<E>_n <E>_m P) ⊢ <E>_(n+m) P.
  Proof.
    iIntros "H". iInduction n as [ | n] "IH".
    - simpl. destruct m as [ | m]; iMod "H"; iApply "H".
    - simpl. iMod "H". by iApply "IH".
  Qed.

  Global Instance elim_eventuallyN p E (P Q : PROP) n:
    ElimModal True p false (<E>_n P) P (<E>_n Q) (Q).
  Proof.
    iIntros (_) "(P & HPQ)". iPoseProof (intuitionistically_if_elim with "P") as "P".
    iInduction n as [ | n] "IH".
    - iMod "P". iModIntro. by iApply "HPQ".
    - simpl. iMod "P". by iApply ("IH" with "[HPQ]").
  Qed.

  Lemma eventuallyN_compose' E n m P Q: (<E>_n P)%I ∗ (<E>_m (P -∗ Q))%I ⊢ (<E>_(n + m) Q).
  Proof.
    iIntros "[P PQ]". iApply eventuallyN_compose. iMod "P". iMod "PQ". by iApply "PQ".
  Qed.

  Lemma eventually_compose E P Q: (<E> P)%I ∗ (<E> P -∗ Q)%I ⊢ (<E> Q).
  Proof.
    iIntros "[P PQ]". iMod "P". iMod "PQ".
    iDestruct "P" as (n) "P". iDestruct "PQ" as (m) "PQ".
    iModIntro. iExists (n + m). iApply eventuallyN_compose'; iFrame.
  Qed.

  Instance elim_eventually p E (P Q: PROP):
    ElimModal True p false (<E> P) emp (<E> Q) (<E> P -∗ Q)%I.
  Proof.
    iIntros (_) "(P & HPQ)". iPoseProof (intuitionistically_if_elim with "P") as "P".
    iApply eventually_compose; iFrame. by iApply "HPQ".
  Qed.

  Lemma eventually_intro P E: P ⊢ <E> P.
  Proof.
    iIntros "P". iModIntro. iExists 0. by iApply eventuallyN_intro.
  Qed.

  Global Instance eventuallyN_equiv n E: Proper (equiv ==> equiv) (eventuallyN n E).
  Proof.
    intros P Q EQ. induction n; simpl.
    - by f_equiv.
    - by do 3 f_equiv.
  Qed.

  Global Instance eventually_equiv E: Proper (equiv ==> equiv) (eventually E).
  Proof.
    intros P Q EQ. unfold eventually. by repeat f_equiv.
  Qed.

End eventually.

Notation "< E > P" := (eventually E P) (at level 99, E at level 50, P at level 200, format "< E >  P").
Notation "< E >_ n P" := (eventuallyN n E P) (at level 99, E at level 50, n at level 9, P at level 200, format "< E >_ n  P").


Section general_step.

  Context {SI} {PROP: sbi SI} `{FU: BiFUpd SI PROP}.

  Definition gstepN (n: nat) Ei E1 E2 P : PROP := (|={E1, Ei}=> <Ei>_n |={Ei, E2}=> P)%I.
  Definition gstep Ei E1 E2 P : PROP := (|={E1, Ei}=> <Ei> |={Ei, E2}=> P)%I.

  Notation "'>={' E1 '}={' Ei '}={' E2 '}=>_' n P" := (gstepN n Ei E1 E2 P) (at level 99, E1, E2, Ei at level 60, n at level 9, P at level 200 (*, format "|={ E1 , E2 }=>> P" *)).
  Notation "'>={' E1 '}={' Ei '}={' E2 '}=>' P" := (gstep Ei E1 E2 P) (at level 99, E1, E2, Ei at level 60, P at level 200 (*, format "|={ E1 , E2 }=>^ n P"*)).


  (* Fancy Updates *)
  Lemma gstepN_fupd_left n Ei E1 E2 E3 P: (|={E1, E2}=> >={ E2 }={ Ei }={ E3 }=>_n P)%I ⊢ (>={E1}={Ei}={E3}=>_n P)%I.
  Proof.
    iIntros "H". iMod "H". iMod "H". by iModIntro.
  Qed.

  Lemma gstepN_fupd_right n Ei E1 E2 E3 P: (>={ E1 }={ Ei }={ E2 }=>_n |={E2, E3}=> P)%I ⊢ (>={E1}={Ei}={E3}=>_n P)%I.
  Proof.
    iIntros "H". iMod "H"; iModIntro. iPoseProof (eventuallyN_compose' _ n 0) as "Q".
    assert (n + 0 = 0 + n)%nat as -> by lia. iApply "Q"; iFrame.
    iApply eventuallyN_intro. iIntros "H". by iMod "H".
  Qed.

  Lemma gstep_fupd_left Ei E1 E2 E3 P: (|={E1, E2}=> >={ E2 }={ Ei }={ E3 }=> P)%I ⊢ (>={E1}={Ei}={E3}=> P)%I.
  Proof.
    iIntros "H". iMod "H". iMod "H". by iModIntro.
  Qed.

  Existing Instance elim_eventually.
  Lemma gstep_fupd_right Ei E1 E2 E3 P: (>={ E1 }={ Ei }={ E2 }=> |={E2, E3}=> P)%I ⊢ (>={E1}={Ei}={E3}=> P)%I.
  Proof.
    iIntros "H". iMod "H"; iModIntro. iMod "H" as "_".
    iApply eventually_intro. iIntros "H". by iMod "H".
  Qed.


  (* Later Steps *)
  Lemma gstepN_gstep Ei E1 E2 n P: (>={ E1 }={ Ei }={ E2 }=>_n P)%I ⊢ (>={ E1 }={ Ei }={ E2 }=> P)%I.
  Proof.
    iIntros "H". iMod "H". iModIntro.
    by iApply eventuallyN_eventually.
  Qed.

  Lemma gstepN_later Ei E1 E2 n P: Ei ⊆ E1 → (▷ >={E1}={Ei}={E2}=>_n P)%I ⊢ (>={E1}={Ei}={E2}=>_(S n) P)%I.
  Proof.
    iIntros (Hsub) "H". iMod (fupd_intro_mask') as "E1"; eauto.
    iModIntro. simpl. iModIntro. iNext;simpl.
    by iMod "E1" as "_".
  Qed.

  Lemma gstepN_intro Ei E1 E2 P: Ei ⊆ E2 → (|={E1, E2}=> P)%I ⊢ (>={E1}={Ei}={E2}=>_0 P)%I.
  Proof.
    iIntros (Hsub) "H". iMod "H". iMod (fupd_intro_mask') as "E1"; eauto.
    iModIntro. iApply eventuallyN_intro. iMod "E1". by iModIntro.
  Qed.

  Lemma gstepN_intro' Ei E1 E2 P: Ei ⊆ E1 → (|={E1, E2}=> P)%I ⊢ (>={E1}={Ei}={E2}=>_0 P)%I.
  Proof.
    iIntros (Hsub) "H". iMod (fupd_intro_mask') as "Ei1"; eauto. iModIntro.
    iApply eventuallyN_intro. by iMod "Ei1".
  Qed.

  Lemma gstep_squash Ei E1 E2 P: Ei ⊆ E2 → (>={ E1 }={ Ei }={ E2 }=> ▷ P)%I ⊢ (>={ E1 }={ Ei }={ E2 }=> P)%I.
  Proof.
    iIntros (Hsub) "H". do 2 iMod "H". do 2 iModIntro. iDestruct "H" as (n) "H".
    iExists (n + 1). iInduction n as [|n] "IH"; simpl.
    - iMod "H". iMod "H". iMod (fupd_intro_mask') as "Ei2"; eauto.
      iModIntro. iNext. do 2 iModIntro. iMod "Ei2". by iModIntro.
    - iMod "H". by iApply "IH".
  Qed.


  Lemma gstepN_change_iter n Ei Ej E1 E2 P: Ej ⊆ Ei →
    (>={E1}={Ei}={E2}=>_n P)%I ⊢ (>={E1}={Ej}={E2}=>_n P).
  Proof.
    iIntros (Hsub) "H". iMod "H".
    iMod (fupd_intro_mask') as "Eji"; eauto.
    iModIntro. iInduction n as [|n] "IH"; simpl.
    - iModIntro. iMod "Eji" as "_". by iMod "H".
    - iMod "Eji" as "_". iMod "H". iMod (fupd_intro_mask') as "Eji"; eauto.
      iModIntro. iNext. iModIntro. iApply ("IH" with "[H] Eji").
      iApply eventuallyN_fupd_left. iMod "H". by iModIntro.
  Qed.

  Lemma gstep_change_iter Ei Ej E1 E2 P: Ej ⊆ Ei →
    (>={E1}={Ei}={E2}=> P)%I ⊢ (>={E1}={Ej}={E2}=> P).
  Proof.
    iIntros (Hsub) "H". do 2 iMod "H".
    iMod (fupd_intro_mask') as "Eji"; eauto.
    iModIntro. iDestruct "H" as (n) "H". iModIntro. iExists n.
    iApply eventuallyN_fupd_left. iApply gstepN_change_iter; eauto.
    iMod "Eji". by iModIntro.
  Qed.

  Lemma gstep_compose Ei Ej E1 E2 E3 P Q: E2 ⊆ Ei ⊆ Ej →
    (>={E1}={Ei}={E2}=> P) -∗ (>={E2}={Ej}={E3}=> Q) -∗ >={E1}={Ej}={E3}=> P ∗ Q.
  Proof.
    iIntros (Hsub) "P Q". do 2 iMod "P".
    iMod (fupd_intro_mask' _ E2) as "E2i"; first set_solver.
    do 2 iMod "Q". iModIntro. iModIntro.
    iDestruct "P" as (n1) "P". iDestruct "Q" as (n2) "Q".
    iExists (n1 + n2). iInduction n1 as [|n1] "IH"; [iInduction n2 as [|n2] "IH"|]; simpl.
    - iMod "Q". iAssert (|={E2}=> P)%I with "[P E2i]" as "P".
      { iMod "E2i" as "_". by iMod "P". }
      iMod (fupd_intro_mask' _ E2) as "E2j"; first set_solver.
      iMod "P". iMod "E2j" as "_". iModIntro. by iFrame.
    - iMod "Q". by iApply ("IH" with "P Q E2i").
    - iMod (fupd_intro_mask' _ Ei) as "Eij"; first set_solver.
      iMod "P". iMod "Eij" as "_". iModIntro. iNext.
      iSpecialize ("IH" with "[P] Q E2i").
      { by iApply eventuallyN_fupd_left. }
      by iModIntro.
  Qed.

  Lemma gstepN_mono Ei E1 E2 P k1 k2: k1 ≤ k2 → (>={E1}={Ei}={E2}=>_k1 P) ⊢ >={E1}={Ei}={E2}=>_k2 P.
  Proof.
    iIntros (H) "P". iMod "P". iModIntro. by iApply (eventuallyN_mono _ _ k1 k2 H).
  Qed.

  Global Instance gstep_equiv Ei E1 E2: Proper (equiv ==> equiv) (gstep Ei E1 E2).
  Proof.
    intros P Q EQ. unfold gstep. by repeat f_equiv.
  Qed.

  Global Instance gstepN_equiv n Ei E1 E2: Proper (equiv ==> equiv) (gstepN n Ei E1 E2).
  Proof.
    intros P Q EQ. unfold gstepN.  by repeat f_equiv.
  Qed.


  Instance elim_gstep p Ei E1 E2 (P Q: PROP):
    ElimModal True p false (>={E1}={Ei}={E2}=> P) P (>={E1}={Ei}={E2}=> Q) Q.
  Proof.
    iIntros (_) "(P & HPQ)". iPoseProof (intuitionistically_if_elim with "P") as "P".
    iMod "P". iModIntro. iMod "P" as "_". iModIntro. iExists 0. iModIntro. iIntros ">P".
    iModIntro. by iApply "HPQ".
  Qed.

  Existing Instance elim_eventuallyN.
  Instance elim_gstepN p Ei E1 E2 n (P Q: PROP):
    ElimModal True p false (>={E1}={Ei}={E2}=>_n P) P (>={E1}={Ei}={E2}=>_n Q) Q.
  Proof.
    iIntros (_) "(P & HPQ)". iPoseProof (intuitionistically_if_elim with "P") as "P".
    iMod "P". iModIntro. iMod "P". iMod "P". iModIntro. by iApply "HPQ".
  Qed.

  Notation "'>={' E1 '}=={' E2 '}=>^' n P" :=
    (Nat.iter n (gstep ∅ E1 E2) P)
      (at level 99, E1, E2 at level 60, n at level 9, P at level 200,
       format "'>={' E1 '}=={' E2 '}=>^' n  P").

  Instance elim_gstep_N E1 E2 p n P Q :
    ElimModal True p false (>={E1}=={E2}=>^n P) P (>={E1}=={E2}=>^n Q) Q.
  Proof.
    iIntros (_) "(P & HPQ)". iPoseProof (intuitionistically_if_elim with "P") as "P".
    iInduction n as [ | n] "IH". by iApply "HPQ".
    iMod "P". iApply ("IH" with "HPQ P").
  Qed.

  Global Instance gstep_ne E1 E2 E3: NonExpansive (gstep E2 E1 E3).
  Proof. intros α x y Heq. unfold gstep. by do 3 f_equiv. Qed.

  Global Instance gstepN_ne E1 E2 E3 n: NonExpansive (gstepN n E2 E1 E3).
  Proof. intros α x y Heq. unfold gstepN. by do 3 f_equiv. Qed.
End general_step.
Notation "'>={' E1 '}={' Ei '}={' E2 '}=>_' n P" := (gstepN n Ei E1 E2 P) (at level 99, E1, E2, Ei at level 60, n at level 9, P at level 200 , format "'>={' E1 '}={' Ei '}={' E2 '}=>_' n  P" ).
Notation "'>={' E1 '}={' Ei '}={' E2 '}=>' P" := (gstep Ei E1 E2 P) (at level 99, E1, E2, Ei at level 60, P at level 200 (*, format "|={ E1 , E2 }=>^ n P"*)).

Section logical_step.

  Context {SI} {PROP: sbi SI} `{FU: BiFUpd SI PROP}.
  Implicit Types (P Q: PROP).

  Notation "'>={' E1 '}=={' E2 '}=>_' n P" := (gstepN n ∅ E1 E2 P) (at level 99, E1, E2 at level 60, n at level 9, P at level 200 (*, format "|={ E1 , E2 }=>> P" *)).
  Notation "'>={' E1 '}=={' E2 '}=>' P" := (gstep ∅ E1 E2 P) (at level 99, E1, E2 at level 60, P at level 200 (*, format "|={ E1 , E2 }=>^ n P"*)).


  (* Fancy Updates *)
  Lemma lstep_fupd_left E1 E2 E3 P: (|={E1, E2}=> >={E2}=={E3}=> P)%I ⊢ (>={E1}=={E3}=> P)%I.
  Proof. apply gstep_fupd_left. Qed.

  Lemma lstep_fupd_right E1 E2 E3 P: (>={E1}=={E2}=> |={E2, E3}=> P)%I ⊢ (>={E1}=={E3}=> P)%I.
  Proof. apply gstep_fupd_right. Qed.

  Lemma lstepN_fupd_left n E1 E2 E3 P: (|={E1, E2}=> >={E2}=={E3}=>_n P)%I ⊢ (>={E1}=={E3}=>_n P)%I.
  Proof. apply gstepN_fupd_left. Qed.

  Lemma lstepN_fupd_right n E1 E2 E3 P: (>={E1}=={E2}=>_n |={E2, E3}=> P)%I ⊢ (>={E1}=={E3}=>_n P)%I.
  Proof. apply gstepN_fupd_right. Qed.


  (* Later *)
  Lemma lstepN_lstep E1 E2 n P: (>={ E1 }=={ E2 }=>_n P)%I ⊢ (>={ E1 }=={ E2 }=> P)%I.
  Proof. apply gstepN_gstep. Qed.

  Lemma lstepN_later E1 E2 n P: (▷ >={E1}=={E2}=>_n P)%I ⊢ (>={E1}=={E2}=>_(S n) P)%I.
  Proof. apply gstepN_later. set_solver. Qed.

  Lemma lstepN_intro' E1 E2 P: (|={E1, E2}=> P)%I ⊢ (>={E1}=={E2}=>_0 P)%I.
  Proof. apply gstepN_intro. set_solver. Qed.
  Lemma lstepN_intro E1 E2 n P: (|={E1, E2}=> P)%I ⊢ (>={E1}=={E2}=>_n P)%I.
  Proof. iIntros "H". iApply gstepN_mono. 2: by iApply lstepN_intro'. lia. Qed.


  Lemma lstep_squash E1 E2 P: (>={E1}=={E2}=> ▷ P) ⊢ (>={E1}=={E2}=> P).
  Proof. apply gstep_squash. set_solver. Qed.


  Lemma lstep_intro E1 E2 P : (|={E1, E2}=> P)%I ⊢ (>={E1}=={E2}=> P)%I.
  Proof.
   iIntros "H". iApply lstepN_lstep. by iApply lstepN_intro'.
  Qed.

End logical_step.
Notation "'>={' E1 '}=={' E2 '}=>_' n P" := (gstepN n ∅ E1 E2 P) (at level 99, E1, E2 at level 60, n at level 9, P at level 200 , format "'>={' E1 '}=={' E2 '}=>_' n  P" ).
Notation "'>={' E1 '}=={' E2 '}=>' P" := (gstep ∅ E1 E2 P) (at level 99, E1, E2 at level 60, P at level 200 , format "'>={' E1 '}=={' E2 '}=>' P").
Notation "'>={' E1 '}=={' E2 '}=>^' n P" :=
    (Nat.iter n (gstep ∅ E1 E2) P)
      (at level 99, E1, E2 at level 60, n at level 9, P at level 200,
       format "'>={' E1 '}=={' E2 '}=>^' n  P").
