From iris.program_logic.refinement Require Export seq_weakestpre.
From iris.base_logic.lib Require Export invariants na_invariants.
From iris.heap_lang Require Export lang lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation metatheory.
From iris.algebra Require Import auth.
From iris.algebra.ordinals Require Import arithmetic.
Set Default Proof Using "Type".

Section eventloop_code.
  Definition new_stack : val := λ: <>, ref NONEV.

  Definition push : val := λ: "s", λ: "x",
                           let: "hd" := !"s" in
                           let: "p" := ("x", "hd") in
                           "s" <- SOME (ref "p").

  Definition pop : val := (λ: "s",
                           let: "hd" := !"s" in
                           match: "hd" with
                             NONE => NONE
                           | SOME "l" =>
                             let: "p" := !"l" in
                             let: "x" := Fst "p" in
                             "s" <- Snd "p" ;; SOME "x"
                           end).

  Definition enqueue : val := push.

  Definition run : val :=
      λ: "q", rec: "run" <> :=
      match: pop "q" with
        NONE => #()
      | SOME "f" => "f" #() ;; "run" #()
      end.

  Definition mkqueue : val :=
    λ: <>, new_stack #().

End eventloop_code.
Section eventloop_spec.

  Context {SI} {Σ: gFunctors SI} `{Hheap: !heapG Σ} `{Htc: !tcG Σ} `{Hseq: !seqG Σ} (N : namespace).

  Implicit Types (l: loc).

  Fixpoint stack_contents (hd: val) (xs: list val) (φ: val → iProp Σ) :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ l hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x, hd') ∗ φ x ∗ stack_contents hd' xs φ
  end%I.
  Definition stack (l: loc) (xs: list val) (φ: val → iProp Σ): iProp Σ := (∃ hd, l ↦ hd ∗ stack_contents hd xs φ)%I.
  Definition queue (q: val) : iProp Σ := (∃ l, ⌜q = #l⌝ ∗ na_inv seqG_name (N .@ l) (∃ xs, stack l xs (λ f, $ one ∗ SEQ f #() [{_, True}])))%I.


  Lemma new_stack_spec φ:
    sbi_emp_valid (WP (new_stack #()) [{ v, ∃ l, ⌜v = #l⌝ ∗ stack l nil φ }])%I.
  Proof.
    rewrite /new_stack. wp_pures.
    wp_alloc l as "Hl". iFrame.
    rewrite /stack. iExists l; iSplit; auto.
  Qed.

  Lemma push_spec  l xs φ (x : val):
    (stack l xs φ ∗ φ x ⊢ RSWP (push #l x) at 0 ⟨⟨ v, ⌜v = #()⌝ ∗ stack l (x :: xs) φ ⟩⟩)%I.
  Proof.
    iIntros "(Hstack & Hφ)".
    rewrite /push /stack. wp_pures.
    iDestruct "Hstack" as (hd) "[Hl cont]".
    wp_load. wp_pures. wp_alloc r as "Hr". rewrite -tcwp_rwp.
    wp_store. iSplit; auto. iExists (SOMEV #r). iFrame "Hl".
    simpl. iExists r, hd. by iFrame.
  Qed.

  Lemma pop_element_spec  l xs φ (x : val):
    (stack l (x :: xs) φ ⊢ RSWP (pop #l) at 0 ⟨⟨ v, ⌜v = SOMEV x⌝ ∗ φ x ∗ stack l xs φ ⟩⟩)%I.
  Proof.
    iIntros "Hstack".
    rewrite /pop /stack. wp_pures.
    iDestruct "Hstack" as (hd) "[Hl Hcont]".
    iDestruct "Hcont" as (r hd') "(-> & Hr & Hφ & Hcont)".
    wp_load. wp_pures. wp_load. wp_pures. wp_store. wp_pures; iFrame.
    iSplit; eauto. iExists hd'. iFrame.
  Qed.

  Lemma pop_empty_spec  l φ:
    (stack l nil φ ⊢ RSWP (pop #l) at 0 ⟨⟨ v, ⌜v = NONEV⌝ ∗ stack l nil φ ⟩⟩)%I.
  Proof.
    iIntros "Hstack".
    rewrite /pop /stack. wp_pures.
    iDestruct "Hstack" as (hd) "[Hl ->]".
    wp_load. wp_pures; iSplit; eauto.
  Qed.

  Lemma run_spec `{FiniteBoundedExistential SI} q :
    queue q ∗ $ one ⊢ SEQ (run q #()) [{v, ⌜v = #()⌝ }].
  Proof.
    iIntros "[#Q Hc] Hna". rewrite /run. do 2 wp_pure _.
    iLöb as "IH". wp_pures.
    wp_bind (pop _). iDestruct "Q" as (l) "[-> I]".
    iMod (na_inv_acc_open _ _ _ with "I Hna") as "Hinv"; auto.
    iApply (tcwp_burn_credit with "Hc"); first done.
    iNext. iDestruct "Hinv" as "(Hinv & Hna & Hclose)".
    iDestruct "Hinv" as (xs) "Hstack".
    destruct xs as [|f xs].
    - iPoseProof (pop_empty_spec with "Hstack") as "Hwp".
      iApply (rswp_wand with "Hwp"). iIntros (v) "[-> Hstack]".
      iMod ("Hclose" with "[Hstack $Hna]") as "Hna"; eauto.
      wp_pures. by iFrame.
    - iPoseProof (pop_element_spec with "Hstack") as "Hwp".
      iApply (rswp_wand with "Hwp"). iIntros (v) "[-> [[Hone Hwp] Hstack]]".
      iMod ("Hclose" with "[Hstack $Hna]") as "Hna"; eauto.
      wp_pures. iSpecialize ("Hwp" with "Hna").
      wp_bind (f _).
      iApply (rwp_wand with "Hwp"). iIntros (v) "[Hna _]".
      do 2 wp_pure _. rewrite -tcwp_rwp.
      iApply ("IH" with "Hone Hna").
  Qed.

  Lemma enqueue_spec `{FiniteBoundedExistential SI} q (f: val) :
    queue q ∗ $ one ∗ $ one ∗ SEQ (f #()) [{ _, True }] ⊢ SEQ (enqueue q f) [{v, ⌜v = #()⌝ }].
  Proof.
    iIntros "[#Q [Hc Hf]] Hna". rewrite /enqueue.
    iDestruct "Q" as (l) "[-> I]".
    iMod (na_inv_acc_open _ _ _ with "I Hna") as "Hinv"; auto.
    iApply (tcwp_burn_credit with "Hc"); first done.
    iNext. iDestruct "Hinv" as "(Hinv & Hna & Hclose)".
    iDestruct "Hinv" as (xs) "Hstack".
    iPoseProof (push_spec with "[$Hstack $Hf]") as "Hpush".
    iApply (rswp_strong_mono with "Hpush"); auto.
    iIntros (v) "(-> & Hstack)". iMod ("Hclose" with "[Hstack $Hna]"); eauto.
  Qed.

  Lemma mkqueue_spec :
    sbi_emp_valid (SEQ (mkqueue #()) [{ q, queue q}])%I.
  Proof.
    iIntros "Hna". rewrite /mkqueue. wp_pures.
    iMod (new_stack_spec) as "_".
    iIntros (v) "H". iDestruct "H" as (l) "[-> Hstack]".
    iMod (na_inv_alloc with "[Hstack]"); last first.
    { iModIntro. iFrame. iExists l. iSplit; eauto. }
    iNext. by iExists nil.
  Qed.

End eventloop_spec.





Section open_example.

  Variable external_code: val.
  Variable print: val.
  Variable q: val.
  Context {SI} {Σ: gFunctors SI} `{Hheap: !heapG Σ} `{Htc: !tcG Σ} `{Hseq: !seqG Σ} (N : namespace).


  Definition for_loop: val :=
    (rec: "loop" "f"  "n" :=
      if: "n" ≤ #0 then #() else let: "m" := "n" - #1 in "f" #() ;; "loop" "f" "m")%V.

  Notation "'for:' n 'do' e" := (for_loop (λ: <>, e)%V n%V) (at level 200, n at level 200, e at level 200) : val_scope.
  Notation "'for:' n 'do' e" := (for_loop (λ: <>, e)%E n%E) (at level 200, n at level 200, e at level 200) : expr_scope.

  Definition example : expr :=
    let: "n" := external_code #() in
    for: "n" do
      enqueue q (λ: <>, print "Hello World!").

  Lemma for_zero e:
    sbi_emp_valid (WP (for: #0 do e)%V [{ v, ⌜v = #()⌝ }])%I.
  Proof.
    rewrite /for_loop; by wp_pures.
  Qed.

  Lemma for_val (n: nat) e φ:
    WP (for: #n do e)%V [{v, φ v}] ⊢ WP (for: #n do e) [{ v, φ v }].
  Proof.
    rewrite /for_loop; iIntros "H". by wp_pure _.
  Qed.


  Lemma for_succ (n: nat) e φ:
    WP e;; (for: #n do e)%V [{v, φ v}] ⊢ WP (for: #(S n) do e)%V [{ v, φ v }].
  Proof.
    rewrite /for_loop; iIntros "H". wp_pures.
    by replace (S n - 1) with (n: Z) by lia.
  Qed.

  Lemma example_spec `{FiniteBoundedExistential SI}:
    queue N q ∗ $ (omul one) ∗ SEQ external_code #() [{ v, ∃ n: nat, ⌜v = #n⌝ }] ∗ (□ ∀ s: string, SEQ print s [{ _, True }]) ⊢
    SEQ example [{ _, True }].
  Proof.
    iIntros "(#Q & Hc & Hwp & #Hprint) Hna". rewrite /example.
    wp_bind (external_code _). iMod ("Hwp" with "Hna") as "_".
    iIntros (v) "[Hna Hn] !>". iDestruct "Hn" as (n) "->".
    do 2 wp_pure _. iApply (tc_weaken (omul one) (natmul (n * 2)%nat one)); auto; first apply (ord_stepindex.limit_upper_bound (λ n, natmul n one)).
    iFrame "Hc". iIntros "Hc". iApply for_val.
    iInduction n as [|n] "IH".
    - iMod (for_zero) as "_"; iFrame; auto.
    - simpl. rewrite !tc_split. iDestruct "Hc" as "(Ho & Ho' & Hc)".
      iApply for_succ. wp_pures.
      wp_bind (enqueue _ _).
      iMod (enqueue_spec with "[$Q $Ho $Ho'] Hna") as "_".
      + iIntros "Hna". wp_pures. iMod ("Hprint" with "Hna") as "_"; auto.
      + iIntros (v) "[Hna _] !>". wp_pures. iApply ("IH" with "Hna Hc").
  Qed.

End open_example.

