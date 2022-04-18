
From iris.program_logic.refinement Require Export ref_weakestpre ref_adequacy seq_weakestpre.
From iris.examples.refinements Require Export refinement.
From iris.algebra Require Import auth.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".


(* We illustrate here how to derive the rules shown in the paper *)


Section derived.
  Context {SI: indexT} `{Σ: gFunctors SI} `{!rheapG Σ} `{!auth_sourceG Σ (natA SI)} `{!seqG Σ}.

  Definition seq_rswp E e φ : iProp Σ := (na_own seqG_name E -∗ RSWP e at 0 ⟨⟨ v, na_own seqG_name E ∗ φ v ⟩⟩)%I.
  Notation "⟨⟨ P ⟩ ⟩ e ⟨⟨ v , Q ⟩ ⟩" := (□ (P -∗ (seq_rswp ⊤ e (λ v, Q))))%I
  (at level 20, P, e, Q at level 200, format "⟨⟨  P  ⟩ ⟩  e  ⟨⟨  v ,  Q  ⟩ ⟩") : stdpp_scope.
  Notation "{{ P } } e {{ v , Q } }" := (□ (P -∗ SEQ e ⟨⟨ v, Q ⟩⟩))%I
  (at level 20, P, e, Q at level 200, format "{{  P  } }  e  {{  v ,  Q  } }") : stdpp_scope.


  Lemma Value (v: val): (⊢ {{True}} v {{w, ⌜v = w⌝}})%I.
  Proof.
    iIntros "!> _ $". by iApply rwp_value.
  Qed.

  Lemma Frame (e: expr) P R Q: ({{P}} e {{v, Q v}} ⊢ {{P ∗ R}} e {{v, Q v ∗ R}})%I.
  Proof.
    iIntros "#H !> [P $]". by iApply "H".
  Qed.

  Lemma Bind (e: expr) K P Q R:
    ({{P}} e {{v, Q v}} ∗ (∀ v: val, ({{Q v}} fill K (Val v) {{w, R w}}))
    ⊢ {{P}} fill K e {{v, R v}})%I.
  Proof.
    iIntros "[#H1 #H2] !> P Hna".
    iApply rwp_bind. iSpecialize ("H1" with "P Hna").
    iApply (rwp_strong_mono with "H1 []"); auto.
    iIntros (v) "[Hna Q] !>". iApply ("H2" with "Q Hna").
  Qed.

  Lemma Löb (P : iPropI Σ) : (▷ P → P) ⊢ P.
  Proof. iApply bi.löb. Qed.

  Lemma TPPureT (e e': expr) P Q: pure_step e e' → ({{P}} e' {{v, Q v}} ⊢ ⟨⟨P⟩⟩ e ⟨⟨v, Q v⟩⟩)%I.
  Proof.
    iIntros (Hstep) "#H !> P Hna".
    iApply (ref_lifting.rswp_pure_step_later _ _ _ _ _ True); [|done|by iApply ("H" with "P Hna")].
    intros _. apply nsteps_once, Hstep.
  Qed.

  Lemma TPPureS (e e' et: expr) K P Q:
    to_val et = None
    → pure_step e e'
    → (⟨⟨src (fill K e') ∗ P⟩⟩ et ⟨⟨v, Q v⟩⟩ ⊢ {{src (fill K e) ∗ ▷ P}} et {{v, Q v}})%I.
  Proof.
    iIntros (Hexp Hstep) "#H !> [Hsrc P] Hna". iApply (rwp_take_step with "[P Hna] [Hsrc]"); first done; last first.
    - iApply step_pure; last iApply "Hsrc". apply pure_step_ctx; last done. apply _.
    - iIntros "Hsrc'". iApply rswp_do_step. iNext. iApply ("H" with "[$P $Hsrc'] Hna").
  Qed.

  Lemma TPStoreT l (v1 v2: val): (True ⊢ ⟨⟨l ↦ v1⟩⟩ #l <- v2 ⟨⟨w, ⌜w = #()⌝ ∗ l ↦ v2⟩⟩)%I.
  Proof.
    iIntros "_ !> Hl $". iApply (rswp_store with "[$Hl]").
    by iIntros "$".
  Qed.

  Lemma TPStoreS (et: expr) l v1 v2 K P Q:
    to_val et = None
    → (⟨⟨P ∗ src (fill K (Val #())) ∗ l ↦s v2⟩⟩ et ⟨⟨v, Q v⟩⟩
      ⊢ {{src (fill K (#l <- v2)) ∗ l ↦s v1 ∗ ▷ P}} et {{v, Q v}})%I.
  Proof.
    iIntros (Hexp) "#H !> [Hsrc [Hloc P]] Hna". iApply (rwp_take_step with "[P Hna] [Hsrc Hloc]"); first done; last first.
    - iApply step_store. iFrame.
    - iIntros "Hsrc'". iApply rswp_do_step. iNext. iApply ("H" with "[$P $Hsrc'] Hna").
  Qed.

  Lemma TPStutterT (e: expr) P Q: to_val e = None → (⟨⟨P⟩⟩ e ⟨⟨v, Q v⟩⟩ ⊢ {{P}} e {{v, Q v}})%I.
  Proof.
    iIntros (H) "#H !> P Hna". iApply rwp_no_step; first done.
    by iApply ("H" with "P Hna").
  Qed.

  Lemma TPStutterSStore (et : expr) v1 v2 K l P Q : 
    to_val et = None
    → {{P ∗ src (fill K (Val #())) ∗ l ↦s v2}} et {{v, Q v}} 
    ⊢ {{l ↦s v1 ∗ src (fill K (#l <- v2)) ∗ P}} et {{v, Q v}}. 
  Proof. 
    iIntros (Hv) "#H !> [Hloc [Hsrc P]] Hna". 
    iApply (rwp_weaken with "[H Hna] [P Hloc Hsrc]"); first done.
    - instantiate (1 := (P ∗ src (fill K #()) ∗ l ↦s v2)%I). 
      iIntros "H1". iApply ("H" with "[H1] [Hna]"); done. 
    - iApply src_update_mono. iSplitL "Hsrc Hloc". 
      iApply step_store. by iFrame. 
      iIntros "[H0 H1]". by iFrame.
  Qed. 

  Lemma TPStutterSPure (et es es' : expr) P Q : 
    to_val et = None
    → pure_step es es'
    → {{ P ∗ src(es') }} et {{v, Q v}}
      ⊢ {{ P ∗ src(es)}} et {{v, Q v}}.
  Proof. 
    iIntros (H0 H) "#H !> [P Hsrc] Hna".
    iApply (rwp_weaken with "[H Hna] [P Hsrc]"); first done. 
    - instantiate (1 := (P ∗ src es')%I). iIntros "H1". 
      by iApply ("H" with "[H1] Hna"). 
    - iApply src_update_mono. iSplitL "Hsrc". 
      by iApply step_pure. iIntros "?"; by iFrame. 
  Qed.  

  Lemma HoareLöb X P Q e : 
    (∀ x :X, {{P x ∗ ▷ (∀ x, {{P x}} e {{v, Q x v}})}} e {{ v, Q x v}})
    ⊢ ∀ x, {{ P x }} e {{v, Q x v}}. 
  Proof. 
    iIntros "H". iApply bi.löb. 
    iIntros "#H1" (x). 
    (*iIntros "H0".*)
    (*iSpecialize ("H" with x). *)
    (*iApply ("H"). iModIntro.*)
  Abort. 

End derived.
