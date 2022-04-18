From iris.program_logic Require Export weakestpre adequacy.
From iris.program_logic.refinement Require Export ref_weakestpre ref_adequacy tc_weakestpre.
From iris.algebra Require Import auth.
From iris.heap_lang Require Import proofmode notation.
From iris.base_logic.lib Require Import proph_map.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Definition heapΣ SI : gFunctors SI := #[invΣ SI; gen_heapΣ loc val; proph_mapΣ proph_id (val * val)].
Instance subG_heapPreG {SI} {Σ: gFunctors SI} : subG (heapΣ SI) Σ → heapPreG Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy {SI} `{TransfiniteIndex SI} (Σ: gFunctors SI) `{!heapPreG Σ} s e σ φ :
  (∀ `{!heapG Σ}, sbi_emp_valid (WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}%I)) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _). iIntros (??) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iModIntro. iExists
    (λ σ κs, (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I),
    (λ _, True%I).
  iFrame. iApply (Hwp (HeapG _ _ _ _ _)).
Qed.


Arguments satisfiable_at {_ _ _} _ _%I.
Lemma satisfiable_at_add {SI} (Σ: gFunctors SI) `{!invG Σ} E P Q: satisfiable_at E P → sbi_emp_valid Q → satisfiable_at E (P ∗ Q).
Proof.
  intros Hsat Hval. eapply satisfiable_at_mono; first eauto.
  iIntros "$". iApply Hval.
Qed.

Lemma satisfiable_at_add' {SI} (Σ: gFunctors SI) `{!invG Σ} E Q: satisfiable_at E True → sbi_emp_valid Q → satisfiable_at E Q.
Proof.
  intros Hsat Hval. eapply satisfiable_at_mono; first eauto.
  iIntros "_". iApply Hval.
Qed.
