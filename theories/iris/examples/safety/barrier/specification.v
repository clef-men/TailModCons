From iris.program_logic Require Export hoare.
From iris.heap_lang Require Import proofmode.
From iris.examples.safety.barrier Require Export barrier.
From iris.examples.safety.barrier Require Import proof.
Set Default Proof Using "Type".
Import uPred.

Section spec.
Local Set Default Proof Using "Type*".
Context `{Σ : gFunctors SI} `{!heapG Σ, !barrierG Σ}.

Lemma barrier_spec (N : namespace) :
  ∃ recv send : loc → iProp Σ -n> iProp Σ,
    (∀ P, ⊢ {{ True }} newbarrier #()
                     {{ v, ∃ l : loc, ⌜v = #l⌝ ∗ recv l P ∗ send l P }}) ∧
    (∀ l P, ⊢ {{ send l P ∗ P }} signal #l {{ _, True }}) ∧
    (∀ l P, ⊢ {{ recv l P }} wait #l {{ _, P }}) ∧
    (∀ l P Q, recv l (P ∗ Q) -∗ |={↑N, ∅}=> ▷ |={∅, ↑N}=> recv l P ∗ recv l Q) ∧
    (∀ l P Q, (P -∗ Q) -∗ recv l P -∗ recv l Q).
Proof.
  exists (λ l, OfeMor (recv N l)), (λ l, OfeMor (send N l)).
  split_and?; simpl.
  - iIntros (P) "!# _". iApply (newbarrier_spec _ P with "[]"); [done..|].
    iNext. eauto.
  - iIntros (l P) "!# [Hl HP]". iApply (signal_spec with "[$Hl $HP]"). by eauto.
  - iIntros (l P) "!# Hl". iApply (wait_spec with "Hl"). eauto.
  - iIntros (l P Q). by iApply recv_split.
  - apply recv_weaken.
Qed.
End spec.
