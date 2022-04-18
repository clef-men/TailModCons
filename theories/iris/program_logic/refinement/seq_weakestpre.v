From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import na_invariants.
From iris.program_logic.refinement Require Import ref_weakestpre tc_weakestpre.
Set Default Proof Using "Type".


(* sequential reasoning *)
Class seqG {SI} (Σ: gFunctors SI) := {
  seqG_na_invG :> na_invG Σ;
  seqG_name: gname;
}.

Definition seq {SI A Λ} {Σ: gFunctors SI} `{!source Σ A} `{!ref_irisG Λ Σ} `{!seqG Σ} E (e: expr Λ) Φ : iProp Σ :=
  (na_own seqG_name E -∗ RWP e ⟨⟨ v, na_own seqG_name E ∗ Φ v ⟩⟩)%I.

Definition se_inv {SI} {Σ: gFunctors SI} `{!invG Σ} `{!seqG Σ} (N: namespace) (P: iProp Σ) := na_inv seqG_name N P.

Notation "'SEQ' e @ E ⟨⟨ v , Q ⟩ ⟩" := (seq E e%E (λ v, Q)) (at level 20, e, Q at level 200,
format "'[' 'SEQ'  e  '/' '[          ' @  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'SEQ' e ⟨⟨ v , Q ⟩ ⟩" := (seq ⊤ e%E (λ v, Q)) (at level 20, e, Q at level 200,
format "'[' 'SEQ'  e  '/' '[          ' ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.

Lemma seq_value {SI A Λ} {Σ: gFunctors SI} `{!source Σ A} `{!ref_irisG Λ Σ} `{!seqG Σ} Φ E (v: val Λ) e `{!IntoVal e v}: Φ v ⊢ SEQ e @ E ⟨⟨ v, Φ v⟩⟩.
Proof.
  iIntros "Hv Hna". iApply rwp_value. iFrame.
Qed.


Notation "'SEQ' e @ E [{ v , Q } ]" := (@seq _ (ordA _) _ _ _ _ _ E e%E (λ v, Q)) (at level 20, e, Q at level 200,
format "'[' 'SEQ'  e  '/' '[          ' @  E  [{  v ,  Q  } ] ']' ']'") : bi_scope.
Notation "'SEQ' e [{ v , Q } ]" := (@seq _ (ordA _) _ _ _ _ _ ⊤ e%E (λ v, Q)) (at level 20, e, Q at level 200,
format "'[' 'SEQ'  e  '/' '[          ' [{  v ,  Q  } ] ']' ']'") : bi_scope.
