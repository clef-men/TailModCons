From iris.base_logic Require Export own.
From iris.algebra Require Import agree ofe.
From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* "Saved anything" -- this can give you saved propositions, saved predicates,
   saved whatever-you-like. *)

Class savedAnythingG (SI : indexT) (Σ : gFunctors SI) (F : oFunctor SI) := SavedAnythingG {
  saved_anything_inG :> inG Σ (agreeR (F (iPreProp Σ)));
  saved_anything_contractive : oFunctorContractive F (* NOT an instance to avoid cycles with [subG_savedAnythingΣ]. *)
}.
Definition savedAnythingΣ (SI : indexT) (F : oFunctor SI) `{!oFunctorContractive F} : gFunctors SI :=
  #[ GFunctor (agreeRF F) ].

Instance subG_savedAnythingΣ {SI Σ} {F : oFunctor SI} `{!oFunctorContractive F} :
  subG (savedAnythingΣ SI F) Σ → savedAnythingG SI Σ F.
Proof. solve_inG. Qed.

Definition saved_anything_own {SI} `{!savedAnythingG SI Σ F}
    (γ : gname) (x : F (iProp Σ)) : iProp Σ :=
  own γ (to_agree $ (oFunctor_map F (iProp_fold, iProp_unfold) x)).
Typeclasses Opaque saved_anything_own.
Instance: Params (@saved_anything_own) 4 := {}.

Section saved_anything.
  Context `{!savedAnythingG SI Σ F}.
  Implicit Types x y : F (iProp Σ).
  Implicit Types γ : gname.

  Global Instance saved_anything_persistent γ x :
    Persistent (saved_anything_own γ x).
  Proof. rewrite /saved_anything_own; apply _. Qed.

  Global Instance saved_anything_ne γ : NonExpansive (saved_anything_own γ).
  Proof. solve_proper. Qed.
  Global Instance saved_anything_proper γ : Proper ((≡) ==> (≡)) (saved_anything_own γ).
  Proof. solve_proper. Qed.

  Lemma saved_anything_alloc_strong x (I : gname → Prop) :
    pred_infinite I →
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∧ saved_anything_own γ x.
  Proof. intros ?. by apply own_alloc_strong. Qed.

  Lemma saved_anything_alloc_cofinite x (G : gset gname) :
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_anything_own γ x. 
  Proof. by apply own_alloc_cofinite. Qed.

  Lemma saved_anything_alloc x : ⊢ |==> ∃ γ, saved_anything_own γ x. 
  Proof. by apply own_alloc. Qed.

  Lemma saved_anything_agree γ x y :
    saved_anything_own γ x -∗ saved_anything_own γ y -∗ x ≡ y.
  Proof.
    iIntros "Hx Hy". rewrite /saved_anything_own.
    iDestruct (own_valid_2 with "Hx Hy") as "Hv".
    rewrite agree_validI agree_equivI.
    set (G1 := oFunctor_map F (iProp_fold, iProp_unfold)).
    set (G2 := oFunctor_map F (@iProp_unfold _ Σ, @iProp_fold _ Σ)).
    assert (∀ z, G2 (G1 z) ≡ z) as help.
    { intros z. rewrite /G1 /G2 -oFunctor_compose -{2}[z]oFunctor_id.
      apply (ne_proper (oFunctor_map F)); split=>?; apply iProp_fold_unfold. }
    rewrite -{2}[x]help -{2}[y]help. by iApply f_equiv.
  Qed.
End saved_anything.

(** Provide specialized versions of this for convenience. **)

(* Saved propositions. *)
Notation savedPropG Σ := (savedAnythingG _ Σ (▶ ( ∙ _))).
Notation savedPropΣ := (savedAnythingΣ _ (▶ (∙ _))).

Definition saved_prop_own {SI} {Σ : gFunctors SI} `{!savedPropG Σ} (γ : gname) (P: iProp Σ) :=
  saved_anything_own (F := ▶ (∙ _)) γ (Next P).

Instance saved_prop_own_contractive {SI} {Σ : gFunctors SI} `{!savedPropG Σ} γ :
  Contractive (saved_prop_own γ).
Proof. solve_contractive. Qed.

Lemma saved_prop_alloc_strong {SI} {Σ : gFunctors SI} `{!savedPropG Σ} (I : gname → Prop) (P: iProp Σ) :
  pred_infinite I →
  ⊢ |==> ∃ γ, ⌜I γ⌝ ∧ saved_prop_own γ P. 
Proof. iIntros (?). by iApply saved_anything_alloc_strong. Qed.

Lemma saved_prop_alloc_cofinite {SI} {Σ : gFunctors SI} `{!savedPropG Σ} (G : gset gname) (P: iProp Σ) :
  ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_prop_own γ P. 
Proof. iApply saved_anything_alloc_cofinite. Qed.

Lemma saved_prop_alloc `{Σ : gFunctors SI} `{!savedPropG Σ} (P: iProp Σ) :
  ⊢ |==> ∃ γ, saved_prop_own γ P. 
Proof. iApply saved_anything_alloc. Qed.

Lemma saved_prop_agree `{Σ : gFunctors SI} `{!savedPropG Σ} γ P Q :
  saved_prop_own γ P -∗ saved_prop_own γ Q -∗ ▷ (P ≡ Q).
Proof.
  iIntros "HP HQ". iApply later_equivI. iApply (saved_anything_agree with "HP HQ").
Qed.

(* Saved predicates. *)
Notation savedPredG Σ A := (savedAnythingG _ Σ (A -d> ▶ (∙ _))).
Notation savedPredΣ A := (savedAnythingΣ _ (A -d> ▶ (∙ _))).

Definition saved_pred_own `{Σ : gFunctors SI} `{!savedPredG Σ A} (γ : gname) (Φ : A → iProp Σ) :=
  saved_anything_own (F := A -d> ▶ (∙ _)) γ (OfeMor Next ∘ Φ).

Instance saved_pred_own_contractive `{Σ : gFunctors SI} `{!savedPredG Σ A} γ :
  Contractive (saved_pred_own γ : (A -d> iProp Σ) → iProp Σ).
Proof.
  solve_proper_prepare. 
  f_equiv. intros a; simpl. f_contractive.
  intros ??. by apply H. 
Qed.

Lemma saved_pred_alloc_strong `{Σ : gFunctors SI} `{!savedPredG Σ A} (I : gname → Prop) (Φ : A → iProp Σ) :
  pred_infinite I →
  ⊢ |==> ∃ γ, ⌜I γ⌝ ∧ saved_pred_own γ Φ. 
Proof. iIntros (?). by iApply saved_anything_alloc_strong. Qed.

Lemma saved_pred_alloc_cofinite `{Σ : gFunctors SI} `{!savedPredG Σ A} (G : gset gname) (Φ : A → iProp Σ) :
  ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_pred_own γ Φ. 
Proof. iApply saved_anything_alloc_cofinite. Qed.

Lemma saved_pred_alloc `{Σ : gFunctors SI} `{!savedPredG Σ A} (Φ : A → iProp Σ) :
  ⊢ |==> ∃ γ, saved_pred_own γ Φ. 
Proof. iApply saved_anything_alloc. Qed.

(* We put the `x` on the outside to make this lemma easier to apply. *)
Lemma saved_pred_agree `{Σ : gFunctors SI} `{!savedPredG Σ A} γ Φ Ψ x :
  saved_pred_own γ Φ -∗ saved_pred_own γ Ψ -∗ ▷ (Φ x ≡ Ψ x).
Proof.
  unfold saved_pred_own. iIntros "#HΦ #HΨ /=". iApply later_equivI.
  iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
  by iDestruct (discrete_fun_equivI with "Heq") as "?".
Qed.
