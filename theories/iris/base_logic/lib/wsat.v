From iris.base_logic.lib Require Export own.
From stdpp Require Export coPset namespaces.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

(** All definitions in this file are internal to [fancy_updates] with the
exception of what's in the [invG] module. The module [invG] is thus exported in
[fancy_updates], which [wsat] is only imported. *)
Module invG.
  Class invG {SI} (Σ : gFunctors SI) : Set := WsatG {
    inv_inG :> inG Σ (authR (gmapUR positive (agreeR (laterO (iPreProp Σ)))));
    enabled_inG :> inG Σ (coPset_disjR SI);
    disabled_inG :> inG Σ (gset_disjR positive);
    invariant_name : gname;
    enabled_name : gname;
    disabled_name : gname;
  }.

  Definition invΣ (SI: indexT) : gFunctors SI :=
    #[GFunctor (authRF (gmapURF positive (agreeRF (laterOF (idOF SI)))));
      GFunctor (coPset_disjUR SI);
      GFunctor (gset_disjUR positive)].

  Class invPreG {SI} (Σ : gFunctors SI) : Set := WsatPreG {
    inv_inPreG :> inG Σ (authR (gmapUR positive (agreeR (laterO (iPreProp Σ)))));
    enabled_inPreG :> inG Σ (coPset_disjR SI);
    disabled_inPreG :> inG Σ (gset_disjR positive);
  }.

  Instance subG_invΣ {SI} {Σ: gFunctors SI} : subG (invΣ SI) Σ → invPreG Σ.
  Proof. solve_inG. Qed.
End invG.
Import invG.

Definition invariant_unfold {SI} {Σ: gFunctors SI} (P : iProp Σ) : agree (later (iPreProp Σ)) :=
  to_agree (Next (iProp_unfold P)).
Definition ownI {SI} {Σ: gFunctors SI} `{!invG Σ} (i : positive) (P : iProp Σ) : iProp Σ :=
  own invariant_name (◯ {[ i := invariant_unfold P ]}).
Arguments ownI {_ _ _} _ _%I.
Typeclasses Opaque ownI.
Instance: Params (@invariant_unfold) 2 := {}.
Instance: Params (@ownI) 4 := {}.

Definition ownE {SI} {Σ: gFunctors SI} `{!invG Σ} (E : coPset) : iProp Σ :=
  own enabled_name (CoPset E).
Typeclasses Opaque ownE.
Instance: Params (@ownE) 4 := {}.

Definition ownD {SI} {Σ: gFunctors SI} `{!invG Σ} (E : gset positive) : iProp Σ :=
  own disabled_name (GSet E).
Typeclasses Opaque ownD.
Instance: Params (@ownD) 4 := {}.

Definition wsat {SI} {Σ: gFunctors SI} `{!invG Σ} : iProp Σ :=
  locked (∃ I : gmap positive (iProp Σ),
    own invariant_name (● (invariant_unfold <$> I : gmap _ _)) ∗
    [∗ map] i ↦ Q ∈ I, ▷ Q ∗ ownD {[i]} ∨ ownE {[i]})%I.

Section wsat.
Context {SI} {Σ: gFunctors SI} `{!invG Σ}.
Implicit Types P : iProp Σ.

(* Invariants *)
Instance invariant_unfold_contractive : Contractive (@invariant_unfold SI Σ).
Proof. intros α P Q H. unfold invariant_unfold.
       f_equiv. eapply Next_contractive. intros β Hβ.
         by rewrite (H β Hβ).
Qed.
Global Instance ownI_contractive i : Contractive (@ownI SI Σ _ i).
Proof. solve_contractive. Qed.
Global Instance ownI_persistent i P : Persistent (ownI i P).
Proof. rewrite /ownI. apply _. Qed.

Lemma ownE_empty : (|==> ownE ∅)%I.
Proof.
  rewrite /uPred_valid /bi_emp_valid.
  by rewrite (own_unit (coPset_disjUR SI) enabled_name).
Qed.
Lemma ownE_op E1 E2 : E1 ## E2 → ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof. intros. by rewrite /ownE -own_op coPset_disj_union. Qed.
Lemma ownE_disjoint E1 E2 : ownE E1 ∗ ownE E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownE -own_op own_valid. by iIntros (?%coPset_disj_valid_op). Qed.
Lemma ownE_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownE_op|].
  iIntros "HE". iDestruct (ownE_disjoint with "HE") as %?.
  iSplit; first done. iApply ownE_op; by try iFrame.
Qed.
Lemma ownE_singleton_twice i : ownE {[i]} ∗ ownE {[i]} ⊢ False.
Proof. rewrite ownE_disjoint. iIntros (?); set_solver. Qed.

Lemma ownD_empty : (|==> ownD ∅)%I.
Proof.
  rewrite /uPred_valid /bi_emp_valid.
  by rewrite (own_unit (gset_disjUR positive) disabled_name).
Qed.
Lemma ownD_op E1 E2 : E1 ## E2 → ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof. intros. by rewrite /ownD -own_op gset_disj_union. Qed.
Lemma ownD_disjoint E1 E2 : ownD E1 ∗ ownD E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownD -own_op own_valid. by iIntros (?%gset_disj_valid_op). Qed.
Lemma ownD_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownD_op|].
  iIntros "HE". iDestruct (ownD_disjoint with "HE") as %?.
  iSplit; first done. iApply ownD_op; by try iFrame.
Qed.
Lemma ownD_singleton_twice i : ownD {[i]} ∗ ownD {[i]} ⊢ False.
Proof. rewrite ownD_disjoint. iIntros (?); set_solver. Qed.

Lemma invariant_lookup (I : gmap positive (iProp Σ)) i P :
  own invariant_name (● (invariant_unfold <$> I : gmap _ _)) ∗
  own invariant_name (◯ {[i := invariant_unfold P]}) ⊢
  ∃ Q, ⌜I !! i = Some Q⌝ ∗ ▷ (Q ≡ P).
Proof.
  rewrite -own_op own_valid auth_both_validI /=. iIntros "[_ [#HI #HvI]]".
  iDestruct "HI" as (I') "HI". rewrite gmap_equivI gmap_validI.
  iSpecialize ("HI" $! i). iSpecialize ("HvI" $! i).
  rewrite lookup_fmap lookup_op lookup_singleton bi.option_equivI.
  case: (I !! i)=> [Q|] /=; [|case: (I' !! i)=> [Q'|] /=; by iExFalso].
  iExists Q; iSplit; first done.
  iAssert (invariant_unfold Q ≡ invariant_unfold P)%I as "?".
  { case: (I' !! i)=> [Q'|] //=.
    iRewrite "HI" in "HvI". rewrite uPred.option_validI agree_validI.
    iRewrite -"HvI" in "HI". by rewrite agree_idemp. }
  rewrite /invariant_unfold.
  by rewrite agree_equivI bi.later_equivI iProp_unfold_equivI.
Qed.

Lemma ownI_open i P : wsat ∗ ownI i P ∗ ownE {[i]} ⊢ wsat ∗ ▷ P ∗ ownD {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HiE)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup I i P with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_opM_delete _ _ i with "HI") as "[[[HQ $]|HiE'] HI]"; eauto.
  - iSplitR "HQ"; last by iNext; iRewrite -"HPQ".
    iExists I. iFrame "Hw". iApply (big_opM_delete _ _ i); eauto.
    iFrame "HI"; eauto.
  - iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as %[].
Qed.
Lemma ownI_close i P : wsat ∗ ownI i P ∗ ▷ P ∗ ownD {[i]} ⊢ wsat ∗ ownE {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HP & HiD)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_opM_delete _ _ i with "HI") as "[[[HQ ?]|$] HI]"; eauto.
  - iDestruct (ownD_singleton_twice with "[$]") as %[].
  - iExists I. iFrame "Hw". iApply (big_opM_delete _ _ i); eauto.
    iFrame "HI". iLeft. iFrame "HiD". by iNext; iRewrite "HPQ".
Qed.

Lemma ownI_alloc φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat ∗ ▷ P ==∗ ∃ i, ⌜φ i⌝ ∗ wsat ∗ ownI i P.
Proof.
  iIntros (Hfresh) "[Hw HP]". rewrite /wsat -!lock.
  iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HE".
  iMod (own_updateP with "[$]") as "HE".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom _ I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HE" as (X) "[Hi HE]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply auth_update_alloc,
     (alloc_singleton_local_update _ i (invariant_unfold P)); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite fmap_insert insert_singleton_op ?lookup_fmap ?HIi. }
  iApply (big_opM_insert _ I); first done.
  iFrame "HI". iLeft. by rewrite /ownD; iFrame.
Qed.

Lemma ownI_alloc_open φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat ==∗ ∃ i, ⌜φ i⌝ ∗ (ownE {[i]} -∗ wsat) ∗ ownI i P ∗ ownD {[i]}.
Proof.
  iIntros (Hfresh) "Hw". rewrite /wsat -!lock. iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HD".
  iMod (own_updateP with "[$]") as "HD".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom _ I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HD" as (X) "[Hi HD]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply auth_update_alloc,
     (alloc_singleton_local_update _ i (invariant_unfold P)); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  rewrite -/(ownD _). iFrame "HD".
  iIntros "HE". iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite fmap_insert insert_singleton_op ?lookup_fmap ?HIi. }
  iApply (big_opM_insert _ I); first done.
  iFrame "HI". by iRight.
Qed.
End wsat.

(* Allocation of an initial wolibrld *)
Lemma wsat_alloc_strong {SI: indexT} {Σ: gFunctors SI} `{!invPreG Σ} :
  bi_emp_valid (|==> ∃ γI γE γD : gname, let H := WsatG _ _ _ _ _ γI γE γD in wsat ∗ ownE ⊤)%I.
Proof.
  iIntros.
  iMod (own_alloc (● (∅ : gmap positive _))) as (γI) "HI"; first by rewrite auth_auth_valid.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro; iExists γI, γE, γD.
  rewrite /wsat /ownE -lock; iFrame.
  iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.


Lemma wsat_alloc {SI: indexT} {Σ: gFunctors SI} `{!invPreG Σ} :
  bi_emp_valid (|==> ∃ _ : invG Σ, wsat ∗ ownE ⊤)%I.
Proof.
  iIntros. iMod wsat_alloc_strong as (γI γE γD) "H". iModIntro.
  by iExists _.
Qed.


(* Global Invariants Instance *)
Definition γ_inv: gname := encode ("invariants.inv").
Definition γ_enabled: gname := encode ("invariants.enabled").
Definition γ_disabled: gname := encode ("invariants.disabled").
Definition inv_gnames : coPset := {[ γ_inv; γ_enabled; γ_disabled ]}.

Class invS {SI} (Σ : gFunctors SI) : Set := InvS {
  invS_inv_inG :> inG Σ (authR (gmapUR positive (agreeR (laterO (iPreProp Σ)))));
  invS_enabled_inG :> inG Σ (coPset_disjR SI);
  invS_disabled_inG :> inG Σ (gset_disjR positive);
}.

Instance invS_invG {SI} {Σ : gFunctors SI} (IS: invS Σ) : invG Σ :=
  WsatG _ _ _ _ _ γ_inv γ_enabled γ_disabled.


Lemma initial_wsat {SI} {Σ : gFunctors SI} `{invS SI Σ}:
  initial inv_gnames (wsat ∗ ownE ⊤)%I.
Proof.
  feed pose proof (initial_alloc γ_inv (● (∅ : gmap positive _))) as HI;
    first by rewrite auth_auth_valid.
  feed pose proof (initial_alloc γ_enabled (CoPset ⊤)) as HE;
    first done.
  feed pose proof (initial_alloc γ_disabled (GSet ∅)) as HD;
    first done.
  feed pose proof (initial_combine _ _ _ _ HI HE) as H1;
    first set_solver.
  feed pose proof (initial_combine _ _ _ _ H1 HD) as H2;
    first set_solver.
  eapply initial_mono; last eauto.
  rewrite /wsat /ownE -lock. iIntros "[[HI $] HD]".
  iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.

