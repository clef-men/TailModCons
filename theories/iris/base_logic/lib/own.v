From stdpp Require Import coPset.
From iris.algebra Require Import functions gmap.
From iris.base_logic.lib Require Export iprop.
From iris.algebra Require Import proofmode_classes.
Set Default Proof Using "Type".
Import uPred.

(** The class [inG Σ A] expresses that the CMRA [A] is in the list of functors
[Σ]. This class is similar to the [subG] class, but written down in terms of
individual CMRAs instead of (lists of) CMRA *functors*. This additional class is
needed because Coq is otherwise unable to solve type class constraints due to
higher-order unification problems. *)
Class inG {SI} (Σ : gFunctors SI) (A : cmraT SI) :=
  InG { inG_id : gid Σ; inG_prf : A = Σ inG_id (iPreProp Σ) _ }.
Arguments inG_id {_ _ _} _.

Lemma subG_inG {SI} Σ (F : gFunctor SI) : subG F Σ → inG Σ (F (iPreProp Σ) _).
Proof. move=> /(_ 0%fin) /= [j ->]. by exists j. Qed.

(** This tactic solves the usual obligations "subG ? Σ → {in,?}G ? Σ" *)
Ltac solve_inG :=
  (* Get all assumptions *)
  intros;
  (* Unfold the top-level xΣ. We need to support this to be a function. *)
  lazymatch goal with
  | H : subG (?xΣ _ _ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _) _ |- _ => try unfold xΣ in H
  | H : subG ?xΣ _ |- _ => try unfold xΣ in H
  end;
  (* Take apart subG for non-"atomic" lists *)
  repeat match goal with
         | H : subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
         end;
  (* Try to turn singleton subG into inG; but also keep the subG for typeclass
     resolution -- to keep them, we put them onto the goal. *)
  repeat match goal with
         | H : subG _ _ |- _ => move:(H); (apply subG_inG in H || clear H)
         end;
  (* Again get all assumptions *)
  intros;
  (* We support two kinds of goals: Things convertible to inG;
     and records with inG and typeclass fields. Try to solve the
     first case. *)
  try done;
  (* That didn't work, now we're in for the second case. *)
  split; (assumption || by apply _).

(** * Definition of the connective [own] *)
Definition iRes_singleton {SI} {Σ: gFunctors SI} {A} {i : inG Σ A} (γ : gname) (a : A) : iResUR Σ :=
  discrete_fun_singleton (inG_id i) {[ γ := cmra_transport inG_prf a ]}.
Instance: Params (@iRes_singleton) 4 := {}.

Definition own_def {SI} {Σ: gFunctors SI} `{!inG Σ A} (γ : gname) (a : A) : iProp Σ :=
  uPred_ownM (iRes_singleton γ a).
Definition own_aux : seal (@own_def). by eexists. Qed.
Definition own {SI Σ A i} := own_aux.(unseal) SI Σ A i.
Definition own_eq : @own = @own_def := own_aux.(seal_eq).
Instance: Params (@own) 5 := {}.
Typeclasses Opaque own.

(** * Properties about ghost ownership *)
Section global.
Context {SI} {Σ: gFunctors SI} `{Hin: !inG Σ A}.
Implicit Types a : A.

(** ** Properties of [iRes_singleton] *)
Global Instance iRes_singleton_ne γ :
  NonExpansive (@iRes_singleton SI Σ A _ γ).
Proof. by intros n a a' Ha; apply discrete_fun_singleton_ne; rewrite Ha. Qed.
Lemma iRes_singleton_op γ a1 a2 :
  iRes_singleton γ (a1 ⋅ a2) ≡ iRes_singleton γ a1 ⋅ iRes_singleton γ a2.
Proof.
  by rewrite /iRes_singleton discrete_fun_op_singleton op_singleton cmra_transport_op.
Qed.

(** ** Properties of [own] *)
Global Instance own_ne γ : NonExpansive (@own SI Σ A _ γ).
Proof. rewrite !own_eq. solve_proper. Qed.
Global Instance own_proper γ :
  Proper ((≡) ==> (⊣⊢)) (@own SI Σ A _ γ) := ne_proper _.

Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ∗ own γ a2.
Proof. by rewrite !own_eq /own_def -ownM_op iRes_singleton_op. Qed.
Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 ⊢ own γ a2.
Proof. move=> [c ->]. by rewrite own_op sep_elim_l. Qed.

Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (@own SI Σ A _ γ).
Proof. intros a1 a2. apply own_mono. Qed.

Lemma own_valid γ a : own γ a ⊢ ✓ a.
Proof.
  rewrite !own_eq /own_def ownM_valid /iRes_singleton.
  rewrite discrete_fun_validI (forall_elim (inG_id _)) discrete_fun_lookup_singleton.
  rewrite gmap_validI (forall_elim γ) lookup_singleton option_validI.
  (* implicit arguments differ a bit *)
  by trans (✓ cmra_transport inG_prf a : iProp Σ)%I; last destruct inG_prf.
Qed.
Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ✓ (a1 ⋅ a2).
Proof. apply wand_intro_r. by rewrite -own_op own_valid. Qed.
Lemma own_valid_3 γ a1 a2 a3 : own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
Proof. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
Proof. apply: bi.persistent_entails_r. apply own_valid. Qed.
Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
Proof. by rewrite comm -own_valid_r. Qed.

Global Instance own_timeless γ a : Discrete a → Timeless (own γ a).
Proof. rewrite !own_eq /own_def; apply _. Qed.
Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a).
Proof. rewrite !own_eq /own_def; apply _. Qed.

Lemma later_own `{FiniteIndex SI} γ a : ▷ own γ a -∗ ◇ (∃ b, own γ b ∧ ▷ (a ≡ b)).
Proof.
  rewrite own_eq /own_def later_ownM. apply exist_elim=> r.
  assert (NonExpansive (λ r : iResUR Σ, r (inG_id Hin) !! γ)).
  { intros n r1 r2 Hr. f_equiv. by specialize (Hr (inG_id _)). }
  rewrite (f_equiv (λ r : iResUR Σ, r (inG_id Hin) !! γ) _ r).
  rewrite {1}/iRes_singleton discrete_fun_lookup_singleton lookup_singleton.
  rewrite option_equivI. case Hb: (r (inG_id _) !! γ)=> [b|]; last first.
  { by rewrite and_elim_r /sbi_except_0 -or_intro_l. }
  rewrite -except_0_intro -(exist_intro (cmra_transport (eq_sym inG_prf) b)).
  apply and_mono.
  - rewrite /iRes_singleton. assert (∀ {A A' : cmraT SI} (Heq : A' = A) (a : A),
      cmra_transport Heq (cmra_transport (eq_sym Heq) a) = a) as ->
      by (by intros ?? ->).
    apply ownM_mono=> /=.
    exists (discrete_fun_insert (inG_id _) (delete γ (r (inG_id Hin))) r).
    intros i'. rewrite discrete_fun_lookup_op.
    destruct (decide (i' = inG_id _)) as [->|?].
    + rewrite discrete_fun_lookup_insert discrete_fun_lookup_singleton.
      intros γ'. rewrite lookup_op. destruct (decide (γ' = γ)) as [->|?].
      * by rewrite lookup_singleton lookup_delete Hb.
      * by rewrite lookup_singleton_ne // lookup_delete_ne // left_id.
    + rewrite discrete_fun_lookup_insert_ne //.
      by rewrite discrete_fun_lookup_singleton_ne // left_id.
  - apply later_mono.
    by assert (∀ {A A' : cmraT SI} (Heq : A' = A) (a' : A') (a : A),
      cmra_transport Heq a' ≡ a ⊢@{iPropI Σ}
        a' ≡ cmra_transport (eq_sym Heq) a) as -> by (by intros ?? ->).
Qed.

(** ** Allocation *)
(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc_strong a (P : gname → Prop) :
  pred_infinite P →
  ✓ a → bi_emp_valid (|==> ∃ γ, ⌜P γ⌝ ∧ own γ a)%I.
Proof.
  intros HP Ha.
  rewrite -(bupd_mono (∃ m, ⌜∃ γ, P γ ∧ m = iRes_singleton γ a⌝ ∧ uPred_ownM m)%I).
  - rewrite /uPred_valid /bi_emp_valid (ownM_unit emp).
    eapply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty (inG_id _));
      first (eapply alloc_updateP_strong', cmra_transport_valid, Ha);
      naive_solver.
  - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]].
    by rewrite !own_eq /own_def -(exist_intro γ) pure_True // left_id.
Qed.
Lemma own_alloc_cofinite a (G : gset gname) :
  ✓ a → bi_emp_valid (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ own γ a)%I.
Proof.
  intros Ha.
  apply (own_alloc_strong a (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (i := fresh (G ∪ E)).
  exists i. apply not_elem_of_union, is_fresh.
Qed.
Lemma own_alloc a : ✓ a → bi_emp_valid (|==> ∃ γ, own γ a)%I.
Proof.
  intros Ha. rewrite /uPred_valid /bi_emp_valid (own_alloc_cofinite a ∅) //; [].
  apply bupd_mono, exist_mono=>?. eauto using and_elim_r.
Qed.

(** ** Frame preserving updates *)
Lemma own_updateP P γ a : a ~~>: P → own γ a ==∗ ∃ a', ⌜P a'⌝ ∧ own γ a'.
Proof.
  intros Ha. rewrite !own_eq.
  rewrite -(bupd_mono (∃ m, ⌜∃ a', m = iRes_singleton γ a' ∧ P a'⌝ ∧ uPred_ownM m)%I).
  - eapply bupd_ownM_updateP, discrete_fun_singleton_updateP;
      first by (eapply singleton_updateP', cmra_transport_updateP', Ha).
    naive_solver.
  - apply exist_elim=>m; apply pure_elim_l=>-[a' [-> HP]].
    rewrite -(exist_intro a'). by apply and_intro; [apply pure_intro|].
Qed.

Lemma own_update γ a a' : a ~~> a' → own γ a ==∗ own γ a'.
Proof.
  intros; rewrite (own_updateP (eq a')); last by apply cmra_update_updateP.
  by apply bupd_mono, exist_elim=> a''; apply pure_elim_l=> ->.
Qed.
Lemma own_update_2 γ a1 a2 a' :
  a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'.
Proof. intros. apply wand_intro_r. rewrite -own_op. by apply own_update. Qed.
Lemma own_update_3 γ a1 a2 a3 a' :
  a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
Proof. intros. do 2 apply wand_intro_r. rewrite -!own_op. by apply own_update. Qed.
End global.

Arguments own_valid {_ _ _} [_] _ _.
Arguments own_valid_2 {_ _ _} [_] _ _ _.
Arguments own_valid_3 {_ _ _} [_] _ _ _ _.
Arguments own_valid_l {_ _ _} [_] _ _.
Arguments own_valid_r {_ _ _} [_] _ _.
Arguments own_updateP {_ _ _} [_] _ _ _ _.
Arguments own_update {_ _ _} [_] _ _ _ _.
Arguments own_update_2 {_ _ _} [_] _ _ _ _ _.
Arguments own_update_3 {_ _ _} [_] _ _ _ _ _ _.

Lemma own_unit {SI} A `{!inG Σ (A:ucmraT SI)} γ : (|==> own γ ε)%I.
Proof.
  rewrite /uPred_valid /bi_emp_valid (ownM_unit emp) !own_eq /own_def.
  apply bupd_ownM_update, discrete_fun_singleton_update_empty.
  apply (alloc_unit_singleton_update (cmra_transport inG_prf ε)); last done.
  - apply cmra_transport_valid, ucmra_unit_valid.
  - intros x; destruct inG_prf. by rewrite left_id.
Qed.

(* TODO: this is a nice property but we do not have a usecase yet. *)
Lemma cmra_own_exists_commute {SI} {Σ: gFunctors SI} (A: cmraT SI) `{Hin: !inG Σ A} X (φ: X → iProp Σ) a γ : ✓ a → (∀ b n, ✓{n} b → ✓{n} (b ⋅ a)) → ((own γ a -∗ ∃ x, φ x) ⊢ (∃ x, own γ a -∗ φ x))%I.
Proof.
  intros HvalA Hval. rewrite own_eq /own_def; apply uPred_primitive.exists_own_wand.
  intros f n Hv. intros id γ'; simpl.
  rewrite discrete_fun_lookup_op /iRes_singleton.
  destruct (decide (inG_id _ = id)) as [[]|].
  - rewrite discrete_fun_lookup_singleton lookup_op.
    destruct (decide (γ = γ')) as [->|].
    + rewrite lookup_singleton. specialize (Hv (inG_id Hin) γ').
      destruct ((@lookup gname _ _ (@gmap_lookup gname _ _ (@cmra_car SI _)) γ' (f (inG_id Hin)))) as [u|].
      * rewrite -Some_op /cmra_transport. destruct inG_prf. simpl.
        apply Some_validN, Hval, Hv.
      * rewrite left_id. apply Some_validN, cmra_transport_validN.
        apply cmra_valid_validN, HvalA.
    + rewrite lookup_singleton_ne; auto.
      rewrite right_id. by apply Hv.
  - rewrite discrete_fun_lookup_singleton_ne; auto.
    rewrite right_id. by apply Hv.
Qed.


Lemma ucmra_own_exists_commute {SI} {Σ: gFunctors SI} (A: ucmraT SI) `{Hin: !inG Σ A} X (φ: X → iProp Σ) a γ : (∀ b n, ✓{n} b → ✓{n} (b ⋅ a)) → ((own γ a -∗ ∃ x, φ x) ⊢ (∃ x, own γ a -∗ φ x))%I.
Proof.
  intros Hval. apply cmra_own_exists_commute; last done.
  assert (a ≡ ε ⋅ a) as -> by (rewrite left_id //=).
  apply cmra_valid_validN; intros n; apply Hval, ucmra_unit_validN.
Qed.

(** Big op class instances *)
Instance own_cmra_sep_homomorphism {SI} `{!inG Σ (A:ucmraT SI)} :
  WeakMonoidHomomorphism op uPred_sep (≡) (own γ).
Proof. split; try apply _. apply own_op. Qed.

(** Proofmode class instances *)
Section proofmode_classes.
  Context {SI} {Σ: gFunctors SI} `{!inG Σ A}.
  Implicit Types a b : A.

  Global Instance into_sep_own γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) own_op. Qed.
  Global Instance into_and_own p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) own_op sep_and. Qed.

  Global Instance from_sep_own γ a b1 b2 :
    IsOp a b1 b2 → FromSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /FromSep -own_op -is_op. Qed.
  Global Instance from_and_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (own γ a) (own γ b1) (own γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_classes.


Definition initial_def {SI} {Σ: gFunctors SI} (G: coPset) (P: iProp Σ): Prop :=
  (∃ m: iResUR Σ, ✓ m ∧ (∀ i, dom _ (m i) ⊆ G) ∧ (uPred_ownM m ⊢ P)).
Definition initial_aux : seal (@initial_def). by eexists. Qed.
Definition initial {SI Σ} := initial_aux.(unseal) SI Σ.
Definition initial_eq : @initial = @initial_def := initial_aux.(seal_eq).
Instance: Params (@initial) 4 := {}.
Typeclasses Opaque initial.


(* TODO: the following lemma is a modified version of dom_op. There should be a lemma generalizing both. *)
Lemma dom_coPset_op {SI} {A : cmraT SI} (m1 m2: gmap gname A) : dom coPset (m1 ⋅ m2) = dom _ m1 ∪ dom _ m2.
Proof.
  apply elem_of_equiv_L=> i; rewrite elem_of_union !elem_of_dom.
  unfold is_Some; setoid_rewrite lookup_op.
  destruct (@lookup positive _ _ (@gmap_lookup positive _ _ (@cmra_car SI A)) i m1),
            (@lookup positive _ _ (@gmap_lookup positive _ _ (@cmra_car SI A)) i m2);
  naive_solver.
Qed.

Lemma initial_alloc {SI} {Σ: gFunctors SI} `{!inG Σ A} (γ : gname) (a : A):
  ✓ a → initial {[ γ ]} (own γ a).
Proof.
  rewrite initial_eq /initial_def.
  intros Hv. exists (iRes_singleton γ a). split; [|split].
  - unfold iRes_singleton.
    apply cmra_valid_validN. intros α.
    apply discrete_fun_singleton_validN.
    by apply cmra_valid_validN, singleton_valid, cmra_transport_valid.
  - intros i γ'. rewrite /iRes_singleton.
    unfold discrete_fun_singleton, discrete_fun_insert.
    destruct decide.
    + destruct e; simpl. by rewrite dom_singleton.
    + naive_solver.
  - by rewrite own_eq /own_def.
Qed.


Lemma initial_combine {SI} {Σ: gFunctors SI} G1 G2 (P Q: iProp Σ):
  initial G1 P → initial G2 Q → G1 ## G2 → initial (G1 ∪ G2) (P ∗ Q)%I.
Proof.
  rewrite initial_eq /initial_def; intros (m1 & V1 & H1 & HP) (m2 & V2 & H2 & HQ) G12.
  exists (λ i, m1 i ⋅ m2 i). split; [|split].
  - intros i γ. rewrite lookup_op.
    specialize (H1 i). specialize (H2 i).
    destruct (m1 i !! γ) as [r|] eqn: EQ1; first destruct (m2 i !! γ) as [r'|] eqn: EQ2.
    + assert (γ ∈ dom coPset (m1 i))
        by by apply (elem_of_dom_2 (m1 i) γ r (D := coPset)).
      assert (γ ∈ dom coPset (m2 i))
        by by apply (elem_of_dom_2 (m2 i) γ r' (D := coPset)).
      set_solver.
    + rewrite EQ2 right_id. apply V1.
    + rewrite EQ1 left_id. apply V2.
  - intros i. rewrite dom_coPset_op. set_solver.
  - by rewrite ownM_op HP HQ.
Qed.

Lemma initial_mono {SI} {Σ: gFunctors SI} G (P Q: iProp Σ):
  (P ⊢ Q) → initial G P → initial G Q.
Proof.
  rewrite initial_eq /initial_def.
  intros PQ (m & V & H & HP).
  exists m; split; last split; eauto.
  by rewrite HP PQ.
Qed.

Lemma initial_weaken {SI} {Σ: gFunctors SI} G1 G2 (P: iProp Σ):
  initial G1 P → G1 ⊆ G2 → initial G2 P.
Proof.
  rewrite initial_eq /initial_def.
  intros (m & V & H & HP) Hsub.
  exists m; split; last split; eauto.
  set_solver.
Qed.

From iris.base_logic Require Import satisfiable.
Lemma initial_satisfiable {SI} {Σ: gFunctors SI} G (P: iProp Σ):
  initial G P → satisfiable P.
Proof.
  rewrite initial_eq /initial_def.
  intros (m & V & H & HP). simpl.
  intros α. exists m. split.
  - by apply cmra_valid_validN.
  - destruct HP as [HP]. apply HP; first by apply cmra_valid_validN.
    unseal. rewrite /uPred_ownM_def. exists ε.
    by rewrite right_id.
Qed.