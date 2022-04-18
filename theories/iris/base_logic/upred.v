From Coq.Init Require Import Nat.
From iris.algebra Require Export cmra updates.
From iris.bi Require Import notation.
From stdpp Require Import finite.
Set Default Proof Using "Type".
Local Hint Extern 1 (_ ≼ _) => etrans; [eassumption|] : index.
Local Hint Extern 1 (_ ≼ _) => etrans; [|eassumption] : index.
(*Local Hint Extern 10 (_ ≤ _) => lia : core.*)
Local Hint Extern 10 (_ ⪯ _) => by etransitivity : core.

(** The basic definition of the uPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

(* A good way of understanding this definition of the uPred OFE is to
   consider the OFE uPred0 of monotonous SProp predicates. That is,
   uPred0 is the OFE of non-expansive functions from M to SProp that
   are monotonous with respect to CMRA inclusion. This notion of
   monotonicity has to be stated in the SProp logic. Together with the
   usual closedness property of SProp, this gives exactly uPred_mono.

   Then, we quotient uPred0 *in the sProp logic* with respect to
   equivalence on valid elements of M. That is, we quotient with
   respect to the following *sProp* equivalence relation:
     P1 ≡ P2 := ∀ x, ✓ x → (P1(x) ↔ P2(x))       (1)
   When seen from the ambiant logic, obtaining this quotient requires
   definig both a custom Equiv and Dist.


   It is worth noting that this equivalence relation admits canonical
   representatives. More precisely, one can show that every
   equivalence class contains exactly one element P0 such that:
     ∀ x, (✓ x → P0(x)) → P0(x)                 (2)
   (Again, this assertion has to be understood in sProp). Intuitively,
   this says that P0 trivially holds whenever the resource is invalid.
   Starting from any element P, one can find this canonical
   representative by choosing:
     P0(x) := ✓ x → P(x)                        (3)

   Hence, as an alternative definition of uPred, we could use the set
   of canonical representatives (i.e., the subtype of monotonous
   sProp predicates that verify (2)). This alternative definition would
   save us from using a quotient. However, the definitions of the various
   connectives would get more complicated, because we have to make sure
   they all verify (2), which sometimes requires some adjustments. We
   would moreover need to prove one more property for every logical
   connective.
 *)

Record uPred {I: indexT} (M : ucmraT I) : Type := UPred {
  uPred_holds :> I → M → Prop;

  uPred_mono n1 n2 x1 x2 :
    uPred_holds n1 x1 → x1 ≼{n1} x2 → n2 ⪯ n1 → uPred_holds n2 x2
}.
Bind Scope bi_scope with uPred.
Arguments uPred_holds {_ _} _%I _ _ : simpl never.
Add Printing Constructor uPred.
Instance: Params (@uPred_holds) 4 := {}.

Section cofe.
  Context {SI: indexT} {M : ucmraT SI}.

  Inductive uPred_equiv' (P Q : uPred M) : Prop :=
    { uPred_in_equiv : ∀ n x, ✓{n} x → P n x ↔ Q n x }.
  Instance uPred_equiv : Equiv (uPred M) := uPred_equiv'.
  Inductive uPred_dist' (n : SI) (P Q : uPred M) : Prop :=
    { uPred_in_dist : ∀ n' x, n' ⪯ n → ✓{n'} x → P n' x ↔ Q n' x }.
  Instance uPred_dist : Dist SI (uPred M) := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin SI (uPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q i x);[apply HP|apply HQ].
    - intros α β P Q HPQ Hpre; split=> i x ??; apply HPQ;[|eauto]. transitivity β; eauto.
  Qed.
  Canonical Structure uPredO : ofeT SI := OfeT (uPred M) uPred_ofe_mixin.

  Program Definition uPred_compl : chain uPredO → uPredO := λ c,
    {| uPred_holds n x := ∀ n', n' ⪯ n → ✓{n'}x → c n' n' x |}.
  Next Obligation.
    move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply uPred_mono.
    eapply HP, cmra_validN_includedN, cmra_includedN_le=>//; transitivity n2; eauto.
    eapply cmra_includedN_le=>//; transitivity n2; eauto. done.
  Qed.

  Program Definition uPred_bcompl' α : bchain uPredO α → uPredO := λ c,
    {| uPred_holds n x := ∀ n' (Hn': n' ≺ α), n' ⪯ n →  ✓{n'}x → c n' Hn' n' x |}.
    Next Obligation.
    move=> /= α c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn3 Hn23 Hv. eapply uPred_mono.
    eapply HP, cmra_validN_includedN, cmra_includedN_le=>//; transitivity n2; eauto.
    eapply cmra_includedN_le=>//; transitivity n2; eauto. done.
  Qed.
  Lemma uPred_bcompl'_ne α (c d : bchain uPredO α) (β : SI): (∀ (γ : SI) (Hγ : γ ≺ α), c γ Hγ ≡{β}≡ d γ Hγ) → uPred_bcompl' α c ≡{β}≡ uPred_bcompl' α d.
  Proof.
    intros Hne; split=> i x Hiβ Hv; split.
    all: intros H' j Hjα Hji Hvj; specialize (H' j Hjα Hji Hvj); eapply Hne; eauto 4 with index.
  Qed.

  Definition uPred_bcompl α (Hα : zero ≺ α) := uPred_bcompl' α.

  Global Program Instance uPred_cofe : Cofe uPredO :=
    {| compl := uPred_compl; bcompl := uPred_bcompl |}.
  Next Obligation.
    intros α c; split=>i x Hiα Hv.
    etrans; [|by symmetry; apply (chain_cauchy' c)]. split=>H'; [by apply H'|].
    intros n' Hin' H. eapply (chain_cauchy' c n' i); eauto.
    by eapply uPred_mono.
  Qed.
  Next Obligation.
    intros α Hα c; split=>i x Hiα Hv.
    etrans; [|unshelve by symmetry; apply (bchain_cauchy' α c)]; eauto 2 with index.
    split=>H'; [by apply H'|]. intros n' Hn' Hin' H. unshelve eapply (bchain_cauchy' α c n' i); eauto 2 with index.
    by eapply uPred_mono.
  Qed.
  Next Obligation.
    intros. by apply uPred_bcompl'_ne.
  Qed.


  Lemma bcompl_unfold α Hα (C: bchain uPredO α) n x: bcompl Hα C n x ↔ ∀ n' (Hn': n' ≺ α), n' ⪯ n →  ✓{n'}x → C n' Hn' n' x.
  Proof. reflexivity. Qed.

  Lemma compl_unfold  (C: chain uPredO) n x: compl C n x ↔ ∀ n', n' ⪯ n →  ✓{n'}x → C n' n' x.
  Proof. reflexivity. Qed.

  Global Program Instance truncatable : ProtoTruncatable uPredO :=
  {
    proto_trunc α := λne a, uPred_bcompl' (index_succ _ α) (bchain_const a (index_succ _ α)  );
  }.
  Next Obligation.
    intros α α' x y Heq. by apply uPred_bcompl'_ne.
  Qed.
  Next Obligation.
    intros α x y H. cbn. constructor => n x' Hvn; split.
    all: intros H' j Hjα Hjn Hvj; cbn; apply H, H'; auto.
    all: apply index_succ_iff in Hjα; auto.
  Qed.
  Next Obligation.
    intros α x. cbn. constructor => n x' Hnα Hvn. split.
    - intros H'. apply H'; auto. apply index_succ_iff; auto.
    - intros H'. intros j Hjα Hjn Hvj. cbn. eapply uPred_mono.
      apply H'. all: auto.
  Qed.

  Global Instance bcompl_unique : BcomplUnique uPredO.
  Proof.
    intros α Hα c d Heq. constructor => n x Hna Hvn.
    rewrite !bcompl_unfold. split; intros H n' Hn' Hle Hvn'; apply Heq; eauto.
  Qed.

End cofe.
Arguments uPredO {_} _.

Instance uPred_ne {I} {M: ucmraT I} (P : uPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply uPred_mono; eauto; by rewrite Hx.
Qed.
Instance uPred_proper {I} {M: ucmraT I} (P : uPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply uPred_ne, equiv_dist. Qed.

Lemma uPred_holds_ne {I} {M: ucmraT I} (P Q : uPred M) n1 n2 x :
  P ≡{n2}≡ Q → n2 ⪯ n1 → ✓{n2} x → Q n1 x → P n2 x.
Proof.
  intros [Hne] ???. eapply Hne; try done. eauto using uPred_mono, cmra_validN_le.
Qed.

(* Equivalence to the definition of uPred in the appendix. *)
Lemma uPred_alt {I: indexT} {M : ucmraT I} (P: I → M → Prop) :
  (∀ n1 n2 x1 x2, P n1 x1 → x1 ≼{n1} x2 → n2 ⪯ n1 → P n2 x2) ↔
  ( (∀ x n1 n2, n2 ⪯ n1 → P n1 x → P n2 x) (* Pointwise down-closed *)
  ∧ (∀ n x1 x2, x1 ≡{n}≡ x2 → ∀ m, m ⪯ n → P m x1 ↔ P m x2) (* Non-expansive *)
  ∧ (∀ n x1 x2, x1 ≼{n} x2 → ∀ m, m ⪯ n → P m x1 → P m x2) (* Monotonicity *)
  ).
Proof.
  (* Provide this lemma to eauto. *)
  assert (∀ n1 n2 (x1 x2 : M), n2 ⪯ n1 → x1 ≡{n1}≡ x2 → x1 ≼{n2} x2).
  { intros ????? H. eapply cmra_includedN_le; last done. by rewrite H. }
  (* Now go ahead. *)
  split.
  - intros Hupred. repeat split; eauto using cmra_includedN_le.
  - intros (Hdown & _ & Hmono) **. eapply Hmono; [done..|]. eapply Hdown; done.
Qed.

(** functor *)
Program Definition uPred_map {I: indexT} {M1 M2 : ucmraT I} (f : M2 -n> M1)
  `{!CmraMorphism f} (P : uPred M1) :
  uPred M2 := {| uPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using uPred_mono, cmra_morphism_monotoneN. Qed.

Instance uPred_map_ne {I: indexT} {M1 M2 : ucmraT I} (f : M2 -n> M1)
  `{!CmraMorphism f} n : Proper (dist n ==> dist n) (uPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using cmra_morphism_validN.
Qed.
Lemma uPred_map_id {I} {M : ucmraT I} (P : uPred M): uPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed.
Lemma uPred_map_compose {I} {M1 M2 M3 : ucmraT I} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!CmraMorphism f, !CmraMorphism g} (P : uPred M3):
  uPred_map (g ◎ f) P ≡ uPred_map f (uPred_map g P).
Proof. by split=> n x Hx. Qed.
Lemma uPred_map_ext {I} {M1 M2 : ucmraT I} (f g : M1 -n> M2)
      `{!CmraMorphism f} `{!CmraMorphism g}:
  (∀ x, f x ≡ g x) → ∀ x, uPred_map f x ≡ uPred_map g x.
Proof. intros Hf P; split=> n x Hx /=; by rewrite /uPred_holds /= Hf. Qed.
Definition uPredO_map {I} {M1 M2 : ucmraT I} (f : M2 -n> M1) `{!CmraMorphism f} :
  uPredO M1 -n> uPredO M2 := OfeMor (uPred_map f : uPredO M1 → uPredO M2).
Lemma uPredO_map_ne {I} {M1 M2 : ucmraT I} (f g : M2 -n> M1)
    `{!CmraMorphism f, !CmraMorphism g} n :
  f ≡{n}≡ g → uPredO_map f ≡{n}≡ uPredO_map g.
Proof.
  by intros Hfg P; split=> n' y ??;
    rewrite /uPred_holds /= (dist_le _ _ _ _(Hfg y)).
Qed.

Program Definition uPredOF {I} (F : urFunctor I) : oFunctor I := {|
  oFunctor_car A B := uPredO (urFunctor_car F B A);
  oFunctor_map A1 A2 B1 B2 fg := uPredO_map (urFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros I F A1 A2 B1 B2 n P Q HPQ.
  apply uPredO_map_ne, urFunctor_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros I F A B P; simpl. rewrite -{2}(uPred_map_id P).
  apply uPred_map_ext=>y. by rewrite urFunctor_id.
Qed.
Next Obligation.
  intros I F A1 A2 A3 B1 B2 B3 f g f' g' P; simpl. rewrite -uPred_map_compose.
  apply uPred_map_ext=>y; apply urFunctor_compose.
Qed.

Instance uPredOF_contractive {I} (F: urFunctor I) :
  urFunctorContractive F → oFunctorContractive (uPredOF F).
Proof.
  intros ? A1 A2 B1 B2 n P Q HPQ. apply uPredO_map_ne, urFunctor_contractive.
  intros β Hβ; split; by apply HPQ.
Qed.

(** logical entailement *)
Inductive uPred_entails {I} {M: ucmraT I} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
Hint Resolve uPred_mono : uPred_def.

(** logical connectives *)
Program Definition uPred_pure_def {I} {M: ucmraT I} (φ : Prop) : uPred M :=
  {| uPred_holds n x := φ |}.
Solve Obligations with done.
Definition uPred_pure_aux : seal (@uPred_pure_def). by eexists. Qed.
Definition uPred_pure {I} {M: ucmraT I} := uPred_pure_aux.(unseal) I M.
Definition uPred_pure_eq :
  @uPred_pure = @uPred_pure_def := uPred_pure_aux.(seal_eq).

Program Definition uPred_and_def {I} {M: ucmraT I} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_and_aux : seal (@uPred_and_def). by eexists. Qed.
Definition uPred_and {I} {M} := uPred_and_aux.(unseal) I M.
Definition uPred_and_eq: @uPred_and = @uPred_and_def := uPred_and_aux.(seal_eq).

Program Definition uPred_or_def {I} {M: ucmraT I} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_or_aux : seal (@uPred_or_def). by eexists. Qed.
Definition uPred_or {I M} := uPred_or_aux.(unseal) I M.
Definition uPred_or_eq: @uPred_or = @uPred_or_def := uPred_or_aux.(seal_eq).

Program Definition uPred_impl_def {I} {M: ucmraT I} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       x ≼ x' → n' ⪯ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros I M P Q n1 n1' x1 x1' HPQ [x2 Hx1'] Hn1 n2 x3 [x4 Hx3] ?; simpl in *.
  rewrite Hx3 (dist_le _ _ _ _ Hx1'); auto. intros ??.
  eapply HPQ; auto. exists (x2 ⋅ x4); by rewrite assoc.
Qed.
Definition uPred_impl_aux : seal (@uPred_impl_def). by eexists. Qed.
Definition uPred_impl {I M} := uPred_impl_aux.(unseal) I M.
Definition uPred_impl_eq :
  @uPred_impl = @uPred_impl_def := uPred_impl_aux.(seal_eq).

Program Definition uPred_forall_def {I} {M: ucmraT I} {A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_forall_aux : seal (@uPred_forall_def). by eexists. Qed.
Definition uPred_forall {I M A} := uPred_forall_aux.(unseal) I M A.
Definition uPred_forall_eq :
  @uPred_forall = @uPred_forall_def := uPred_forall_aux.(seal_eq).

Program Definition uPred_exist_def {I} {M: ucmraT I} {A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_exist_aux : seal (@uPred_exist_def). by eexists. Qed.
Definition uPred_exist {I M A} := uPred_exist_aux.(unseal) I M A.
Definition uPred_exist_eq: @uPred_exist = @uPred_exist_def := uPred_exist_aux.(seal_eq).

Program Definition uPred_internal_eq_def {I} {M: ucmraT I} {A : ofeT I} (a1 a2 : A) : uPred M :=
  {| uPred_holds n x := a1 ≡{n}≡ a2 |}.
Solve Obligations with naive_solver eauto 2 using (dist_le (A:=A)).
Definition uPred_internal_eq_aux : seal (@uPred_internal_eq_def). by eexists. Qed.
Definition uPred_internal_eq {I M A} := uPred_internal_eq_aux.(unseal) I M A.
Definition uPred_internal_eq_eq:
  @uPred_internal_eq = @uPred_internal_eq_def := uPred_internal_eq_aux.(seal_eq).

Program Definition uPred_sep_def {I} {M: ucmraT I} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  intros I M P Q n1 n2 x y (x1&x2&Hx&?&?) [z Hy] Hn.
  exists x1, (x2 ⋅ z); split_and?; eauto using uPred_mono, cmra_includedN_l.
  eapply dist_le, Hn. by rewrite Hy Hx assoc.
Qed.
Definition uPred_sep_aux : seal (@uPred_sep_def). by eexists. Qed.
Definition uPred_sep {I M} := uPred_sep_aux.(unseal) I M.
Definition uPred_sep_eq: @uPred_sep = @uPred_sep_def := uPred_sep_aux.(seal_eq).

Program Definition uPred_wand_def {I} {M: ucmraT I} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       n' ⪯ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros I M P Q n1 n1' x1 x1' HPQ ? Hn n3 x3 ???; simpl in *.
  eapply uPred_mono with n3 (x1 ⋅ x3);
    eauto using cmra_validN_includedN, cmra_monoN_r, cmra_includedN_le.
Qed.
Definition uPred_wand_aux : seal (@uPred_wand_def). by eexists. Qed.
Definition uPred_wand {I M} := uPred_wand_aux.(unseal) I M.
Definition uPred_wand_eq :
  @uPred_wand = @uPred_wand_def := uPred_wand_aux.(seal_eq).

(* Equivalently, this could be `∀ y, P n y`.  That's closer to the intuition
   of "embedding the step-indexed logic in Iris", but the two are equivalent
   because Iris is afine.  The following is easier to work with. *)
Program Definition uPred_plainly_def {I} {M: ucmraT I} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using uPred_mono, ucmra_unit_validN.
Definition uPred_plainly_aux : seal (@uPred_plainly_def). by eexists. Qed.
Definition uPred_plainly {I M} := uPred_plainly_aux.(unseal) I M.
Definition uPred_plainly_eq :
  @uPred_plainly = @uPred_plainly_def := uPred_plainly_aux.(seal_eq).

Program Definition uPred_persistently_def {I} {M: ucmraT I} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (core x) |}.
Next Obligation.
  intros M; naive_solver eauto using uPred_mono, @cmra_core_monoN.
Qed.
Definition uPred_persistently_aux : seal (@uPred_persistently_def). by eexists. Qed.
Definition uPred_persistently {I M} := uPred_persistently_aux.(unseal) I M.
Definition uPred_persistently_eq :
  @uPred_persistently = @uPred_persistently_def := uPred_persistently_aux.(seal_eq).

Program Definition uPred_later_def {I} {M: ucmraT I} (P : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n', n' ≺ n → P n' x |}.
Next Obligation.
  intros I M P n1 n2 x1 x2 H1 H2 Hle n' Hlt; simpl in *.
  eapply uPred_mono. eapply H1.
  all: eauto using index_lt_le_trans, cmra_includedN_le.
Qed.
Definition uPred_later_aux : seal (@uPred_later_def). by eexists. Qed.
Definition uPred_later {I M} := uPred_later_aux.(unseal) I M.
Definition uPred_later_eq :
  @uPred_later = @uPred_later_def := uPred_later_aux.(seal_eq).

Program Definition uPred_ownM_def {I} {M: ucmraT I} (a : M) : uPred M :=
  {| uPred_holds n x := a ≼{n} x |}.
Next Obligation.
  intros I M a n1 n2 x1 x [a' Hx1] [x2 Hx] Hn. eapply cmra_includedN_le=>//.
  exists (a' ⋅ x2). by rewrite Hx(assoc op) Hx1.
Qed.
Definition uPred_ownM_aux : seal (@uPred_ownM_def). by eexists. Qed.
Definition uPred_ownM {I M} := uPred_ownM_aux.(unseal) I M.
Definition uPred_ownM_eq :
  @uPred_ownM = @uPred_ownM_def := uPred_ownM_aux.(seal_eq).

Program Definition uPred_cmra_valid_def {I} {M: ucmraT I} {A : cmraT I} (a : A) : uPred M :=
  {| uPred_holds n x := ✓{n} a |}.
Solve Obligations with naive_solver eauto 2 using cmra_validN_le.
Definition uPred_cmra_valid_aux : seal (@uPred_cmra_valid_def). by eexists. Qed.
Definition uPred_cmra_valid {I M A} := uPred_cmra_valid_aux.(unseal) I M A.
Definition uPred_cmra_valid_eq :
  @uPred_cmra_valid = @uPred_cmra_valid_def := uPred_cmra_valid_aux.(seal_eq).

Program Definition uPred_bupd_def {I} {M: ucmraT I} (Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ k yf,
      k ⪯ n → ✓{k} (x ⋅ yf) → ∃ x', ✓{k} (x' ⋅ yf) ∧ Q k x' |}.
Next Obligation.
  intros I M Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk.
  rewrite (dist_le _ _ _ _ Hx); last auto. intros Hxy.
  destruct (HQ k (x3 ⋅ yf)) as (x'&?&?); [auto|by rewrite assoc|].
  exists (x' ⋅ x3); split; first by rewrite -assoc.
  eauto using uPred_mono, cmra_includedN_l.
Qed.
Definition uPred_bupd_aux : seal (@uPred_bupd_def). by eexists. Qed.
Definition uPred_bupd {I M} := uPred_bupd_aux.(unseal) I M.
Definition uPred_bupd_eq :
  @uPred_bupd = @uPred_bupd_def := uPred_bupd_aux.(seal_eq).

(** Global uPred-specific Notation *)
Notation "✓ x" := (uPred_cmra_valid x) (at level 20) : bi_scope.

(** Promitive logical rules.
    These are not directly usable later because they do not refer to the BI
    connectives. *)
Module uPred_primitive.
Definition unseal_eqs :=
  (uPred_pure_eq, uPred_and_eq, uPred_or_eq, uPred_impl_eq, uPred_forall_eq,
  uPred_exist_eq, uPred_internal_eq_eq, uPred_sep_eq, uPred_wand_eq,
  uPred_plainly_eq, uPred_persistently_eq, uPred_later_eq, uPred_ownM_eq,
  uPred_cmra_valid_eq, @uPred_bupd_eq).
Ltac unseal :=
  rewrite !unseal_eqs /=.

Section primitive.
Context {I: indexT} {M : ucmraT I}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.
Arguments uPred_holds {_ _} !_ _ _ /.
Hint Immediate uPred_in_entails : core.

Notation "P ⊢ Q" := (@uPred_entails I M P%I Q%I) : stdpp_scope.
Notation "(⊢)" := (@uPred_entails I M) (only parsing) : stdpp_scope.
Notation "P ⊣⊢ Q" := (@uPred_equiv I M P%I Q%I) : stdpp_scope.
Notation "(⊣⊢)" := (@uPred_equiv I M) (only parsing) : stdpp_scope.

Notation "'True'" := (uPred_pure True) : bi_scope.
Notation "'False'" := (uPred_pure False) : bi_scope.
Notation "'⌜' φ '⌝'" := (uPred_pure φ%type%stdpp) : bi_scope.
Infix "∧" := uPred_and : bi_scope.
Infix "∨" := uPred_or : bi_scope.
Infix "→" := uPred_impl : bi_scope.
Notation "∀ x .. y , P" :=
  (uPred_forall (λ x, .. (uPred_forall (λ y, P)) ..)) : bi_scope.
Notation "∃ x .. y , P" :=
  (uPred_exist (λ x, .. (uPred_exist (λ y, P)) ..)) : bi_scope.
Infix "∗" := uPred_sep : bi_scope.
Infix "-∗" := uPred_wand : bi_scope.
Notation "□ P" := (uPred_persistently P) : bi_scope.
Notation "■ P" := (uPred_plainly P) : bi_scope.
Notation "x ≡ y" := (uPred_internal_eq x y) : bi_scope.
Notation "▷ P" := (uPred_later P) : bi_scope.
Notation "|==> P" := (uPred_bupd P) : bi_scope.
Notation "▷^ n P" := (Nat.iter n uPred_later P) : bi_scope.
Notation "▷? p P" := (Nat.iter (Nat.b2n p) uPred_later P) : bi_scope.
Notation "⧍ P" := (∃ n, ▷^n P)%I : bi_scope.
Notation "⧍^ n P" := (Nat.iter n (λ Q, ⧍ Q) P)%I : bi_scope.
(** Entailment *)
Lemma entails_po : PreOrder (⊢).
Proof.
  split.
  - by intros P; split=> x i.
  - by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
Qed.
Lemma entails_anti_sym : AntiSymm (⊣⊢) (⊢).
Proof. intros P Q HPQ HQP; split=> x n; by split; [apply HPQ|apply HQP]. Qed.
Lemma equiv_spec P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof.
  split.
  - intros HPQ; split; split=> x i; apply HPQ.
  - intros [??]. exact: entails_anti_sym.
Qed.
Lemma entails_lim (cP cQ : chain (uPredO M)) :
  (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
Proof.
  intros Hlim; split=> n m ? HP.
  eapply uPred_holds_ne, Hlim, HP; rewrite ?conv_compl; eauto using chain_cauchy.
Qed.

Lemma entails_blim α (cP cQ: bchain (uPredO M) α) Hα:
  (∀ β Hβ, cP β Hβ ⊢ cQ β Hβ) → bcompl Hα cP ⊢ bcompl Hα cQ.
Proof.
  intros Hlim; split=> β m Hv HP δ Hδ Hδβ Hv'.
  eapply Hlim, HP; eauto.
Qed.

(** Non-expansiveness and setoid morphisms *)
Lemma pure_ne n : Proper (iff ==> dist n) (@uPred_pure I M).
Proof. intros φ1 φ2 Hφ. by unseal; split. Qed.

Lemma and_ne : NonExpansive2 (@uPred_and I M).
Proof.
  intros n P P' HP Q Q' HQ; unseal; split=> x n' ??.
  split; (intros [??]; split; [by apply HP|by apply HQ]).
Qed.

Lemma or_ne : NonExpansive2 (@uPred_or I M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x n' ??.
  unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
Qed.

Lemma impl_ne :
  NonExpansive2 (@uPred_impl I M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x n' ??.
  unseal; split; intros HPQ x' n'' ????; apply HQ, HPQ, HP; auto.
Qed.

Lemma sep_ne : NonExpansive2 (@uPred_sep I M).
Proof.
  intros n P P' HP Q Q' HQ; split=> n' x ??.
  unseal; split; intros (x1&x2&?&?&?); ofe_subst x;
    exists x1, x2; split_and!; try (apply HP || apply HQ);
    eauto using cmra_validN_op_l, cmra_validN_op_r.
Qed.

Lemma wand_ne :
  NonExpansive2 (@uPred_wand I M).
Proof.
  intros n P P' HP Q Q' HQ; split=> n' x ??; unseal; split; intros HPQ x' n'' ???;
    apply HQ, HPQ, HP; eauto using cmra_validN_op_r.
Qed.

Lemma internal_eq_ne (A : ofeT I) :
  NonExpansive2 (@uPred_internal_eq I M A).
Proof.
  intros n x x' Hx y y' Hy; split=> n' z; unseal; split; intros; simpl in *.
  - hnf. by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy).
  - hnf. by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy).
Qed.

Lemma forall_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_forall I M A).
Proof.
  by intros Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
Qed.

Lemma exist_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_exist I M A).
Proof.
  intros Ψ1 Ψ2 HΨ.
  unseal; split=> n' x ??; split; intros [a ?]; exists a; by apply HΨ.
Qed.

Lemma later_contractive : Contractive (@uPred_later I M).
Proof.
  unseal; intros n P Q HPQ; split=> -n' x H ? //=; split=> Hl m Hm; eapply HPQ.
  all: eauto using index_lt_le_trans, cmra_validN_le.
Qed.

Lemma plainly_ne : NonExpansive (@uPred_plainly I M).
Proof.
  intros n P1 P2 HP.
  unseal; split=> n' x; split; apply HP; eauto using @ucmra_unit_validN.
Qed.

Lemma persistently_ne : NonExpansive (@uPred_persistently I M).
Proof.
  intros n P1 P2 HP.
  unseal; split=> n' x; split; apply HP; eauto using @cmra_core_validN.
Qed.

Lemma ownM_ne : NonExpansive (@uPred_ownM I M).
Proof.
  intros n a b Ha.
  unseal; split=> n' x ? ? /=.
  by rewrite (dist_le _ _ _ _ Ha).
Qed.

Lemma cmra_valid_ne {A : cmraT I} :
  NonExpansive (@uPred_cmra_valid I M A).
Proof.
  intros n a b Ha; unseal; split=> n' x ? /=.
  by rewrite (dist_le _ _ _ _ Ha).
Qed.

Lemma bupd_ne : NonExpansive (@uPred_bupd I M).
Proof.
  intros n P Q HPQ.
  unseal; split=> n' x; split; intros HP k yf ??;
    destruct (HP k yf) as (x'&?&?); auto;
    exists x'; split; auto; apply HPQ; eauto using cmra_validN_op_l.
Qed.

(** Introduction and elimination rules *)
Lemma pure_intro φ P : φ → P ⊢ ⌜φ⌝.
Proof. by intros ?; unseal; split. Qed.
Lemma pure_elim' φ P : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P.
Proof. unseal; intros HP; split=> n x ??. by apply HP. Qed.
Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ x : A, ⌜φ x⌝) ⊢ ⌜∀ x : A, φ x⌝.
Proof. by unseal. Qed.

Lemma and_elim_l P Q : P ∧ Q ⊢ P.
Proof. by unseal; split=> n x ? [??]. Qed.
Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
Proof. by unseal; split=> n x ? [??]. Qed.
Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
Proof. intros HQ HR; unseal; split=> n x ??; by split; [apply HQ|apply HR]. Qed.

Lemma or_intro_l P Q : P ⊢ P ∨ Q.
Proof. unseal; split=> n x ??; left; auto. Qed.
Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
Proof. unseal; split=> n x ??; right; auto. Qed.
Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
Proof. intros HP HQ; unseal; split=> n x ? [?|?]. by apply HP. by apply HQ. Qed.

Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
Proof.
  unseal; intros HQ; split=> n x ?? n' x' ????. apply HQ; [eauto|].
  split; eauto using uPred_mono, cmra_included_includedN.
Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof. unseal; intros HP ; split=> n x ? [??]; apply HP with n x; auto. Qed.

Lemma forall_intro {A} P (Ψ : A → uPred M): (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
Proof. unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ. Qed.
Lemma forall_elim {A} {Ψ : A → uPred M} a : (∀ a, Ψ a) ⊢ Ψ a.
Proof. unseal; split=> n x ? HP; apply HP. Qed.

Lemma exist_intro {A} {Ψ : A → uPred M} a : Ψ a ⊢ ∃ a, Ψ a.
Proof. unseal; split=> n x ??; by exists a. Qed.
Lemma exist_elim {A} (Φ : A → uPred M) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
Proof. unseal; intros HΦΨ; split=> n x ? [a ?]; by apply HΦΨ with a. Qed.

(** BI connectives *)
Lemma sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
Proof.
  intros HQ HQ'; unseal.
  split; intros n' x ? (x1&x2&?&?&?); exists x1,x2; ofe_subst x;
    eauto 7 using cmra_validN_op_l, cmra_validN_op_r, uPred_in_entails.
Qed.
Lemma True_sep_1 P : P ⊢ True ∗ P.
Proof.
  unseal; split; intros n x ??. exists (core x), x. by rewrite cmra_core_l.
Qed.
Lemma True_sep_2 P : True ∗ P ⊢ P.
Proof.
  unseal; split; intros n x ? (x1&x2&?&_&?); ofe_subst;
    eauto using uPred_mono, cmra_includedN_r.
Qed.
Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
Proof.
  unseal; split; intros n x ? (x1&x2&?&?&?); exists x2, x1; by rewrite (comm op).
Qed.
Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
Proof.
  unseal; split; intros n x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
  exists y1, (y2 ⋅ x2); split_and?; auto.
  + by rewrite (assoc op) -Hy -Hx.
  + by exists y2, x2.
Qed.
Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
Proof.
  unseal=> HPQR; split=> n x ?? n' x' ???; apply HPQR; auto.
  exists x, x'; split_and?; auto.
  eapply uPred_mono with n x; eauto using cmra_validN_op_l.
Qed.
Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
Proof.
  unseal =>HPQR. split; intros n x ? (?&?&?&?&?). ofe_subst.
  eapply HPQR; eauto using cmra_validN_op_l.
Qed.


(** persistently *)
Lemma persistently_mono P Q : (P ⊢ Q) → □ P ⊢ □ Q.
Proof. intros HP; unseal; split=> n x ? /=. by apply HP, cmra_core_validN. Qed.
Lemma persistently_elim P : □ P ⊢ P.
Proof.
  unseal; split=> n x ? /= H; eauto using uPred_mono, cmra_included_core, cmra_included_includedN.
Qed.
Lemma persistently_idemp_2 P : □ P ⊢ □ □ P.
Proof. unseal; split=> n x ?? /=. by rewrite cmra_core_idemp. Qed.

Lemma persistently_forall_2 {A} (Ψ : A → uPred M) : (∀ a, □ Ψ a) ⊢ (□ ∀ a, Ψ a).
Proof. by unseal. Qed.
Lemma persistently_exist_1 {A} (Ψ : A → uPred M) : (□ ∃ a, Ψ a) ⊢ (∃ a, □ Ψ a).
Proof. by unseal. Qed.

Lemma persistently_and_sep_l_1 P Q : □ P ∧ Q ⊢ P ∗ Q.
Proof.
  unseal; split=> n x ? [??]; exists (core x), x; simpl in *.
  by rewrite cmra_core_l.
Qed.

(** Plainly *)
Lemma plainly_mono P Q : (P ⊢ Q) → ■ P ⊢ ■ Q.
Proof. intros HP; unseal; split=> n x ? /=. apply HP, ucmra_unit_validN. Qed.
Lemma plainly_elim_persistently P : ■ P ⊢ □ P.
Proof. unseal; split; simpl; eauto using uPred_mono, @ucmra_unit_leastN. Qed.
Lemma plainly_idemp_2 P : ■ P ⊢ ■ ■ P.
Proof. unseal; split=> n x ?? //. Qed.

Lemma plainly_forall_2 {A} (Ψ : A → uPred M) : (∀ a, ■ Ψ a) ⊢ (■ ∀ a, Ψ a).
Proof. by unseal. Qed.
Lemma plainly_exist_1 {A} (Ψ : A → uPred M) : (■ ∃ a, Ψ a) ⊢ (∃ a, ■ Ψ a).
Proof. by unseal. Qed.

Lemma prop_ext P Q : ■ ((P -∗ Q) ∧ (Q -∗ P)) ⊢ P ≡ Q.
Proof.
  unseal; split=> n x ? /= HPQ. split=> n' x' ??.
    move: HPQ=> [] /(_ n' x'); rewrite !left_id=> ?.
    move=> /(_ n' x'); rewrite !left_id=> ?. naive_solver.
Qed.

(* The following two laws are very similar, and indeed they hold not just for □
   and ■, but for any modality defined as `M P n x := ∀ y, R x y → P n y`. *)
Lemma persistently_impl_plainly P Q : (■ P → □ Q) ⊢ □ (■ P → Q).
Proof.
  unseal; split=> /= n x ? HPQ n' x' ????.
  eapply uPred_mono with n' (core x)=>//; [|by apply cmra_included_includedN].
  apply (HPQ n' x); eauto using cmra_validN_le.
Qed.

Lemma plainly_impl_plainly P Q : (■ P → ■ Q) ⊢ ■ (■ P → Q).
Proof.
  unseal; split=> /= n x ? HPQ n' x' ????.
  eapply uPred_mono with n' ε=>//; [|by apply cmra_included_includedN].
  apply (HPQ n' x); eauto using cmra_validN_le.
Qed.

(** Later *)

Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
Proof.
  unseal=> HP; split=> -n x ?? n' ?. apply HP; eauto using cmra_validN_le.
Qed.
Lemma later_intro P : P ⊢ ▷ P.
Proof.
  unseal; split=> n /= x ? HP n' Hn'.
  apply uPred_mono with n x; eauto using cmra_validN_le.
Qed.
Lemma later_forall_2 {A} (Φ : A → uPred M) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
Proof. unseal; split=> n x Hv H n' Hn' a. by eapply H. Qed.
Lemma later_exist_false `{FI: FiniteIndex I} {A} (Φ : A → uPred M) :
  (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
Proof.
  unseal; split=> -n x Hv /= H; eauto.
  destruct (finite_index n) as [|[m []]]; eauto.
  right. edestruct H as [y]; eauto. exists y.
  intros; eauto using uPred_mono.
Qed.

Lemma later_finite_exist_false `{BI: FiniteBoundedExistential I} {A} (Φ : A → uPred M) (Q: A → Prop):
  pred_finite Q →
  (∀ a, Φ a ⊢ ⌜Q a⌝) →
  (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
Proof.
  intros Hq Hfin.
  unseal; split=> -n x Hv /= H; eauto.
  destruct (index_is_zero n) as [->|Hterm].
  - left. intros ? [] % index_lt_zero_is_normal.
  - destruct (can_commute_finite_bounded_exists _ (λ a n, Φ a n x) Q n); eauto using uPred_mono.
    intros m Hmn. destruct (H m Hmn) as [y HΦ]. destruct (Hfin y) as [HQ].
    exists y. split; eauto. revert HQ. unseal. intros HQ. eapply HQ; last eauto.
    eauto using cmra_validN_le.
Qed.

Lemma later_sep_1 `{FI: FiniteIndex I} P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q.
Proof.
  unseal; split=> n x ? //= H.
  destruct (finite_index n) as [Hterm|[m [Hmn ?]]]; eauto.
  { exists x, (core x); rewrite cmra_core_r; (repeat split; eauto); intros ? [] % Hterm. }
  destruct (H m Hmn) as (x1&x2&Hx&?&?). destruct (cmra_extend m x x1 x2) as (y1&y2&Hx'&Hy1&Hy2); eauto using cmra_validN_le; simpl in *.
  exists y1, y2; split; [by rewrite Hx'|]; split=> n' Hn'; eapply uPred_mono; eauto; by rewrite ?Hy1 ?Hy2.
Qed.
Lemma later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q).
Proof.
  unseal; split=> n x ? //=. intros (x1&x2&Hx&Hx1&Hx2) n' Hn'.
  exists x1, x2; repeat split; eauto using dist_le.
Qed.

Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
Proof.
  unseal; split=> -n x ? /= HP. destruct (index_lt_dec_minimum n) as [|[n']]; eauto.
  right. intros. eapply uPred_mono.
  - eapply HP; eauto.
  - eauto using cmra_included_includedN.
  - erewrite index_zero_is_unique at 1; eauto using index_zero_minimum.
Qed.

Lemma later_persistently_1 P : ▷ □ P ⊢ □ ▷ P.
Proof. by unseal. Qed.
Lemma later_persistently_2 P : □ ▷ P ⊢ ▷ □ P.
Proof. by unseal. Qed.
Lemma later_plainly_1 P : ▷ ■ P ⊢ ■ ▷ P.
Proof. by unseal. Qed.
Lemma later_plainly_2 P : ■ ▷ P ⊢ ▷ ■ P.
Proof. by unseal. Qed.

(** Internal equality *)
Lemma internal_eq_refl {A : ofeT I} P (a : A) : P ⊢ (a ≡ a).
Proof. unseal; by split=> n x ??; simpl. Qed.
Lemma internal_eq_rewrite {A : ofeT I} a b (Ψ : A → uPred M) :
  NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
Proof. intros HΨ. unseal; split=> n x ?? n' x' ??? Ha. by apply HΨ with n a. Qed.

Lemma fun_ext {A} {B : A → ofeT I} (g1 g2 : discrete_fun B) :
  (∀ i, g1 i ≡ g2 i) ⊢ g1 ≡ g2.
Proof. by unseal. Qed.
Lemma sig_eq {A : ofeT I} (P : A → Prop) (x y : sigO P) :
  proj1_sig x ≡ proj1_sig y ⊢ x ≡ y.
Proof. by unseal. Qed.

Lemma later_eq_1 {A : ofeT I} (x y : A) : Next x ≡ Next y ⊢ ▷ (x ≡ y).
Proof. by unseal. Qed.
Lemma later_eq_2 {A : ofeT I} (x y : A) : ▷ (x ≡ y) ⊢ Next x ≡ Next y.
Proof. by unseal. Qed.

Lemma discrete_eq_1 {A : ofeT I} (a b : A) : Discrete a → a ≡ b ⊢ ⌜a ≡ b⌝.
Proof.
  unseal=> ?. split=> n x ?. by apply (discrete_iff n).
Qed.

(** Basic update modality *)
Lemma bupd_intro P : P ⊢ |==> P.
Proof.
  unseal. split=> n x ? HP k yf ?; exists x; split; first done.
  apply uPred_mono with n x; eauto using cmra_validN_op_l.
Qed.
Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ⊢ |==> Q.
Proof.
  unseal. intros HPQ; split=> n x ? HP k yf ??.
  destruct (HP k yf) as (x'&?&?); eauto.
  exists x'; split; eauto using uPred_in_entails, cmra_validN_op_l.
Qed.
Lemma bupd_trans P : (|==> |==> P) ⊢ |==> P.
Proof. unseal; split; naive_solver. Qed.
Lemma bupd_frame_r P R : (|==> P) ∗ R ⊢ |==> P ∗ R.
Proof.
  unseal; split; intros n x ? (x1&x2&Hx&HP&?) k yf ??.
  destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto.
  { by rewrite assoc -(dist_le _ _ _ _ Hx); last auto. }
  exists (x' ⋅ x2); split; first by rewrite -assoc.
  exists x', x2. eauto using uPred_mono, cmra_validN_op_l, cmra_validN_op_r.
Qed.
Lemma bupd_plainly P : (|==> ■ P) ⊢ P.
Proof.
  unseal; split => n x Hnx /= Hng.
  destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
  eapply uPred_mono; eauto using ucmra_unit_leastN.
Qed.

(** Own *)
Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
Proof.
  unseal; split=> n x ?; split.
  - intros [z ?]; exists a1, (a2 ⋅ z); split; [by rewrite (assoc op)|].
    split. by exists (core a1); rewrite cmra_core_r. by exists z.
  - intros (y1&y2&Hx&[z1 Hy1]&[z2 Hy2]); exists (z1 ⋅ z2).
    by rewrite (assoc op _ z1) -(comm op z1) (assoc op z1)
      -(assoc op _ a2) (comm op z1) -Hy1 -Hy2.
Qed.
Lemma persistently_ownM_core (a : M) : uPred_ownM a ⊢ □ uPred_ownM (core a).
Proof.
  split=> n x /=; unseal; intros Hx. simpl. by apply cmra_core_monoN.
Qed.
Lemma ownM_unit P : P ⊢ (uPred_ownM ε).
Proof. unseal; split=> n x ??; by  exists x; rewrite left_id. Qed.
Lemma later_ownM `{FI: FiniteIndex I} a : ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ (a ≡ b).
Proof.
  unseal; split=> -n x /= ? Hax.
  destruct (finite_index n) as [H|[m []]].
  { exists x. split; eauto. intros ? [] % H. }
  edestruct Hax as [y ?]; eauto.
  destruct (cmra_extend m x a y) as (a'&y'&Hx&H2&?); eauto using cmra_validN_le.
  exists a'. rewrite Hx. split; eauto using cmra_includedN_l.
  intros; eapply dist_le. symmetry; eapply H2. eauto.
Qed.

Lemma bupd_ownM_updateP x (Φ : M → Prop) :
  x ~~>: Φ → uPred_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ uPred_ownM y.
Proof.
  unseal=> Hup; split=> n x2 ? [x3 Hx] k yf ??.
  destruct (Hup k (Some (x3 ⋅ yf))) as (y&?&?); simpl in *.
  { rewrite /= assoc -(dist_le _ _ _ _ Hx); auto. }
  exists (y ⋅ x3); split; first by rewrite -assoc.
  exists y; eauto using cmra_includedN_l.
Qed.

(** Valid *)
Lemma ownM_valid (a : M) : uPred_ownM a ⊢ ✓ a.
Proof.
  unseal; split=> n x Hv [a' ?]; ofe_subst; eauto using cmra_validN_op_l.
Qed.
Lemma cmra_valid_intro {A : cmraT I} P (a : A) : ✓ a → P ⊢ (✓ a).
Proof. unseal=> ?; split=> n x ? _ /=; by apply cmra_valid_validN. Qed.
Lemma cmra_valid_elim {A : cmraT I} (a : A) : ¬ ✓{zero} a → ✓ a ⊢ False.
Proof. unseal=> Ha; split=> n x ??; apply Ha, cmra_validN_le with n; auto using index_zero_minimum. Qed.
Lemma plainly_cmra_valid_1 {A : cmraT I} (a : A) : ✓ a ⊢ ■ ✓ a.
Proof. by unseal. Qed.
Lemma cmra_valid_weaken {A : cmraT I} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
Proof. unseal; split=> n x _; apply cmra_validN_op_l. Qed.

Lemma prod_validI {A B : cmraT I} (x : A * B) : ✓ x ⊣⊢ ✓ x.1 ∧ ✓ x.2.
Proof. by unseal. Qed.
Lemma option_validI {A : cmraT I} (mx : option A) :
  ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True : uPred M end.
Proof. unseal. by destruct mx. Qed.

Lemma discrete_valid {A : cmraT I} `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
Proof. unseal; split=> n x _. by rewrite /= -cmra_discrete_valid_iff. Qed.


Lemma discrete_fun_validI {A} {B : A → ucmraT I} (g : discrete_fun B) : ✓ g ⊣⊢ ∀ i, ✓ g i.
Proof. by unseal. Qed.



(** Consistency/soundness statement *)
Lemma pure_soundness φ : (True ⊢ ⌜ φ ⌝) → φ.
Proof. unseal=> -[H]. by apply (H zero ε); eauto using ucmra_unit_validN. Qed.

Lemma later_soundness P : (True ⊢ ▷ P) → (True ⊢ P).
Proof.
  unseal=> -[HP]; split=> n x Hx _.
  apply uPred_mono with n ε; eauto using ucmra_unit_leastN.
  apply (HP (index_succ _ n)); eauto using ucmra_unit_validN.
  constructor.
Qed.

Lemma big_later_soundness `{TransfiniteIndex I} P: (True ⊢ ⧍ P) → (True ⊢ P).
  unseal=> -[HP]; split=> n x Hx _. apply uPred_mono with n ε; eauto using ucmra_unit_leastN.
  edestruct (HP (upper_limit n) ε) as [m LP]; first eauto using ucmra_unit_validN; first done.
  eapply uPred_mono in LP; last (right; apply (upper_limit_is_limit m n));
    eauto using ucmra_unit_validN.
  induction m; eauto.
  eapply IHm, uPred_mono; first eapply LP; eauto. simpl; eapply index_succ_greater.
Qed.

Lemma big_laterN_soundness `{TransfiniteIndex I} n P: (True ⊢ ⧍^n P) → (True ⊢ P).
  intros B. induction n as [|n IH]; simpl in *; eauto using big_later_soundness.
Qed.


(* TODO: once we have fixed sbi, remove these -- currently, they are proved in the model because they cannot be derived from sbi *)
Definition timeless (P: uPred M) := ▷ P ⊢ ▷ False ∨ P.
Section move_once_fixed.
  Lemma pure_timeless φ: timeless ⌜φ⌝.
  Proof.
    unfold timeless; unseal. split=> n x Hv //= Hφ.
    destruct (index_lt_dec_minimum n) as [|[]]; eauto.
  Qed.

  Lemma timeless_zero P: timeless P → (▷ False → P) ⊢ P.
  Proof.
    unfold timeless; unseal; intros [H]; split=> n x Hv //= HP; simpl in *.
    induction n  as [n IH] using (well_founded_ind (index_lt_wf I)).
    destruct (index_lt_dec_minimum n) as [H'|[m ?]]; eauto.
    edestruct H; eauto.
    intros; eapply IH; eauto using cmra_validN_le, index_le_lt_trans.
  Qed.

  Lemma later_or_timeless  P Q: timeless P → timeless Q → ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q.
  Proof.
    intros HP % timeless_zero HQ % timeless_zero.
    revert HP HQ; unseal; intros [HP] [HQ]. constructor => n x Hv.
    split; last by (intros [HfP | HfQ] β Hβ; [left | right]; eauto).
    move => //= HPQ; simpl in *.
    destruct (index_lt_dec_minimum n) as [H'|[m ?]].
    - left; intros; by edestruct H'.
    - assert (zero ≺ n) as Hterm by eauto using index_le_lt_trans.
      destruct (HPQ zero Hterm) as [HP'|HQ'].
      + left; intros; eapply HP; eauto using cmra_validN_le.
        intros m' x' Hext Hle Hv' Hterm'.
        assert (m' = zero) as -> by eauto using index_zero_is_unique.
        eauto using uPred_mono, cmra_included_includedN.
      + right; intros; eapply HQ; eauto using cmra_validN_le.
        intros m' x' Hext Hle Hv' Hterm'.
        assert (m' = zero) as -> by eauto using index_zero_is_unique.
        eauto using uPred_mono, cmra_included_includedN.
  Qed.

  Lemma later_sep_timeless P Q: timeless P → timeless Q → ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q.
  Proof.
    intros HP % timeless_zero HQ % timeless_zero.
    revert HP HQ; unseal; intros [HP] [HQ]; split=> n x Hv.
    split. 2: { cbn. intros (x1 & x2 & Hx & Hx1 & Hx2) n' Hn'. exists x1, x2.
      split; [ by eapply dist_mono | split; [by apply Hx1 | by apply Hx2]].
    }
    move=> //= HPQ; simpl in *.
    destruct (index_lt_dec_minimum n) as [H'|[m ?]].
    - exists (core x), x. repeat split.
      { symmetry; eapply equiv_dist, cmra_core_l. }
      all: intros ? ?; exfalso; by eapply H'.
    - assert (zero ≺ n) as Hterm by eauto using index_le_lt_trans.
      destruct (HPQ zero Hterm) as (x1&x2&Hx&Hx1&Hx2).
      destruct (cmra_extend zero x x1 x2) as (y1&y2&Hx'&Hy1&Hy2); eauto using cmra_validN_le.
      exists y1, y2. repeat split.
      { by eapply equiv_dist. }
      + intros. eapply HP.
        { erewrite Hx' in Hv; eauto using cmra_validN_op_l, cmra_validN_le. }
        intros m' x' Hext Hle Hv' Hterm'.
        assert (m' = zero) as -> by eauto using index_zero_is_unique.
        eapply uPred_mono; eauto. rewrite -Hy1; eauto using cmra_included_includedN.
      + intros. eapply HQ.
        { erewrite Hx' in Hv; eauto using cmra_validN_op_r, cmra_validN_le. }
        intros m' x' Hext Hle Hv' Hterm'.
        assert (m' = zero) as -> by eauto using index_zero_is_unique.
        eapply uPred_mono; eauto. rewrite -Hy2; eauto using cmra_included_includedN.
  Qed.

  Lemma later_exist_timeless  {A} (Ψ : A → uPred M) :
    (∀ x, timeless (Ψ x)) → ▷ (∃ x, Ψ x) ⊢ ▷ False ∨ ∃ x, ▷ Ψ x.
  Proof.
    intros Htime. assert (∀ x, (▷ False → Ψ x) ⊢ Ψ x) as H0 by eauto using timeless_zero.
    revert H0; unseal; intros H0; split=> n x Hv //= HΨ; simpl in *.
    destruct (index_lt_dec_minimum n) as [H'|[m ?]].
    - by left.
    - right; assert (zero ≺ n) as Hterm by eauto using index_le_lt_trans.
      destruct (HΨ zero Hterm) as [a Ha]. destruct (H0 a) as [H0']; simpl in *.
      exists a; intros m' Hm'; apply H0'; eauto using cmra_validN_le.
      intros n' ?????; assert (n' = zero) as -> by eauto using index_zero_is_unique.
      eauto using uPred_mono, cmra_included_includedN.
  Qed.
End move_once_fixed.


(* this is a nice property but we have no use case yet *)
Lemma exists_own_wand X (φ: X → uPred M) a : (∀ b n, ✓{n} b → ✓{n} (b ⋅ a)) → (uPred_ownM a -∗ ∃ x, φ x) ⊢ (∃ x, uPred_ownM a -∗ φ x).
Proof.
  intros Hval; split=> n b Hv; unseal. intros Hex.
  feed pose proof (Hex n a) as Hex; eauto.
  destruct Hex as [x Hφ].
  exists x. intros n' a' Hn' Hv' Ha.
  eapply uPred_mono; last reflexivity; last first.
  apply cmra_monoN_l, Ha.
  eapply uPred_mono; first apply Hφ; eauto.
Qed.



Lemma later_or_commute_classically P Q:
  (∀ X: Prop, X \/ ¬ X) →
  ▷ (P ∨ Q) ⊢ ▷ P ∨ ▷ Q.
Proof.
  intros XM; unseal; split=> n x Hv //= HPQ.
  destruct (XM ((∀ n' : I, n' ≺ n → P n' x) ∨ (∀ n' : I, n' ≺ n → Q n' x))) as [|H]; eauto.
  left; intros n1 Hn1; destruct (XM (P n1 x)); eauto.
  exfalso; eapply H.
  right; intros n2 Hn2; destruct (XM (Q n2 x)); eauto.
  exfalso.
  destruct (index_le_total n1 n2).
  - destruct (HPQ n2 Hn2) as []; eauto using uPred_mono.
  - destruct (HPQ n1 Hn1) as []; eauto using uPred_mono.
Qed.


Section later_or_is_classical.
  Variable (ω: I) (m: M) (f: I → bool).
  Hypothesis (ω_sup: ∀ n, n ≺ ω → index_succ I n ≺ ω).
  Hypothesis (comm: ∀ P Q, ▷ (P ∨ Q) ⊢ ▷ P ∨ ▷ Q).
  Hypothesis
    (Hdec: (∀ n : I, n ≺ ω → (∀ m, m ⪯ n → f m = false) ∨ (∃ m : I, f m = true))).
  Hypothesis (Hm:  ✓{ω} m).
  Hypothesis (Hl: zero ≺ ω).

  Local Program Definition P : uPred M :=
    {| uPred_holds n x := ∀ n', n' ⪯ n → f n' = false |}.
  Next Obligation.
    simpl; eauto.
  Qed.

  Let Q : uPred M := ⌜∃ m, f m = true⌝.

  Lemma dec_halting: (∀ n, n ≺ ω → f n = false) ∨ (∃ m, f m = true).
 Proof using Hdec Hl Hm I M Q comm f m ω.
    specialize (comm P Q). revert comm. unfold Q. unseal.
    intros [H]; simpl in H.
    destruct (H ω m Hm Hdec) as [Ht|Hf].
    - left; intros; eapply Ht; eauto.
    - right; eapply Hf; eauto.
  Qed.

End later_or_is_classical.

End primitive.
End uPred_primitive.
