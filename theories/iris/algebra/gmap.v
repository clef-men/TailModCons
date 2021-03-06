From iris.algebra Require Export cmra.
From stdpp Require Export list gmap.
From iris.algebra Require Import updates local_updates.
From iris.base_logic Require Import base_logic.
From iris.algebra Require Import proofmode_classes.
Set Default Proof Using "Type".

Section cofe.
Context `{Countable K} {SI} {A : ofeT SI}.
Implicit Types m : gmap K A.
Implicit Types i : K.

Instance gmap_dist : Dist SI (gmap K A) := λ n m1 m2,
  ∀ i, m1 !! i ≡{n}≡ m2 !! i.
Definition gmap_ofe_mixin : OfeMixin SI (gmap K A).
Proof.
  split.
  - intros m1 m2; split.
    + by intros Hm n k; apply equiv_dist.
    + intros Hm k; apply equiv_dist; intros n; apply Hm.
  - intros n; split.
    + by intros m k.
    + by intros m1 m2 ? k.
    + by intros m1 m2 m3 ?? k; trans (m2 !! k).
  - intros n n' m1 m2 ? k ?; eapply dist_le; eauto.
Qed.
Canonical Structure gmapO : ofeT SI := OfeT (gmap K A) gmap_ofe_mixin.


Program Definition gmap_chain (c: chain gmapO) (k: K) : chain (optionO A) :=
  mkchain _ _ (λ n, c n !! k) _.
Next Obligation. intros c k α β Hβ. by apply c. Qed.
Program Definition gmap_bchain {α} (c: bchain gmapO α) (k: K) : bchain (optionO A) α :=
  mkbchain _ _ _ (λ β Hβ, c β Hβ !! k) _.
Next Obligation. intros α c k β γ Hβγ Hβ Hγ; by apply c. Qed.

Definition gmap_compl `{Cofe SI A} : (chain gmapO) → gmapO := λ c,
  map_imap (λ i _, compl (gmap_chain c i)) (c zero).
Definition gmap_bcompl `{Cofe SI A} : ∀ α Hα , (bchain gmapO α) → gmapO := λ α Hα c,
    map_imap (λ i _, bcompl Hα (gmap_bchain c i)) (c zero Hα).

Global Program Instance gmap_cofe `{Cofe SI A} : Cofe gmapO :=
  {| compl := gmap_compl; bcompl := gmap_bcompl |}.
Next Obligation.
  intros ? n c k. rewrite /gmap_compl map_lookup_imap.
  feed inversion (λ H, chain_cauchy' c zero n H k); simplify_option_eq; auto.
  rewrite conv_compl /=. by apply reflexive_eq.
Qed.
Next Obligation.
  intros ? α Hα c β Hβ k. rewrite /bcompl /gmap_bcompl.
  rewrite map_lookup_imap.
  specialize (bchain_cauchy' _ c zero β Hα Hβ (index_zero_minimum β)  k) as H'.
  inversion H'; simplify_option_eq; auto.
  unshelve rewrite conv_bcompl /=; eauto. by apply reflexive_eq.
Qed.
Next Obligation.
  intros ? α Hα c d β Hne k; rewrite /gmap_bcompl.
  rewrite !map_lookup_imap.
  feed inversion (Hne zero Hα k); eauto; cbn.
  eapply bcompl_ne; intros ??; apply Hne.
Qed.

Global Instance gmap_ofe_discrete : OfeDiscrete A → OfeDiscrete gmapO.
Proof. intros ? m m' ? i. by apply (discrete _). Qed.
(*TODO: why doesn't this go automatically? *)
Global Instance gmapO_leibniz: LeibnizEquiv A → LeibnizEquiv gmapO.
Proof. intros; change (LeibnizEquiv (gmap K A)); apply _. Qed.

Global Instance lookup_ne k :
  NonExpansive (lookup k : gmap K A → option A).
Proof. by intros m1 m2. Qed.
Global Instance lookup_proper k :
  Proper ((≡) ==> (≡)) (lookup k : gmap K A → option A) := _.
Global Instance alter_ne f k n :
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (alter f k).
Proof.
  intros ? m m' Hm k'.
  by destruct (decide (k = k')); simplify_map_eq; rewrite (Hm k').
Qed.
Global Instance insert_ne i :
  NonExpansive2 (insert (M:=gmap K A) i).
Proof.
  intros n x y ? m m' ? j; destruct (decide (i = j)); simplify_map_eq;
    [by constructor|by apply lookup_ne].
Qed.
Global Instance singleton_ne i :
  NonExpansive (singletonM i : A → gmap K A).
Proof. by intros ????; apply insert_ne. Qed.
Global Instance delete_ne i :
  NonExpansive (delete (M:=gmap K A) i).
Proof.
  intros n m m' ? j; destruct (decide (i = j)); simplify_map_eq;
    [by constructor|by apply lookup_ne].
Qed.

Global Instance gmap_empty_discrete : Discrete (∅ : gmap K A).
Proof.
  intros m Hm i; specialize (Hm i); rewrite lookup_empty in Hm |- *.
  inversion_clear Hm; constructor.
Qed.
Global Instance gmap_lookup_discrete m i : Discrete m → Discrete (m !! i).
Proof.
  intros ? [x|] Hx; [|by symmetry; apply: discrete].
  assert (m ≡{zero}≡ <[i:=x]> m)
    by (by symmetry in Hx; inversion Hx; ofe_subst; rewrite insert_id).
  by rewrite (discrete m (<[i:=x]>m)) // lookup_insert.
Qed.
Global Instance gmap_insert_discrete m i x :
  Discrete x → Discrete m → Discrete (<[i:=x]>m).
Proof.
  intros ?? m' Hm j; destruct (decide (i = j)); simplify_map_eq.
  { by apply: discrete; rewrite -Hm lookup_insert. }
  by apply: discrete; rewrite -Hm lookup_insert_ne.
Qed.
Global Instance gmap_singleton_discrete i x :
  Discrete x → Discrete ({[ i := x ]} : gmap K A) := _.
Lemma insert_idN n m i x :
  m !! i ≡{n}≡ Some x → <[i:=x]>m ≡{n}≡ m.
Proof. intros (y'&?&->)%dist_Some_inv_r'. by rewrite insert_id. Qed.
End cofe.

Arguments gmapO _ {_ _ _} _.

(* CMRA *)
Section cmra.
Context `{Countable K} {SI} {A : cmraT SI}.
Implicit Types m : gmap K A.

Instance gmap_unit : Unit (gmap K A) := (∅ : gmap K A).
Instance gmap_op : Op (gmap K A) := merge op.
Instance gmap_pcore : PCore (gmap K A) := λ m, Some (omap pcore m).
Instance gmap_valid : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).
Instance gmap_validN : ValidN SI (gmap K A) := λ n m, ∀ i, ✓{n} (m !! i).

Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
Proof. by apply lookup_merge. Qed.
Lemma lookup_core m i : core m !! i = core (m !! i).
Proof. by apply lookup_omap. Qed.

Lemma lookup_included (m1 m2 : gmap K A) : m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
Proof.
  split; [by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm|].
  revert m2. induction m1 as [|i x m Hi IH] using map_ind=> m2 Hm.
  { exists m2. by rewrite left_id. }
  destruct (IH (delete i m2)) as [m2' Hm2'].
  { intros j. move: (Hm j); destruct (decide (i = j)) as [->|].
    - intros _. rewrite Hi. apply: ucmra_unit_least.
    - rewrite lookup_insert_ne // lookup_delete_ne //. }
  destruct (Hm i) as [my Hi']; simplify_map_eq.
  exists (partial_alter (λ _, my) i m2')=>j; destruct (decide (i = j)) as [->|].
  - by rewrite Hi' lookup_op lookup_insert lookup_partial_alter.
  - move: (Hm2' j). by rewrite !lookup_op lookup_delete_ne //
      lookup_insert_ne // lookup_partial_alter_ne.
Qed.

Lemma gmap_cmra_mixin : CmraMixin SI (gmap K A).
Proof.
  apply cmra_total_mixin.
  - eauto.
  - intros n m1 m2 m3 Hm i; by rewrite !lookup_op (Hm i).
  - intros n m1 m2 Hm i; by rewrite !lookup_core (Hm i).
  - intros n m1 m2 Hm ? i; by rewrite -(Hm i).
  - intros m; split.
    + by intros ? n i; apply cmra_valid_validN.
    + intros Hm i; apply cmra_valid_validN=> n; apply Hm.
  - intros n m Hm i ? ?; eauto using cmra_validN_le.
  - by intros m1 m2 m3 i; rewrite !lookup_op assoc.
  - by intros m1 m2 i; rewrite !lookup_op comm.
  - intros m i. by rewrite lookup_op lookup_core cmra_core_l.
  - intros m i. by rewrite !lookup_core cmra_core_idemp.
  - intros m1 m2; rewrite !lookup_included=> Hm i.
    rewrite !lookup_core. by apply cmra_core_mono.
  - intros n m1 m2 Hm i; apply cmra_validN_op_l with (m2 !! i).
    by rewrite -lookup_op.
  - intros n m y1 y2 Hm Heq.
    refine ((λ FUN, _) (λ i, cmra_extend n (m !! i) (y1 !! i) (y2 !! i) (Hm i) _));
      last by rewrite -lookup_op.
    exists (map_imap (λ i _, projT1 (FUN i)) y1).
    exists (map_imap (λ i _, proj1_sig (projT2 (FUN i))) y2).
    split; [|split]=>i; rewrite ?lookup_op !map_lookup_imap;
    destruct (FUN i) as (z1i&z2i&Hmi&Hz1i&Hz2i)=>/=.
    + destruct (y1 !! i), (y2 !! i); inversion Hz1i; inversion Hz2i; subst=>//.
    + revert Hz1i. case: (y1!!i)=>[?|] //.
    + revert Hz2i. case: (y2!!i)=>[?|] //.
Qed.
Canonical Structure gmapR := CmraT SI (gmap K A) gmap_cmra_mixin.

Global Instance gmap_cmra_discrete : CmraDiscrete A → CmraDiscrete gmapR.
Proof. split; [apply _|]. intros m ? i. by apply: cmra_discrete_valid. Qed.

Lemma gmap_ucmra_mixin : UcmraMixin SI (gmap K A).
Proof.
  split.
  - by intros i; rewrite lookup_empty.
  - by intros m i; rewrite /= lookup_op lookup_empty (left_id_L None _).
  - constructor=> i. by rewrite lookup_omap lookup_empty.
Qed.
Canonical Structure gmapUR := UcmraT SI (gmap K A) gmap_ucmra_mixin.

(** Internalized properties *)
Lemma gmap_equivI {M} m1 m2 : m1 ≡ m2 ⊣⊢@{uPredI M} ∀ i, m1 !! i ≡ m2 !! i.
Proof. by uPred.unseal. Qed.
Lemma gmap_validI {M} m : ✓ m ⊣⊢@{uPredI M} ∀ i, ✓ (m !! i).
Proof. by uPred.unseal. Qed.
End cmra.

Arguments gmapR _ {_ _ _} _.
Arguments gmapUR _ {_ _ _} _.

Section properties.
Context `{Countable K} {SI} {A : cmraT SI}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

Global Instance lookup_op_homomorphism :
  MonoidHomomorphism op op (≡) (lookup i : gmap K A → option A).
Proof. split; [split|]; try apply _. intros m1 m2; by rewrite lookup_op. done. Qed.

Lemma lookup_opM m1 mm2 i : (m1 ⋅? mm2) !! i = m1 !! i ⋅ (mm2 ≫= (lookup i)).
Proof. destruct mm2; by rewrite /= ?lookup_op ?right_id_L. Qed.

Lemma lookup_validN_Some n m i x : ✓{n} m → m !! i ≡{n}≡ Some x → ✓{n} x.
Proof. by move=> /(_ i) Hm Hi; move:Hm; rewrite Hi. Qed.
Lemma lookup_valid_Some m i x : ✓ m → m !! i ≡ Some x → ✓ x.
Proof. move=> Hm Hi. move:(Hm i). by rewrite Hi. Qed.

Lemma insert_validN n m i x : ✓{n} x → ✓{n} m → ✓{n} <[i:=x]>m.
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
Lemma insert_valid m i x : ✓ x → ✓ m → ✓ <[i:=x]>m.
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
Lemma singleton_validN n i x : ✓{n} ({[ i := x ]} : gmap K A) ↔ ✓{n} x.
Proof.
  split.
  - move=>/(_ i); by simplify_map_eq.
  - intros. apply insert_validN. done. apply: ucmra_unit_validN.
Qed.
Lemma singleton_valid i x :✓ ({[ i := x ]} : gmap K A) ↔ ✓ x.
Proof. rewrite !cmra_valid_validN. by setoid_rewrite singleton_validN. Qed.

Lemma delete_validN n m i : ✓{n} m → ✓{n} (delete i m).
Proof. intros Hm j; destruct (decide (i = j)); by simplify_map_eq. Qed.
Lemma delete_valid m i : ✓ m → ✓ (delete i m).
Proof. intros Hm j; destruct (decide (i = j)); by simplify_map_eq. Qed.

Lemma insert_singleton_op m i x : m !! i = None → <[i:=x]> m = {[ i := x ]} ⋅ m.
Proof.
  intros Hi; apply map_eq=> j; destruct (decide (i = j)) as [->|].
  - by rewrite lookup_op lookup_insert lookup_singleton Hi right_id_L.
  - by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id_L.
Qed.

Lemma core_singleton (i : K) (x : A) cx :
  pcore x = Some cx → core ({[ i := x ]} : gmap K A) = {[ i := cx ]}.
Proof. apply omap_singleton. Qed.
Lemma core_singleton' (i : K) (x : A) cx :
  pcore x ≡ Some cx → core ({[ i := x ]} : gmap K A) ≡ {[ i := cx ]}.
Proof.
  intros (cx'&?&->)%equiv_Some_inv_r'. by rewrite (core_singleton _ _ cx').
Qed.
Lemma op_singleton (i : K) (x y : A) :
  {[ i := x ]} ⋅ {[ i := y ]} = ({[ i := x ⋅ y ]} : gmap K A).
Proof. by apply (merge_singleton _ _ _ x y). Qed.
Global Instance is_op_singleton i a a1 a2 :
  IsOp a a1 a2 → IsOp' ({[ i := a ]} : gmap K A) {[ i := a1 ]} {[ i := a2 ]}.
Proof. rewrite /IsOp' /IsOp=> ->. by rewrite -op_singleton. Qed.

Global Instance gmap_core_id m : (∀ x : A, CoreId x) → CoreId m.
Proof.
  intros; apply core_id_total=> i.
  rewrite lookup_core. apply (core_id_core _).
Qed.
Global Instance gmap_singleton_core_id i (x : A) :
  CoreId x → CoreId {[ i := x ]}.
Proof. intros. by apply core_id_total, core_singleton'. Qed.

Lemma singleton_includedN n m i x :
  {[ i := x ]} ≼{n} m ↔ ∃ y, m !! i ≡{n}≡ Some y ∧ Some x ≼{n} Some y.
Proof.
  split.
  - move=> [m' /(_ i)]; rewrite lookup_op lookup_singleton=> Hi.
    exists (x ⋅? m' !! i). rewrite -Some_op_opM.
    split. done. apply cmra_includedN_l.
  - intros (y&Hi&[mz Hy]). exists (partial_alter (λ _, mz) i m).
    intros j; destruct (decide (i = j)) as [->|].
    + by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
    + by rewrite lookup_op lookup_singleton_ne// lookup_partial_alter_ne// left_id.
Qed.
(* We do not have [x ≼ y ↔ ∀ n, x ≼{n} y], so we cannot use the previous lemma *)
Lemma singleton_included m i x :
  {[ i := x ]} ≼ m ↔ ∃ y, m !! i ≡ Some y ∧ Some x ≼ Some y.
Proof.
  split.
  - move=> [m' /(_ i)]; rewrite lookup_op lookup_singleton.
    exists (x ⋅? m' !! i). rewrite -Some_op_opM.
    split. done. apply cmra_included_l.
  - intros (y&Hi&[mz Hy]). exists (partial_alter (λ _, mz) i m).
    intros j; destruct (decide (i = j)) as [->|].
    + by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
    + by rewrite lookup_op lookup_singleton_ne// lookup_partial_alter_ne// left_id.
Qed.
Lemma singleton_included_exclusive m i x :
  Exclusive x → ✓ m →
  {[ i := x ]} ≼ m ↔ m !! i ≡ Some x.
Proof.
  intros ? Hm. rewrite singleton_included. split; last by eauto.
  intros (y&?&->%(Some_included_exclusive _)); eauto using lookup_valid_Some.
Qed.

Global Instance singleton_cancelable i x :
  Cancelable (Some x) → Cancelable {[ i := x ]}.
Proof.
  intros ? n m1 m2 Hv EQ j. move: (Hv j) (EQ j). rewrite !lookup_op.
  destruct (decide (i = j)) as [->|].
  - rewrite lookup_singleton. by apply cancelableN.
  - by rewrite lookup_singleton_ne // !(left_id None _).
Qed.

Global Instance gmap_cancelable (m : gmap K A) :
  (∀ x : A, IdFree x) → (∀ x : A, Cancelable x) → Cancelable m.
Proof.
  intros ?? n m1 m2 ?? i. apply (cancelableN (m !! i)); by rewrite -!lookup_op.
Qed.

Lemma insert_op m1 m2 i x y :
  <[i:=x ⋅ y]>(m1 ⋅ m2) =  <[i:=x]>m1 ⋅ <[i:=y]>m2.
Proof. by rewrite (insert_merge (⋅) m1 m2 i (x ⋅ y) x y). Qed.

Lemma insert_updateP (P : A → Prop) (Q : gmap K A → Prop) m i x :
  x ~~>: P →
  (∀ y, P y → Q (<[i:=y]>m)) →
  <[i:=x]>m ~~>: Q.
Proof.
  intros Hx%option_updateP' HP; apply cmra_total_updateP=> n mf Hm.
  destruct (Hx n (Some (mf !! i))) as ([y|]&?&?); try done.
  { by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
  exists (<[i:=y]> m); split; first by auto.
  intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
  destruct (decide (i = j)); simplify_map_eq/=; auto.
Qed.
Lemma insert_updateP' (P : A → Prop) m i x :
  x ~~>: P → <[i:=x]>m ~~>: λ m', ∃ y, m' = <[i:=y]>m ∧ P y.
Proof. eauto using insert_updateP. Qed.
Lemma insert_update m i x y : x ~~> y → <[i:=x]>m ~~> <[i:=y]>m.
Proof. rewrite !cmra_update_updateP; eauto using insert_updateP with subst. Qed.

Lemma singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) i x :
  x ~~>: P → (∀ y, P y → Q {[ i := y ]}) → {[ i := x ]} ~~>: Q.
Proof. apply insert_updateP. Qed.
Lemma singleton_updateP' (P : A → Prop) i x :
  x ~~>: P → {[ i := x ]} ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. apply insert_updateP'. Qed.
Lemma singleton_update i (x y : A) : x ~~> y → {[ i := x ]} ~~> {[ i := y ]}.
Proof. apply insert_update. Qed.

Lemma delete_update m i : m ~~> delete i m.
Proof.
  apply cmra_total_update=> n mf Hm j; destruct (decide (i = j)); subst.
  - move: (Hm j). rewrite !lookup_op lookup_delete left_id.
    apply cmra_validN_op_r.
  - move: (Hm j). by rewrite !lookup_op lookup_delete_ne.
Qed.

Lemma dom_op m1 m2 : dom (gset K) (m1 ⋅ m2) = dom _ m1 ∪ dom _ m2.
Proof.
  apply elem_of_equiv_L=> i; rewrite elem_of_union !elem_of_dom.
  unfold is_Some; setoid_rewrite lookup_op.
  destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma dom_included m1 m2 : m1 ≼ m2 → dom (gset K) m1 ⊆ dom _ m2.
Proof.
  rewrite lookup_included=>? i; rewrite !elem_of_dom. by apply is_Some_included.
Qed.

Section freshness.
  Local Set Default Proof Using "Type*".
  Context `{!Infinite K}.
  Lemma alloc_updateP_strong (Q : gmap K A → Prop) (I : K → Prop) m x :
    pred_infinite I →
    ✓ x → (∀ i, m !! i = None → I i → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    move=> /(pred_infinite_set I (C:=gset K)) HP ? HQ.
    apply cmra_total_updateP. intros n mf Hm.
    destruct (HP (dom (gset K) (m ⋅ mf))) as [i [Hi1 Hi2]].
    assert (m !! i = None).
    { eapply (not_elem_of_dom (D:=gset K)). revert Hi2.
      rewrite dom_op not_elem_of_union. naive_solver. }
    exists (<[i:=x]>m); split.
    - by apply HQ.
    - rewrite insert_singleton_op //.
      rewrite -assoc -insert_singleton_op;
        last by eapply (not_elem_of_dom (D:=gset K)).
    by apply insert_validN; [apply cmra_valid_validN|].
  Qed.
  Lemma alloc_updateP (Q : gmap K A → Prop) m x :
    ✓ x → (∀ i, m !! i = None → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    move=>??.
    eapply alloc_updateP_strong with (I:=λ _, True);
    eauto using pred_infinite_True.
  Qed.
  Lemma alloc_updateP_strong' m x (I : K → Prop) :
    pred_infinite I →
    ✓ x → m ~~>: λ m', ∃ i, I i ∧ m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_strong. Qed.
  Lemma alloc_updateP' m x :
    ✓ x → m ~~>: λ m', ∃ i, m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP. Qed.
  Lemma alloc_updateP_cofinite (Q : gmap K A → Prop) (J : gset K) m x :
    ✓ x → (∀ i, m !! i = None → i ∉ J → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    eapply alloc_updateP_strong.
    apply (pred_infinite_set (C:=gset K)).
    intros E. exists (fresh (J ∪ E)).
    apply not_elem_of_union, is_fresh.
  Qed.
  Lemma alloc_updateP_cofinite' m x (J : gset K) :
    ✓ x → m ~~>: λ m', ∃ i, i ∉ J ∧ m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_cofinite. Qed.
End freshness.

Lemma alloc_unit_singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) u i :
  ✓ u → LeftId (≡) u (⋅) →
  u ~~>: P → (∀ y, P y → Q {[ i := y ]}) → ∅ ~~>: Q.
Proof.
  intros ?? Hx HQ. apply cmra_total_updateP=> n gf Hg.
  destruct (Hx n (gf !! i)) as (y&?&Hy).
  { move:(Hg i). rewrite ![∅ ⋅ gf]left_id; last apply _.
    case: (gf !! i)=>[x|]; rewrite /= ?left_id //.
    intros; by apply cmra_valid_validN. }
  exists {[ i := y ]}; split; first by auto.
  intros i'; destruct (decide (i' = i)) as [->|].
  - rewrite lookup_op lookup_singleton.
    move:Hy; case: (gf !! i)=>[x|]; rewrite /= ?right_id //.
  - move:(Hg i'). by rewrite !lookup_op lookup_singleton_ne // !left_id.
Qed.
Lemma alloc_unit_singleton_updateP' (P: A → Prop) u i :
  ✓ u → LeftId (≡) u (⋅) →
  u ~~>: P → ∅ ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. eauto using alloc_unit_singleton_updateP. Qed.
Lemma alloc_unit_singleton_update (u : A) i (y : A) :
  ✓ u → LeftId (≡) u (⋅) → u ~~> y → (∅:gmap K A) ~~> {[ i := y ]}.
Proof.
  rewrite !cmra_update_updateP;
    eauto using alloc_unit_singleton_updateP with subst.
Qed.

Lemma alloc_local_update m1 m2 i x :
  m1 !! i = None → ✓ x → (m1,m2) ~l~> (<[i:=x]>m1, <[i:=x]>m2).
Proof.
  rewrite cmra_valid_validN=> Hi ?.
  apply local_update_unital=> n mf Hmv Hm; simpl in *.
  split; auto using insert_validN.
  intros j; destruct (decide (i = j)) as [->|].
  - move: (Hm j); rewrite Hi symmetry_iff dist_None lookup_op op_None=>-[_ Hj].
    by rewrite lookup_op !lookup_insert Hj.
  - rewrite Hm lookup_insert_ne // !lookup_op lookup_insert_ne //.
Qed.

Lemma alloc_singleton_local_update m i x :
  m !! i = None → ✓ x → (m,∅) ~l~> (<[i:=x]>m, {[ i:=x ]}).
Proof. apply alloc_local_update. Qed.

Lemma insert_local_update m1 m2 i x y x' y' :
  m1 !! i = Some x → m2 !! i = Some y →
  (x, y) ~l~> (x', y') →
  (m1, m2) ~l~> (<[i:=x']>m1, <[i:=y']>m2).
Proof.
  intros Hi1 Hi2 Hup; apply local_update_unital=> n mf Hmv Hm; simpl in *.
  destruct (Hup n (mf !! i)) as [? Hx']; simpl in *.
  { move: (Hmv i). by rewrite Hi1. }
  { move: (Hm i). by rewrite lookup_op Hi1 Hi2 Some_op_opM (inj_iff Some). }
  split; auto using insert_validN.
  rewrite Hm Hx'=> j; destruct (decide (i = j)) as [->|].
  - by rewrite lookup_insert lookup_op lookup_insert Some_op_opM.
  - by rewrite lookup_insert_ne // !lookup_op lookup_insert_ne.
Qed.

Lemma singleton_local_update m i x y x' y' :
  m !! i = Some x →
  (x, y) ~l~> (x', y') →
  (m, {[ i := y ]}) ~l~> (<[i:=x']>m, {[ i := y' ]}).
Proof.
  intros. rewrite /singletonM /map_singleton -(insert_insert ∅ i y' y).
  by eapply insert_local_update; [|eapply lookup_insert|].
Qed.

Lemma delete_local_update m1 m2 i x `{!Exclusive x} :
  m2 !! i = Some x → (m1, m2) ~l~> (delete i m1, delete i m2).
Proof.
  intros Hi. apply local_update_unital=> n mf Hmv Hm; simpl in *.
  split; auto using delete_validN.
  rewrite Hm=> j; destruct (decide (i = j)) as [<-|].
  - rewrite lookup_op !lookup_delete left_id symmetry_iff dist_None.
    apply eq_None_not_Some=> -[y Hi'].
    move: (Hmv i). rewrite Hm lookup_op Hi Hi' -Some_op. by apply exclusiveN_l.
  - by rewrite lookup_op !lookup_delete_ne // lookup_op.
Qed.

Lemma delete_singleton_local_update m i x `{!Exclusive x} :
  (m, {[ i := x ]}) ~l~> (delete i m, ∅).
Proof.
  rewrite -(delete_singleton i x).
  by eapply delete_local_update, lookup_singleton.
Qed.

Lemma delete_local_update_cancelable m1 m2 i mx `{!Cancelable mx} :
  m1 !! i ≡ mx → m2 !! i ≡ mx →
  (m1, m2) ~l~> (delete i m1, delete i m2).
Proof.
  intros Hm1i Hm2i. apply local_update_unital=> n mf Hmv Hm; simpl in *.
  split; [eauto using delete_validN|].
  intros j. destruct (decide (i = j)) as [->|].
  - move: (Hm j). rewrite !lookup_op Hm1i Hm2i !lookup_delete. intros Hmx.
    rewrite (cancelableN mx n (mf !! j) None) ?right_id // -Hmx -Hm1i. apply Hmv.
  - by rewrite lookup_op !lookup_delete_ne // Hm lookup_op.
Qed.

Lemma delete_singleton_local_update_cancelable m i x `{!Cancelable (Some x)} :
  m !! i ≡ Some x → (m, {[ i := x ]}) ~l~> (delete i m, ∅).
Proof.
  intros. rewrite -(delete_singleton i x).
  apply (delete_local_update_cancelable m _ i (Some x));
    [done|by rewrite lookup_singleton].
Qed.

Lemma gmap_fmap_mono {B : cmraT SI} (f : A → B) m1 m2 :
  Proper ((≡) ==> (≡)) f →
  (∀ x y, x ≼ y → f x ≼ f y) → m1 ≼ m2 → fmap f m1 ≼ fmap f m2.
Proof.
  intros ??. rewrite !lookup_included=> Hm i.
  rewrite !lookup_fmap. by apply option_fmap_mono.
Qed.
End properties.

Section unital_properties.
Context `{Countable K} {SI} {A : ucmraT SI}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

Lemma insert_alloc_local_update m1 m2 i x x' y' :
  m1 !! i = Some x → m2 !! i = None →
  (x, ε) ~l~> (x', y') →
  (m1, m2) ~l~> (<[i:=x']>m1, <[i:=y']>m2).
Proof.
  intros Hi1 Hi2 Hup. apply local_update_unital=> n mf Hm1v Hm.
  assert (mf !! i ≡{n}≡ Some x) as Hif.
  { move: (Hm i). by rewrite lookup_op Hi1 Hi2 left_id. }
  destruct (Hup n (mf !! i)) as [Hx'v Hx'eq].
  { move: (Hm1v i). by rewrite Hi1. }
  { by rewrite Hif -(inj_iff Some) -Some_op_opM -Some_op left_id. }
  split.
  - by apply insert_validN.
  - simpl in Hx'eq. by rewrite -(insert_idN n mf i x) // -insert_op -Hm Hx'eq Hif.
Qed.
End unital_properties.

(** Functor *)
Instance gmap_fmap_ne `{Countable K} {SI} {A B : ofeT SI} (f : A → B) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==>dist n) (fmap (M:=gmap K) f).
Proof. by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne. Qed.
Instance gmap_fmap_cmra_morphism `{Countable K} {SI} {A B : cmraT SI} (f : A → B)
  `{!CmraMorphism f} : CmraMorphism (fmap f : gmap K A → gmap K B).
Proof.
  split; try apply _.
  - by intros n m ? i; rewrite lookup_fmap; apply (cmra_morphism_validN _).
  - intros m. apply Some_proper=>i. rewrite lookup_fmap !lookup_omap lookup_fmap.
    case: (m!!i)=>//= ?. apply cmra_morphism_pcore, _.
  - intros m1 m2 i. by rewrite lookup_op !lookup_fmap lookup_op cmra_morphism_op.
Qed.
Definition gmapO_map `{Countable K} {SI} {A B: ofeT SI} (f: A -n> B) :
  gmapO K A -n> gmapO K B := OfeMor (fmap f : gmapO K A → gmapO K B).
Instance gmapO_map_ne `{Countable K} {SI} {A B: ofeT SI} :
  NonExpansive (@gmapO_map K _ _ SI A B).
Proof.
  intros n f g Hf m k; rewrite /= !lookup_fmap.
  destruct (_ !! k) eqn:?; simpl; constructor; apply Hf.
Qed.

Program Definition gmapOF K `{Countable K} {SI} (F : oFunctor SI) : oFunctor SI := {|
  oFunctor_car A B := gmapO K (oFunctor_car F A B);
  oFunctor_map A1 A2 B1 B2 fg := gmapO_map (oFunctor_map F fg)
|}.
Next Obligation.
  by intros K SI ?? F A1 A2 B1 B2 n f g Hfg; apply gmapO_map_ne, oFunctor_ne.
Qed.
Next Obligation.
  intros K SI ?? F A B x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply oFunctor_id.
Qed.
Next Obligation.
  intros K SI ?? F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply oFunctor_compose.
Qed.
Instance gmapOF_contractive K `{Countable K} {SI} (F: oFunctor SI) :
  oFunctorContractive F → oFunctorContractive (gmapOF K F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply gmapO_map_ne, oFunctor_contractive.
Qed.

Program Definition gmapURF K `{Countable K} {SI} (F : rFunctor SI) : urFunctor SI := {|
  urFunctor_car A B := gmapUR K (rFunctor_car F A B);
  urFunctor_map A1 A2 B1 B2 fg := gmapO_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros K SI ?? F A1 A2 B1 B2 n f g Hfg; apply gmapO_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros K SI ?? F A B x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply rFunctor_id.
Qed.
Next Obligation.
  intros K SI ?? F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply rFunctor_compose.
Qed.
Instance gmapRF_contractive K `{Countable K} {SI} (F: rFunctor SI) :
  rFunctorContractive F → urFunctorContractive (gmapURF K F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply gmapO_map_ne, rFunctor_contractive.
Qed.
