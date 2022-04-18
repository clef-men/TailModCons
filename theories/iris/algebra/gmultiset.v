From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From stdpp Require Export sets gmultiset countable.
Set Default Proof Using "Type".

(* The multiset union CMRA *)
Section gmultiset.
  Context `{SI : indexT} `{Countable K}.
  Implicit Types X Y : gmultiset K.

  Canonical Structure gmultisetO := discreteO SI (gmultiset K).

  Instance gmultiset_valid : Valid (gmultiset K) := λ _, True.
  Instance gmultiset_validN : ValidN SI (gmultiset K) := λ _ _, True.
  Instance gmultiset_unit : Unit (gmultiset K) := (∅ : gmultiset K).
  Instance gmultiset_op : Op (gmultiset K) := disj_union.
  Instance gmultiset_pcore : PCore (gmultiset K) := λ X, Some ∅.

  (* TODO: seems like these were in stdpp at some point, but they are not anymore *)
  Notation "⊎ Y" := (λ x, disj_union x Y) (at level 50).
  Notation "X ⊎" := (disj_union X) (at level 50).

  Lemma gmultiset_op_disj_union X Y : X ⋅ Y = X ⊎ Y.
  Proof. done. Qed.
  Lemma gmultiset_core_empty X : core X = ∅.
  Proof. done. Qed.
  Lemma gmultiset_included X Y : X ≼ Y ↔ X ⊆ Y.
  Proof.
    split.
    - intros [Z ->%leibniz_equiv].
      rewrite gmultiset_op_disj_union. apply gmultiset_disj_union_subseteq_l.
    - intros ->%gmultiset_disj_union_difference. by exists (Y ∖ X).
  Qed.

  Lemma gmultiset_ra_mixin : RAMixin (gmultiset K).
  Proof.
    apply ra_total_mixin; eauto.
    - by intros X Y Z ->%leibniz_equiv.
    - by intros X Y ->%leibniz_equiv.
    - solve_proper.
    - intros X1 X2 X3. by rewrite !gmultiset_op_disj_union assoc_L.
    - intros X1 X2. by rewrite !gmultiset_op_disj_union comm_L.
    - intros X. by rewrite gmultiset_core_empty left_id.
    - intros X1 X2 HX. rewrite !gmultiset_core_empty. exists ∅.
      by rewrite left_id.
  Qed.

  Canonical Structure gmultisetR := discreteR SI (gmultiset K) gmultiset_ra_mixin.

  Global Instance gmultiset_cmra_discrete : CmraDiscrete gmultisetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma gmultiset_ucmra_mixin : UcmraMixin SI (gmultiset K).
  Proof. split. done. intros X. by rewrite gmultiset_op_disj_union left_id_L. done. Qed.
  Canonical Structure gmultisetUR := UcmraT SI (gmultiset K) gmultiset_ucmra_mixin.

  Global Instance gmultiset_cancelable X : Cancelable X.
  Proof.
    apply: discrete_cancelable=> Y Z _ ?. fold_leibniz. by apply (inj (X ⊎)).
  Qed.

  Lemma gmultiset_opM X mY : X ⋅? mY = X ⊎ default ∅ mY.
  Proof. destruct mY; by rewrite /= ?right_id_L. Qed.

  Lemma gmultiset_update X Y : X ~~> Y.
  Proof. done. Qed.

  Lemma gmultiset_local_update X Y X' Y' : X ⊎ Y' = X' ⊎ Y → (X,Y) ~l~> (X', Y').
  Proof.
    intros HXY. rewrite local_update_unital_discrete=> Z' _. intros ->%leibniz_equiv.
    split; first done. apply leibniz_equiv_iff, (inj (⊎ Y)).
    rewrite -HXY !gmultiset_op_disj_union.
    by rewrite -(comm_L _ Y) (comm_L _ Y') assoc_L.
  Qed.

  Lemma gmultiset_local_update_alloc X Y X' : (X,Y) ~l~> (X ⊎ X', Y ⊎ X').
  Proof. apply gmultiset_local_update. by rewrite (comm_L _ Y) assoc_L. Qed.

  Lemma gmultiset_local_update_dealloc X Y X' :
    X' ⊆ Y → (X,Y) ~l~> (X ∖ X', Y ∖ X').
  Proof.
    intros ->%gmultiset_disj_union_difference. apply local_update_total_valid.
    intros _ _ ->%gmultiset_included%gmultiset_disj_union_difference.
    apply gmultiset_local_update. apply gmultiset_eq=> x.
    repeat (rewrite multiplicity_difference || rewrite multiplicity_disj_union).
    lia.
  Qed.
End gmultiset.

Arguments gmultisetO _ {_ _}.
Arguments gmultisetR _ {_ _}.
Arguments gmultisetUR _ {_ _}.
