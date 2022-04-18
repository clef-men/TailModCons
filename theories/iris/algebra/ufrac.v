(** This file provides a "bounded" version of the fractional camera whose
elements are in the interval (0,..) instead of (0,1]. *)
From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
Set Default Proof Using "Type".

(** Since the standard (0,1] fractional camera [frac] is used more often, we
define [ufrac] through a [Definition] instead of a [Notation]. That way, Coq
infers the [frac] camera by default when using the [Qp] type. *)
Definition ufrac := Qp.

Section ufrac.
Context {SI : indexT}.
Canonical Structure ufracO := leibnizO SI ufrac.

Instance ufrac_valid : Valid ufrac := λ x, True.
Instance ufrac_pcore : PCore ufrac := λ _, None.
Instance ufrac_op : Op ufrac := λ x y, (x + y)%Qp.

Lemma ufrac_included (x y : ufrac) : x ≼ y ↔ (x < y)%Qc.
Proof. by rewrite Qp_lt_sum. Qed.

Corollary ufrac_included_weak (x y : ufrac) : x ≼ y → (x ≤ y)%Qc.
Proof. intros ?%ufrac_included. auto using Qclt_le_weak. Qed.

Definition ufrac_ra_mixin : RAMixin ufrac.
Proof. split; try apply _; try done. Qed.
Canonical Structure ufracR := discreteR SI ufrac ufrac_ra_mixin.

Global Instance ufrac_cmra_discrete : CmraDiscrete ufracR.
Proof. apply discrete_cmra_discrete. Qed.
End ufrac.

Section fix_index. 
  Context {SI : indexT}. 
  Global Instance ufrac_cancelable (q : ufrac) : Cancelable (I := SI) q.
  Proof. intros ?????. by apply Qp_eq, (inj (Qcplus q)), (Qp_eq (q+y) (q+z))%Qp. Qed.

  Global Instance ufrac_id_free (q : ufrac) : IdFree (I := SI) q.
  Proof.
    intros [q0 Hq0] ? EQ%Qp_eq. rewrite -{1}(Qcplus_0_r q) in EQ.
    eapply Qclt_not_eq; first done. by apply (inj (Qcplus q)).
  Qed.

  Lemma ufrac_op' (q p : ufrac) : cmra_op (I := SI) _ p q = (p + q)%Qp.
  Proof. done. Qed.

  Global Instance is_op_ufrac (q : ufrac) : IsOp' (SI := SI) q (q/2)%Qp (q/2)%Qp.
  Proof. by rewrite /IsOp' /IsOp /op ufrac_op' Qp_div_2. Qed.
End fix_index.
