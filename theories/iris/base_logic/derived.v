From iris.base_logic Require Export bi.
From iris.bi Require Export bi.
Set Default Proof Using "Type".
Import bi base_logic.bi.uPred.
Require iris.bi.big_op.


(** Derived (and not-so-derived) laws for Iris-specific primitive connectives (own, valid). *)

Module uPred.
Section derived.
Context `{M : ucmraT SI}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

(* TODO: The following lemmas are currently proved in the model. Remove these once this has been fixed in sbi. *)
Section remove_once_fixed.
Global Instance pure_timeless φ : Timeless (PROP := uPredSI M) ⌜φ⌝.
  apply uPred_primitive.pure_timeless.
Qed.

Global Instance emp_timeless `{BiAffine SI PROP} : Timeless (PROP:= uPredSI M) emp.
Proof. rewrite -bi.True_emp. apply _. Qed.

Lemma later_or_timeless P Q: Timeless P → Timeless Q → ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q.
Proof. apply uPred_primitive.later_or_timeless. Qed.
Global Instance or_timeless P Q : Timeless P → Timeless Q → Timeless (P ∨ Q).
Proof.
  intros; rewrite /Timeless bi.except_0_or later_or_timeless.
  apply or_elim; [apply bi.or_intro_l', H | apply  bi.or_intro_r', H0].
Qed.

Lemma later_sep_timeless P Q: Timeless P → Timeless Q → ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q.
Proof. apply uPred_primitive.later_sep_timeless. Qed.
Global Instance sep_timeless P Q: Timeless P → Timeless Q → Timeless (P ∗ Q).
Proof.
  intros; rewrite /Timeless bi.except_0_sep later_sep_timeless. auto using bi.sep_mono.
Qed.

Global Instance wand_timeless P Q : Timeless Q → Timeless (P -∗ Q).
Proof.
  rewrite /Timeless=> HQ. rewrite bi.later_false_em.
  apply bi.or_mono, bi.wand_intro_l; first done.
  rewrite -{2}(bi.löb Q); apply bi.impl_intro_l.
  rewrite HQ /sbi_except_0 !bi.and_or_r. apply bi.or_elim.
  - by rewrite (comm _ P) bi.persistent_and_sep_assoc bi.impl_elim_r bi.wand_elim_l.
  - apply bi.and_elim_l.
Qed.

Lemma later_exist_timeless {A} (Ψ : A → uPredSI M) :
  (∀ x, Timeless (Ψ x)) →  ▷ (∃ x, Ψ x) ⊢ ▷ False ∨ ∃ x, ▷ Ψ x.
Proof. apply uPred_primitive.later_exist_timeless. Qed.

Global Instance exist_timeless {A} (Ψ : A → uPredSI M) :
  (∀ x, Timeless (Ψ x)) → Timeless (∃ x, Ψ x).
Proof.
  intros H; apply later_exist_timeless in H as Ht; rewrite /Timeless Ht. apply bi.or_elim.
  - rewrite /sbi_except_0; apply bi.or_intro_l.
  - apply bi.exist_elim=> x. rewrite -(bi.exist_intro x); auto. by apply H.
Qed.
Global Instance persistently_timeless P : Timeless P → Timeless (<pers> P).
Proof.
  intros. rewrite /Timeless /sbi_except_0 bi.later_persistently_1.
  by rewrite H /sbi_except_0 bi.persistently_or {1}bi.persistently_elim.
Qed.

Global Instance absorbingly_timeless P : Timeless P → Timeless (<absorb> P).
Proof. rewrite /bi_absorbingly; apply _. Qed.

Global Instance intuitionistically_timeless P :
  Timeless (PROP:= uPredSI M) emp → Timeless P → Timeless (□ P).
Proof. rewrite /bi_intuitionistically; apply _. Qed.

Global Instance eq_timeless  {A : ofeT SI} (a b : A) :
  Discrete a → Timeless (PROP:= uPredSI M) (a ≡ b).
Proof. intros. rewrite /Discrete !bi.discrete_eq. apply pure_timeless. Qed.

Import iris.bi.big_op.

Global Instance big_sepL_timeless {A} (Φ : nat → A → uPredSI M) (l :list A) :
  (∀ k x, Timeless (Φ k x)) → Timeless ([∗ list] k↦x ∈ l, Φ k x).
Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
Global Instance big_sepL_timeless_id (Ps : list (uPredSI M)) :
    TCForall Timeless Ps → Timeless ([∗] Ps).
Proof. induction 1; simpl; apply _. Qed.

Global Instance big_sepL2_timeless {A B} (Φ : nat → A → B → uPredSI M) l1 l2 :
  (∀ k x1 x2, Timeless (Φ k x1 x2)) →
  Timeless ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
Proof. rewrite big_sepL2_alt. apply _. Qed.

Global Instance big_sepM_timeless `{Countable K} {A} (Φ : K → A → uPredSI M) (m : gmap K A) :
  (∀ k x, Timeless (Φ k x)) → Timeless ([∗ map] k↦x ∈ m, Φ k x).
Proof. intros. apply big_sepL_timeless=> _ [??]; apply _. Qed.


Global Instance big_sepM2_empty_timeless `{Countable K} {A B} (Φ : K → A → B → uPredSI M) :
  Timeless ([∗ map] k↦x1;x2 ∈ ∅;∅, Φ k x1 x2).
Proof. rewrite /big_sepM2 map_zip_with_empty. apply _. Qed.
Global Instance big_sepM2_timeless `{Countable K} {A B} (Φ : K → A → B → uPredSI M) m1 m2 :
  (∀ k x1 x2, Timeless (Φ k x1 x2)) →
  Timeless ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2).
Proof. intros. rewrite /big_sepM2. apply _. Qed.

Global Instance big_sepS_timeless `{Countable A} (Φ : A → uPredSI M) (X : gset A) :
  (∀ x, Timeless (Φ x)) → Timeless ([∗ set] x ∈ X, Φ x).
Proof. rewrite /big_opS. apply _. Qed.

Global Instance big_sepMS_timeless `{Countable A} (Φ : A → uPredSI M) (X : gmultiset A) :
  (∀ x, Timeless (Φ x)) → Timeless ([∗ mset] x ∈ X, Φ x).
Proof. rewrite /big_opMS. apply _. Qed.

End remove_once_fixed.



(** Propers *)
Global Instance uPred_valid_proper : Proper ((⊣⊢) ==> iff) (@uPred_valid SI M).
Proof. solve_proper. Qed.
Global Instance uPred_valid_mono : Proper ((⊢) ==> impl) (@uPred_valid SI M).
Proof. solve_proper. Qed.
Global Instance uPred_valid_flip_mono :
  Proper (flip (⊢) ==> flip impl) (@uPred_valid SI M).
Proof. solve_proper. Qed.

Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@uPred_ownM SI M) := ne_proper _.
Global Instance cmra_valid_proper {A : cmraT SI} :
  Proper ((≡) ==> (⊣⊢)) (@uPred_cmra_valid SI M A) := ne_proper _.

(** Own and valid derived *)
Lemma persistently_cmra_valid_1 {A : cmraT SI} (a : A) : ✓ a ⊢ <pers> (✓ a : uPred M).
Proof. by rewrite {1}plainly_cmra_valid_1 plainly_elim_persistently. Qed.
Lemma intuitionistically_ownM (a : M) : CoreId a → □ uPred_ownM a ⊣⊢ uPred_ownM a.
Proof.
  rewrite /bi_intuitionistically affine_affinely=>?; apply (anti_symm _);
    [by rewrite persistently_elim|].
  by rewrite {1}persistently_ownM_core core_id_core.
Qed.
Lemma ownM_invalid (a : M) : ¬ ✓{zero} a → uPred_ownM a ⊢ False.
Proof. by intros; rewrite ownM_valid cmra_valid_elim. Qed.
Global Instance ownM_mono : Proper (flip (≼) ==> (⊢)) (@uPred_ownM SI M).
Proof. intros a b [b' ->]. by rewrite ownM_op sep_elim_l. Qed.
Lemma ownM_unit' : uPred_ownM ε ⊣⊢ True.
Proof. apply (anti_symm _); first by apply pure_intro. apply ownM_unit. Qed.
Lemma plainly_cmra_valid {A : cmraT SI} (a : A) : ■ ✓ a ⊣⊢ ✓ a.
Proof. apply (anti_symm _), plainly_cmra_valid_1. apply plainly_elim, _. Qed.
Lemma intuitionistically_cmra_valid {A : cmraT SI} (a : A) : □ ✓ a ⊣⊢ ✓ a.
Proof.
  rewrite /bi_intuitionistically affine_affinely. intros; apply (anti_symm _);
    first by rewrite persistently_elim.
  apply:persistently_cmra_valid_1.
Qed.
Lemma bupd_ownM_update x y : x ~~> y → uPred_ownM x ⊢ |==> uPred_ownM y.
Proof.
  intros; rewrite (bupd_ownM_updateP _ (eq y)); last by apply cmra_update_updateP.
  by apply bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
Qed.

(** Timeless instances *)
Global Instance valid_timeless {A : cmraT SI} `{!CmraDiscrete A} (a : A) :
  Timeless (✓ a : uPred M)%I.
Proof. rewrite /Timeless !discrete_valid. apply (timeless _). Qed.
Arguments uPred_holds {_ _} _%I _ _ : simpl nomatch.
Global Instance ownM_timeless (a : M) : Discrete a → Timeless (uPred_ownM a).
Proof.
  (* TODO: find proof which does not unseal *)
  intros ?. rewrite /Timeless. unfold sbi_except_0. unseal. split=> n x Hv //=.
  destruct (index_lt_dec_minimum n) as [|[m]]; eauto.
  assert (zero ≺ n) as Hterm by eauto using index_le_lt_trans.
  intros Hlt; right; eapply cmra_included_includedN, cmra_discrete_included_l; eauto using cmra_validN_le.
Qed.

(** Plainness *)
Global Instance cmra_valid_plain {A : cmraT SI} (a : A) :
  Plain (✓ a : uPred M)%I.
Proof. rewrite /Persistent. apply plainly_cmra_valid_1. Qed.

(** Persistence *)
Global Instance cmra_valid_persistent {A : cmraT SI} (a : A) :
  Persistent (✓ a : uPred M)%I.
Proof. rewrite /Persistent. apply persistently_cmra_valid_1. Qed.
Global Instance ownM_persistent a : CoreId a → Persistent (@uPred_ownM SI M a).
Proof.
  intros. rewrite /Persistent -{2}(core_id_core a). apply persistently_ownM_core.
Qed.

(** For big ops *)
Global Instance uPred_ownM_sep_homomorphism :
  MonoidHomomorphism op uPred_sep (≡) (@uPred_ownM SI M).
Proof. split; [split; try apply _|]. apply ownM_op. apply ownM_unit'. Qed.

(** Consistency/soundness statement *)
Lemma bupd_plain_soundness P `{!Plain P} : bi_emp_valid (|==> P) → bi_emp_valid P.
Proof.
  eapply bi_emp_valid_mono. etrans; last exact: bupd_plainly. apply bupd_mono'.
  apply: plain.
Qed.

Corollary soundness φ n : (▷^n ⌜ φ ⌝ : uPred M)%I → φ.
Proof.
  induction n as [|n IH]=> /=.
  - apply pure_soundness.
  - intros H. by apply IH, later_soundness.
Qed.

(* TODO: go through the interface *)
Lemma transfinite_soundness φ `{TransfiniteIndex SI}: ((⧍ ⌜φ⌝)%I : uPred M) → φ.
Proof.
  intros H'; eapply pure_soundness, uPred_primitive.big_later_soundness, H'.
Qed.

Corollary consistency_modal n : ¬ (▷^n False : uPred M)%I.
Proof. exact (soundness False n). Qed.

Corollary consistency : ¬(False : uPred M)%I.
Proof. exact (consistency_modal 0). Qed.

End derived.

End uPred.
