From iris.algebra Require Import base stepindex.

(** counter-examples for existential properties *)
Section existential_negative.
  (* Transfinite step-index types cannot validate the bounded existential property. *)
  Context {SI : indexT}. 
  Record sProp := 
    { 
      prop : SI → Prop; 
      prop_downclosed : ∀ α β, α ≺ β → prop β → prop α
    }. 
  Program Definition sProp_later (P : sProp) := Build_sProp (λ γ, ∀ γ', γ' ≺ γ → prop P γ') _.
  Next Obligation. 
    intros [P Pdown] α β Hα. cbn. eauto with index.
  Qed.
  Program Definition sProp_false := Build_sProp (λ _, False) _. 
  Next Obligation.  intros. assumption. Qed.

  Program Definition sProp_ex {X} (Φ : X → sProp) := Build_sProp (λ α, ∃ x, prop (Φ x) α) _. 
  Next Obligation. 
    intros X Φ α β Hα. cbn. intros [x H]. exists x. by eapply prop_downclosed. 
  Qed.

  Definition bounded_existential (X : Type) (Φ : X → sProp) α:=
    (∀ β, β ≺ α → ∃ x : X, prop (Φ x) β)
    → ∃ x : X, ∀ β, β ≺ α → prop (Φ x) β.
  Definition existential (X : Type) (Φ : X → sProp) := 
    (∀ α, ∃ x : X, prop (Φ x) α) 
    → ∃ x : X, ∀ α, prop (Φ x) α. 

  Section transfinite.
    Hypothesis (ω: SI).
    Hypothesis (is_limit_of_nat: ∀ n, Nat.iter n (index_succ SI) zero ≺ ω).
    Hypothesis (is_smallest: ∀ α, α ≺ ω → ∃ n, α = Nat.iter n (index_succ SI) zero).
    
    Lemma transfinite_no_bounded_existential : 
      bounded_existential nat (λ n, Nat.iter n sProp_later sProp_false) ω → False.
    Proof. 
      intros H. unfold bounded_existential in H. edestruct H as [n H']. 
      { intros β Hβ. apply is_smallest in Hβ as (n & ->). exists (S n).
        induction n as [ | n IH]. 
        - intros ? []%index_lt_zero_is_normal.
        - intros α Hα. apply index_succ_iff in Hα as [ -> | Hα]. now apply IH. 
          intros β Hβ. apply IH. eauto with index. 
      } 
      specialize (H' (Nat.iter n (index_succ SI) zero) ltac:(apply is_limit_of_nat)). 
      induction n as [ | n IH]; cbn in H'. exact H'. 
      apply IH. apply H'. apply index_succ_greater. 
    Qed.
  End transfinite.
End existential_negative.

Section no_later_exists.
(** A step-indexed logic cannot have 
  * a sound later-operation,  
  * Löb induction 
  * Commutation of later with existentials: ▷ (∃ x. P) ⊢ ▷ False ∨ ∃ x. ▷ P
  * the existential property for countable types, if ⊢ ∃ n : nat. P n, then there is n : nat such that ⊢ P n. 
*)

  Context 
    (PROP : Type) (* the type of propositions *)
    (entail : PROP → PROP → Prop) (* the entailment relation *)
    (TRUE : PROP) (* the true proposition *)
    (FALSE : PROP) (* the false proposition *)
    (later : PROP → PROP) (* the later modality *)
    (ex : (nat → PROP) → PROP). (* for simplicity, we restrict to predicates over nat here since we don't need more for the proof *)

  Implicit Types (P Q: PROP). 

  Notation "▷ P" := (later P) (at level 20). 
  Notation "P ⊢ Q" := (entail P Q) (at level 60). 
  Notation "⊢ P" := (entail TRUE P) (at level 60). 

  (* standard structural rules *)
  Context 
    (cut : ∀ P Q R, P ⊢ Q → Q ⊢ R → P ⊢ R)
    (assumption : ∀ P, P ⊢ P)
    (ex_intro : ∀ P Φ, (∃ n, P ⊢ Φ n) → P ⊢ ex Φ)
    (ex_elim : ∀ P Φ, (∀ n, Φ n ⊢ P) → ex Φ ⊢ P). 

  
  (* relevant assumptions about our step-indexed logic *)
  Context 
    (logic_sound: ¬ ⊢ FALSE) 
    (later_sound: ∀ P, ⊢ ▷ P → ⊢ P) (* later is sound *)
    (existential : ∀ (Φ : nat → PROP), (⊢ ex Φ) → ∃ n, ⊢ (Φ n)) (* the existential property for nat *)
    (Löb : ∀ P, (▷ P ⊢ P) → ⊢ P). (* Löb induction *)
    
  (* now later commuting with existentials is contradictory *)
  Lemma no_later_existential_commuting : 
    (∀ Φ, ▷ (ex Φ) ⊢ (ex (λ n, ▷ (Φ n))) )
    → False.
  Proof. 
    intros Hcomm. apply logic_sound.  
    assert (∃ n, ⊢ Nat.iter n later FALSE) as [ n Hf]. 
    { apply existential. 
      apply Löb. 
      eapply cut. apply Hcomm. 
      apply ex_elim. 
      intros n. apply ex_intro. exists (S n). apply assumption. 
    } 
    induction n as [ | n IH]. 
    exact Hf. 
    apply IH. apply later_sound, Hf. 
  Qed.
End no_later_exists.


From iris.algebra Require Export cmra updates.
From iris.base_logic Require Import upred. 
From iris.bi Require Import notation.
Section more_counterexamples. 
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

  Import uPred_primitive. 

  Section bounded_limit_preserving_counterexample.

    Definition F (P: uPred M) : uPred M := P.
    Definition G (P: uPred M) : uPred M := (∃ n, ▷^n False)%I.
    Definition c {α: I} : bchain (uPredO M) α := bchain_const (∃ n, ▷^n False)%I α.

    Hypothesis (omega: I).
    Hypothesis (is_limit_of_nat: ∀ n, Nat.iter n (index_succ I) zero ≺ omega).
    Hypothesis (is_smallest: ∀ α, α ≺ omega → ∃ n, α = Nat.iter n (index_succ I) zero).

    Notation "'ω'" := omega.
    Lemma zero_omega: zero ≺ ω.
    Proof using I is_limit_of_nat omega. eapply (is_limit_of_nat 0). Qed.

    Lemma bounded_limit_preserving_entails_counterexample:
      ¬ BoundedLimitPreserving (λ P, F P ⊢ G P).
    Proof using I M is_limit_of_nat is_smallest omega.
      intros H. specialize (H ω zero_omega c); simpl in H.
      assert (∀ β : I, β ≺ ω → F (⧍ ⌜False⌝) ⊢ G (⧍ ⌜False⌝)) as H'.
      { intros ??. destruct (entails_po (I:=I) (M:=M)) as [R _]. apply R. }
      specialize (H H'). destruct H as [H].
      specialize (H ω ε (ucmra_unit_validN ω)).
      unfold F in *. assert (bcompl zero_omega c ω ε) as H''.
      { eapply bcompl_unfold. unfold c; simpl.
        intros n' Hn' _ Hv. eapply is_smallest in Hn'.
        destruct Hn' as [m ->]. unseal.
        exists (S m). clear Hv H' H. induction m; cbn.
        - intros ? [] % index_lt_zero_is_normal.
        - intros n' Hn' n'' Hn''. eapply uPred_mono.
          eapply IHm; eauto.
          eapply index_lt_le_trans. eapply Hn''.
          eapply index_succ_iff, Hn'.
          all: eauto.
      }
      specialize (H H''). unfold G in *.
      revert H; unseal. intros [n].
      eapply uPred_mono with (n2 := (Nat.iter (S n) (index_succ I) zero)) in H; eauto.
      clear H' H''. induction n; simpl in *; eauto.
    Qed.

  End bounded_limit_preserving_counterexample.

  Section ne_does_not_preserve_limits.
    (* we show that, in general, non-expansive maps do not preserve limits. *)

    Program Definition f : uPredO M -n> uPredO M := λne P, (P ∧ ∃ n, ▷^n False)%I.
    Next Obligation.
      intros α x y Heq. apply and_ne. apply Heq. reflexivity.
    Qed.
    Definition c0 {α: I} : bchain (uPredO M) α := bchain_const (True)%I α.

    Hypothesis (omega: I).
    Hypothesis (is_limit_of_nat: ∀ n, Nat.iter n (index_succ I) zero ≺ omega).
    Hypothesis (is_smallest: ∀ α, α ≺ omega → ∃ n, α = Nat.iter n (index_succ I) zero).


    Notation "'ω'" := omega.
    Lemma zero_omega': zero ≺ ω.
    Proof using I is_limit_of_nat omega. eapply (is_limit_of_nat 0). Qed.

    Lemma test : ¬ (f (bcompl zero_omega' c0) ≡ bcompl zero_omega' (bchain_map f c0)).
    Proof using is_smallest.
      intros Heq. destruct Heq as [Heq]. specialize (Heq omega ε (ucmra_unit_validN _)).
      cbn in Heq. destruct Heq as [_ H1].
      revert H1. rewrite !bcompl_unfold; cbn. unseal. intros H. destruct H as [ _ H].
      2: { destruct H as [n H]. eapply uPred_mono with (n2 := Nat.iter (S n) (index_succ I) zero) in H; eauto.
        induction n as [ | n IH]; cbn in H; [tauto | ].
        eapply IH. apply H. eapply index_succ_greater.
      }
      intros. split; [easy | ]. apply is_smallest in Hn' as [nn ->]. exists (S nn).
      clear H0 H. induction nn as [ | n IH]; cbn.
      - intros ? []%index_lt_zero_is_normal.
      - intros n' Hn' n'' Hn''. apply IH. eapply index_lt_le_trans.
        exact Hn''. apply index_succ_iff, Hn'.
    Qed.
  End ne_does_not_preserve_limits.

End more_counterexamples.
