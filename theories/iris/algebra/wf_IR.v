From iris.algebra Require Export ofe.
Set Default Proof Using "Type".
Require Import Coq.Logic.Eqdep_dec. 

(** * Well-founded induction-recursion schemes *)

Section IR.
  (** In the most general setting we consider, we have a well-founded decidable partial order *)
  Variable (X : Type).  (* the type of indices *)
  Variable (rel : X → X → Prop).
  Notation "a ≺ b" := (rel a b). 
  Notation "a ⪯ b" := (rc rel a b). 

  Variable (rel_wf : wf rel).
  Variable (rel_transitive : Transitive rel). 
  Variable (existT_X_inj2 : ∀ (p : X → Type) (x : X) (H1 H2 : p x),  existT x H1 = existT x H2 → H1 = H2). 
  Variable (rel_rc_total : ∀ x1 x2, {x1 ⪯ x2} + {x2 ⪯ x1}). 

  Implicit Type (P : X → Prop). 

  (** A is our type of approximations -- we want to define a : A (λ _, True) using wf IR *)
  Variable (A : ∀ (P : X → Prop), Type). 
  (** A_agree is an equivalence relation (in a suitable sense) on A, capturing that two approximations agree in some way *)
  Variable (A_agree : ∀ {P1 P2}, A P1 → A P2 → Prop). 
  Variable (A_agree_transitive : ∀ (P0 P1 P2 : X → Prop) A0 A1 A2, (∀ γ, P0 γ → P2 γ → P1 γ) 
      → @A_agree P0 P1 A0 A1 → @A_agree P1 P2 A1 A2 → @A_agree P0 P2 A0 A2). 
  Variable (A_agree_symmetric : ∀ P0 P1 A0 A1, @A_agree P0 P1 A0 A1 → @A_agree P1 P0 A1 A0). 

  (** we can merge previous approximations coherently *)
  Variable (step_merge : ∀ P (IH : ∀ x, P x → A (λ y, y ⪯ x)), 
   (∀ x0 x1 H0 H1, A_agree (IH x0 H0) (IH x1 H1)) 
   → A P). 
  Variable (merge_agree : ∀ P Hlt, ∀ x Hx H, A_agree (Hlt x Hx) (step_merge P Hlt H)). 
  Variable (merge_preserve : ∀ P (Hlt1 : ∀ x, P x → A (λ y, y ⪯ x)) (Hlt2 : ∀ x, P x → A (λ y, y ⪯ x)), 
    ∀ (H1 : ∀ x1 x2 Hx1 Hx2, A_agree (Hlt1 x1 Hx1) (Hlt1 x2 Hx2))
    (H2 : ∀ x1 x2 Hx1 Hx2, A_agree (Hlt2 x1 Hx1) (Hlt2 x2 Hx2)),
    (∀ x Hx, A_agree (Hlt1 x Hx) (Hlt2 x Hx))
    → A_agree (step_merge P Hlt1 H1) (step_merge P Hlt2 H2)). 

  (** the inductive step *)
  Variable (step : ∀ x, A (λ y, y ≺ x) → A (λ y, y ⪯ x)). 
  Variable (step_agree : ∀ x IH, A_agree IH (step x IH) ). 
  Variable (step_preserve : ∀ x IH1 IH2, A_agree IH1 IH2 → A_agree (step x IH1) (step x IH2)). 

  (** an inductive predicate capturing exactly the structure of the induction: if IR_spec β approx holds, 
    then approx was obtained by inductively applying step and merging *)
  Inductive IR_spec : ∀ (x : X), A (λ y, y ⪯ x) → Prop := 
    | wf_step x (IH : ∀ y, y ≺ x → A (λ y', y' ⪯ y))
        (IH_spec : ∀ y Hy, IR_spec y (IH y Hy))
        (IH_agree : ∀ y1 y2 Hy1 Hy2, A_agree (IH y1 Hy1) (IH y2 Hy2))
        : IR_spec x (step x (step_merge (λ y, y ≺ x) IH IH_agree)). 

  (** thus, we obtain as a consequence that two approximations satisfying this specification must agree
    (as merging and step both preserve agreement) *)
  Lemma IR_spec_unique x1 x2 A1 A2 : x1 ⪯ x2 → IR_spec x1 A1 → IR_spec x2 A2 → A_agree A1 A2. 
  Proof using step_preserve step_agree rel_wf rel_transitive merge_preserve merge_agree existT_X_inj2 A_agree_transitive. 
    revert x2 x1 A1 A2. refine (Fix rel_wf _ _). intros x2 IH x1 A1 A2 Hle H1 H2. 
    destruct Hle. 
    - subst. inversion H1. subst. apply existT_X_inj2 in H3. subst. 
      inversion H2. subst. apply existT_X_inj2 in H3. subst. 
      apply step_preserve. apply merge_preserve. 
      intros. apply IH; [ assumption| reflexivity| apply IH_spec| apply IH_spec0]. 
    - subst. inversion H2. subst. apply existT_X_inj2 in H4. subst. 
      eapply A_agree_transitive.
      3: { eapply step_agree. } 
      2: { eapply A_agree_transitive. 3: { apply merge_agree. } 
        2: eapply IH. 2: apply H. all: cbn; eauto.
      } 
      cbn. intros γ H0 _. destruct H0; subst; eauto. 
      Unshelve. cbn; eauto. 
  Qed.

  Lemma IR_spec_unique' (P : X → Prop) (H : ∀ x, P x → A (λ y, y ⪯ x)): 
    (∀ (x : X) (Hx : P x), IR_spec x (H x Hx)) 
    → ∀ x0 x1 Hx0 Hx1, A_agree (H x0 Hx0) (H x1 Hx1). 
  Proof using step_preserve step_agree rel_wf rel_transitive rel_rc_total merge_preserve merge_agree existT_X_inj2 A_agree_transitive A_agree_symmetric. 
    intros H1 x0 x1 Hx0 Hx1. 
    destruct (rel_rc_total x0 x1) as [H2 | H2].
    - apply IR_spec_unique; eauto. 
    - apply A_agree_symmetric. apply IR_spec_unique; eauto.
  Qed. 

  (** By well-founded induction we can obtain, for every x, an approximation which satisfies the spec *)
  Lemma A_all x : { H : A (λ y, y ⪯ x) & IR_spec x H}. 
  Proof using step_preserve step_agree rel_wf rel_transitive rel_rc_total merge_preserve merge_agree existT_X_inj2 A_agree_transitive A_agree_symmetric. 
    revert x. refine (Fix rel_wf _ _). intros x IH. 
    set (IH1 := λ y Hy, projT1 (IH y Hy)). 
      assert (IH2 : ∀ x0 x1 (Hx0 : x0 ≺ x) (Hx1 : x1 ≺ x), A_agree (IH1 x0 Hx0) (IH1 x1 Hx1)). 
      { apply IR_spec_unique'. intros. exact (projT2 (IH x0 Hx)). } 
      exists (step x (step_merge _ IH1 IH2)). 
      constructor. intros. exact (projT2 (IH y Hy)).
  Qed. 

  Definition A_all_d x := projT1 (A_all x). 
  Definition A_all_p x := projT2 (A_all x). 

  Corollary A_all_agree x0 x1 : A_agree (A_all_d x0) (A_all_d x1). 
  Proof. 
    destruct (rel_rc_total x0 x1) as [H0 | H0].
    - apply IR_spec_unique; eauto using A_all_p. 
    - apply A_agree_symmetric. apply IR_spec_unique; eauto using A_all_p.
  Qed. 

  (** finally, we can merge all of these approximations together *)
  Definition full_A : A (λ _, True) := step_merge (λ _, True) (λ x _, A_all_d x) (λ x1 x2 _ _ , A_all_agree x1 x2).
End IR.


(** we now specialize this construction to stepindices *)
Section IR_wf_index. 
  Variable (SI : indexT). 
  Variable (A : ∀ (P : SI → Prop), Type). 
  Variable (A_agree : ∀ {P1 P2}, A P1 → A P2 → Prop). 
  Variable (A_agree_transitive : ∀ (P0 P1 P2 : SI → Prop) A0 A1 A2, (∀ γ, P0 γ → P2 γ → P1 γ) 
      → @A_agree P0 P1 A0 A1 → @A_agree P1 P2 A1 A2 → @A_agree P0 P2 A0 A2). 
  Variable (A_agree_symmetric : ∀ P0 P1 A0 A1, @A_agree P0 P1 A0 A1 → @A_agree P1 P0 A1 A0). 

  Implicit Type (P : SI → Prop).

  (* we can merge previous approximations coherently *)
  Variable (step_merge : ∀ P (IH : ∀ x, P x → A (λ y, y ⪯ x)), (∀ x0 x1 H0 H1, A_agree (IH x0 H0) (IH x1 H1)) → A P). 
  Variable (merge_agree : ∀ P Hlt, ∀ x Hx H, A_agree (Hlt x Hx) (step_merge P Hlt H)). 
  Variable (merge_preserve : ∀ P (Hlt1 : ∀ x, P x → A (λ y, y ⪯ x)) (Hlt2 : ∀ x, P x → A (λ y, y ⪯ x)), 
    ∀ (H1 : ∀ x1 x2 Hx1 Hx2, A_agree (Hlt1 x1 Hx1) (Hlt1 x2 Hx2))
    (H2 : ∀ x1 x2 Hx1 Hx2, A_agree (Hlt2 x1 Hx1) (Hlt2 x2 Hx2)),
    (∀ x Hx, A_agree (Hlt1 x Hx) (Hlt2 x Hx))
    → A_agree (step_merge P Hlt1 H1) (step_merge P Hlt2 H2)). 

  Variable (step : ∀ x, A (λ y, y ≺ x) → A (λ y, y ⪯ x)). 
  Variable (step_agree : ∀ x IH, A_agree IH (step x IH) ). 
  Variable (step_preserve : ∀ x IH1 IH2, A_agree IH1 IH2 → A_agree (step x IH1) (step x IH2)). 

  Lemma existT_index_inj2 (p : SI → Type) (x : SI) (H1 H2 : p x) : existT x H1 = existT x H2 → H1 = H2. 
  Proof. 
    apply inj_pair2_eq_dec. apply index_eq_dec. 
  Qed.
  Definition full_A_SI : A (λ _, True). 
  Proof using step_preserve step_merge step_agree step merge_preserve merge_agree A_agree_transitive A_agree_symmetric A_agree. 
    unshelve eapply full_A.
    by apply index_lt. 
    by exact (@A_agree).
    by apply step_merge. 
    by exact step.
    all: eauto. 
    - apply SI. 
    - apply SI. 
    - apply existT_index_inj2. 
    - intros x1 x2. destruct (index_le_lt_dec x1 x2) as [H1 | H1]. by left. eauto.
  Qed.

End IR_wf_index.

(** Finally, we can derive a transfinite induction scheme which relies on an extension operation for the inductive step *)
Section IR_transfinite_index_cons.
  Variable (SI : indexT). 

  Variable (A : ∀ (P : SI → Prop), Type). 
  Variable (A_agree : ∀ {P1 P2}, A P1 → A P2 → Prop). 
  Variable (A_agree_trivial : ∀ P1 P2 (A1 : A P1) (A2 : A P2), (∀ γ, P1 γ → P2 γ → False) → A_agree A1 A2). 
  Variable (A_agree_transitive : ∀ (P0 P1 P2 : SI → Prop) A0 A1 A2, (∀ γ, P0 γ → P2 γ → P1 γ) 
      → @A_agree P0 P1 A0 A1 → @A_agree P1 P2 A1 A2 → @A_agree P0 P2 A0 A2). 
  Variable (A_agree_symmetric : ∀ P0 P1 A0 A1, @A_agree P0 P1 A0 A1 → @A_agree P1 P0 A1 A0). 
  Variable (A_agree_reflexive : ∀ P A, @A_agree P P A A). 

  (** extension operation -- it is always relative to a particular approximation *)
  Variable (E : ∀ γ (approx : A (λ y, y ≺ γ)), Type). 
  (** agreement of extensions is dependent on the agreement of the approximations they are based on *)
  Variable (E_agree : ∀ γ ap0 ap1, E γ ap0 → E γ ap1 → A_agree ap0 ap1 → Prop). 

  Variable (extend : ∀ γ ap (ext : E γ ap) (succ_or_limit : {γ' | γ = succ γ'} + {index_is_limit γ}), A (λ y, y ⪯ γ)). 
  Variable (extend_agree : ∀ γ ap ext succ_or_limit, A_agree ap (extend γ ap ext succ_or_limit)). 
  Variable (extend_coherent : ∀ γ ap0 ap1 ext0 ext1 succ_or_limit, 
    ∀ H: A_agree ap0 ap1, 
    E_agree γ ap0 ap1 ext0 ext1 H
    → A_agree (extend γ ap0 ext0 succ_or_limit) (extend γ ap1 ext1 succ_or_limit)). 

  Implicit Type (P : SI → Prop).

  (** we can merge previous approximations coherently *)
  Variable (step_merge : ∀ P (IH : ∀ x, P x → A (λ y, y ⪯ x)), (∀ x0 x1 H0 H1, A_agree (IH x0 H0) (IH x1 H1)) →  A P). 
  Variable (merge_agree : ∀ P Hlt , ∀ x Hx H, A_agree (Hlt x Hx) (step_merge P Hlt H)). 
  Variable (merge_coherent : ∀ P (Hlt1 : ∀ x, P x → A (λ y, y ⪯ x)) (Hlt2 : ∀ x, P x → A (λ y, y ⪯ x)), 
    ∀ (H1 : ∀ x1 x2 Hx1 Hx2, A_agree (Hlt1 x1 Hx1) (Hlt1 x2 Hx2))
      (H2 : ∀ x1 x2 Hx1 Hx2, A_agree (Hlt2 x1 Hx1) (Hlt2 x2 Hx2)), 
   (∀ x Hx, A_agree (Hlt1 x Hx) (Hlt2 x Hx))
    → A_agree (step_merge P Hlt1 H1) (step_merge P Hlt2 H2)). 

  (** base case*)
  Variable (base : A (λ y, y ⪯ zero)). 

  (** successor case *)
  Variable (succ_step : ∀ β (IH : A (λ y, y ≺ succ β)), E (succ β) IH). 
  Variable (succ_extension_coherent : ∀ β IH0 IH1 (H : A_agree IH0 IH1), 
    E_agree (succ β) IH0 IH1 (succ_step β IH0) (succ_step β IH1) H). 

  (** limit case *)
  Variable (limit_step : ∀ (β : limit_idx SI) (IH : A (λ y, y ≺ β)), E β IH). 
  Variable (limit_extension_coherent : ∀ (β : limit_idx SI) IH0 IH1 (H : A_agree IH0 IH1), 
    E_agree β IH0 IH1 (limit_step β IH0) (limit_step β IH1) H). 


  Definition full_A_transfinite : A (λ _, True). 
  Proof using succ_step succ_extension_coherent step_merge merge_coherent merge_agree limit_step limit_extension_coherent extend_coherent extend_agree extend base E_agree E A_agree_trivial A_agree_transitive A_agree_symmetric A_agree_reflexive A_agree.
    unshelve eapply full_A_SI.
    - apply @A_agree. 
    - apply step_merge. 
    - refine (ord_match _ _ _ _). 
      + intros. apply base. 
      + intros β IH. unshelve eapply extend. exact IH. 2: left; by exists β. eapply succ_step. 
      + intros β IH. unshelve eapply extend. exact IH. 2: right; apply limit_index_is_limit. 
        apply limit_step. 
    - apply A_agree_transitive. 
    - apply A_agree_symmetric. 
    - apply merge_agree. 
    - apply merge_coherent. 
    - intros x IH. unfold ord_match. destruct index_is_zero as [-> | Hnt]; cbn.
      { apply A_agree_trivial. intros. index_contra_solve. } 
      destruct index_dec_limit as [[β ->] | H2]; cbn. 
      { apply extend_agree. } 
      { apply extend_agree. } 
    - intros x IH1 IH2 H. unfold ord_match. destruct index_is_zero as [-> | Hnt]; cbn.
      { intros. apply A_agree_reflexive. } 
      destruct index_dec_limit as [[β ->] | H2]; cbn. 
      { unshelve eapply extend_coherent. exact H. eapply succ_extension_coherent. } 
      { unshelve eapply extend_coherent. exact H. 
        set (xlim := mklimitidx _ _ _). 
        enough (E_agree xlim IH1 IH2 (limit_step xlim IH1) (limit_step xlim IH2) H) as H0 by exact H0. 
        eapply limit_extension_coherent. 
      } 
  Qed.
End IR_transfinite_index_cons.
