(** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in the Iris sense. *)
From iris.algebra Require Export base.
From iris.program_logic Require Import language.
Set Default Proof Using "Type".

(* TAKE CARE: When you define an [ectxLanguage] canonical structure for your
language, you need to also define a corresponding [language] canonical
structure. Use the coercion [LanguageOfEctx] as defined in the bottom of this
file for doing that. *)

Section ectx_language_mixin.
  Context {expr val ectx state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (head_step : expr → state → list observation → expr → state → list expr → Prop).

  Record EctxLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_head_stuck e1 σ1 κ e2 σ2 efs :
      head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    mixin_fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e);

    (* There are a whole lot of sensible axioms (like associativity, and left and
    right identity, we could demand for [comp_ectx] and [empty_ectx]. However,
    positivity suffices. *)
    mixin_ectx_positive K1 K2 :
      comp_ectx K1 K2 = empty_ectx → K1 = empty_ectx ∧ K2 = empty_ectx;

    mixin_step_by_val K K' e1 e1' σ1 κ e2 σ2 efs :
      fill K e1 = fill K' e1' →
      to_val e1 = None →
      head_step e1' σ1 κ e2 σ2 efs →
      ∃ K'', K' = comp_ectx K K'';
  }.
End ectx_language_mixin.

Structure ectxLanguage := EctxLanguage {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;
  observation : Type;

  of_val : val → expr;
  to_val : expr → option val;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  head_step : expr → state → list observation → expr → state → list expr → Prop;

  ectx_language_mixin :
    EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill head_step
}.

Arguments EctxLanguage {_ _ _ _ _ _ _ _ _ _ _} _.
Arguments of_val {_} _%V.
Arguments to_val {_} _%E.
Arguments empty_ectx {_}.
Arguments comp_ectx {_} _ _.
Arguments fill {_} _ _%E.
Arguments head_step {_} _%E _ _ _%E _ _.

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {Λ : ectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  (* Only project stuff out of the mixin that is not also in language *)
  Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply ectx_language_mixin. Qed.
  Lemma ectx_positive K1 K2 :
    comp_ectx K1 K2 = empty_ectx → K1 = empty_ectx ∧ K2 = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.
  Lemma step_by_val K K' e1 e1' σ1 κ e2 σ2 efs :
    fill K e1 = fill K' e1' →
    to_val e1 = None →
    head_step e1' σ1 κ e2 σ2 efs →
    ∃ K'', K' = comp_ectx K K''.
  Proof. apply ectx_language_mixin. Qed.

  Definition head_reducible (e : expr Λ) (σ : state Λ) :=
    ∃ κ e' σ' efs, head_step e σ κ e' σ' efs.
  Definition head_reducible_no_obs (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' efs, head_step e σ [] e' σ' efs.
  Definition head_irreducible (e : expr Λ) (σ : state Λ) :=
    ∀ κ e' σ' efs, ¬head_step e σ κ e' σ' efs.
  Definition head_stuck (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ head_irreducible e σ.

  (* All non-value redexes are at the root.  In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step (e1 : expr Λ) (σ1 : state Λ) (κ : list (observation Λ))
      (e2 : expr Λ) (σ2 : state Λ) (efs : list (expr Λ)) : Prop :=
    Ectx_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step e1' σ1 κ e2' σ2 efs → prim_step e1 σ1 κ e2 σ2 efs.

  Lemma Ectx_step' K e1 σ1 κ e2 σ2 efs :
    head_step e1 σ1 κ e2 σ2 efs → prim_step (fill K e1) σ1 κ (fill K e2) σ2 efs.
  Proof. econstructor; eauto. Qed.

  Definition ectx_lang_mixin : LanguageMixin of_val to_val prim_step.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros ?????? [??? -> -> ?%val_head_stuck].
      apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
  Qed.

  Canonical Structure ectx_lang : language := Language ectx_lang_mixin.

  Definition head_atomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ σ κ e' σ' efs,
      head_step e σ κ e' σ' efs →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  (* Some lemmas about this language *)
  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma head_prim_step e1 σ1 κ e2 σ2 efs :
    head_step e1 σ1 κ e2 σ2 efs → prim_step e1 σ1 κ e2 σ2 efs.
  Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma head_reducible_no_obs_reducible e σ :
    head_reducible_no_obs e σ → head_reducible e σ.
  Proof. intros (?&?&?&?). eexists. eauto. Qed.
  Lemma not_head_reducible e σ : ¬head_reducible e σ ↔ head_irreducible e σ.
  Proof. unfold head_reducible, head_irreducible. naive_solver. Qed.


  Lemma fill_prim_step K e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs → prim_step (fill K e1) σ1 κ (fill K e2) σ2 efs.
  Proof.
    destruct 1 as [K' e1' e2' -> ->].
    rewrite !fill_comp. by econstructor.
  Qed.
  Lemma fill_reducible K e σ : reducible e σ → reducible (fill K e) σ.
  Proof.
    intros (κ&e'&σ'&efs&?). exists κ, (fill K e'), σ', efs.
    by apply fill_prim_step.
  Qed.
  Lemma head_prim_reducible e σ : head_reducible e σ → reducible e σ.
  Proof. intros (κ&e'&σ'&efs&?). eexists κ, e', σ', efs. by apply head_prim_step. Qed.
  Lemma head_prim_fill_reducible e K σ :
    head_reducible e σ → reducible (fill K e) σ.
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  Lemma head_prim_reducible_no_obs e σ : head_reducible_no_obs e σ → reducible_no_obs e σ.
  Proof. intros (e'&σ'&efs&?). eexists e', σ', efs. by apply head_prim_step. Qed.
  Lemma head_prim_irreducible e σ : irreducible e σ → head_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_reducible e σ :
    reducible e σ → sub_redexes_are_values e → head_reducible e σ.
  Proof.
    intros (κ&e'&σ'&efs&[K e1' e2' -> -> Hstep]) ?.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty /head_reducible; eauto.
  Qed.
  Lemma prim_head_irreducible e σ :
    head_irreducible e σ → sub_redexes_are_values e → irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck e σ :
    head_stuck e σ → sub_redexes_are_values e → stuck e σ.
  Proof.
    intros [] ?. split; first done.
    by apply prim_head_irreducible.
  Qed.

  Lemma ectx_language_atomic a e :
    head_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ κ e' σ' efs [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty. eapply Hatomic_step. by rewrite fill_empty.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 κ e2 σ2 efs :
    head_reducible e1 σ1 →
    prim_step e1 σ1 κ e2 σ2 efs →
    head_step e1 σ1 κ e2 σ2 efs.
  Proof.
    intros (κ'&e2''&σ2''&efs''&?) [K e1' e2' -> -> Hstep].
    destruct (step_by_val K empty_ectx e1' (fill K e1') σ1 κ' e2'' σ2'' efs'')
      as [K' [-> _]%symmetry%ectx_positive];
      eauto using fill_empty, fill_not_val, val_head_stuck.
    by rewrite !fill_empty.
  Qed.

  (* Every evaluation context is a context. *)
  Global Instance ectx_lang_ctx K : LanguageCtx (fill K).
  Proof.
    split; simpl.
    - eauto using fill_not_val.
    - intros ?????? [K' e1' e2' Heq1 Heq2 Hstep].
      by exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp.
    - intros e1 σ1 κ e2 σ2 ? Hnval [K'' e1'' e2'' Heq1 -> Hstep].
      destruct (step_by_val K K'' e1 e1'' σ1 κ e2'' σ2 efs) as [K' ->]; eauto.
      rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
      exists (fill K' e2''); rewrite -fill_comp; split; auto.
      econstructor; eauto.
  Qed.

  Record pure_head_step (e1 e2 : expr Λ) := {
    pure_head_step_safe σ1 : head_reducible_no_obs e1 σ1;
    pure_head_step_det σ1 κ e2' σ2 efs :
      head_step e1 σ1 κ e2' σ2 efs → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = []
  }.

  Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros σ. destruct (Hp1 σ) as (e2' & σ2 & efs & ?).
      eexists e2', σ2, efs. by apply head_prim_step.
    - intros σ1 κ e2' σ2 efs ?%head_reducible_prim_step; eauto using head_reducible_no_obs_reducible.
  Qed.

  Global Instance pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill K e1) (fill K e2).
  Proof. apply: pure_exec_ctx. Qed.
End ectx_language.

Arguments ectx_lang : clear implicits.
Coercion ectx_lang : ectxLanguage >-> language.

(* This definition makes sure that the fields of the [language] record do not
refer to the projections of the [ectxLanguage] record but to the actual fields
of the [ectxLanguage] record. This is crucial for canonical structure search to
work.

Note that this trick no longer works when we switch to canonical projections
because then the pattern match [let '...] will be desugared into projections. *)
Definition LanguageOfEctx (Λ : ectxLanguage) : language :=
  let '@EctxLanguage E V C St K of_val to_val empty comp fill head mix := Λ in
  @Language E V St K of_val to_val _
    (@ectx_lang_mixin (@EctxLanguage E V C St K of_val to_val empty comp fill head mix)).
