From stdpp Require Import gmap.

From Autosubst Require Export Autosubst.

From iris.program_logic Require Export language ectx_language ectxi_language.

From TMC Require Import locations.

Module lang.

(* ---- index ---- *)

Inductive index := one | two.

Global Instance index_lookup_total {X} : LookupTotal index X (X * X) :=
  λ t p,
    match t with
    | one => fst p
    | two => snd p
    end
.

Global Instance index_insert {X} : Insert index X (X * X) :=
  λ t x p,
    match t with
    | one => (x, snd p)
    | two => (fst p, x)
    end
.

Global Instance index_eq_dec : EqDecision index.
Proof. solve_decision. Qed.

Global Instance index_countable : Countable index.
Proof.
  apply (inj_countable (
    λ i,
      match i with
      | one => 1%nat
      | two => 2%nat
      end
    ) (
    λ n,
      match n with
      | 1%nat => Some one
      | 2%nat => Some two
      | _ => None
      end
    )
  ).
  intros []; auto.
Qed.

(* ---- val ---- *)

Inductive val :=
  | Loc : loc -> val
  | Idx : index -> val
  | Unit : val
.

Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Qed.

Global Instance val_countable : Countable val.
Proof.
  apply (inj_countable' (
    λ v,
      match v with
      | Loc l => inl l
      | Idx i => inr (inl i)
      | Unit => inr (inr ())
      end
    ) (
    λ v,
      match v with
      | inl l => Loc l
      | inr (inl i) => Idx i
      | inr (inr ()) => Unit
      end
    )
  ).
  intros []; auto.
Qed.

Global Instance val_inhabited : Inhabited val := populate (Unit).

Canonical Structure valO SI := leibnizO SI val.

(* ---- expr ---- *)

Inductive expr :=
  | Val : val -> expr
  | Var : var -> expr
  | Fail : expr
  | Let : expr -> {bind expr} -> expr
  | Pair : expr -> expr -> expr
  | PairIdx : index -> expr -> expr -> expr
  | Match : expr -> expr -> {bind 2 of expr} -> expr
  | Store : expr -> expr -> expr -> expr
.

Global Instance expr_ids : Ids expr. derive. Defined.
Global Instance expr_rename : Rename expr. derive. Defined.
Global Instance expr_subst : Subst expr. derive. Defined.
Global Instance expr_subst_lemmas : SubstLemmas expr. derive. Qed.

Notation of_val := Val (only parsing).

Definition to_val e : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end
.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e => //=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ? ?. congruence. Qed.

Global Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Qed.

Global Instance expr_countable : Countable expr.
Proof.
  apply (inj_countable' (
    fix enc e :=
      match e with
      | Val v => GenLeaf $ inl v
      | Var x => GenLeaf $ inr $ inl x
      | Fail => GenLeaf $ inr $ inr ()
      | Let e1 e2 => GenNode 0 [enc e1; enc e2]
      | Pair e1 e2 => GenNode 1 [enc e1; enc e2]
      | PairIdx one e1 e2 => GenNode 2 [enc e1; enc e2]
      | PairIdx two e1 e2 => GenNode 3 [enc e1; enc e2]
      | Match e0 e1 e2 => GenNode 4 [enc e0; enc e1; enc e2]
      | Store e1 e2 e3 => GenNode 5 [enc e1; enc e2; enc e3]
      end
  ) (
    fix dec e :=
      match e with
      | GenLeaf (inl v) => Val v
      | GenLeaf (inr (inl x)) => Var x
      | GenLeaf (inr (inr ())) => Fail
      | GenNode 0 [e1; e2] => Let (dec e1) (dec e2)
      | GenNode 1 [e1; e2] => Pair (dec e1) (dec e2)
      | GenNode 2 [e1; e2] => PairIdx one (dec e1) (dec e2)
      | GenNode 3 [e1; e2] => PairIdx two (dec e1) (dec e2)
      | GenNode 4 [e0; e1; e2] => Match (dec e0) (dec e1) (dec e2)
      | GenNode 5 [e1; e2; e3] => Store (dec e1) (dec e2) (dec e3)
      | _ => Fail
      end
    )
  ).
  intros e. induction e; try congruence. destruct i; congruence.
Qed.

Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure exprO SI := leibnizO SI expr.

(* ---- state ---- *)

Definition state := gmap loc (val * val).

Global Instance state_eq_dec : EqDecision state.
Proof. solve_decision. Defined.

Global Instance state_inhabited : Inhabited state := populate inhabitant.

Canonical Structure stateO SI := leibnizO SI state.

(* ---- ectx_item ---- *)

Inductive ectx_item :=
  | LetCtx : expr -> ectx_item
  | PairOneLCtx : expr -> ectx_item
  | PairOneRCtx : val -> ectx_item
  | PairTwoRCtx : expr -> ectx_item
  | PairTwoLCtx : val -> ectx_item
  | MatchCtx : expr -> expr -> ectx_item
  | Store1Ctx : expr -> expr -> ectx_item
  | Store2Ctx : val -> expr -> ectx_item
  | Store3Ctx : val -> val -> ectx_item
.

Definition fill_item Ki e :=
  match Ki with
  | LetCtx e2 => Let e e2
  | PairOneLCtx e2 => PairIdx one e e2
  | PairOneRCtx v1 => PairIdx one (Val v1) e
  | PairTwoRCtx e1 => PairIdx two e1 e
  | PairTwoLCtx v2 => PairIdx two e (Val v2)
  | MatchCtx e1 e2 => Match e e1 e2
  | Store1Ctx e2 e3 => Store e e2 e3
  | Store2Ctx v1 e3 => Store (Val v1) e e3
  | Store3Ctx v1 v2 => Store (Val v1) (Val v2) e
  end
.

(* ---- observation ---- *)

Definition observation : Set := False.

(* ---- head_step ---- *)

Inductive head_step : expr → state → list observation → expr → state → list expr → Prop :=
  | LetS v e σ :
      head_step
        (Let (Val v) e) σ []
        e.[Val v .: ids] σ []
  | MatchUnitS e1 e2 σ :
      head_step
        (Match (Val Unit) e1 e2) σ []
        e1 σ []
  | MatchPairS l v1 v2 e1 e2 σ :
      σ !! l = Some (v1, v2) →
      head_step
        (Match (Val $ Loc l) e1 e2) σ []
        e2.[Val v2 .: Val v1 .: ids] σ []
  | PairS e1 e2 i σ :
      head_step
        (Pair e1 e2) σ []
        (PairIdx i e1 e2) σ []
  | PairIdxS i v1 v2 l σ σ' :
      σ !! l = None →
      σ' = <[l := (v1, v2)]> σ →
      head_step
        (PairIdx i (Val v1) (Val v2)) σ []
        (Val $ Loc l) σ' []
  | StoreS l i v vs σ σ' :
      σ !! l = Some vs →
      σ' = <[l := <[i := v]> vs]> σ →
      head_step
        (Store (Val $ Loc l) (Val $ Idx i) (Val v)) σ []
        (Val Unit) σ' []
.

Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ? ? ?; simplify_eq /=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs :
  head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. revert κ e2. induction Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. revert Ki1. induction Ki2, Ki1; naive_solver eauto with f_equal. Qed.

Lemma alloc_fresh i v1 v2 σ :
  let l := fresh_locs (dom (gset loc) σ) in
  head_step
    (PairIdx i (Val v1) (Val v2)) σ []
    (Val $ Loc l) (<[l := (v1, v2)]> σ) [].
Proof.
  apply PairIdxS; try done.
  apply (not_elem_of_dom (D := gset loc)).
  setoid_rewrite <- Z.add_0_r. by apply fresh_locs_fresh.
Qed.

Lemma mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

End lang.

Canonical Structure ectxi_lang := EctxiLanguage lang.mixin.
Canonical Structure ectx_lang := EctxLanguageOfEctxi ectxi_lang.
Canonical Structure lang := LanguageOfEctx ectx_lang.

Global Instance cfg_eq_dec : EqDecision (cfg lang).
Proof. solve_decision. Defined.

Export lang.

Lemma to_val_fill_some K e v :
  to_val (fill K e) = Some v → K = [] ∧ e = Val v.
Proof.
  intro H. destruct K as [|Ki K]; first by apply of_to_val in H. exfalso.
  assert (to_val e ≠ None) as He.
  { intro A. by rewrite fill_not_val in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (Ki :: K) (Val w)) = None).
  { destruct Ki; simpl; apply fill_not_val; done. }
  by simplify_eq.
Qed.

Lemma to_val_fill_none e K :
  to_val e = None → to_val (fill K e) = None.
Proof.
  intros H; destruct (to_val (fill K e)) eqn: Hval; auto.
  apply to_val_fill_some in Hval as [_ ->]. discriminate.
Qed.

Lemma prim_step_to_val_is_head_step e σ1 κs w σ2 efs :
  prim_step e σ1 κs (Val w) σ2 efs → head_step e σ1 κs (Val w) σ2 efs.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.
