From iris.algebra Require Import auth gmap.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.program_logic.refinement Require Export ref_weakestpre.
From iris.program_logic.refinement Require Import ref_ectx_lifting.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics notation.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".


Class heapPreG {SI} (Σ: gFunctors SI) := HeapPreG {
  heap_preG_inv :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc val Σ;
  heap_preG_proph :> proph_mapPreG proph_id (val * val) Σ
}.


Class heapG {SI} (Σ: gFunctors SI) := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ
}.

Instance heapG_irisG {SI} {Σ: gFunctors SI} `{!heapG Σ} : irisG heap_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ :=
    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I;
  fork_post _ := True%I;
}.

Instance heapG_ref_irisG {SI} {Σ: gFunctors SI} `{!heapG Σ} : ref_irisG heap_lang Σ := {
  ref_state_interp σ _ := (gen_heap_ctx σ.(heap))%I;
  ref_fork_post _ := True%I;
}.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Definition array {SI} {Σ: gFunctors SI} `{!heapG Σ} (l : loc) (vs : list val) : iProp Σ :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦ v)%I.
Notation "l ↦∗ vs" := (array l vs)
  (at level 20, format "l  ↦∗  vs") : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _ _) => eapply CmpXchgS : core.
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _ _) => apply alloc_fresh : core.
Local Hint Extern 0 (head_step NewProph _ _ _ _ _) => apply new_proph_id_fresh : core.
Local Hint Resolve to_of_val : core.

Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
Proof. solve_atomic. Qed.
Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. Qed.
Instance skip_atomic s  : Atomic s Skip.
Proof. solve_atomic. Qed.
Instance new_proph_atomic s : Atomic s NewProph.
Proof. solve_atomic. Qed.
Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof. solve_atomic. Qed.

Instance proph_resolve_atomic s e v1 v2 :
  Atomic s e → Atomic s (Resolve e (Val v1) (Val v2)).
Proof.
  rename e into e1. intros H σ1 e2 κ σ2 efs [Ks e1' e2' Hfill -> step].
  simpl in *. induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
  - subst. inversion_clear step. by apply (H σ1 (Val v) κs σ2 efs), head_prim_step.
  - rewrite fill_app. rewrite fill_app in Hfill.
    assert (∀ v, Val v = fill Ks e1' → False) as fill_absurd.
    { intros v Hv. assert (to_val (fill Ks e1') = Some v) as Htv by by rewrite -Hv.
      apply to_val_fill_some in Htv. destruct Htv as [-> ->]. inversion step. }
    destruct K; (inversion Hfill; clear Hfill; subst; try
      match goal with | H : Val ?v = fill Ks e1' |- _ => by apply fill_absurd in H end).
    refine (_ (H σ1 (fill (Ks ++ [K]) e2') _ σ2 efs _)).
    + destruct s; intro Hs; simpl in *.
      * destruct Hs as [v Hs]. apply to_val_fill_some in Hs. by destruct Hs, Ks.
      * apply irreducible_resolve. by rewrite fill_app in Hs.
    + econstructor 1 with (K := Ks ++ [K]); try done. simpl. by rewrite fill_app.
Qed.

Instance resolve_proph_atomic s v1 v2 : Atomic s (ResolveProph (Val v1) (Val v2)).
Proof. by apply proph_resolve_atomic, skip_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof. solve_pure_exec. Qed.
(* Higher-priority instance for EqOp. *)
Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2) 1
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

Section lifting.
Context {SI} {Σ: gFunctors SI} `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types sz off : nat.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.
Lemma swp_fork k s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ SWP Fork e at k @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply swp_lift_atomic_head_step.
  iIntros (σ1 κ κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.
(*
Lemma twp_fork s E e Φ :
  WP e @ s; ⊤ [{ _, True }] -∗ Φ (LitV LitUnit) -∗ WP Fork e @ s; E [{ Φ }].
Proof.
  iIntros "He HΦ". iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1 κs n) "Hσ !>"; iSplit; first by eauto.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.
 *)

Lemma array_nil l : l ↦∗ [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l v : l ↦∗ [v] ⊣⊢ l ↦ v.
Proof. by rewrite /array /= right_id loc_add_0. Qed.

Lemma array_app l vs ws :
  l ↦∗ (vs ++ ws) ⊣⊢ l ↦∗ vs ∗ (l +ₗ length vs) ↦∗ ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  by setoid_rewrite loc_add_assoc.
Qed.

Lemma array_cons l v vs : l ↦∗ (v :: vs) ⊣⊢ l ↦ v ∗ (l +ₗ 1) ↦∗ vs.
Proof.
  rewrite /array big_sepL_cons loc_add_0.
  setoid_rewrite loc_add_assoc.
  setoid_rewrite Nat2Z.inj_succ.
  by setoid_rewrite Z.add_1_l.
Qed.

Lemma heap_array_to_array l vs :
  ([∗ map] l' ↦ v ∈ heap_array l vs, l' ↦ v) -∗ l ↦∗ vs.
Proof.
  iIntros "Hvs". iInduction vs as [|v vs] "IH" forall (l); simpl.
  { by rewrite /array. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite array_cons.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]".
  by iApply "IH".
Qed.

Lemma heap_array_to_seq_meta l vs n :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma update_array l vs off v :
  vs !! off = Some v →
  sbi_emp_valid (l ↦∗ vs -∗ ((l +ₗ off) ↦ v ∗ ∀ v', (l +ₗ off) ↦ v' -∗ l ↦∗ <[off:=v']>vs))%I.
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗ X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs)%nat as H by (apply lookup_lt_is_Some; by eexists).
  rewrite take_length min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗ <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite take_length min_l; last by lia. iFrame.
  rewrite drop_insert; last by lia. done.
Qed.

(** Heap *)
Lemma wp_allocN s E v n :
  0 < n →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs k) "[Hσ Hκs] !>"; iSplit; first by auto with lia.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_alloc_gen with "Hσ") as "(Hσ & Hl & Hm)".
  { apply (heap_array_map_disjoint _ l (replicate (Z.to_nat n) v)); eauto.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iModIntro; iSplit; first done. iFrame "Hσ Hκs". iApply "HΦ". iSplitL "Hl".
  - by iApply heap_array_to_array.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.
Lemma swp_allocN k s E v n :
  0 < n →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) at k @ s; E
  {{{ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply swp_lift_atomic_head_step_no_fork.
  iIntros (σ1 κ κs k') "[Hσ Hκs] !>"; iSplit; first by auto with lia.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_alloc_gen with "Hσ") as "(Hσ & Hl & Hm)".
  { apply (heap_array_map_disjoint _ l (replicate (Z.to_nat n) v)); eauto.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iModIntro; iSplit; first done. iFrame "Hσ Hκs". iApply "HΦ". iSplitL "Hl".
  - by iApply heap_array_to_array.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

(*Lemma twp_allocN s E v n :
  0 < n →
  [[{ True }]] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  [[{ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs k) "[Hσ Hκs] !>"; iSplit; first by destruct n; auto with lia.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_alloc_gen with "Hσ") as "(Hσ & Hl & Hm)".
  { apply (heap_array_map_disjoint _ l (replicate (Z.to_nat n) v)); eauto.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iModIntro; do 2 (iSplit; first done). iFrame "Hσ Hκs". iApply "HΦ". iSplitL "Hl".
  - by iApply heap_array_to_array.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.*)

Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_allocN; auto with lia.
  iIntros "!>" (l) "/= (? & ? & _)".
  rewrite array_singleton loc_add_0. iApply "HΦ"; iFrame.
Qed.
Lemma swp_alloc k s E v :
  {{{ True }}} Alloc (Val v) at k @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply swp_allocN; auto with lia.
  iIntros "!>" (l) "/= (? & ? & _)".
  rewrite array_singleton loc_add_0. iApply "HΦ"; iFrame.
Qed.

(*Lemma twp_alloc s E v :
  [[{ True }]] Alloc (Val v) @ s; E [[{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_allocN; auto with lia.
  iIntros (l) "/= (? & ? & _)".
  rewrite array_singleton loc_add_0. iApply "HΦ"; iFrame.
Qed.*)

Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma swp_load k s E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Val $ LitV $ LitLoc l) at k @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply swp_lift_atomic_head_step_no_fork.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(*Lemma twp_load s E l q v :
  [[{ l ↦{q} v }]] Load (Val $ LitV $ LitLoc l) @ s; E [[{ RET v; l ↦{q} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iSplit; first done. iFrame. by iApply "HΦ".
Qed.*)

Lemma wp_store s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
Lemma swp_store k s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) at k @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply swp_lift_atomic_head_step_no_fork.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

(*Lemma twp_store s E l v' v :
  [[{ l ↦ v' }]] Store (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iSplit; first done. iFrame. by iApply "HΦ".
Qed.*)

Lemma wp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma swp_cmpxchg_fail k s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) at k @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply swp_lift_atomic_head_step_no_fork.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
(*Lemma twp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{q} v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iModIntro; iSplit=> //. iSplit; first done. iFrame. by iApply "HΦ".
Qed.*)

Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
Lemma swp_cmpxchg_suc k s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) at k @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply swp_lift_atomic_head_step_no_fork.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
(*Lemma twp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  [[{ l ↦ v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iSplit; first done. iFrame. by iApply "HΦ".
Qed.*)

Lemma wp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
Lemma swp_faa k s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) at k @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply swp_lift_atomic_head_step_no_fork.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
(*Lemma twp_faa s E l i1 i2 :
  [[{ l ↦ LitV (LitInt i1) }]] FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  [[{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ e2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iSplit; first done. iFrame. by iApply "HΦ".
Qed.*)

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ HR] !>". iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep). inv_head_step.
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma swp_new_proph k s E :
  {{{ True }}}
    NewProph at k @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply swp_lift_atomic_head_step_no_fork.
  iIntros (σ1 κ κs n) "[Hσ HR] !>". iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep). inv_head_step.
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply Ectx_step with (K:=[]); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor. by apply prim_step_to_val_is_head_step.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  head_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst. inversion step. by constructor.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - assert (fill_item K (fill Ks e1') = fill (Ks ++ [K]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item K (fill Ks e2') = fill (Ks ++ [K]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [K]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply Ectx_step with (K0 := Ks ++ [K]); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - assert (to_val (fill Ks e1') = Some vp); first by rewrite -H1 //.
      apply to_val_fill_some in H. destruct H as [-> ->]. inversion step.
    - assert (to_val (fill Ks e1') = Some vt); first by rewrite -H2 //.
      apply to_val_fill_some in H. destruct H as [-> ->]. inversion step.
Qed.


Arguments gstep : simpl never.
Existing Instance elim_gstep.
Lemma wp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (σ1 κ κs n) "[Hσ Hκ]". destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! σ1 [] κs n with "[$Hσ $Hκ]") as "[Hs WPe]".
    iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inversion step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - rewrite -app_assoc.
    iMod ("WPe" $! σ1 _ _ n with "[$Hσ $Hκ]") as "[Hs WPe]".
    iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). apply step_resolve in step; last done.
    inversion step; simplify_list_eq.
    iMod ("WPe" $! (Val w') σ2 efs with "[%]") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "[[$ Hκ] WPe]".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed.

Arguments gstepN : simpl never.
Existing Instance elim_gstepN.
Lemma swp_resolve k s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  proph p pvs -∗
  SWP e at k @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  SWP Resolve e (Val $ LitV $ LitProphecy p) (Val v) at k @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A) "Hp WPe". rewrite !swp_unfold /swp_def /=. simpl in *.
  iIntros (σ1 κ κs n) "[Hσ Hκ]". destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! σ1 [] κs n with "[$Hσ $Hκ]") as "[Hs WPe]". iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inversion step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - rewrite -app_assoc.
    iMod ("WPe" $! σ1 _ _ n with "[$Hσ $Hκ]") as "[Hs WPe]". iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). apply step_resolve in step; last done.
    inversion step; simplify_list_eq.
    iMod ("WPe" $! (Val w') σ2 efs with "[%]") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "[[$ Hκ] WPe]".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed.

(** Lemmas for some particular expression inside the [Resolve]. *)
Lemma wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v :
  {{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply (wp_resolve with "Hp"); first done.
  iApply wp_pure_step_later=> //=. iApply wp_value.
  iIntros "!>" (vs') "HEq Hp". iApply "HΦ". iFrame.
Qed.

Lemma swp_resolve_proph k s E (p : proph_id) (pvs : list (val * val)) v :
  {{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) at k @ s; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply (swp_resolve with "Hp").
  iApply swp_pure_step_later=> //=. iApply wp_value.
  iIntros "!>" (vs') "HEq Hp". iApply "HΦ". iFrame.
Qed.

Lemma wp_resolve_cmpxchg_suc s E l (p : proph_id) (pvs : list (val * val)) v1 v2 v :
  vals_compare_safe v1 v1 →
  {{{ proph p pvs ∗ ▷ l ↦ v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v1, #true) ; ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ v2 }}}.
Proof.
  iIntros (Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
  iApply (wp_cmpxchg_suc with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma swp_resolve_cmpxchg_suc k s E l (p : proph_id) (pvs : list (val * val)) v1 v2 v :
  vals_compare_safe v1 v1 →
  {{{ proph p pvs ∗ ▷ l ↦ v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v at k @ s; E
  {{{ RET (v1, #true) ; ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ v2 }}}.
Proof.
  iIntros (Hcmp Φ) "[Hp Hl] HΦ".
  iApply (swp_resolve with "Hp").
  assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
  iApply (swp_cmpxchg_suc with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma wp_resolve_cmpxchg_fail s E l (p : proph_id) (pvs : list (val * val)) q v' v1 v2 v :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ proph p pvs ∗ ▷ l ↦{q} v' }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v', #false) ; ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{q} v' }}}.
Proof.
  iIntros (NEq Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  iApply (wp_cmpxchg_fail with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma swp_resolve_cmpxchg_fail k s E l (p : proph_id) (pvs : list (val * val)) q v' v1 v2 v :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ proph p pvs ∗ ▷ l ↦{q} v' }}}
    Resolve (CmpXchg #l v1 v2) #p v at k @ s; E
  {{{ RET (v', #false) ; ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{q} v' }}}.
Proof.
  iIntros (NEq Hcmp Φ) "[Hp Hl] HΦ".
  iApply (swp_resolve with "Hp").
  iApply (swp_cmpxchg_fail with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

(** Array lemmas *)
Lemma wp_allocN_vec s E v n :
  0 < n →
  {{{ True }}}
    AllocN #n v @ s ; E
  {{{ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply wp_allocN; [ lia | done | .. ]. iNext.
  iIntros (l) "[Hl Hm]". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.

Lemma swp_allocN_vec k s E v n :
  0 < n →
  {{{ True }}}
    AllocN #n v at k @ s ; E
  {{{ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply swp_allocN; [ lia | done | .. ]. iNext.
  iIntros (l) "[Hl Hm]". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.

Lemma wp_load_offset s E l off vs v :
  vs !! off = Some v →
  {{{ ▷ l ↦∗ vs }}} ! #(l +ₗ off) @ s; E {{{ RET v; l ↦∗ vs }}}.
Proof.
  iIntros (Hlookup Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_load with "Hl1"). iIntros "!> Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.

Lemma swp_load_offset k s E l off vs v :
  vs !! off = Some v →
  {{{ ▷ l ↦∗ vs }}} ! #(l +ₗ off) at k @ s; E {{{ RET v; l ↦∗ vs }}}.
Proof.
  iIntros (Hlookup Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (swp_load with "Hl1"). iIntros "!> Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_load_offset_vec s E l sz (off : fin sz) (vs : vec val sz) :
  {{{ ▷ l ↦∗ vs }}} ! #(l +ₗ off) @ s; E {{{ RET vs !!! off; l ↦∗ vs }}}.
Proof. apply wp_load_offset. by apply vlookup_lookup. Qed.

Lemma swp_load_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) :
  {{{ ▷ l ↦∗ vs }}} ! #(l +ₗ off) at k @ s; E {{{ RET vs !!! off; l ↦∗ vs }}}.
Proof. apply swp_load_offset. by apply vlookup_lookup. Qed.


Lemma wp_store_offset s E l off vs v :
  is_Some (vs !! off) →
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
Proof.
  iIntros ([w Hlookup] Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_store with "Hl1"). iNext. iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma swp_store_offset k s E l off vs v :
  is_Some (vs !! off) →
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v at k @ s; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
Proof.
  iIntros ([w Hlookup] Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (swp_store with "Hl1"). iNext. iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply wp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.
Lemma swp_store_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v at k @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply swp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.


Lemma wp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v', #true); l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (Hlookup ?? Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_cmpxchg_suc with "Hl1"); [done..|].
  iNext. iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma swp_cmpxchg_suc_offset k s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 at k @ s; E
  {{{ RET (v', #true); l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (Hlookup ?? Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (swp_cmpxchg_suc with "Hl1"); [done..|].
  iNext. iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert. eapply wp_cmpxchg_suc_offset=> //.
  by apply vlookup_lookup.
Qed.
Lemma swp_cmpxchg_suc_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 at k @ s; E
  {{{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert. eapply swp_cmpxchg_suc_offset=> //.
  by apply vlookup_lookup.
Qed.

Lemma wp_cmpxchg_fail_offset s E l off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v0, #false); l ↦∗ vs }}}.
Proof.
  iIntros (Hlookup HNEq Hcmp Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_cmpxchg_fail with "Hl1"); first done.
  { destruct Hcmp; by [ left | right ]. }
  iIntros "!> Hl1". iApply "HΦ". iDestruct ("Hl2" $! v0) as "Hl2".
  rewrite list_insert_id; last done. iApply "Hl2". iApply "Hl1".
Qed.

Lemma swp_cmpxchg_fail_offset k s E l off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 at k @ s; E
  {{{ RET (v0, #false); l ↦∗ vs }}}.
Proof.
  iIntros (Hlookup HNEq Hcmp Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (swp_cmpxchg_fail with "Hl1"); first done.
  { destruct Hcmp; by [ left | right ]. }
  iIntros "!> Hl1". iApply "HΦ". iDestruct ("Hl2" $! v0) as "Hl2".
  rewrite list_insert_id; last done. iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_cmpxchg_fail_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #false); l ↦∗ vs }}}.
Proof. intros. eapply wp_cmpxchg_fail_offset=> //. by apply vlookup_lookup. Qed.
Lemma swp_cmpxchg_fail_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 at k @ s; E
  {{{ RET (vs !!! off, #false); l ↦∗ vs }}}.
Proof. intros. eapply swp_cmpxchg_fail_offset=> //. by apply vlookup_lookup. Qed.

Lemma wp_faa_offset s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof.
  iIntros (Hlookup Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_faa with "Hl1").
  iNext. iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma swp_faa_offset k s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 at k @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof.
  iIntros (Hlookup Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (swp_faa with "Hl1").
  iNext. iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert. apply wp_faa_offset=> //.
  by apply vlookup_lookup.
Qed.
Lemma swp_faa_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 at k @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert. apply swp_faa_offset=> //.
  by apply vlookup_lookup.
Qed.

End lifting.



Section refinements.

  Context {SI} {Σ: gFunctors SI} {A: Type} `{!source Σ A} `{!heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types efs : list expr.
  Implicit Types σ : state.
  Implicit Types v : val.
  Implicit Types vs : list val.
  Implicit Types l : loc.
  Implicit Types sz off : nat.

  (* TODO: Uniform approch to where the refinement *)
  Existing Instance heapG_invG.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma rswp_fork k s E e Φ :
  RWP e @ s; ⊤ ⟨⟨ _, True ⟩⟩ -∗ Φ (LitV LitUnit) -∗ RSWP Fork e at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "He HΦ". iApply rswp_lift_atomic_head_step.
  iIntros (σ1 n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs κ Hstep); inv_head_step. by iFrame.
Qed.

(** Heap *)
Lemma rswp_allocN k s E v n :
  0 < n →
  ⟨⟨⟨ True ⟩⟩⟩ AllocN (Val $ LitV $ LitInt $ n) (Val v) at k @ s; E
  ⟨⟨⟨ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ ⟩⟩⟩.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply rswp_lift_atomic_head_step_no_fork.
  iIntros (σ1 k') "Hσ !>"; iSplit; first by auto with lia.
  iNext; iIntros (v2 σ2 efs κ Hstep); inv_head_step.
  iMod (@gen_heap_alloc_gen with "Hσ") as "(Hσ & Hl & Hm)".
  { apply (heap_array_map_disjoint _ l (replicate (Z.to_nat n) v)); eauto.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iModIntro; iSplit; first done. iFrame "Hσ". iApply "HΦ". iSplitL "Hl".
  - by iApply heap_array_to_array.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

Lemma rswp_alloc k s E v :
  ⟨⟨⟨ True ⟩⟩⟩ Alloc (Val v) at k @ s; E ⟨⟨⟨ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ ⟩⟩⟩.
Proof.
  iIntros (Φ) "_ HΦ". iApply rswp_allocN; auto with lia.
  iIntros "!>" (l) "/= (? & ? & _)".
  rewrite array_singleton loc_add_0. iApply "HΦ"; iFrame.
Qed.

(* TODO: we can always get rid of the later if the goal is a WP anyway. Having it in the rule seems unnecessary.*)
Lemma rswp_load k s E l q v :
  ⟨⟨⟨ ▷ l ↦{q} v ⟩⟩⟩ Load (Val $ LitV $ LitLoc l) at k @ s; E ⟨⟨⟨ RET v; l ↦{q} v ⟩⟩⟩.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply rswp_lift_atomic_head_step_no_fork.
  iIntros (σ1 n) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs κ Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* TODO: we can always get rid of the later if the goal is a WP anyway. Having it in the rule seems unnecessary.*)
Lemma rswp_store k s E l v' v :
  ⟨⟨⟨ ▷ l ↦ v' ⟩⟩⟩ Store (Val $ LitV (LitLoc l)) (Val v) at k @ s; E
  ⟨⟨⟨ RET LitV LitUnit; l ↦ v ⟩⟩⟩.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply rswp_lift_atomic_head_step_no_fork.
  iIntros (σ1 n) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs κ Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma rswp_cmpxchg_fail k s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  ⟨⟨⟨ ▷ l ↦{q} v' ⟩⟩⟩ CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) at k @ s; E
  ⟨⟨⟨ RET PairV v' (LitV $ LitBool false); l ↦{q} v' ⟩⟩⟩.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply rswp_lift_atomic_head_step_no_fork.
  iIntros (σ1 n) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs κ Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma rswp_cmpxchg_suc k s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  ⟨⟨⟨ ▷ l ↦ v' ⟩⟩⟩ CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) at k @ s; E
  ⟨⟨⟨ RET PairV v' (LitV $ LitBool true); l ↦ v2 ⟩⟩⟩.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply rswp_lift_atomic_head_step_no_fork.
  iIntros (σ1 n) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs κ Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma rswp_faa k s E l i1 i2 :
  ⟨⟨⟨ ▷ l ↦ LitV (LitInt i1) ⟩⟩⟩ FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) at k @ s; E
  ⟨⟨⟨ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) ⟩⟩⟩.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply rswp_lift_atomic_head_step_no_fork.
  iIntros (σ1 n) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs κ Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma rswp_allocN_vec k s E v n :
  0 < n →
  ⟨⟨⟨ True ⟩⟩⟩
    AllocN #n v at k @ s ; E
  ⟨⟨⟨ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ ⟩⟩⟩.
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply rswp_allocN; [ lia | done | .. ]. iNext.
  iIntros (l) "[Hl Hm]". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.

Lemma rswp_load_offset k s E l off vs v :
  vs !! off = Some v →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ ! #(l +ₗ off) at k @ s; E ⟨⟨⟨ RET v; l ↦∗ vs ⟩⟩⟩.
Proof.
  iIntros (Hlookup Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (rswp_load with "Hl1"). iIntros "!> Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.

Lemma rswp_load_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) :
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ ! #(l +ₗ off) at k @ s; E ⟨⟨⟨ RET vs !!! off; l ↦∗ vs ⟩⟩⟩.
Proof. apply rswp_load_offset. by apply vlookup_lookup. Qed.

Lemma rswp_store_offset k s E l off vs v :
  is_Some (vs !! off) →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ #(l +ₗ off) <- v at k @ s; E ⟨⟨⟨ RET #(); l ↦∗ <[off:=v]> vs ⟩⟩⟩.
Proof.
  iIntros ([w Hlookup] Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (rswp_store with "Hl1"). iNext. iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma rswp_store_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) v :
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ #(l +ₗ off) <- v at k @ s; E ⟨⟨⟨ RET #(); l ↦∗ vinsert off v vs ⟩⟩⟩.
Proof.
  setoid_rewrite vec_to_list_insert. apply rswp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.

Lemma rswp_cmpxchg_suc_offset k s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩
    CmpXchg #(l +ₗ off) v1 v2 at k @ s; E
  ⟨⟨⟨ RET (v', #true); l ↦∗ <[off:=v2]> vs ⟩⟩⟩.
Proof.
  iIntros (Hlookup ?? Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (rswp_cmpxchg_suc with "Hl1"); [done..|].
  iNext. iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma rswp_cmpxchg_suc_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩
    CmpXchg #(l +ₗ off) v1 v2 at k @ s; E
  ⟨⟨⟨ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs ⟩⟩⟩.
Proof.
  intros. setoid_rewrite vec_to_list_insert. eapply rswp_cmpxchg_suc_offset=> //.
  by apply vlookup_lookup.
Qed.

Lemma rswp_cmpxchg_fail_offset k s E l off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩
    CmpXchg #(l +ₗ off) v1 v2 at k @ s; E
  ⟨⟨⟨ RET (v0, #false); l ↦∗ vs ⟩⟩⟩.
Proof.
  iIntros (Hlookup HNEq Hcmp Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (rswp_cmpxchg_fail with "Hl1"); first done.
  { destruct Hcmp; by [ left | right ]. }
  iIntros "!> Hl1". iApply "HΦ". iDestruct ("Hl2" $! v0) as "Hl2".
  rewrite list_insert_id; last done. iApply "Hl2". iApply "Hl1".
Qed.

Lemma rswp_cmpxchg_fail_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩
    CmpXchg #(l +ₗ off) v1 v2 at k @ s; E
  ⟨⟨⟨ RET (vs !!! off, #false); l ↦∗ vs ⟩⟩⟩.
Proof. intros. eapply rswp_cmpxchg_fail_offset=> //. by apply vlookup_lookup. Qed.

Lemma rswp_faa_offset k s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ FAA #(l +ₗ off) #i2 at k @ s; E
  ⟨⟨⟨ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs ⟩⟩⟩.
Proof.
  iIntros (Hlookup Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (rswp_faa with "Hl1").
  iNext. iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma rswp_faa_offset_vec k s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ FAA #(l +ₗ off) #i2 at k @ s; E
  ⟨⟨⟨ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs ⟩⟩⟩.
Proof.
  intros. setoid_rewrite vec_to_list_insert. apply rswp_faa_offset=> //.
  by apply vlookup_lookup.
Qed.


(* refinement weakest pre versions *)
(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma rwp_fork s E e Φ :
  RWP e @ s; ⊤ ⟨⟨ _, True ⟩⟩ -∗ Φ (LitV LitUnit) -∗ RWP Fork e @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_fork with "H HΦ").
Qed.

(** Heap *)
Lemma rwp_allocN s E v n :
  0 < n →
  ⟨⟨⟨ True ⟩⟩⟩ AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  ⟨⟨⟨ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ ⟩⟩⟩.
Proof.
  iIntros (Hn Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_allocN _ _ _ _ _ Hn Φ with "H HΦ").
Qed.

Lemma rwp_alloc s E v :
  ⟨⟨⟨ True ⟩⟩⟩ Alloc (Val v) @ s; E ⟨⟨⟨ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ ⟩⟩⟩.
Proof.
  iIntros (Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_alloc with "H HΦ").
Qed.

Lemma rwp_load s E l q v :
  ⟨⟨⟨ ▷ l ↦{q} v ⟩⟩⟩ Load (Val $ LitV $ LitLoc l) @ s; E ⟨⟨⟨ RET v; l ↦{q} v ⟩⟩⟩.
Proof.
  iIntros (Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_load with "H HΦ").
Qed.

Lemma rwp_store s E l v' v :
  ⟨⟨⟨ ▷ l ↦ v' ⟩⟩⟩ Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  ⟨⟨⟨ RET LitV LitUnit; l ↦ v ⟩⟩⟩.
Proof.
  iIntros (Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_store with "H HΦ").
Qed.

Lemma rwp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  ⟨⟨⟨ ▷ l ↦{q} v' ⟩⟩⟩ CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  ⟨⟨⟨ RET PairV v' (LitV $ LitBool false); l ↦{q} v' ⟩⟩⟩.
Proof.
  iIntros (?? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_cmpxchg_fail with "H HΦ").
Qed.

Lemma rwp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  ⟨⟨⟨ ▷ l ↦ v' ⟩⟩⟩ CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  ⟨⟨⟨ RET PairV v' (LitV $ LitBool true); l ↦ v2 ⟩⟩⟩.
Proof.
  iIntros (?? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_cmpxchg_suc with "H HΦ").
Qed.

Lemma rwp_faa s E l i1 i2 :
  ⟨⟨⟨ ▷ l ↦ LitV (LitInt i1) ⟩⟩⟩ FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  ⟨⟨⟨ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) ⟩⟩⟩.
Proof.
  iIntros (Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_faa with "H HΦ").
Qed.

Lemma rwp_allocN_vec s E v n :
  0 < n →
  ⟨⟨⟨ True ⟩⟩⟩
    AllocN #n v @ s ; E
  ⟨⟨⟨ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ ⟩⟩⟩.
Proof.
  iIntros (? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_allocN_vec with "H HΦ").
Qed.

Lemma rwp_load_offset s E l off vs v :
  vs !! off = Some v →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ ! #(l +ₗ off) @ s; E ⟨⟨⟨ RET v; l ↦∗ vs ⟩⟩⟩.
Proof.
  iIntros (? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_load_offset with "H HΦ").
Qed.

Lemma rwp_load_offset_vec s E l sz (off : fin sz) (vs : vec val sz) :
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ ! #(l +ₗ off) @ s; E ⟨⟨⟨ RET vs !!! off; l ↦∗ vs ⟩⟩⟩.
Proof. apply rwp_load_offset. by apply vlookup_lookup. Qed.

Lemma rwp_store_offset s E l off vs v :
  is_Some (vs !! off) →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ #(l +ₗ off) <- v @ s; E ⟨⟨⟨ RET #(); l ↦∗ <[off:=v]> vs ⟩⟩⟩.
Proof.
  iIntros (? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_store_offset with "H HΦ").
Qed.

Lemma rwp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ #(l +ₗ off) <- v @ s; E ⟨⟨⟨ RET #(); l ↦∗ vinsert off v vs ⟩⟩⟩.
Proof.
  iIntros (Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_store_offset_vec with "H HΦ").
Qed.

Lemma rwp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  ⟨⟨⟨ RET (v', #true); l ↦∗ <[off:=v2]> vs ⟩⟩⟩.
Proof.
  iIntros (??? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_cmpxchg_suc_offset with "H HΦ").
Qed.

Lemma rwp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  ⟨⟨⟨ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs ⟩⟩⟩.
Proof.
  iIntros (?? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_cmpxchg_suc_offset_vec with "H HΦ").
Qed.

Lemma rwp_cmpxchg_fail_offset s E l off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  ⟨⟨⟨ RET (v0, #false); l ↦∗ vs ⟩⟩⟩.
Proof.
  iIntros (??? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_cmpxchg_fail_offset with "H HΦ").
Qed.

Lemma rwp_cmpxchg_fail_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  ⟨⟨⟨ RET (vs !!! off, #false); l ↦∗ vs ⟩⟩⟩.
Proof. intros. eapply rwp_cmpxchg_fail_offset=> //. by apply vlookup_lookup. Qed.

Lemma rwp_faa_offset s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ FAA #(l +ₗ off) #i2 @ s; E
  ⟨⟨⟨ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs ⟩⟩⟩.
Proof.
  iIntros (? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_faa_offset with "H HΦ").
Qed.

Lemma rwp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  ⟨⟨⟨ ▷ l ↦∗ vs ⟩⟩⟩ FAA #(l +ₗ off) #i2 @ s; E
  ⟨⟨⟨ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs ⟩⟩⟩.
Proof.
  iIntros (? Φ) "H HΦ"; iApply rwp_no_step; auto; last by iApply (rswp_faa_offset_vec with "H HΦ").
Qed.
End refinements.
