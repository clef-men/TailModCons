From iris.program_logic.refinement Require Export ref_weakestpre ref_source seq_weakestpre.
From iris.base_logic.lib Require Export invariants na_invariants.
From iris.heap_lang Require Export lang lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation metatheory.
From iris.algebra Require Import auth gmap excl frac agree mlist.
Set Default Proof Using "Type".

Inductive rtc_list {A : Type} (R : relation A) : list A → Prop :=
| rtc_list_nil : rtc_list R nil
| rtc_list_once : ∀ x, rtc_list R [x]
| rtc_list_l : ∀ x y l, R x y → rtc_list R (y :: l) → rtc_list R (x :: y :: l).

Lemma rtc_list_r {A : Type} (R : relation A) (x y: A) (l: list A) :
  R x y →
  rtc_list R (l ++ [x]) →
  rtc_list R (l ++ [x] ++ [y]).
Proof.
  rewrite app_assoc.
  intros HR Hrtc.
  remember (l ++ [x]) as l' eqn:Heql. revert x y HR l Heql; induction Hrtc; intros.
  - apply rtc_list_once.
  - symmetry in Heql. apply app_singleton in Heql as [(?&Heq)|(?&?)]; last by congruence.
    apply rtc_list_l; last apply rtc_list_once.
    inversion Heq; subst; eauto.
  - destruct l0; first by (simpl in Heql; congruence).
    inversion Heql; subst.
    simpl; apply rtc_list_l; first done.
    rewrite app_comm_cons. eapply IHHrtc; eauto.
Qed.

Lemma rtc_list_app_r {A: Type} (R: relation A) l1 l2:
    rtc_list R (l1 ++ l2) → rtc_list R l2.
Proof.
  revert l2. induction l1; first done.
  intros l2 Hrtc. inversion Hrtc as [| | ???? Hrtc' [Heq1 Heq2]].
  - assert (l2 = []) as -> by (eapply app_eq_nil; eauto).
    constructor.
  - apply IHl1. rewrite -Heq2; eauto.
Qed.

Lemma rtc_list_rtc {A: Type} (R: relation A) (x y : A) (l : list A):
  rtc_list R ([x] ++ l ++ [y]) →
  rtc R x y.
Proof.
  revert x y.
  induction l as [| a l IHl]; intros x y Hrtc.
  - inversion Hrtc; subst; eauto using rtc_l, rtc_refl.
  - inversion Hrtc; subst.
    apply (rtc_l _ _ a); auto.
Qed.

Lemma rtc_list_lookup_last_rtc {A: Type} (R: relation A) (x y : A) (l : list A) (i: nat) :
  (l ++ [y]) !! i = Some x →
  rtc_list R (l ++ [y]) →
  rtc R x y.
Proof.
  rewrite lookup_app_Some.
  intros [Hl|Hr].
  * apply elem_of_list_split_length in Hl.
    destruct Hl as (l1&l2&Heq&Hlen). subst.
    rewrite -app_assoc => Hrtc. apply rtc_list_app_r in Hrtc.
    rewrite -app_comm_cons in Hrtc. eapply rtc_list_rtc; eauto.
    simpl; eauto.
  * destruct Hr as (_&Hlookup). intros.
    destruct (i - length l)%nat.
    ** rewrite /= in Hlookup. inversion Hlookup. apply rtc_refl.
    ** exfalso. rewrite /= lookup_nil in Hlookup. congruence.
Qed.

(* HeapLang <={log} HeapLang *)
Definition tpoolUR SI : ucmraT SI := gmapUR nat (exclR (exprO SI)).
Definition cfgUR SI := prodUR (tpoolUR SI) (gen_heapUR SI loc val).

Class rheapPreG {SI} (Σ: gFunctors SI) := RHeapPreG {
  rheapPreG_heapG :> heapPreG Σ;
  rheapPreG_ghost_repr :> inG Σ (authR (cfgUR SI)); (* the source ghost state *)
  rheapPreG_fmlistG :> fmlistG (cfg heap_lang) Σ;
}.

Class rheapG {SI} (Σ: gFunctors SI) := RHeapG {
  rheapG_heapG :> heapG Σ;
  rheapG_ghost_repr :> inG Σ (authR (cfgUR SI)); (* the source ghost state *)
  rheapG_ghost_name: gname;
  rheapG_fmlistG :> fmlistG (cfg heap_lang) Σ;
  rheapG_fmlist_name: gname;
}.

Section source_ghost_state.
  Context {SI: indexT} `{Σ: gFunctors SI} `{!rheapG Σ}.

  Fixpoint to_tpool_go (i : nat) (tp : list expr) : tpoolUR SI :=
    match tp with
    | [] => ∅
    | e :: tp => <[i:=Excl e]>(to_tpool_go (S i) tp)
    end.
  Definition to_tpool : list expr → tpoolUR SI := to_tpool_go 0.

  Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own rheapG_ghost_name (◯ (∅, {[ l := (q, to_agree v) ]})).

  Definition tpool_mapsto (j : nat) (e: expr) : iProp Σ :=
    own rheapG_ghost_name (◯ ({[ j := Excl e ]}, ∅)).

  Global Instance heapS_mapsto_timeless l q v : Timeless (heapS_mapsto l q v).
  Proof. apply _. Qed.

  Typeclasses Opaque heapS_mapsto tpool_mapsto.


  Section thread_pool_conversion.
  Open Scope nat.
  (** Conversion to tpools and back *)
  Lemma to_tpool_valid es : ✓ to_tpool es.
  Proof.
    rewrite /to_tpool. move: 0.
    induction es as [|e es]=> n //; simpl. by apply insert_valid.
  Qed.

  Lemma tpool_lookup tp j : to_tpool tp !! j = Excl <$> tp !! j.
  Proof.
    cut (∀ i, to_tpool_go i tp !! (i + j) = Excl <$> tp !! j).
    { intros help. apply (help 0). }
    revert j. induction tp as [|e tp IH]=> //= -[|j] i /=.
    - by rewrite Nat.add_0_r lookup_insert.
    - by rewrite -Nat.add_succ_comm lookup_insert_ne; last lia.
  Qed.
  Lemma tpool_lookup_Some tp j e : to_tpool tp !! j = Excl' e → tp !! j = Some e.
  Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.
  Hint Resolve tpool_lookup_Some : core.

  Lemma to_tpool_insert tp j e :
    j < length tp →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    intros. apply: map_eq=> i. destruct (decide (i = j)) as [->|].
    - by rewrite tpool_lookup lookup_insert list_lookup_insert.
    - rewrite tpool_lookup lookup_insert_ne // list_lookup_insert_ne //.
      by rewrite tpool_lookup.
  Qed.
  Lemma to_tpool_insert' tp j e :
    is_Some (to_tpool tp !! j) →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    rewrite tpool_lookup fmap_is_Some lookup_lt_is_Some. apply to_tpool_insert.
  Qed.

  Lemma to_tpool_snoc tp e :
    to_tpool (tp ++ [e]) = <[length tp:=Excl e]>(to_tpool tp).
  Proof.
    intros. apply: map_eq=> i.
    destruct (lt_eq_lt_dec i (length tp)) as [[?| ->]|?].
    - rewrite lookup_insert_ne; last lia. by rewrite !tpool_lookup lookup_app_l.
    - by rewrite lookup_insert tpool_lookup lookup_app_r // Nat.sub_diag.
    - rewrite lookup_insert_ne; last lia.
      rewrite !tpool_lookup ?lookup_ge_None_2 ?app_length //=;
      change (ofe_car _ (exprO SI)) with expr; lia.
  Qed.

  Lemma tpool_singleton_included tp j e :
    {[j := Excl e]} ≼ to_tpool tp → tp !! j = Some e.
  Proof.
    move=> /singleton_included [ex [/leibniz_equiv_iff]].
    rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included ?]. by f_equal.
  Qed.
  Lemma tpool_singleton_included' tp j e :
    {[j := Excl e]} ≼ to_tpool tp → to_tpool tp !! j = Excl' e.
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.

End thread_pool_conversion.

End source_ghost_state.
Notation "l '↦s{' q } v" := (heapS_mapsto l q v) (at level 20, q at level 50, format "l  '↦s{' q }  v") : bi_scope.
Notation "l '↦s' v" := (heapS_mapsto l 1 v) (at level 20) : bi_scope.
Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.
Notation src e := (0 ⤇ e)%I.


Definition heap_srcT : Set := (list expr * (gmap loc val * gmap proph_id unit)).
Definition to_cfg '(es, (h, m)): cfg heap_lang := (es, {| heap := h; used_proph_id := {| mapset.mapset_car := m |} |}).
Global Instance heap_lang_source {SI} {Σ: gFunctors SI} `{!rheapG Σ}: source Σ heap_srcT := {|
  source_rel := λ s s', erased_step (to_cfg s) (to_cfg s');
  source_interp := (λ '(tp, (h, proph)), own rheapG_ghost_name (● ((to_tpool tp, to_gen_heap SI h): cfgUR SI)) ∗
                                             ∃ l, let l' := (l ++ [to_cfg (tp, (h, proph))]) in
                                                  ⌜rtc_list (erased_step) l'⌝ ∗
                                                  fmlist rheapG_fmlist_name 1 l')%I
|}.


Section heap_lang_source_steps.

    Context {SI: indexT} `{Σ: gFunctors SI} `{!rheapG Σ} `{!auth_sourceG Σ (natA SI)}.

    (* we use stuttering heap lang as a source *)
    Global Instance: source Σ (heap_srcT * nat) | 0 := _.

    Lemma step_insert tp j (e: expr) σ e' σ' efs κ:
      tp !! j = Some e → prim_step e σ κ e' σ' efs →
      erased_step (tp, σ) (<[j:= e']> tp ++ efs, σ').
    Proof.
      intros. rewrite -(take_drop_middle tp j e) //.
      rewrite insert_app_r_alt take_length_le ?Nat.sub_diag /=;
        eauto using lookup_lt_Some, Nat.lt_le_incl.
      rewrite -(assoc_L (++)) /=. exists κ.
      eapply step_atomic; eauto.
    Qed.


    Lemma pure_step_prim_step (e1 e2: expr) σ:
      pure_step e1 e2 → prim_step e1 σ [] e2 σ [].
    Proof.
      destruct 1 as [safe det]. destruct (safe σ) as (e' & σ' & efs & step).
      by specialize (det σ [] e' σ' efs step) as (_ & -> & -> & ->).
    Qed.


    (* allocate stuttering budget post-hoc *)
    Lemma step_frame (c1 c2: heap_srcT) (n m k: nat):
      (c1, n) ↪ (c2, m) → (c1, (n + k)%nat) ↪ (c2, (m + k)%nat).
    Proof.
      inversion 1; subst.
      - by apply lex_left.
      - apply lex_right, auth_source_step_frame; eauto; done.
    Qed.

    Lemma steps_frame (c1 c2: heap_srcT) (n m k: nat):
      (c1, n) ↪⁺ (c2, m) → (c1, (n + k)%nat) ↪⁺ (c2, (m + k)%nat).
    Proof.
      intros Hsteps.
      remember (c1, n) as p. revert n c1 Heqp.
      remember (c2, m) as q. revert m c2 Heqq.
      induction Hsteps as [? ? Hstep|p [c' m'] q Hstep Hsteps]; intros n c2 -> m c1 ->.
      - apply tc_once, step_frame, Hstep.
      - eapply tc_l; first eapply step_frame, Hstep.
        by eapply IHHsteps.
    Qed.

    Lemma step_add_stutter (c1 c2: heap_srcT) (n m: nat) c:
      (c1, n) ↪⁺ (c2, m) → c1 ≠ c2 → (c1, n) ↪⁺ (c2, (m + c)%nat).
    Proof.
      intros Hsteps.
      remember (c1, n) as p. revert n c1 Heqp.
      remember (c2, m) as q. revert m c2 Heqq.
      induction Hsteps as [? ? Hstep|p [c2 m] q Hstep Hsteps]; intros k c3 -> n c1 -> Hneq.
      - inversion Hstep; subst.
        + by eapply tc_once, lex_left.
        + naive_solver.
      - inversion Hstep; subst.
        + eapply tc_l; first apply lex_left; eauto.
          eapply steps_frame, Hsteps.
        + eapply tc_l; first apply lex_right; eauto.
    Qed.


    Lemma step_inv_alloc c E P j e1:
      (j ⤇ e1 -∗ src_update E P) ∗ (P -∗ ∃ e2, j ⤇ e2 ∗ ⌜e2 ≠ e1⌝)
      ⊢ j ⤇ e1 -∗ src_update E (P ∗ $ c).
    Proof.
      rewrite /src_update. iIntros "[Hupd HP] Hj".
      iIntros ([[tp [h m]] n]) "[Hsrc Hcred]".
      iDestruct "Hsrc" as "(Hsrc&Hl)".
      iDestruct (own_valid_2 with "Hsrc Hj") as %[[Htp%tpool_singleton_included'%tpool_lookup_Some _]%prod_included _]%auth_both_valid.
      iSpecialize ("Hupd" with "Hj"). iMod ("Hupd" $! (tp, (h, m), n) with "[$Hsrc $Hl $Hcred]") as ([[tp' [h' m']] m''] Hsteps) "[[[Hsrc Hsrcl] Hcred] P]".
      iAssert (⌜∃ e2, tp' !! j = Some e2 ∧ e2 ≠ e1⌝)%I as %Htp'; last destruct Htp' as [e2 [Htp' Hneq]].
      { iDestruct ("HP" with "P") as (e2) "[Hj %]".
        iDestruct (own_valid_2 with "Hsrc Hj") as %[[Htp'%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
        iPureIntro; exists e2. split; first eapply tpool_lookup_Some, Htp'. done.
      }
      iMod (own_update _ (● m'')  (● (m'' + c)%nat ⋅ ◯ c) with "Hcred") as "[Hnat Hc]".
      { eapply auth_update_alloc, nat_local_update. rewrite /ε //= /nat_unit. }
      iModIntro. iExists (tp', (h', m'), (m'' + c)%nat). iFrame.
      iPureIntro. apply step_add_stutter; eauto.
      injection 1 as -> ->.
      eapply Hneq. eapply Some_inj. rewrite -Htp -Htp' //=.
    Qed.


    (* stuttering rule *)
    Lemma step_stutter E c:
      srcF (natA SI) (S c) ⊢ src_update E (srcF (natA SI) c).
    Proof.
      rewrite /src_update.
      iIntros "Hf" ([[tp σ] n]) "[H● Hnat]".
      iDestruct (own_valid_2 with "Hnat Hf") as %[Hle%nat_included _]%auth_both_valid.
      destruct n as [|n]; first lia.
      iMod (own_update_2 _ (● (S n))  (◯ (S c)) (● n ⋅ ◯ c) with "Hnat Hf") as "[Hnat Hc]".
      { eapply auth_update, nat_local_update. lia. }
      iModIntro. iExists (tp, σ, n); iFrame.
      iPureIntro. apply tc_once, lex_right; simpl; lia.
    Qed.

    Lemma src_log E j (e: expr) :
      j ⤇ e ⊢ weak_src_update E (j ⤇ e ∗
              ∃ tp σ i, ⌜ tp !! j = Some e ⌝ ∗ fmlist_idx rheapG_fmlist_name i (to_cfg (tp, σ))).
    Proof.
      iIntros "Hj".
      rewrite /weak_src_update /tpool_mapsto /source_interp //=.
      iIntros ([[tp [h m]] n]) "[[H● Hl] Hnat]".
      iDestruct (own_valid_2 with "H● Hj") as %[[H1%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
      iDestruct "Hl" as (l Htrace) "Hfmlist".
      iMod (fmlist_get_lb with "Hfmlist") as "(Hfmlist&Hlb)".
      iDestruct (fmlist_lb_to_idx _ _ (length l) with "Hlb") as "Hidx".
      { rewrite lookup_app_r; last lia. replace (length l - length l)%nat with O by lia. rewrite //. }
      iModIntro. iExists (tp, (h, m), n). iFrame.
      iSplit; first eauto. iSplit.
      { iExists _. iFrame. eauto. }
      iExists tp, (h, m), (length l).
      iSplit; eauto.
      iPureIntro. eapply (tpool_lookup_Some (SI:=SI)); auto.
    Qed.

    Lemma src_get_trace' j (e: expr) i cfg σ :
      j ⤇ e ∗ fmlist_idx rheapG_fmlist_name i cfg ∗ source_interp σ -∗
              j ⤇ e ∗
              source_interp σ ∗
              ∃ tp σ, ⌜ tp !! j = Some e ∧ rtc erased_step cfg (to_cfg (tp, σ)) ⌝.
    Proof.
      iIntros "(Hj&Hidx&Hinterp)".
      rewrite /tpool_mapsto /source_interp //=.
      destruct σ as [[tp [h m]] n].
      iDestruct "Hinterp" as "[[H● Hl] Hnat]".
      iDestruct "Hl" as (l Htrace) "Hfmlist".
      iDestruct (fmlist_idx_agree_2 with "[$] [$]") as %Hlookup.
      iDestruct (own_valid_2 with "H● Hj") as %[[H1%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
      iFrame.
      iSplit; first eauto.
      iExists tp, (h, m).
      iPureIntro. split.
      * eapply (tpool_lookup_Some (SI:=SI)); auto.
      * eapply rtc_list_lookup_last_rtc; eauto.
    Qed.

    Lemma src_get_trace E j (e: expr) i cfg :
      j ⤇ e ∗ fmlist_idx rheapG_fmlist_name i cfg ⊢ weak_src_update E (j ⤇ e ∗
              ∃ tp σ, ⌜ tp !! j = Some e ∧ rtc erased_step cfg (to_cfg (tp, σ)) ⌝).
    Proof.
      iIntros "(Hj&Hidx)".
      rewrite /weak_src_update /tpool_mapsto /source_interp //=.
      iIntros ([[tp [h m]] n]) "[[H● Hl] Hnat]".
      iDestruct "Hl" as (l Htrace) "Hfmlist".
      iDestruct (fmlist_idx_agree_2 with "[$] [$]") as %Hlookup.
      iDestruct (own_valid_2 with "H● Hj") as %[[H1%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
      iModIntro. iExists (tp, (h, m), n). iFrame.
      iSplit; first eauto. iSplit.
      { iExists _. iFrame. eauto. }
      iExists tp, (h, m).
      iPureIntro. split.
      * eapply (tpool_lookup_Some (SI:=SI)); auto.
      * eapply rtc_list_lookup_last_rtc; eauto.
    Qed.

    (* operational rules *)
    Lemma step_pure E j (e1 e2: expr):
      pure_step e1 e2 → j ⤇ e1 ⊢ src_update E (j ⤇ e2).
    Proof.
      iIntros (Hp) "Hj"; rewrite /src_update /tpool_mapsto /source_interp //=.
      iIntros ([[tp [h m]] n]) "[[H● Hl] Hnat]".
      iDestruct (own_valid_2 with "H● Hj") as %[[H1%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
      iMod (own_update_2 with "H● Hj") as "[H● Hj]".
      { eapply auth_update, prod_local_update_1, singleton_local_update; eauto.
        by eapply (exclusive_local_update) with (x' := Excl e2). }
      iDestruct "Hl" as (l Htrace) "Hfmlist".
      iMod (fmlist_update_snoc (to_cfg (<[j:= e2]> tp, (h, m))) with "[$]") as "(Hfmlist&_)".
      iFrame "Hj". iModIntro. iExists (((<[j:= e2]> tp), (h, m)), n).
      rewrite to_tpool_insert'; eauto; iFrame.
      iSplit.
      - iPureIntro.
        replace (<[j:=e2]> tp) with (<[j:=e2]> tp ++ []) by rewrite right_id_L //=.
        eapply tc_once, lex_left, step_insert; first by eapply tpool_lookup_Some.
        apply pure_step_prim_step, Hp.
      - iExists _. iFrame. iPureIntro. rewrite -app_assoc. apply rtc_list_r; auto.
        replace (<[j:=e2]> tp) with (<[j:=e2]> tp ++ []) by rewrite right_id_L //=.
        eapply step_insert; first by eapply tpool_lookup_Some.
        apply pure_step_prim_step, Hp.
    Qed.

    Lemma steps_pure n E j (e1 e2: expr):
      nsteps pure_step (S n) e1 e2 → j ⤇ e1 ⊢ src_update E (j ⤇ e2).
    Proof.
      remember (S n) as m. intros H; revert n Heqm; induction H as [|? e1 e2 e3 Hstep Hsteps]; intros m.
      - discriminate 1.
      - injection 1 as ->. destruct m.
        + inversion Hsteps; subst. by apply step_pure.
        + iIntros "P". iApply src_update_bind; iSplitL.
          * iApply step_pure; eauto.
          * by iApply IHHsteps.
    Qed.

    Lemma steps_pure_exec E j e1 e2 φ n:
      PureExec φ (S n) e1 e2 → φ → j ⤇ e1 ⊢ src_update E (j ⤇ e2).
    Proof.
      intros Hp Hφ. specialize (pure_exec Hφ); eapply steps_pure.
    Qed.

    Lemma step_load E j K (l: loc) q v:
      j ⤇ fill K (Load #l) ∗ l ↦s{q} v ⊢ src_update E (j ⤇ fill K (of_val v) ∗ l ↦s{q} v).
    Proof.
      iIntros "[Hj Hl]"; rewrite /src_update /tpool_mapsto /source_interp //=.
      iIntros ([[tp [h m]] n]) "[[H● Hfmlist] Hnat]".
      iDestruct (own_valid_2 with "H● Hj") as %[[H1%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
      iDestruct (own_valid_2 with "H● Hl") as %[[_ ?%gen_heap_singleton_included]%prod_included ?]%auth_both_valid.
      iMod (own_update_2 with "H● Hj") as "[H● Hj]".
      { by eapply auth_update, prod_local_update_1, singleton_local_update,
          (exclusive_local_update _ (Excl (fill K (of_val v)))). }
      iDestruct "Hfmlist" as (tr Htrace) "Hfmlist".
      iMod (fmlist_update_snoc (to_cfg (<[j:= fill K (of_val v)]> tp, (h, m))) with "[$]") as "(Hfmlist&_)".
      iFrame "Hj Hl". iModIntro. iExists (((<[j:=fill K (of_val v)]> tp), (h, m)), n).
      rewrite to_tpool_insert'; last eauto. iFrame. iSplit.
      - iPureIntro.
        replace (<[j:=fill K v]> tp) with (<[j:=fill K v]> tp ++ []) by rewrite right_id_L //=.
        eapply tc_once, lex_left, step_insert; first by eapply tpool_lookup_Some.
        apply fill_prim_step, head_prim_step.
        econstructor; eauto.
      - iExists _. iFrame. iPureIntro. rewrite -app_assoc. apply rtc_list_r; auto.
        replace (<[j:=fill K v]> tp) with (<[j:=fill K v]> tp ++ []) by rewrite right_id_L //=.
        eapply step_insert; first by eapply tpool_lookup_Some.
        apply fill_prim_step, head_prim_step.
        econstructor; eauto.
    Qed.

    Lemma step_store E j K (l: loc) (v v': val):
      j ⤇ fill K (Store #l v) ∗ l ↦s v' ⊢ src_update E (j ⤇ fill K #() ∗ l ↦s v).
    Proof.
      iIntros "[Hj Hl]"; rewrite /src_update /tpool_mapsto /heapS_mapsto /source_interp //=.
      iIntros ([[tp [h m]] n]) "[[H● Hfmlist] Hnat]".
      iDestruct (own_valid_2 with "H● Hj") as %[[H1%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
      iDestruct (own_valid_2 with "H● Hl") as %[[_ Hl%gen_heap_singleton_included]%prod_included ?]%auth_both_valid.
      iMod (own_update_2 with "H● Hj") as "[H● Hj]".
      { by eapply auth_update, prod_local_update_1, singleton_local_update,
          (exclusive_local_update _ (Excl (fill K (of_val #())))). }
      iMod (own_update_2 with "H● Hl") as "[H● Hl]".
      { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree v)); last done.
      by rewrite /to_gen_heap lookup_fmap Hl. }
      iDestruct "Hfmlist" as (tr Htrace) "Hfmlist".
      iMod (fmlist_update_snoc (to_cfg (<[j:= fill K (of_val #())]> tp, (<[l:=v]>h, m))) with "[$]") as
          "(Hfmlist&_)".
      iFrame "Hj Hl". iExists (((<[j:=fill K (of_val #())]> tp), (<[l:=v]> h, m)), n).
      rewrite -to_gen_heap_insert -to_tpool_insert' //=; eauto.
      iModIntro. iFrame. iSplit.
      - iPureIntro.
        replace (<[j:=fill K #()]> tp) with (<[j:=fill K #()]> tp ++ []) by rewrite right_id_L //=.
        eapply tc_once, lex_left, step_insert; first by eapply tpool_lookup_Some.
        apply fill_prim_step, head_prim_step.
        econstructor; eauto.
      - iExists _. iFrame. iPureIntro. rewrite -app_assoc. apply rtc_list_r; auto.
        replace (<[j:=fill K #()]> tp) with (<[j:=fill K #()]> tp ++ []) by rewrite right_id_L //=.
        eapply step_insert; first by eapply tpool_lookup_Some.
        apply fill_prim_step, head_prim_step.
        econstructor; eauto.
    Qed.

    Lemma step_alloc E j K (v : val):
      j ⤇ fill K (Alloc v)  ⊢ src_update E (∃ l: loc, j ⤇ fill K #l ∗ l ↦s v).
    Proof.
      iIntros "Hj"; rewrite /src_update /tpool_mapsto /heapS_mapsto /source_interp //=.
      iIntros ([[tp [h m]] n]) "[[H● Hfmlist] Hnat]".
      destruct (exist_fresh (dom (gset loc) h)) as [l Hl%not_elem_of_dom].
      iDestruct (own_valid_2 with "H● Hj") as %[[H1%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
      iMod (own_update_2 with "H● Hj") as "[H● Hj]".
      { by eapply auth_update, prod_local_update_1, singleton_local_update,
          (exclusive_local_update _ (Excl (fill K (of_val #l)))). }
      iMod (own_update with "H●") as "[H● Hl]".
      { eapply auth_update_alloc, prod_local_update_2, (alloc_singleton_local_update _ l (1%Qp,to_agree v)); last done.
        by apply lookup_to_gen_heap_None. }
      iDestruct "Hfmlist" as (tr Htrace) "Hfmlist".
      iMod (fmlist_update_snoc (to_cfg (<[j:= fill K (of_val #l)]> tp, (<[l:=v]>h, m))) with "[$]") as
          "(Hfmlist&_)".
      iModIntro. iExists (((<[j:=fill K (of_val #l)]> tp), (<[l:=v]> h, m)), n).
      rewrite -to_gen_heap_insert to_tpool_insert' //=; eauto. iFrame.
      iSplitR; [| iSplitL "Hfmlist"]; last by iExists l; iFrame.
      - iPureIntro.
        replace (<[j:=fill K #l]> tp) with (<[j:=fill K #l]> tp ++ []) by rewrite right_id_L //=.
        eapply tc_once, lex_left, step_insert; first by eapply tpool_lookup_Some.
        apply fill_prim_step, head_prim_step.
        pose proof (AllocNS 1 v {| heap := h; used_proph_id := {| mapset.mapset_car := m |} |} l) as H.
        rewrite state_init_heap_singleton in H; simpl in H. apply H; first lia.
        intros i ??; assert (i = 0) as -> by lia; simpl; rewrite loc_add_0 //=.
      - iExists _. iFrame. iPureIntro. rewrite -app_assoc. apply rtc_list_r; auto.
        replace (<[j:=fill K #l]> tp) with (<[j:=fill K #l]> tp ++ []) by rewrite right_id_L //=.
        eapply step_insert; first by eapply tpool_lookup_Some.
        apply fill_prim_step, head_prim_step.
        pose proof (AllocNS 1 v {| heap := h; used_proph_id := {| mapset.mapset_car := m |} |} l) as H.
        rewrite state_init_heap_singleton in H; simpl in H. apply H; first lia.
        intros i ??; assert (i = 0) as -> by lia; simpl; rewrite loc_add_0 //=.
    Qed.

End heap_lang_source_steps.


(* some proof automation for source languages *)
From iris.proofmode Require Import tactics coq_tactics reduction.
Ltac strip_ectx e cb :=
  match e with
  | fill ?K ?e' => strip_ectx e' ltac:(fun K' e'' => match K' with nil => cb K e'' | _ => cb (K ++ K') e'' end)
  | _ => cb (@nil ectx_item) e
  end.

Ltac src_bind_core e efoc cb :=
    strip_ectx e ltac:(fun K e' => reshape_expr e' ltac:(fun K' e'' => unify e'' efoc; cb (K' ++ K) e'')).

Ltac src_bind_core' e cb :=
    strip_ectx e ltac:(fun K e' => reshape_expr e' ltac:(fun K' e'' => cb (K' ++ K) e'')).

Lemma src_change e1 e2 {SI: indexT} `{Σ: gFunctors SI} `{!rheapG Σ} `{!auth_sourceG Σ (natA SI)} j Δ (G: iProp Σ):
  e1 = e2 →
  envs_entails Δ (j ⤇ e2 -∗ G) →
  envs_entails Δ (j ⤇ e1 -∗ G).
Proof. by intros ->. Qed.

Tactic Notation "src_bind" open_constr(efoc) :=
  match goal with
  | [|- envs_entails ?Δ (?j ⤇ ?e -∗ ?G)] =>
    src_bind_core e efoc ltac:(fun K e' => apply (src_change e (fill K e')); first reflexivity)
  end.

Tactic Notation "src_bind" open_constr(efoc) "in" constr(H) :=
  iRevert H;
  src_bind efoc;
  last iIntros H.

Lemma tac_src_pures_rwp e1 e2 {SI: indexT} `{Σ: gFunctors SI} `{!rheapG Σ} `{!auth_sourceG Σ (natA SI)}
      φ e Δ j E s Φ:
  PureExec φ 1 e1 e2 →
  to_val e = None →
  φ →
  envs_entails Δ (j ⤇ e2 -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩) →
  envs_entails Δ (j ⤇ e1 -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩).
Proof.
  rewrite envs_entails_eq=> ? ? ? ->.
  iIntros "H Hj".  iApply (rwp_weaken with "H"); auto.
  by iApply @steps_pure_exec.
Qed.

Lemma tac_src_pures e1 e2 {SI: indexT} `{Σ: gFunctors SI} `{!rheapG Σ} `{!auth_sourceG Σ (natA SI)}
      φ Δ j E P:
  PureExec φ 1 e1 e2 →
  φ →
  envs_entails Δ (j ⤇ e2 -∗ weak_src_update E P) →
  envs_entails Δ (j ⤇ e1 -∗ src_update E P).
Proof.
  rewrite envs_entails_eq=> ? ? ->.
  iIntros "H Hj".
  iApply (weak_src_update_bind_r with "[$H Hj]").
  by iApply @steps_pure_exec.
Qed.

Lemma tac_src_load_rwp {SI: indexT} `{Σ: gFunctors SI} `{!rheapG Σ} `{!auth_sourceG Σ (natA SI)}
      e s Φ Δ E i j K l q v:
  to_val e = None →
  envs_lookup i Δ = Some (false, l ↦s{q} v)%I →
  envs_entails Δ (j ⤇ fill K (Val v) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩) →
  envs_entails Δ (j ⤇ fill K (Load (LitV l)) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩).
Proof.
  rewrite envs_entails_eq=> ?? Henvs.
  iIntros "H Hj".
  rewrite envs_lookup_split //.
  iDestruct "H" as "(Hl&Hw)".
  iApply (rwp_weaken with "[Hw] [Hl Hj]"); first done; last first.
  { iApply step_load. iFrame. }
  iIntros "(Hj&Hl)".
  iSpecialize ("Hw" with "[$]"). iApply (Henvs with "[$] [$]").
Qed.

Lemma tac_src_load {SI: indexT} `{Σ: gFunctors SI} `{!rheapG Σ} `{!auth_sourceG Σ (natA SI)}
      Δ E P i j K l q v:
  envs_lookup i Δ = Some (false, l ↦s{q} v)%I →
  envs_entails Δ (j ⤇ fill K (Val v) -∗ weak_src_update E P) →
  envs_entails Δ (j ⤇ fill K (Load (LitV l)) -∗ src_update E P).
Proof.
  rewrite envs_entails_eq=> ? Henvs.
  iIntros "H Hj".
  rewrite envs_lookup_split //.
  iDestruct "H" as "(Hl&Hw)".
  iApply (weak_src_update_bind_r with "[-]").
  iSplitL "Hl Hj".
  { iApply step_load. iFrame. }
  iIntros "(Hj&Hl)".
  iApply (Henvs with "[Hw Hl] Hj").
  by iApply "Hw".
Qed.

Lemma tac_src_store {SI: indexT} `{Σ: gFunctors SI} `{!rheapG Σ} `{!auth_sourceG Σ (natA SI)}
      Δ Δ' E P i j K l v v':
  envs_lookup i Δ = Some (false, l ↦s v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦s v')) Δ = Some Δ' →
  envs_entails Δ' (j ⤇ fill K (Val $ LitV LitUnit) -∗ weak_src_update E P) →
  envs_entails Δ (j ⤇ fill K (Store (LitV l) (Val v')) -∗ src_update E P).
Proof.
  rewrite envs_entails_eq=> ?? Henvs.
  iIntros "H Hj".
  rewrite envs_simple_replace_sound //.
  iDestruct "H" as "(Hl&Hw)".
  iApply (weak_src_update_bind_r with "[-]").
  iSplitL "Hl Hj".
  { iApply step_store. iFrame. }
  iIntros "(Hj&Hl)".
  iApply (Henvs with "[Hw Hl] Hj").
  iApply "Hw". simpl. rewrite right_id. eauto.
Qed.

Ltac weak_to_src_update :=
  lazymatch goal with
  | [|- envs_entails ?Δ (weak_src_update _ _)] =>
     iApply src_update_weak_src_update
  | _ => idtac
  end.

Tactic Notation "src_pure" open_constr(efoc) :=
  match goal with
  | [|- envs_entails ?Δ (?j ⤇ ?e -∗ src_update _ _)] =>
      src_bind_core e efoc ltac:(fun K e' => eapply (tac_src_pures (fill K e'));
                                             [iSolveTC|try solve_vals_compare_safe| simpl ectx_language.fill])
  | [|- envs_entails ?Δ (?j ⤇ ?e -∗ rwp _ _ _ _)] =>
        src_bind_core e efoc ltac:(fun K e' => eapply (tac_src_pures_rwp (fill K e'));
                                               [iSolveTC|done|try solve_vals_compare_safe|simpl])
  end.

Tactic Notation "src_pure" open_constr(efoc) "in" constr(H) :=
  weak_to_src_update;
  iRevert H;
  src_pure efoc;
  last iIntros H.

Tactic Notation "src_load" open_constr (efoc) :=
  lazymatch goal with
  | [|- envs_entails ?Δ (?j ⤇ ?e -∗ rwp _ _ _ _)] =>
        src_bind_core e efoc ltac:(fun K e' => eapply (tac_src_load_rwp _ _ _ _ _ _ _ K);
                                               [done|iAssumptionCore| simpl fill])
  | [|- envs_entails ?Δ (?j ⤇ ?e -∗ weak_src_update _ _)] =>
     iApply src_update_weak_src_update;
     src_bind_core e efoc ltac:(fun K e' => eapply (tac_src_load _ _ _ _ _ K);
                                        [iAssumptionCore| simpl fill])
  | [|- envs_entails ?Δ (?j ⤇ ?e -∗ src_update _ _)] =>
     src_bind_core e efoc ltac:(fun K e' => eapply (tac_src_load _ _ _ _ _ K);
                                        [iAssumptionCore| simpl fill])
  end.

Tactic Notation "src_load" "in" constr(H) :=
  weak_to_src_update;
  iRevert H;
  src_bind (! _)%E;
  src_load _;
  last iIntros H.

Tactic Notation "pattern" open_constr(e) "in" tactic(f) := f e.

Ltac single_pure_exec :=
  match goal with
  | [|- PureExec ?φ 1 ?e1 ?e2] => apply _
  | [|- PureExec ?φ 1 (fill ?K1 ?e1) (fill ?K2 ?e2)] =>
    unify K1 K2; eapply pure_exec_fill; single_pure_exec
  | [|- PureExec ?φ 1 ?e1 ?e2 ] =>
    reshape_expr e1 ltac:(fun K e1 =>
    pattern (_: expr) in ltac:(fun e2' =>
      unify e2 (fill K e2');
      change (PureExec φ 1 (fill K e1) (fill K e2'));
      apply pure_exec_fill, _
    ))
  end.


Lemma pure_exec_cons φ ψ n (e1 e2 e3: expr):
  PureExec φ 1 e1 e2 → PureExec ψ n e2 e3 → PureExec (φ ∧ ψ) (S n) e1 e3.
Proof.
  intros H1 H2 [Hφ Hψ]; econstructor; eauto.
  specialize (H1 Hφ).
  by inversion H1 as [|x y z a Hpure Hstep]; subst; inversion Hstep; subst.
Qed.


Lemma pure_exec_zero (e: expr): PureExec True 0 e e.
Proof.
  intros ?. econstructor.
Qed.

Ltac pure_exec_cons :=
  match goal with
  | [|- PureExec ?φ 0 ?e1 ?e2] =>
    apply pure_exec_zero
  | [|- PureExec ?φ ?n ?e1 ?e2] =>
    unify e1 e2; apply pure_exec_zero
  | [|- PureExec ?φ ?n ?e1 ?e2] =>
    (eapply pure_exec_cons; [single_pure_exec|]); simpl
  end.

Ltac pure_exec := repeat pure_exec_cons.




Arguments satisfiable_at {_ _ _} _ _%I.

Lemma satisfiable_update_alloc {SI} {Σ: gFunctors SI} `{LargeIndex SI} `{!invG Σ} {E} {P} Q:
   satisfiable_at E P → (⊢ |==> ∃ γ: gname, Q γ) → ∃ γ, satisfiable_at E (P ∗ Q γ).
Proof.
  intros Hsat Hent. apply satisfiable_at_exists; first done.
  eapply satisfiable_at_fupd with (E1 := E).
  eapply satisfiable_at_mono; first apply Hsat.
  iIntros "$". iMod (Hent) as "$"; eauto.
Qed.

Lemma satisfiable_update_alloc_2 {SI} {Σ: gFunctors SI} `{LargeIndex SI} `{!invG Σ} {E} {P} Φ:
   satisfiable_at E P → (⊢ |==> ∃ γ1 γ2: gname, Φ γ1 γ2) → ∃ γ1 γ2, satisfiable_at E (P ∗ Φ γ1 γ2).
Proof.
  intros Hsat Hent.
  eapply satisfiable_at_mono with (Q := (|==> ∃ γ1 γ2, P ∗ Φ γ1 γ2)%I) in Hsat.
  - eapply satisfiable_at_bupd in Hsat as Hsat.
    apply satisfiable_at_exists in Hsat as [γ1 Hsat]; auto.
    apply satisfiable_at_exists in Hsat as [γ2 Hsat]; eauto.
  - iIntros "$". by iMod Hent.
Qed.

Lemma satisfiable_at_alloc {SI A} {Σ: gFunctors SI} `{LargeIndex SI} `{!inG Σ A} `{!invG Σ} {E} {P} (a: A):
   satisfiable_at E P → ✓ a → ∃ γ, satisfiable_at E (P ∗ own γ a).
Proof.
  intros Hsat Hent. apply satisfiable_update_alloc; first done.
  by eapply own_alloc.
Qed.

Lemma satisfiable_at_add {SI} (Σ: gFunctors SI) `{!invG Σ} E P Q: satisfiable_at E P → sbi_emp_valid Q → satisfiable_at E (P ∗ Q).
Proof.
  intros Hsat Hval. eapply satisfiable_at_mono; first eauto.
  iIntros "$". iApply Hval.
Qed.

Lemma satisfiable_at_add' {SI} (Σ: gFunctors SI) `{!invG Σ} E Q: satisfiable_at E True → sbi_emp_valid Q → satisfiable_at E Q.
Proof.
  intros Hsat Hval. eapply satisfiable_at_mono; first eauto.
  iIntros "_". iApply Hval.
Qed.

Lemma satisfiable_at_gen_heap {SI} {Σ: gFunctors SI} `{LargeIndex SI} `{!heapPreG Σ} κ σ:
  ∃ Hheap: heapG Σ, satisfiable_at ⊤ ((gen_heap_ctx (heap σ)) ∗ proph_map_ctx κ (used_proph_id σ)).
Proof.
  (* allocate invariants *)
  edestruct satisfiable_at_intro as [Hinv Hsat].
  eapply satisfiable_update_alloc_2 in Hsat as (γ_gen_heap & γ_gen_heap_meta & Hsat); last eapply (alloc_gen_heap _ _ σ.(heap)).
  pose (Hgen := GenHeapG SI loc val _ _ _ _ _ _ γ_gen_heap γ_gen_heap_meta).

  (* TODO: prophecies are not really included in the refinement version *)
  (* allocate prophecies *)
  eapply satisfiable_update_alloc in Hsat as (γ_proph_map & Hsat); last apply (proph_map_init' κ σ.(used_proph_id)).
  pose (Hproph := ProphMapG SI proph_id (val * val) Σ _ _ _ γ_proph_map).
  exists (HeapG _ _ _ _ _).
  eapply satisfiable_at_mono; first apply Hsat.
  by iIntros "[[_ $] $]".
Qed.


Lemma satisfiable_at_ref_heapG {SI} {Σ: gFunctors SI} `{LargeIndex SI} `{!heapPreG Σ} n σ:
  ∃ Hheap: heapG Σ, satisfiable_at ⊤ (ref_state_interp n σ).
Proof.
  edestruct (satisfiable_at_gen_heap nil) as [Hheap Hsat].
  exists Hheap. eapply satisfiable_at_mono; first eauto.
  iIntros "($ & _)".
Qed.

Lemma satisfiable_at_rheapG {SI} {Σ: gFunctors SI} `{LargeIndex SI} `{!rheapPreG Σ} n σ h m tp:
  ∃ Hheap: rheapG Σ, satisfiable_at ⊤ (ref_state_interp σ n ∗ source_interp (tp, (h, m)) ∗ own rheapG_ghost_name (◯ (to_tpool tp, to_gen_heap SI h))).
Proof.
  edestruct (satisfiable_at_ref_heapG) as [Hheap Hsat].
  eapply (satisfiable_at_alloc (● (to_tpool tp, to_gen_heap SI h) ⋅ ◯ (to_tpool tp, to_gen_heap SI h))) in Hsat as [γ Hsat]; last first.
  { apply auth_both_valid; repeat split; eauto using to_tpool_valid, to_gen_heap_valid. }
  eapply (satisfiable_at_alloc ((●{1} (MList [to_cfg (tp, (h, m))])))) in Hsat as [γ' Hsat]; last first.
  { apply auth_auth_valid.
    cbv; auto. }
  exists (RHeapG _ _ _ _ γ _ γ').
  eapply satisfiable_at_mono; first apply Hsat.
  iIntros "(($&($&$))&H3)".
  iExists nil. simpl. rewrite /fmlist. iFrame.
  iPureIntro. apply rtc_list_once.
Qed.

Lemma rtc_to_cfg {SI} {Σ: gFunctors SI} `{!rheapG Σ} x y: rtc source_rel x y → rtc erased_step (to_cfg x) (to_cfg y).
Proof.
  induction 1; first done.
  econstructor; by eauto.
Qed.

Lemma sn_to_cfg {SI} {Σ: gFunctors SI} `{!rheapG Σ} x: sn erased_step (to_cfg x) → sn source_rel x.
Proof.
  remember (to_cfg x) as σ; intros Hsn; revert x Heqσ.
  induction Hsn as [x _ IH]; intros [ts [h m]] ->.
  constructor. intros [ts' [h' m']] Hstep.
  eapply IH; eauto. apply Hstep.
Qed.

From iris.program_logic Require Import ref_adequacy.
(* Adequacy Theorem *)
Section adequacy.
  Context {SI: indexT} `{C: Classical}  `{LI: LargeIndex SI} {Σ: gFunctors SI}.
  Context `{Hpre: !rheapPreG Σ} `{Hna: !na_invG Σ} `{Hauth: !inG Σ (authR (natA SI))}.

  Theorem heap_lang_ref_adequacy (φ: val → val → Prop) (s t: expr) σ σ_src:
    (∀ `{!rheapG Σ} `{!seqG Σ} `{!auth_sourceG Σ (natA SI)}, src s ⊢ SEQ t ⟨⟨ v, ∃ v': val, src v' ∗ ⌜φ v v'⌝ ⟩⟩) →
    (∀ σ' v, rtc erased_step ([t], σ) ([Val v], σ') → ∃ v': val, ∃ σ_src' ts, rtc erased_step ([s], σ_src) (Val v' :: ts, σ_src') ∧ φ v v') ∧
    (sn erased_step ([s], σ_src) → sn erased_step ([t], σ)).
  Proof using SI C LI Σ Hpre Hna Hauth.
    intros Hobj.
    (* allocate the heap *)
    edestruct (satisfiable_at_rheapG 0 σ (heap σ_src) (mapset.mapset_car (used_proph_id σ_src)) [s]) as [Hheap Hsat].
    (* allocate sequential invariants *)
    eapply satisfiable_update_alloc in Hsat as [seqG_name Hsat]; last apply na_alloc.
    pose (seq := {| seqG_na_invG := _; seqG_name := seqG_name |}).
    (* allocte stuttering credits *)
    eapply (satisfiable_at_alloc (● 0%nat ⋅ ◯ 0%nat)) in Hsat as [authG_name Hsat]; last first.
    { apply auth_both_valid; by split. }
    pose (stutter := {| sourceG_inG := _; sourceG_name := authG_name |}).
    specialize (Hobj Hheap seq stutter).
    eapply satisfiable_at_mono in Hsat as Hsat; last first; [|split].
    - iIntros "[[(SI & Hsrc & Hsrc') Hna] [Hc Hc']]".
      iPoseProof (Hobj with "[Hsrc'] Hna") as "Hwp".
      + assert ((◯ (to_tpool [s], to_gen_heap SI (heap σ_src))) ≡ (◯ (to_tpool [s], ∅) ⋅ ◯ (∅, to_gen_heap SI (heap σ_src)))) as ->.
        { by rewrite -auth_frag_op pair_op left_id right_id. }
        iDestruct "Hsrc'" as "[$ _]".
      + iClear "Hc'". iCombine "Hsrc Hc" as "Hsrc".
        iCombine "Hsrc SI Hwp" as "G". iExact "G".
    - intros σ' v Hsteps. eapply (rwp_result _ _ ([s], (heap σ_src, mapset.mapset_car (used_proph_id σ_src)), 0%nat)) in Hsteps; last apply Hsat.
      destruct Hsteps as ([[ts [h p]] c] & m & Hsteps & Hsat').
      eapply satisfiable_at_pure.
      eapply satisfiable_at_mono; first apply Hsat'.
      iIntros "(Hsrc & SI & _ & Hv)". iDestruct "Hv" as (v') "[Hsrc' %]".
      iExists v', {| heap := h; used_proph_id := {| mapset.mapset_car := p |} |}.
      iDestruct "Hsrc" as "[[Hsrc _] _]".
      iDestruct (own_valid_2 with "Hsrc Hsrc'") as %[[H1%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
      destruct ts as [|e ts]; first naive_solver.
      iExists ts.
      iPureIntro. split; auto.
      rewrite tpool_lookup in H1.
      injection H1 as ->.
      eapply lex_rtc in Hsteps.
      eapply rtc_to_cfg in Hsteps; simpl in Hsteps.
      destruct σ_src as [? [?]]; apply Hsteps.
    - intros Hsn. destruct σ_src as [h_src [p_src]]; simpl in *. eapply (rwp_sn_preservation _ ([s], (h_src, p_src), 0%nat) _ _ 0).
      { eapply sn_lex; first apply (sn_to_cfg ([s], (h_src, p_src))); eauto.
        intros y; apply lt_wf. }
      eapply satisfiable_at_mono; first apply Hsat.
      iIntros "($ & $ & $)".
    Qed.

End adequacy.
