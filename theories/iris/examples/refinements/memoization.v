
From iris.program_logic.refinement Require Export ref_weakestpre ref_source seq_weakestpre.
From iris.base_logic.lib Require Export invariants na_invariants.
From iris.examples.refinements Require Export refinement.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation metatheory.
From iris.algebra Require Import auth gmap excl frac agree.
Set Default Proof Using "Type".

Definition refN := nroot .@ "ref".

Lemma fill_item_injective a (e e': expr): fill_item a e = fill_item a e' → e = e'.
Proof.
  induction a; simpl; injection 1; eauto.
Qed.

Lemma fill_injective K (e e': expr): fill K e = fill K e' → e = e'.
Proof.
  revert e e'; induction K; intros e e'; simpl; eauto.
  intros ? % IHK. by eapply fill_item_injective.
Qed.

Definition eq_heaplang : val := (λ: "n1" "n2", "n1" = "n2").

Notation exec := (tc (@pure_step heap_lang)).

Section map_simple.

  Context {SI: indexT} {A: Type} `{Σ: gFunctors SI} `{!heapG Σ} `{!source Σ A}.
  Context (Comparable: val → iProp Σ).
  Context `{Comparable_timeless: ∀ v, Timeless (Comparable v)}.

  Fixpoint contents (kvs: list (val * val)) (l: loc) : iProp Σ :=
    (match kvs with
    | nil => l ↦ NONEV
    | (k, n) :: kvs' => ∃(l': loc), Comparable k ∗ l ↦ SOMEV ((k, n), #l') ∗ contents kvs' l'
    end)%I.

  Global Instance contents_timeless kvs l: Timeless (contents kvs l).
  Proof using Comparable_timeless.
    revert l; induction kvs as [|[] kvs IH]; intros l; simpl; apply _.
  Qed.
  Definition map : val :=
    λ: <>, ref (ref NONE).

  Definition get : val :=
    λ: "m" "eq" "a",
    (rec: "get" "h" "a" :=
      match: !"h" with
        NONE => NONE
      | SOME "p" =>
        let: "kv" := Fst "p" in
        let: "next" := Snd "p" in
        if: "eq" (Fst "kv") "a" then SOME (Snd "kv") else "get" "next" "a"
      end) (!"m") "a".

  Definition set : val :=
    λ: "h" "a" "v",
      "h" <- ref (SOME (("a", "v"), !"h")).

  Fixpoint to_map (kvs: list (val * val)) : gmap val val :=
    match kvs with
    | nil => ∅
    | (k, n) :: kvs => <[k := n]> (to_map kvs)
    end.

  Definition Map v (h: gmap val val) :=
    (∃ (l l': loc) kvs, ⌜v = #l⌝ ∗ ⌜h = to_map kvs⌝ ∗ l ↦ #l' ∗ contents kvs l')%I.

  Global Instance Map_timeless v h: Timeless (Map v h).
  Proof using Comparable_timeless. apply _. Qed.

  Lemma map_spec: ⊢ ⟨⟨⟨ True ⟩⟩⟩ map #() ⟨⟨⟨ v, RET v; Map v ∅ ⟩⟩⟩.
  Proof.
    iModIntro; iIntros (Φ) "_ Hpost". rewrite /map. wp_pures.
    wp_alloc r as "Hr". wp_alloc h as "Hh".
    iApply "Hpost".
    iExists h, r, nil; simpl; iFrame; iSplit; done.
  Qed.

  Definition embed (o: option val) :=
    match o with
    | None => NONEV
    | Some k => SOMEV k
    end.

  Definition eqfun (eq : val) (Q: val → val → iProp Σ) :=
    (∀ n1 n2,
    ⟨⟨⟨ Comparable n1 ∗ Comparable n2 ⟩⟩⟩ eq n1 n2
    ⟨⟨⟨ b, RET #(b: bool); Comparable n1 ∗ Comparable n2 ∗
        match b with
        | true => Q n1 n2
        | _ => Q n1 n2 -∗ False
        end ⟩⟩⟩)%I.

  Lemma get_spec h eq Q m (n: val) :
    ⊢ ⟨⟨⟨ Map m h ∗ eqfun eq Q ∗ Comparable n ⟩⟩⟩ get m eq n
      ⟨⟨⟨ o, RET (embed o);
          match o with
          | Some v => ∃ n', ⌜ h !! n' = Some v ⌝ ∗ Q n' n ∗ Map m h
          | None => (∀ n', ⌜ n' ∈ dom (gset val) h ⌝ -∗ Q n' n -∗ False) ∗ Map m h
          end ⟩⟩⟩.
  Proof using Comparable_timeless.
    iModIntro; iIntros (Φ) "(HM&#Heq&Hcompn) Hpost". rewrite /get {1}/Map.
    wp_pures. iDestruct "HM" as (l r kvs -> ->) "[Hr Hc]".
    wp_load.
    (* we prepare the goal for the induction *)
    iAssert (∀ o, contents kvs r -∗
              match o with
              | Some v => ∃ n' : val, ⌜to_map kvs !! n' = Some v⌝ ∗ Q n' n
              | None => (∀ n', ⌜ n' ∈ dom (gset val) (to_map kvs) ⌝ -∗ Q n' n -∗ False)
              end -∗ Φ (embed o))%I with "[Hr Hpost]" as "Hpost".
    { iIntros (o) "H1 H2". iApply "Hpost". destruct o.
      - iDestruct "H2" as (n') "(?&?)".
        iExists n'. iFrame. iExists l, r, kvs; iFrame; done.
      - iFrame. iExists l, r, kvs; iFrame; done.
    }
    wp_pure _. iInduction kvs as [|[k n'] kvs] "IH" forall (r) "Hc"; simpl.
    - wp_pures. wp_load. wp_pures.
      iApply ("Hpost" $! None with "[$]").
      iIntros (? Hin) "_". iPureIntro. set_solver.
    - iDestruct "Hc" as (l') "[Hcompk [Hr Hc]]". wp_pures.
      wp_load. wp_pures.
      wp_bind (eq k n).
      wp_apply ("Heq" with "[$Hcompk $Hcompn]").
      iIntros (b) "(Hcompk&Hcompn&Hif)".
      destruct b.
      + wp_pures. subst.
        iApply ("Hpost" $! (Some n') with "[Hcompk Hr Hc]").
        { iExists _; iFrame. }
        iExists k. rewrite lookup_insert.
        eauto.
      + wp_pure _. iApply ("IH" $! l' with "[$] [Hpost Hr Hcompk Hif] Hc").
        iIntros (o) "Hc H". iApply ("Hpost" with "[Hr Hcompk Hc] [H Hif]").
        { iExists _. iFrame. }
        { destruct o.
          * iDestruct "H" as (k') "(Heq'&HQ)".
            iAssert (⌜k' ≠ k⌝)%I with "[-]" as %Hneq.
            { iIntros (->). by iApply "Hif". }
            iExists k'. rewrite lookup_insert_ne //. iFrame.
          * iIntros (? Hin) "HQ".
            set_unfold in Hin. destruct Hin as [->|Hin].
            + by iApply "Hif".
            + by iApply "H".
        }
  Qed.

  Lemma set_spec h m (n k: val) :
    ⊢ ⟨⟨⟨ Map m h ∗ Comparable k ⟩⟩⟩ set m k n ⟨⟨⟨ RET #(); Map m (<[k := n]> h) ⟩⟩⟩.
  Proof.
    iModIntro; iIntros (Φ) "(HM&Hcomp) Hpost". rewrite /set /Map.
    wp_pures. iDestruct "HM" as (l r kvs -> ->) "[Hr Hc]".
    wp_load. wp_alloc r' as "Hr'". wp_store.
    iApply "Hpost". iExists l, r', ((k, n) :: kvs); simpl; iFrame; repeat iSplit; auto.
    iExists r. iFrame.
  Qed.

End map_simple.


Section memoization_functions.
  Definition memoize: val :=
    λ: "eq" "f",
      let: "h" := map #() in
      λ: "a",
      match: get "h" "eq" "a" with
        NONE => let: "y" := "f" "a" in set "h" "a" "y";; "y"
      | SOME "y" => "y"
      end.


  Definition mem_rec: val :=
    λ: "eq" "F",
    let: "h" := map #() in
    rec: "mem_rec" "a" :=
      match: get "h" "eq" "a" with
        NONE =>
          let: "y" := "F" "mem_rec" "a" in
          set "h" "a" "y";; "y"
      | SOME "y" => "y"
      end.
End memoization_functions.





Section timeless_memoization.
  Context {SI: indexT} {A: Type} `{Σ: gFunctors SI} `{Heap: !rheapG Σ} `{Cred: !auth_sourceG Σ (natA SI)} `{Seq: !seqG Σ}.


  Implicit Types (c: nat).
  Implicit Types (f g m v: val).
  Implicit Types (e: expr).
  Implicit Types (h: gmap val val).


  Variable (R: expr → val → iProp Σ).
  Variable (Pre Post: val → val → iProp Σ).
  Variable (Comparable: val → iProp Σ).
  Variable (Eq: val → val → iProp Σ).
  Context `{TL: !∀ e v, Timeless (R e v)}.
  Context `{TLPost: !∀ v v', Timeless (Post v v')}.
  Context `{PPre: !∀ v v', Persistent (Pre v v')}.
  Context `{PPost: !∀ v v', Persistent (Post v v')}.
  Context `{PEq: !∀ v v', Persistent (Eq v v')}.
  Context `{Comparable_timeless: ∀ v, Timeless (Comparable v)}.
  Variable (Pre_Comparable : ∀ v v', Pre v v' -∗ Comparable v).
  Variable (Pre_Eq_Proper: ∀ v1 v1' v2, Eq v1 v1' -∗ Pre v1' v2 -∗ Pre v1 v2).

  (* we allow arbitrary stutter *)
  Definition eval e v := (∀ K, src (fill K e) -∗ src_update ⊤ (src (fill K v)))%I.
  Definition mem_inv (m f: val) : iProp Σ :=
    (∃ h, Map Comparable m h ∗
          [∗ map] k ↦ v ∈ h, □ (∀ k', Pre k k' -∗ ∃ v', □ R (f (of_val k')) v' ∗ Post v v'))%I.

  Definition implements (g: val) (f: val) : iProp Σ :=
    (□ ∀ x x' K,
          Pre x x' -∗
          src (fill K (f x')) -∗
          SEQ (g x) ⟨⟨v, ∃ v': val, Post v v' ∗ src (fill K v') ∗
                                    □ (∀ x', Pre x x' -∗ ∃ v', □ R (f x') v' ∗ Post v v') ⟩⟩)%I.


  Lemma memoization_core (eq: val) (f: val) e (n n' : val) m K :
    SEQ e ⟨⟨ h, implements h f ⟩⟩ ∗
    se_inv refN (mem_inv m f) ∗
    □ (∀ e v, R e v -∗ eval e v) ∗
    Pre n n' ∗
    eqfun Comparable eq Eq ∗
    src (fill K (f n')) ⊢
    SEQ (match: get m eq n with
      NONE => let: "y" := e n in set m n "y";; "y"
    | SOME "y" => "y"
    end) ⟨⟨v, ∃ v': val, Post v v' ∗ src (fill K v') ∗ □ (∀ n', Pre n n' -∗ ∃ v', □ R (f n') v' ∗ Post v v') ⟩⟩.
  Proof using Comparable Comparable_timeless Cred Eq Heap PEq PPost PPre Post Pre Pre_Comparable Pre_Eq_Proper R SI
        Seq TL TLPost Σ.
    iIntros "(Spec & #I & #IEval & #HPre & #Heqfun & Hsrc) Hna".
    (* we open the timeless invariant for the get *)
    iMod (na_inv_acc_open_timeless with "I Hna") as "(Hc & Hna & Hclose)"; auto.
    iDestruct "Hc" as (h) "(HM & #Hupd)".
    wp_bind (get m eq n). wp_apply (get_spec with "[$HM $Heqfun]").
    { by iApply Pre_Comparable. }
    iIntros (o) "HM".
    destruct o as [k|] eqn: Heq.
    - (* we have stored this result before *)
      iDestruct "HM" as (n0 Hlookup) "(#Heq&HM)".
      iDestruct (big_sepM_lookup with "Hupd") as "#Hk"; first done.
      iDestruct (Pre_Eq_Proper with "[$] [$]") as "#HPre'".
      iDestruct ("Hk" with "[$]") as (?) "(#HR&#HP)".
      iApply (rwp_weaken with "[-Hsrc] [Hsrc]"); first done; last by iApply "IEval".
      iIntros "Hsrc".
      iApply fupd_rwp. iMod ("Hclose" with "[HM $Hna]") as "Hna".
      { iNext. iExists h. by iFrame. }
      iModIntro. wp_pures.
      iFrame. iExists _. iFrame "# ∗".
      iIntros "!>" (n'') "HPre''".
      iApply "Hk". iApply (Pre_Eq_Proper with "[$] [$]").
    - (* we close the invariant again for the recursive call *)
      iDestruct "HM" as "(Hnin&HM)".
      iMod ("Hclose" with "[HM $Hna]") as "Hna".
      { iNext. iExists _. iFrame "# ∗". }
      wp_pures. wp_bind e.
      iApply (rwp_strong_mono with "[Spec Hna]");[eauto..| by iApply "Spec" |].
      iIntros (g) "[Hna Hres] !>"; simpl.
      iSpecialize ("Hres" with "HPre Hsrc Hna").
      wp_bind (g _). iApply (rwp_wand with "Hres []").
      iIntros (v) "[Hna Hres]". iDestruct "Hres" as (k) "(#HPost & Hsrc & #Hk)".
      iMod (na_inv_acc_open_timeless with "I Hna") as "(Hc & Hna & Hclose)"; auto.
      iDestruct "Hc" as (h2) "(HM & #Hupd')".
      wp_pures. wp_apply (set_spec with "[$HM]").
      { by iApply Pre_Comparable. }
      iIntros "HM".
      iApply fupd_rwp. iMod ("Hclose" with "[HM $Hna]") as "Hna".
      { iNext. iExists (<[n:=_]> h2). iFrame.
        iApply big_sepM_insert_2; simpl; auto.
      }
      iModIntro. wp_pures. iFrame.
      iExists k. iFrame. iFrame "#".
  Qed.


  Lemma memoize_spec eq (f g: val):
    eqfun Comparable eq Eq ∗
    implements g f ∗
    □ (∀ (e : expr) (v : val), R e v -∗ eval e v)
    ⊢ SEQ (memoize eq g) ⟨⟨ h, implements h f ⟩⟩.
  Proof using Comparable Comparable_timeless Cred Eq Heap PEq PPost PPre Post Pre Pre_Comparable Pre_Eq_Proper R SI
        Seq TL TLPost Σ.
    iIntros "[#Heq [#H #R]] Hna". rewrite /memoize. wp_pures. iFrame.
    wp_apply map_spec; first done. iIntros (m) "Hm".
    iMod (na_inv_alloc seqG_name ⊤ refN (mem_inv m f) with "[Hm]") as "#IM".
    { iNext. iExists ∅. iFrame. rewrite big_sepM_empty; done. }
    wp_pures. iFrame.

    iModIntro; iIntros (n n' K) "#HPre Hsrc Hna".
    wp_pure _.
    iDestruct (Pre_Comparable with "HPre") as "Hcomp".
    iApply (memoization_core with "[-Hna] [$Hna]").
      iFrame "IM Hsrc R HPre Heq". iIntros "Hna". wp_value_head. iFrame.
      iApply "H".
  Qed.

  Lemma mem_rec_spec eq (F f: val):
      eqfun Comparable eq Eq ∗
      (□ ∀ g, ▷ implements g f -∗ SEQ (F g) ⟨⟨h, implements h f⟩⟩) ∗
      □ (∀ (e : expr) (v : val), R e v -∗ eval e v) ⊢
      SEQ (mem_rec eq F) ⟨⟨ h, implements h f ⟩⟩.
  Proof using Comparable Comparable_timeless Cred Eq Heap PEq PPost PPre Post Pre Pre_Comparable Pre_Eq_Proper R SI
        Seq TL TLPost Σ.
    iIntros "[#Heq [#H #R]] Hna". rewrite /mem_rec. wp_pures. iFrame.
    wp_apply map_spec; first done. iIntros (m) "Hm".
    iMod (na_inv_alloc seqG_name ⊤ refN (mem_inv m f) with "[Hm]") as "#IM".
    { iNext. iExists ∅. iFrame. rewrite big_sepM_empty; done. }
    wp_pures. iFrame.

    iLöb as "IH". iModIntro. iIntros (n n' K) "#HPre Hsrc Hna".
    wp_pure _.
    iDestruct (Pre_Comparable with "HPre") as "Hcomp".
    iApply (memoization_core with "[-Hna] [$Hna]").
    iFrame "IM Hsrc R HPre Heq". iApply "H". iApply "IH".
  Qed.

End timeless_memoization.

Section pure_nat_memoization.
  Context {SI: indexT} {A: Type} `{Σ: gFunctors SI} `{Heap: !rheapG Σ} `{Cred: !auth_sourceG Σ (natA SI)} `{Seq: !seqG Σ}.


  Implicit Types (c: nat).
  Implicit Types (f g m v: val).
  Implicit Types (e: expr).
  Implicit Types (h: gmap val val).

  Definition natRel (v1 v2: val) : iProp Σ :=
    (∃ n : nat, ⌜ v1 = #n ∧ v2 = #n ⌝)%I.

  Lemma lookup_O {X: Type} (l: list X) (x: X):
    l !! O = Some x →
    ∃ l', l = x :: l'.
  Proof.
    destruct l as [| a l']; rewrite ?lookup_nil; try congruence => //=.
    rewrite /=. intros. exists l'. congruence.
  Qed.

  Definition execV (e: expr) (v: val) : iProp Σ := (⌜exec e v⌝)%I.

  Lemma pure_exec_exec e1 e2 n φ: PureExec φ (S n) e1 e2 → φ → exec e1 e2.
  Proof.
    intros HP Hφ. specialize (HP Hφ); remember (S n) as m; revert n Heqm.
    induction HP as [|n e1 e2 e3 Hstep Hsteps]; first naive_solver.
    injection 1 as <-. destruct n as [|n].
    - inversion Hsteps; subst. eapply tc_once, Hstep.
    - eapply tc_l; naive_solver.
  Qed.

  Lemma exec_frame e1 e2 K: exec e1 e2 → exec (fill K e1) (fill K e2).
  Proof.
    induction 1.
    - eapply tc_once, pure_step_ctx; eauto. apply _.
    - etrans; eauto.
      eapply tc_once, pure_step_ctx; eauto. apply _.
  Qed.

  Lemma exec_src_update e1 e2 j E: exec e1 e2 → j ⤇ e1 ⊢ src_update E (j ⤇ e2).
  Proof.
    induction 1.
    - by apply step_pure.
    - iIntros "H". iApply src_update_bind. iSplitL.
      + iApply step_pure; eauto.
      + iApply IHtc.
  Qed.

  Lemma rtc_r_or_tc {X: Type} (R: relation X) x y:
    rtc R x y → x = y ∨ tc R x y.
  Proof.
    induction 1.
    - by left.
    - right. destruct IHrtc.
      * subst. by apply tc_once.
      * eapply tc_l; eauto.
  Qed.

  Definition natfun_refines (g: val) (f: val) : iProp Σ :=
    (□ ∀ (n : nat) K,
          src (fill K (f #n)) -∗
          SEQ (g #n) ⟨⟨v, ∃ n': nat, ⌜ v = #n' ⌝ ∗ src (fill K v) ⟩⟩)%I.

  Definition natfun_pure (f: val) :=
    ∀ (n1 n2 : nat) tp1 tp2 σ1 σ2 K,
      rtc erased_step (fill K (f #n1) :: tp1, σ1) (fill K (#n2) :: tp2, σ2) →
      (∀ K', rtc pure_step (fill K' (f #n1)) (fill K' (#n2))).

  Lemma natfun_mem_rec_spec (F f: val):
      natfun_pure f →
      (□ ∀ g, ▷ natfun_refines g f -∗ SEQ (F g) ⟨⟨h, natfun_refines h f⟩⟩) ⊢
      SEQ (mem_rec eq_heaplang F) ⟨⟨ h, natfun_refines h f ⟩⟩.
  Proof.
    iIntros (Hpure) "#Href".
    iIntros "Hna".
    iPoseProof (mem_rec_spec
                  (λ e v, ∃ K (n1 n2: nat) tp1 tp2 σ1 σ2, ⌜ e = (f #n1) ∧ v = #n2 ∧
                    rtc erased_step (fill K (f #n1) :: tp1, σ1) (fill K (#n2) :: tp2, σ2)⌝)%I
                  natRel natRel
                  (λ x, ⌜ val_is_unboxed x ⌝)%I (λ x1 x2, ⌜ x1 = x2 ⌝)%I
                  with "[] [$Hna]") as "H"; last first.
    { iApply (rwp_mono with "H").
      iIntros  (?) "($&#H)". rewrite /implements /natfun_refines.
      iIntros "!>" (n K) "Hsrc Hna".
      iSpecialize ("H" $! #n with "[] [$] [$]"); first eauto.
      iApply (rwp_mono with "H").
      iIntros (?) "($&Hrel)".
      iDestruct "Hrel" as (? (n'&->&->)) "(Hsrc&_)".
      iExists n'. eauto.
    }
    { iSplit.
      {
        rewrite /eqfun. iIntros (??) "!>". iIntros (Φ) "(%&%) H".
        rewrite /eq_heaplang. wp_pures.
        wp_pure _; first (rewrite /vals_compare_safe; eauto).
        iApply "H". iFrame "%". rewrite /bool_decide. destruct (decide_rel _); eauto.
      }
      iSplit.
      * iModIntro.
        iIntros (g) "Himpl Hna".
        iSpecialize ("Href" $! g with "[Himpl] [$]").
        {
          iNext. iDestruct "Himpl" as "#Himpl". iIntros (n K) "!> H Hna".
          iSpecialize ("Himpl" with "[] [$] [$]"); eauto.
          iApply (rwp_wand with "Himpl").
          iIntros (?) "($&H)".
          iDestruct "H" as (? (n'&Heq1&Heq2)) "(Hsrc&_)".
          subst; eauto.
        }
        iApply (rwp_wand with "Href").
        iIntros (?) "($&#Hnatfun)".
        rewrite /implements.
        iIntros (?? K) "!> H Hsrc Hna".
        iApply (rwp_weaken' with "[-Hsrc]"); first done; last first.
        { iApply (src_log with "[$]"). }
        iIntros "(Hsrc&Hlog)".
        iDestruct "Hlog" as (tp σ i Hlookup) "#Hfmlist".
        iDestruct "H" as %[n [-> ->]].
        iSpecialize ("Hnatfun" with "[$] [$]").
        iApply rwp_fupd'.
        iApply (rwp_wand with "Hnatfun").
        iIntros (?) "($&H)".
        iIntros (???) "(Hinterp&Hstate)".
        iDestruct "H" as (n' ?) "Hsrc".
        iDestruct (src_get_trace' with "[$]") as "(Hsrc&Hinterp&Hin)".
        iDestruct "Hin" as %(?&σ'&Hlookup'&Hrtc).
        iFrame. iModIntro.
        iExists #n'.
        subst.
        iSplit; first eauto.
        iSplit; first eauto.
        iModIntro. iIntros (?) "H".
        iDestruct "H" as %(?&Heq1&Heq2); subst.
        inversion Heq1 as [Heq].
        iExists #n'. iSplit; eauto.
        iModIntro.
        apply lookup_O in Hlookup as (tp1'&->).
        apply lookup_O in Hlookup' as (tp2'&->).
        iExists _, _, _, _, _,
        {| heap := fst σ; used_proph_id := {| mapset.mapset_car := snd σ |}|},
        {| heap := fst σ'; used_proph_id := {| mapset.mapset_car := snd σ' |}|}.
        iPureIntro.
        split_and!; eauto. rewrite /to_cfg in Hrtc. destruct σ, σ'. eapply Hrtc.
      * iModIntro. iIntros (e v) "H".
        iDestruct "H" as (K n1 n2 tp1 tp2 σ1 σ2) "H".
        iDestruct "H" as %(Heq1&Heq2&Hrtc).
        rewrite /eval.
        iIntros (K') "Hsrc".
        iApply (exec_src_update with "[$]").
        subst.
        apply Hpure in Hrtc. specialize (Hrtc K').
        apply rtc_r_or_tc in Hrtc as [Hr|Htc]; last eauto.
        { apply fill_injective in Hr. congruence. }
    }
    { iIntros (??? -> Hrel). iPureIntro. destruct Hrel as (x&->&->). eauto. }
    { iIntros (?? (n'&->&->)). eauto. }
  Qed.

End pure_nat_memoization.

Section repeatable_refinements.
  Context {SI: indexT} {A: Type} `{Σ: gFunctors SI} `{Heap: !rheapG Σ} `{Cred: !auth_sourceG Σ (natA SI)} `{Sync: !inG Σ (authR (optionUR (exclR (gmapO val (valO SI)))))} `{Seq: !seqG Σ}.


  Implicit Types (c: nat).
  Implicit Types (f g m v: val).
  Implicit Types (e: expr).
  Implicit Types (h: gmap val val).
  Variable (Pre Post: val → val → iProp Σ).
  Variable (Comparable: val → iProp Σ).
  Variable (Eq: val → val → iProp Σ).
  Context `{PPre: !∀ v v', Persistent (Pre v v')}.
  Context `{PPost: !∀ v v', Persistent (Post v v')}.
  Context `{PEq: !∀ v v', Persistent (Eq v v')}.
  Context `{Comparable_timeless: ∀ v, Timeless (Comparable v)}.
  Variable (Pre_Comparable : ∀ v v', Pre v v' ={⊤}=∗ Comparable v).
  Variable (Pre_Eq_Proper: ∀ v1 v1' v2, Eq v1 v1' -∗ Pre v1' v2 -∗ Pre v1 v2).


  (* we allow arbitrary stutter *)
  Definition mem_rec_tl_inv γ m : iProp Σ := (∃ h, Map Comparable m h ∗ own γ (● Excl' h) ∗ $ (1%nat))%I.
  Definition mem_rec_tf_inv γ (f: val) : iProp Σ :=
    (∃ h, own γ (◯ Excl' h) ∗ [∗ map] k ↦ v ∈ h, □ (∀ k', Pre k k' -∗ ∃ v', □ eval (f k') v' ∗ Post v v'))%I.

  Definition tf_implements (g: val) (f: val) : iProp Σ :=
    (□ ∀ x x' c K,
          Pre x x' -∗
          src (fill K (f x')) -∗
          SEQ (g x) ⟨⟨v, ∃ v': val, Post v v' ∗ $c ∗ src (fill K v') ∗
                                    □ (∀ x', Pre x x' -∗ ∃ v', □ eval (f x') v' ∗ Post v v') ⟩⟩)%I.

  Lemma tf_memoization_core `{FiniteBoundedExistential SI} (eq: val) (f: val) e c γ (n n' : val) m K :
    SEQ e ⟨⟨ h, tf_implements h f ⟩⟩ ∗
    se_inv (refN .@ "tl") (mem_rec_tl_inv γ m) ∗
    se_inv (refN .@ "tf") (mem_rec_tf_inv γ f) ∗
    Pre n n' ∗
    eqfun Comparable eq Eq ∗
    src (fill K (f n')) ⊢
    SEQ (match: get m eq n with
      NONE => let: "y" := e n in set m n "y";; "y"
    | SOME "y" => "y"
    end) ⟨⟨v, ∃ v': val, Post v v' ∗ $c ∗ src (fill K v') ∗ □ (∀ n', Pre n n' -∗ ∃ v', □ eval (f n') v' ∗ Post v v') ⟩⟩.
  Proof using Comparable Comparable_timeless Cred Eq Heap PEq PPost PPre Post Pre Pre_Comparable Pre_Eq_Proper SI
              Seq Sync Σ.
    iIntros "(Spec & #IM & #IC & #HPre & #Heqfun & Hsrc) Hna".
    (* we open the timeless invariant for the get *)
    iMod (na_inv_acc_open_timeless with "IM Hna") as "(Hc & Hna & Hclose1)"; auto.
    iDestruct "Hc" as (h) "(HM & H● & Hone)".
    wp_bind (get m eq n).
    iMod (Pre_Comparable with "HPre") as "HComp".
    wp_apply (get_spec with "[$HM $Heqfun $HComp]").
    iIntros (o) "HM".
    destruct o as [k|] eqn: Heq.
    - (* we have stored this result before *)
      iDestruct "HM" as (n0 Hlookup) "(#Heq&HM)".
      iMod (na_inv_acc_open with "IC Hna") as "Hcache"; auto; first solve_ndisj.
      iApply (rwp_take_step with "[-Hone] [Hone]"); first done; last first.
      { iApply step_stutter. iFrame. } iIntros "_".
      iApply rswp_do_step. iNext; simpl. iDestruct "Hcache" as "(HsrcI & Hna & Hclose2)".
      iDestruct "HsrcI" as (h') "[H◯ #Hupd]".
      iDestruct (own_valid_2 with "H● H◯") as % [->%Excl_included%leibniz_equiv _]%auth_both_valid.
      wp_pure _.
      iDestruct (big_sepM_lookup with "Hupd") as "#Hk"; first done.
      iDestruct ("Hk" with "[]") as (?) "(#Heval&#HP)".
      { iApply (Pre_Eq_Proper with "[$] [$]"). }
      iApply (rwp_weaken with "[-Hsrc] [Hsrc]"); first done; last first.
      { iApply (step_inv_alloc (S c) with "[] Hsrc"); iSplitL; first iApply "Heval".
        iIntros "Hsrc". iExists (fill K _). iFrame. iPureIntro. intros ? % fill_injective; discriminate. }
      rewrite nat_srcF_succ. iIntros "(Hsrc & Hone & Hc)".
      iApply fupd_rwp. iMod ("Hclose2" with "[H◯ $Hna]") as "Hna".
      { iNext. iExists h. iFrame. done. }
      iMod ("Hclose1" with "[H● HM $Hna Hone]") as "Hna".
      { iNext. iExists h. iFrame. }
      iModIntro. wp_pures.
      iFrame. iExists _. iFrame "# ∗".
      iIntros "!>" (n'') "HPre''".
      iApply "Hk". iApply (Pre_Eq_Proper with "[$] [$]").
    - (* we close the invariant again for the recursive call *)
      iDestruct "HM" as "(Hnin&HM)".
      iMod ("Hclose1" with "[H● HM $Hna Hone]") as "Hna".
      { iNext. iExists _. iFrame. }
      wp_pures. wp_bind e.
      iApply (rwp_strong_mono with "[Spec Hna]");[eauto..| by iApply "Spec" |].
      iIntros (g) "[Hna Hres] !>"; simpl.
      iSpecialize ("Hres" $! _ _ (S c) with "[$] Hsrc Hna").
      wp_bind (g _). iApply (rwp_wand with "Hres []").
      iIntros (v) "[Hna Hres]". iDestruct "Hres" as (k) "(HPost & Hcred & Hsrc & #Hk)".
      rewrite nat_srcF_succ. iDestruct ("Hcred") as "[Hone Hcred]".
      iMod (na_inv_acc_open_timeless with "IM Hna") as "(Hc & Hna & Hclose1)"; auto.
      iDestruct "Hc" as (h2) "(HM & H● & Hone')".
      iMod (na_inv_acc_open with "IC Hna") as "Hcache"; auto; first solve_ndisj.
      iApply (rwp_take_step with "[-Hone] [Hone]"); first done; last first.
      { iApply step_stutter. iFrame. } iIntros "_".
      iApply rswp_do_step. iNext; simpl. iDestruct "Hcache" as "(HsrcI & Hna & Hclose2)".
      iDestruct "HsrcI" as (h2') "[H◯ #Hupd]".
      iDestruct (own_valid_2 with "H● H◯") as % [->%Excl_included%leibniz_equiv _]%auth_both_valid.
      wp_pures.
      iMod (Pre_Comparable with "HPre") as "HComp".
      wp_apply (set_spec with "[$HM $HComp]").
      iIntros "HM".
      iMod (own_update_2 with "H● H◯") as "[H● H◯]".
      { apply auth_update, option_local_update, (exclusive_local_update _ (Excl (<[n := v]> h2))); done. }
      iApply fupd_rwp. iMod ("Hclose2" with "[H◯ $Hna]") as "Hna".
      { iNext. iExists (<[n:=_]> h2). iFrame.
        iApply big_sepM_insert_2; simpl; eauto. }
      iMod ("Hclose1" with "[H● HM $Hna Hone']") as "Hna".
      { iNext. iExists _. iFrame. }
      iModIntro. wp_pures. iFrame.
      iExists k. iFrame. iFrame "#".
  Qed.

  Lemma tf_memoize_spec `{FiniteBoundedExistential SI} eq (f g: val):
    eqfun Comparable eq Eq ∗
    tf_implements g f ∗
    $ (1%nat)
    ⊢ SEQ (memoize eq g) ⟨⟨ h, tf_implements h f ⟩⟩.
  Proof using Comparable Comparable_timeless Cred Eq Heap PEq PPost PPre Post Pre Pre_Comparable Pre_Eq_Proper SI
        Seq Sync Σ.
    iIntros "(#Heq&#H&Hcred) Hna". rewrite /memoize. wp_pures. iFrame.
    wp_apply map_spec; first done. iIntros (m) "Hm".
    iMod (own_alloc (● (Excl' ∅) ⋅ ◯ (Excl' ∅))) as (γ) "[H● H◯]".
    { apply auth_both_valid_2; done. }
    iMod (na_inv_alloc seqG_name ⊤ (refN .@ "tl") (mem_rec_tl_inv γ m) with "[H● Hm Hcred]") as "#IM".
    { iNext. iExists ∅. iFrame. }
    iMod (na_inv_alloc seqG_name ⊤ (refN .@ "tf") (mem_rec_tf_inv γ f) with "[H◯]") as "#IS".
    { iNext. iExists ∅. iFrame. rewrite big_sepM_empty; done. }
    wp_pures. iFrame.
    iIntros (n n' c K) "!> #HPre Hsrc Hna".
    wp_pure _.
    iDestruct (Pre_Comparable with "HPre") as "Hcomp".
    iApply (tf_memoization_core with "[-Hna] [$Hna]").
    iFrame "IM IS Hsrc HPre Heq". iIntros "Hna". wp_value_head. iFrame.
    iApply "H".
  Qed.

  Lemma tf_mem_rec_spec `{FiniteBoundedExistential SI} eq (F f: val):
      eqfun Comparable eq Eq ∗
      (□ ∀ g, ▷ tf_implements g f -∗ SEQ (F g) ⟨⟨h, tf_implements h f⟩⟩) ∗ $ (1%nat) ⊢
      SEQ (mem_rec eq F) ⟨⟨ h, tf_implements h f ⟩⟩.
  Proof using Comparable Comparable_timeless Cred Eq Heap PEq PPost PPre Post Pre Pre_Comparable Pre_Eq_Proper SI
        Seq Sync Σ.
      iIntros "[#Heq [#HF Hcred]] Hna". rewrite /mem_rec. wp_pures. iFrame.
      wp_apply map_spec; first done. iIntros (m) "Hm".
      iMod (own_alloc (● (Excl' ∅) ⋅ ◯ (Excl' ∅))) as (γ) "[H● H◯]".
      { apply auth_both_valid_2; done. }
      iMod (na_inv_alloc seqG_name ⊤ (refN .@ "tl") (mem_rec_tl_inv γ m) with "[H● Hm Hcred]") as "#IM".
      { iNext. iExists ∅. iFrame. }
      iMod (na_inv_alloc seqG_name ⊤ (refN .@ "tf") (mem_rec_tf_inv γ f) with "[H◯]") as "#IS".
      { iNext. iExists ∅. iFrame. rewrite big_sepM_empty; done. }
      wp_pures. iFrame.

      iLöb as "IH". iModIntro; iIntros (n n' c K) "#HPre Hsrc Hna".
      wp_pure _.
      iDestruct (Pre_Comparable with "HPre") as "Hcomp".
      iApply (tf_memoization_core with "[-Hna] Hna").
      iFrame "IM IS Hsrc HPre Heq". iApply "HF". iApply "IH".
  Qed.

End repeatable_refinements.


Section fibonacci.
  Context {SI: indexT} {A: Type} `{Σ: gFunctors SI} `{Heap: !rheapG Σ} `{Cred: !auth_sourceG Σ (natA SI)}  `{Seq: !seqG Σ}.

  (* we define the body to reduce the number of lemmas we need to prove*)
  Definition Fib (fib : val) (n : expr): expr :=
    if: n = #0 then #0
      else if: n = #1 then #1
      else
        let: "n'" := n - #1 in
        let: "n''" := n - #2 in
        fib "n'" + fib "n''".


  Lemma Fib_zero fib: exec (Fib fib #0) (#0).
  Proof.
    eapply pure_exec_exec.
    - rewrite /Fib; pure_exec.
    - repeat split; solve_vals_compare_safe.
  Qed.

  Lemma Fib_one fib: exec (Fib fib #1) (#1).
  Proof.
    eapply pure_exec_exec.
    - rewrite /Fib; pure_exec.
    - repeat split; solve_vals_compare_safe.
  Qed.

  Lemma Fib_rec fib n: exec (Fib fib #(S (S n))) ((fib #(S n)) + (fib #n))%E.
  Proof.
    eapply pure_exec_exec.
    - rewrite /Fib; pure_exec.
      rewrite bool_decide_eq_false_2; last (injection 1; lia).
      pure_exec.
    - repeat split; try solve_vals_compare_safe.
      + rewrite /bin_op_eval //=. by replace (S (S n) - 1) with (S n: Z) by lia.
      + rewrite /bin_op_eval //=. by replace (S (S n) - 2) with (n: Z) by lia.
  Qed.

  Definition fib : val :=
    rec: "fib" "n" :=
      if: "n" = #0 then #0
      else if: "n" = #1 then #1
      else
        let: "n'" := "n" - #1 in
        let: "n''" := "n" - #2 in
        "fib" "n'" + "fib" "n''".

  Lemma fib_Fib (v: val): exec (fib v) (Fib fib v).
  Proof.
    eapply pure_exec_exec.
    - rewrite /Fib /fib; pure_exec.
    - repeat split.
  Qed.

  Definition fib_template : val :=
    λ: "fib" "n",
      if: "n" = #0 then #0
      else if: "n" = #1 then #1
      else
        let: "n'" := "n" - #1 in
        let: "n''" := "n" - #2 in
        "fib" "n'" + "fib" "n''".

  Tactic Notation "exec_bind" open_constr(efoc) :=
    match goal with
    | [|- exec ?e1 ?e2] =>
      src_bind_core e1 efoc ltac:(fun K e' => change (exec (fill K e') e2))
    end.

  Lemma fib_fundamental_core g K (n: nat):
    (▷ implements execV natRel natRel g fib) ∗
    src (fill K (fib #n)) ⊢
    SEQ (Fib g #n) ⟨⟨v, ∃ m: nat, ⌜v = #m⌝ ∗ src (fill K #m) ∗ □ execV (fib #n) #m ⟩⟩.
  Proof.
  iIntros "[#IH Hsrc] Hna".
  destruct n as [|[|n]]; (iApply (rwp_take_step with "[-Hsrc] [Hsrc]"); first done; last first).
  - iApply exec_src_update; eauto. eapply exec_frame.
    etrans; first apply fib_Fib. eapply Fib_zero.
  - iIntros "Hsrc".  iApply rswp_do_step. iNext. rewrite /Fib.
    wp_pure _; first solve_vals_compare_safe. wp_pures. iFrame.
    iExists 0%nat. iFrame. iSplitL; eauto.
    iModIntro. iPureIntro. etrans; first apply fib_Fib. eapply Fib_zero.
  - iApply exec_src_update; eauto. eapply exec_frame.
    etrans; first apply fib_Fib. eapply Fib_one.
  - iIntros "Hsrc".  iApply rswp_do_step. iNext. rewrite /Fib.
    wp_pure _; first solve_vals_compare_safe. wp_pures.
    wp_pure _; first solve_vals_compare_safe. wp_pures.
    iFrame. iExists 1%nat. iFrame. iSplitL; eauto.
    iModIntro. iPureIntro.
    etrans; first apply fib_Fib. eapply Fib_one.
  - iApply exec_src_update; eauto. eapply exec_frame.
    etrans; first apply fib_Fib. eapply Fib_rec.
  - iIntros "Hsrc".  iApply rswp_do_step. iNext. rewrite /Fib.
    wp_pure _; first solve_vals_compare_safe. wp_pures.
    wp_pure _; first solve_vals_compare_safe.
    rewrite bool_decide_eq_false_2; last (injection 1; lia).
    do 7 wp_pure _.
    (* recursion for n *)
    wp_bind (g  _)%E. replace (S (S n) - 2) with (n: Z) by lia.
    src_bind (fib #n) in "Hsrc".
    iApply (rwp_wand with "[Hna Hsrc]").
    { iApply ("IH" with "[] Hsrc Hna"); first eauto. }
    iIntros (v) "[Hna H]". iDestruct "H" as (m) "(HPre & Hsrc & #Hev1)"; simpl.
    iDestruct "HPre" as %[m' [Heq1 Heq2]]. subst.
    (* recursion for (n + 1) *)
    wp_bind (g  _)%E. replace (S (S n) - 1) with (S n: Z) by lia.
    src_bind (fib _) in "Hsrc".
    iApply (rwp_wand with "[Hna Hsrc]").
    { iApply ("IH" with "[] Hsrc Hna"). eauto. }
    iIntros (v) "[Hna H]". iDestruct "H" as (v') "(HPre & Hsrc & #Hev2)"; simpl.
    iDestruct "HPre" as %[m [Heq1 Heq2]]. subst.
    iFrame. iApply (rwp_weaken with "[-Hsrc] [Hsrc]"); first done; last first.
    { iApply (steps_pure_exec with "Hsrc"). reflexivity. }
    simpl; iIntros "Hsrc"; wp_pure _.
    replace (m + m') with ((m' + m)%nat: Z) by lia.
    iExists (m' + m)%nat; iFrame; iSplitR; auto.
    iModIntro.
    iDestruct "Hev1" as % Hev1. iDestruct "Hev2" as % Hev2. iPureIntro.
    etrans; first eapply fib_Fib.
    etrans; first eapply Fib_rec.
    edestruct Hev1 as (?&Hexec1&?&Heq1&?); eauto.
    edestruct Hev2 as (?&Hexec2&?&Heq2&?); eauto; subst.
    inversion Heq1; subst.
    inversion Heq2; subst.
    exec_bind (fib _); etrans; first eapply exec_frame; eauto; simpl.
    exec_bind (fib _); etrans; first eapply exec_frame; eauto; simpl.
    eapply pure_exec_exec. apply _.
    rewrite /bin_op_eval. destruct (decide _) => //=.
    repeat f_equal. lia.
  Qed.

  Lemma fib_sound:
    ⊢ implements execV natRel natRel fib fib.
  Proof.
    iLöb as "IH".
    iModIntro; iIntros (v v' K) "HPre Hsrc Hna".
    iDestruct "HPre" as %[n [Heq1 Heq2]]. subst.
    rewrite {4}/fib. wp_pure _.
    fold fib. fold (Fib fib #n).
    iApply rwp_mono; last first.
    { iApply (fib_fundamental_core fib K n with "[$Hsrc $IH] Hna"). }
    iIntros (v) "($&H)".
    iDestruct "H" as (m ->) "(Hsrc&#Hexec)". iExists _. iFrame.
    iSplitR; first eauto.
    iModIntro. iIntros (x) "Hrel". iDestruct "Hrel" as %[? [-> ->]]. iExists _. iSplit; eauto.
  Qed.

  Lemma fib_template_sound g:
    ▷ implements execV natRel natRel g fib ⊢ SEQ (fib_template g) ⟨⟨h, implements execV natRel natRel h fib⟩⟩.
  Proof.
    iIntros "#H Hna". rewrite /fib_template. wp_pures. iFrame.
    iModIntro; iIntros (n n' K) "HPre Hsrc Hna".
    wp_pure _. fold (Fib g n).
    iDestruct "HPre" as %[n0 [-> ->]].
    iApply rwp_mono; last first.
    { by iApply (fib_fundamental_core g K n0 with "[$Hsrc] Hna"). }
    iIntros (v) "($&H)".
    iDestruct "H" as (m ->) "(Hsrc&#Hexec)". iExists _. iFrame.
    iSplitR; first eauto.
    iModIntro. iIntros (x) "Hrel". iDestruct "Hrel" as %[? [-> ->]]. iExists _. iSplit; eauto.
  Qed.


  (* memoized versions *)
  Lemma fib_memoized: ⊢ SEQ (memoize eq_heaplang fib) ⟨⟨ h, implements execV natRel natRel h fib ⟩⟩.
  Proof.
    (* XXX: the iApply fails over typeclass resolution (?) if we don't do iStartProof *)
    iStartProof.
    iApply (memoize_spec _ _ _ (λ x, ⌜ val_is_unboxed x ⌝)%I (λ x1 x2, ⌜ x1 = x2 ⌝)%I);
      [| | iSplit; [| iSplit]].
    - iIntros (??) "H". iDestruct "H" as %[? [-> ->]]. eauto.
    - iIntros (??? ->). auto.
    - rewrite /eqfun. iIntros (??) "!>". iIntros (Φ) "(%&%) H".
      rewrite /eq_heaplang. wp_pures.
      wp_pure _; first (rewrite /vals_compare_safe; eauto).
      iApply "H". iFrame "%". rewrite /bool_decide. destruct (decide_rel _); eauto.
    - iApply fib_sound.
    - iModIntro. iIntros (e v Hexec K).
      iApply exec_src_update. apply exec_frame, Hexec.
  Qed.

  Lemma fib_deep_memoized: ⊢ SEQ (mem_rec eq_heaplang fib_template) ⟨⟨ h, implements execV natRel natRel h fib ⟩⟩.
  Proof.
    iStartProof.
    iApply (mem_rec_spec _ _ _ (λ x, ⌜ val_is_unboxed x ⌝)%I (λ x1 x2, ⌜ x1 = x2 ⌝)%I);
      [| | iSplit; [| iSplit]].
    - iIntros (??) "H". iDestruct "H" as %[? [-> ->]]. eauto.
    - iIntros (??? ->). auto.
    - rewrite /eqfun. iIntros (??) "!>". iIntros (Φ) "(%&%) H".
      rewrite /eq_heaplang. wp_pures.
      wp_pure _; first (rewrite /vals_compare_safe; eauto).
      iApply "H". iFrame "%". rewrite /bool_decide. destruct (decide_rel _); eauto.
    - iModIntro. iIntros (g). iApply fib_template_sound.
    - iModIntro. iIntros (e v Hexec K).
      iApply exec_src_update. apply exec_frame, Hexec.
  Qed.
End fibonacci.

Section levenshtein.
  Context {SI: indexT} {A: Type} `{Σ: gFunctors SI} `{Heap: !rheapG Σ} `{Cred: !auth_sourceG Σ (natA SI)}  `{Seq: !seqG Σ}.

  Definition eqstr : val :=
    rec: "eqstr" "s1" "s2" :=
      let: "c1" := !"s1" in
      let: "c2" := !"s2" in
      if: "c1" = "c2" then
        if: "c1" = #0 then
          #true
        else
          "eqstr" ("s1" +ₗ #1) ("s2" +ₗ #1)
      else
        #false.

  Definition Strlen (strlen : val) (l : expr): expr :=
      let: "c" := !l in
      if: "c" = #0 then #0
      else
        let: "r" := strlen (l +ₗ #1) in
        #1 + "r".

  Definition strlen_template : val :=
    λ: "strlen" "l",
      let: "c" := !"l" in
      if: "c" = #0 then #0
      else
        let: "r" := "strlen" ("l" +ₗ #1) in
        #1 + "r".

  Definition strlen : val :=
    rec: "strlen" "l" := strlen_template "strlen" "l".

  Definition min2 : val :=
    λ: "n1" "n2",
    if: "n1" ≤ "n2" then "n1" else "n2".

  Definition min3 : val :=
    λ: "n1" "n2" "n3",
    min2 (min2 "n1" "n2") ("n3").

  (*
  Fixpoint gallina_lev (s1 : list nat) (s2 : list nat) : nat :=
    match s1 with
    | [] => length s2
    | c1 :: s1' =>
      match s2 with
      |  [] => length s1
      | c2 :: s2' =>
        if decide (c1 = c2) then
          gallina_lev s1' s2'
        else
          let r1 := gallina_lev s1 s2' in
          let r2 := gallina_lev s1' s2 in
          let r3 := gallina_lev s1' s2' in
          (1 + min (min r1 r2) r3)%nat
      end
    end.
  *)

  Definition Lev (strlen : val) (lev : val) (s12 : expr): expr :=
      let: "s1" := Fst s12 in
      let: "s2" := Snd s12 in
      let: "c1" := !"s1" in
      if: "c1" = #0 then strlen "s2" else
      let: "c2" := !"s2" in
      if: "c2" = #0 then strlen "s1" else
      if: "c1" = "c2" then lev ("s1" +ₗ #1, "s2" +ₗ #1)
      else
        let: "r1" := lev ("s1", "s2" +ₗ #1) in
        let: "r2" := lev ("s1" +ₗ #1, "s2") in
        let: "r3" := lev ("s1" +ₗ #1, "s2" +ₗ #1) in
        #1 + min3 "r1" "r2" "r3".

  Definition lev_template : val :=
    λ: "strlen" "lev" "s12",
      let: "s1" := Fst "s12" in
      let: "s2" := Snd "s12" in
      let: "c1" := !"s1" in
      if: "c1" = #0 then "strlen" "s2" else
      let: "c2" := !"s2" in
      if: "c2" = #0 then "strlen" "s1" else
      if: "c1" = "c2" then "lev" ("s1" +ₗ #1,"s2" +ₗ #1)
      else
        let: "r1" := "lev" ("s1", "s2" +ₗ #1) in
        let: "r2" := "lev" ("s1" +ₗ #1, "s2") in
        let: "r3" := "lev" ("s1" +ₗ #1, "s2" +ₗ #1) in
        #1 + min3 "r1" "r2" "r3".

  Definition lev_template' (slen : expr) : val :=
    λ: "lev" "s12",
      let: "s1" := Fst "s12" in
      let: "s2" := Snd "s12" in
      let: "c1" := !"s1" in
      if: "c1" = #0 then slen "s2" else
      let: "c2" := !"s2" in
      if: "c2" = #0 then slen "s1" else
      if: "c1" = "c2" then "lev" ("s1" +ₗ #1,"s2" +ₗ #1)
      else
        let: "r1" := "lev" ("s1", "s2" +ₗ #1) in
        let: "r2" := "lev" ("s1" +ₗ #1, "s2") in
        let: "r3" := "lev" ("s1" +ₗ #1, "s2" +ₗ #1) in
        #1 + min3 "r1" "r2" "r3".

  Definition lev : val :=
    rec: "lev" "s12" := lev_template strlen "lev" "s12".

  Notation exec := (tc (@pure_step heap_lang)).

  Tactic Notation "exec_bind" open_constr(efoc) :=
    match goal with
    | [|- exec ?e1 ?e2] =>
      src_bind_core e1 efoc ltac:(fun K e' => change (exec (fill K e') e2))
    end.

  Lemma strlen_Strlen (v: val): exec (strlen v) (Strlen strlen v).
  Proof.
    eapply pure_exec_exec.
    - rewrite /Strlen /strlen /strlen_template; repeat pure_exec.
    - repeat split.
  Qed.

  Lemma lev_Lev (v: val): exec (lev v) (Lev strlen lev v).
  Proof.
    eapply pure_exec_exec.
    - rewrite /Lev /lev /lev_template; repeat pure_exec.
    - repeat split.
  Qed.

  (* C-style null terminated strings *)

  Fixpoint string_is (l: loc) (s: list nat) :=
    match s with
      | [] => (∃ q, l ↦{q} #0)
      | n1 :: s' => ⌜ n1 ≠ O ⌝ ∗ (∃ q, l ↦{q} #n1) ∗ string_is (l +ₗ 1) s'
    end%I.

  Fixpoint src_string_is (l: loc) (s: list nat) :=
    match s with
      | [] => (∃ q, l ↦s{q} #0)
      | n1 :: s' => ⌜ n1 ≠ O ⌝ ∗ (∃ q, l ↦s{q} #n1) ∗ src_string_is (l +ₗ 1) s'
    end%I.

  Lemma string_is_dup l s :
    string_is l s -∗ string_is l s ∗ string_is l s.
  Proof.
    iInduction s as [| n s] "IH" forall (l).
    - iDestruct 1 as (q) "H". iDestruct "H" as "(H1&H2)".
      iSplitL "H1"; iExists _; iFrame.
    - simpl string_is. iDestruct 1 as (Hneq) "(H&Htl)".
      iDestruct "H" as (q) "(H1&H2)".
      iDestruct ("IH" with "Htl") as "(Htl1&Htl2)".
      iSplitL "H1 Htl1"; iFrame "% ∗"; iExists _; iFrame.
  Qed.

  Instance string_is_timeless l s : Timeless (string_is l s).
  Proof. revert l. induction s; apply _. Qed.

  Lemma src_string_is_dup l s :
    src_string_is l s -∗ src_string_is l s ∗ src_string_is l s.
  Proof.
    iInduction s as [| n s] "IH" forall (l).
    - iDestruct 1 as (q) "H". iDestruct "H" as "(H1&H2)".
      iSplitL "H1"; iExists _; iFrame.
    - simpl src_string_is. iDestruct 1 as (Hneq) "(H&Htl)".
      iDestruct "H" as (q) "(H1&H2)".
      iDestruct ("IH" with "Htl") as "(Htl1&Htl2)".
      iSplitL "H1 Htl1"; iFrame "% ∗"; iExists _; iFrame.
  Qed.

  Instance src_string_is_timeless l s : Timeless (src_string_is l s).
  Proof. revert l. induction s; apply _. Qed.

  Definition stringRel_is (v1 v2: val) (s: list nat) : iProp Σ :=
    (∃ (l1 l2 : loc), ⌜ v1 = #l1 ∧ v2 = #l2 ⌝ ∗ string_is l1 s ∗ src_string_is l2 s)%I.

  Definition strN := nroot.@"str".

  Definition imm_stringRel (v1 v2: val) : iProp Σ :=
    (∃ s, inv strN (stringRel_is v1 v2 s))%I.

  Lemma stringRel_inv_acc (v1 v2 : val) s :
    inv strN (stringRel_is v1 v2 s) ={⊤}=∗
    stringRel_is v1 v2 s.
  Proof.
    iIntros "Hinv". iInv "Hinv" as ">H" "Hclo".
    iDestruct "H" as (?? (Heq1&Heq2)) "(His1&His2)".
    iDestruct (string_is_dup with "His1") as "(His1&His1')".
    iDestruct (src_string_is_dup with "His2") as "(His2&His2')".
    iMod ("Hclo" with "[His1' His2']"); iModIntro; iExists _, _; iFrame; eauto.
  Qed.

  Definition pairRel Pa Pb (v1 v2 : val) : iProp Σ :=
    (∃ v1a v1b v2a v2b, ⌜ v1 = PairV v1a v1b⌝ ∗ ⌜v2 = PairV v2a v2b ⌝ ∗ Pa v1a v2a ∗ Pb v1b v2b)%I.

  Definition pair_imm_stringRel := pairRel imm_stringRel imm_stringRel.

  Lemma rwp_strlen l s:
    string_is l s -∗
    RWP (strlen #l) ⟨⟨v, ⌜v = #(length s)⌝ ⟩⟩.
  Proof.
    iIntros "Hstr".
    iInduction s as [| n s] "IH" forall (l).
    - rewrite /strlen/strlen_template. wp_pures.
      iDestruct "Hstr" as (?) "H".
      wp_load. wp_pures. wp_pure _; first solve_vals_compare_safe.
      wp_pures. iFrame. eauto.
    - rewrite /strlen/strlen_template. wp_pures. simpl string_is.
      iDestruct "Hstr" as (?) "(H1&Htl)".
      iDestruct "H1" as (?) "Hl".
      wp_load. wp_pures. wp_pure _; first solve_vals_compare_safe.
      case_bool_decide; wp_pure _; eauto.
      { exfalso. eapply H. inversion H1. lia. }

      wp_bind ((rec: "strlen" "l" :=
                     (λ: "strlen" "l",
                        let: "c" := ! "l" in
                        if: "c" = #0 then #0 else let: "r" := "strlen" ("l" +ₗ #1) in #1 + "r")%V "strlen" "l")%V
                 (#l +ₗ #1))%E.
      wp_pure _.
      iApply (rwp_wand with "[Htl]").
      { iApply ("IH" with "[$]"). }
      iIntros (v) "%". subst. wp_pures. iFrame. iPureIntro.
      do 2 f_equal. simpl. lia.
  Qed.

  Lemma eval_strlen l s:
    src_string_is l s -∗
    eval (strlen #l) #(length s).
  Proof.
    iIntros "Hstr" (K) "H".
    iInduction s as [| n s] "IH" forall (K l).
    - rewrite /strlen/strlen_template.
      do 4 src_pure _ in "H".
      iDestruct "Hstr" as (?) "Hstr".
      src_load in "H". do 4 src_pure _ in "H". iApply weak_src_update_return. by iFrame.
    - rewrite /strlen/strlen_template. do 4 src_pure _ in "H". simpl src_string_is.
      iDestruct "Hstr" as (?) "(H1&Htl)".
      iDestruct "H1" as (?) "Hl".
      src_load in "H".
      do 3 src_pure _ in "H".
      case_bool_decide; src_pure _ in "H"; eauto.
      { exfalso. eapply H. inversion H1. lia. }
      src_pure _ in "H".
      src_bind ((rec: "strlen" "l" :=
                             (λ: "strlen" "l",
                                let: "c" := ! "l" in
                                if: "c" = #0 then #0 else let: "r" := "strlen" ("l" +ₗ #1) in #1 + "r")%V "strlen"
                               "l")%V
                 #(l +ₗ 1))%E in "H".
      iDestruct ("IH" with "Htl H") as "H".
      simpl fill.
      iApply src_update_weak_src_update.
      iApply weak_src_update_bind_r. iFrame.
      iIntros "H".
      do 3 src_pure _ in "H".
      iApply weak_src_update_return.
      replace (S (length s) : Z)%Z with (1 + length s)%Z; first by iFrame.
      rewrite Nat2Z.inj_succ //=. lia.
  Qed.

  Lemma stringRel_is_tl (l1 l2 : loc) n s:
    stringRel_is #l1 #l2 (n :: s) -∗
    stringRel_is #(l1 +ₗ 1) #(l2 +ₗ 1) s ∗
    (stringRel_is #(l1 +ₗ 1) #(l2 +ₗ 1) s -∗ stringRel_is #l1 #l2 (n :: s)).
  Proof.
    rewrite /stringRel_is.
    iDestruct 1 as (?? (Heq1&Heq2)) "(H1&H2)".
    inversion Heq1; subst.
    inversion Heq2; subst.
    simpl string_is. simpl src_string_is.
    iDestruct "H1" as (?) "(H1&Htl1)".
    iDestruct "H2" as (?) "(H2&Htl2)".
    iSplitL "Htl1 Htl2".
    { iExists _, _. iSplit; first eauto. iFrame. }
    iIntros "H". iExists _, _. iSplit; first eauto.
    iDestruct "H" as (?? (Heq1'&Heq2')) "(Htl1&Htl2)".
    iSplitL "H1 Htl1".
    { iSplit; eauto. iFrame. inversion Heq1'. subst. eauto. }
    { iSplit; eauto. iFrame. inversion Heq2'. subst. eauto. }
  Qed.

  Lemma inv_stringRel_is_tl N (l1 l2 : loc) n s:
    inv N (stringRel_is #l1 #l2 (n :: s)) -∗
    inv N (stringRel_is #(l1 +ₗ 1) #(l2 +ₗ 1) s).
  Proof.
    iIntros "Hinv". iApply (inv_alter_timeless with "Hinv").
    iIntros "!> H1".
    iDestruct (stringRel_is_tl with "H1") as "($&$)".
  Qed.

  Lemma min2_spec (n1 n2: nat) :
    ⊢ ⟨⟨⟨ True ⟩⟩⟩ min2 #n1 #n2 ⟨⟨⟨ RET #(min n1 n2) ; True ⟩⟩⟩.
  Proof.
    iIntros "!>" (Φ) "_ HΦ".
    rewrite /min2. wp_pures.
    case_bool_decide; wp_pures.
    - rewrite ->min_l by lia. by iApply "HΦ".
    - rewrite ->min_r by lia. by iApply "HΦ".
  Qed.

  Lemma min3_spec (n1 n2 n3: nat) :
    ⊢ ⟨⟨⟨ True ⟩⟩⟩ min3 #n1 #n2 #n3 ⟨⟨⟨ RET #(min (min n1 n2) n3) ; True ⟩⟩⟩.
  Proof.
    iIntros "!>" (Φ) "_ HΦ".
    rewrite /min3. wp_pures.
    repeat (wp_apply min2_spec; auto; iIntros "_").
  Qed.

  Lemma eval_min2 (n1 n2: nat) :
    eval (min2 #n1 #n2) #(min n1 n2).
  Proof.
    rewrite /eval. iIntros (K) "Hsrc".
    rewrite /min2. do 4 src_pure _ in "Hsrc".
    case_bool_decide; do 1 src_pure _ in "Hsrc".
    - rewrite ->min_l by lia. by iApply weak_src_update_return.
    - rewrite ->min_r by lia. by iApply weak_src_update_return.
  Qed.

  Lemma eval_min3 (n1 n2 n3: nat) :
    eval (min3 #n1 #n2 #n3) #(min (min n1 n2) n3).
  Proof.
    rewrite /eval. iIntros (K) "Hsrc".
    rewrite /min3/min2. do 9 src_pure _ in "Hsrc".
    case_bool_decide; do 1 src_pure _ in "Hsrc".
    - do 4 src_pure _ in "Hsrc".
      case_bool_decide; do 1 src_pure _ in "Hsrc".
      * do 2 rewrite ->min_l by lia. by iApply weak_src_update_return.
      * rewrite ->min_r by lia. by iApply weak_src_update_return.
    - do 4 src_pure _ in "Hsrc".
      case_bool_decide; do 1 src_pure _ in "Hsrc".
      * rewrite ->min_l by lia. rewrite ->min_r by lia. by iApply weak_src_update_return.
      * rewrite ->min_r by lia. by iApply weak_src_update_return.
  Qed.

  Lemma string_is_functional va s s' :
    string_is va s -∗
    string_is va s' -∗
    ⌜s = s'⌝.
  Proof.
    iIntros "Hrel1 Hrel2".
    iInduction s as [| n s] "IH" forall (va s').
    { destruct s'; first auto.
      simpl string_is.
      iDestruct "Hrel1" as (?) "Hva".
      iDestruct "Hrel2" as (Hneq) "(Hva'&?)".
      iDestruct "Hva'" as (?) "Hva'".
      iDestruct (mapsto_agree with "[$] [$]") as %Hfalse.
      iPureIntro. exfalso. inversion Hfalse. lia. }
    destruct s'; first auto.
    - simpl string_is.
      iDestruct "Hrel1" as (Hneq) "(Hva&?)".
      iDestruct "Hva" as (?) "Hva".
      iDestruct "Hrel2" as (?) "Hva'".
      iDestruct (mapsto_agree with "[$] [$]") as %Hfalse.
      iPureIntro. exfalso. inversion Hfalse. lia.
    - simpl string_is.
      iDestruct "Hrel1" as (Hneq) "(Hva&?)".
      iDestruct "Hva" as (?) "Hva".
      iDestruct "Hrel2" as (Hneq') "(Hva'&?)".
      iDestruct "Hva'" as (?) "Hva'".
      iDestruct (mapsto_agree with "[$] [$]") as %Heq1.
      iDestruct ("IH" with "[$] [$]") as %Heq2.
      iPureIntro. subst. inversion Heq1; subst. f_equal; lia.
  Qed.

  Lemma stringRel_is_functional va vb vb' s s' :
    stringRel_is va vb s -∗
    stringRel_is va vb' s' -∗
    ⌜s = s'⌝.
  Proof.
    iIntros "Hrel1 Hrel2".
    iDestruct "Hrel1" as (?? (->&->)) "(His1&?)".
    iDestruct "Hrel2" as (?? (Heq&?)) "(His2&?)".
    inversion Heq; subst. iApply (string_is_functional with "His1 [$]").
  Qed.

  Lemma strlen_fundamental_core slen c K (va vb: val):
    (▷ tf_implements imm_stringRel natRel slen strlen) ∗
    imm_stringRel va vb ∗
    src (fill K (strlen vb)) ⊢
    SEQ (Strlen slen va) ⟨⟨v, ∃ m: nat, ⌜v = #m⌝ ∗ $ c ∗ src (fill K #m) ∗ □ (∀ vb', imm_stringRel va vb' -∗ eval (strlen vb') #m) ⟩⟩.
  Proof.
  iIntros "[#IH [HPre Hsrc]] Hna".
  iDestruct "HPre" as (s) "#Hinv1".
  iApply (rwp_take_step with "[-Hsrc] [Hsrc]"); first done; last first.
  { iApply (step_inv_alloc c with "[] [$Hsrc]").
    iSplitL.
    { iApply exec_src_update; eauto. eapply exec_frame. apply strlen_Strlen. }
    iIntros "H". iExists _. iFrame. iPureIntro.
    rewrite /Strlen/strlen. intros Heq%fill_inj. congruence. }
  iIntros "(Hsrc&$)".  iApply rswp_do_step. iNext. rewrite /Strlen.
  iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
  iDestruct "Hstr1" as (l1a l1b (->&->)) "(Hl1a&Hl1b)".
  destruct s as [| n s].
  {
    iDestruct "Hl1a" as (q1a) "Hl1a".
    iDestruct "Hl1b" as (q1b) "Hl1b".
    wp_load.
    src_load in "Hsrc".
    do 4 src_pure _ in "Hsrc".
     wp_pures. wp_pure _; first solve_vals_compare_safe. wp_pures.
     iFrame. iExists O. iSplit; first eauto. iFrame.
    iModIntro. rewrite /eval. iIntros (vb') "#HPre". iIntros (K') "H".
    iDestruct "HPre" as (s') "#Hinv1'".
    iApply fupd_src_update.
    iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
    iMod (stringRel_inv_acc with "Hinv1'") as "Hstr1'".
    iDestruct (stringRel_is_functional with "Hstr1' Hstr1") as %->.
    iModIntro.
    iClear "Hstr1".
    iRename "Hstr1'" into "Hstr1".
    iDestruct "Hstr1" as (?? (->&->)) "(Hl1a&Hl1b)".
    iDestruct "Hl1a" as (q1a') "Hl1a".
    iDestruct "Hl1b" as (q1b') "Hl1b".
    rewrite /strlen/strlen_template.
    do 4 src_pure _ in "H".
    src_load in "H".
    do 4 src_pure _ in "H".
    iApply weak_src_update_return; by iFrame.
  }
  simpl string_is. simpl src_string_is.
  iDestruct "Hl1a" as (H1neq0) "(Hpts1a&Hl1a)".
  iDestruct "Hpts1a" as (?) "Hpts1a".
  iDestruct "Hl1b" as (H1neq0') "(Hpts1b&Hl1b)".
  iDestruct "Hpts1b" as (?) "Hpts1b".
  wp_load. wp_pures. wp_pure _; first solve_vals_compare_safe.
  src_load in "Hsrc".
  do 3 src_pure _ in "Hsrc".
  rewrite bool_decide_false; last first.
  { intros Heq. inversion Heq. lia. }
  wp_pures.
  do 2 src_pure _ in "Hsrc".
  src_bind (strlen _)%E in "Hsrc".
  iSpecialize ("IH" $! #(l1a +ₗ 1) _ O with "[] Hsrc [$]").
  { iExists _. iApply inv_stringRel_is_tl. eauto. }
  wp_bind (slen _).
  iApply (rwp_wand with "[IH]").
  { wp_apply "IH". }
  iIntros (v) "($&H)".
  iDestruct "H" as (? (m&Heq1&Heq2)) "(_&Hsrc&#Heval')".
  subst. simpl fill. do 3 src_pure _ in "Hsrc". wp_pures. iExists (1 + m)%nat.
  iSplit.
  { iPureIntro. do 2 f_equal. lia. }
  simpl.
  iFrame.
  replace (1 + Z.of_nat m) with (Z.of_nat (S m)) by lia. iFrame.
  iModIntro. rewrite /eval. iIntros (vb') "#HPre". iIntros (K') "H".
  iDestruct "HPre" as (s') "#Hinv1'".
  iApply fupd_src_update.
  iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
  iMod (stringRel_inv_acc with "Hinv1'") as "Hstr1'".
  iDestruct (stringRel_is_functional with "Hstr1' Hstr1") as %->.
  iModIntro.
  iClear "Hstr1".
  iRename "Hstr1'" into "Hstr1".
  iDestruct "Hstr1" as (?? (Heq1a&Heq1b)) "(Hl1a&Hl1b)".
  simpl src_string_is.
  iDestruct "Hl1b" as (H1neq0'') "(Hpts1b&Hl1b)".
  iDestruct "Hpts1b" as (?) "Hpts1b".
  rewrite /strlen/strlen_template.
  do 4 src_pure _ in "H".
  rewrite Heq1b.
  src_load in "H".
  do 3 src_pure _ in "H".
  rewrite bool_decide_false; last first.
  { intros Heq. inversion Heq. lia. }
  do 2 src_pure _ in "H".
  src_bind (_ (#_)%V)%E in "H".
  rewrite fill_cons. simpl ectxi_language.fill_item.
  iApply src_update_weak_src_update.
  iDestruct ("Heval'" with "[]") as (r2') "(Heval''&Hrel)"; [|
  iDestruct "Hrel" as %[? (Heq2&->)]; iDestruct ("Heval''" with "H") as "H"].
  { iExists _. iApply inv_stringRel_is_tl. eauto. }
  simpl fill.
  iApply (src_update_bind with "[$H]").
  iIntros "H".
  simpl.
  rewrite -Heq2.
  do 3 src_pure _ in "H".
  replace (1 + Z.of_nat m) with (Z.of_nat (S m)) by lia.
  iApply weak_src_update_return; by iFrame.
  Qed.

  Lemma lev_fundamental_core g slen c K (va vb: val):
    (▷ tf_implements imm_stringRel natRel slen strlen) ∗
    (▷ tf_implements pair_imm_stringRel natRel g lev) ∗
    pair_imm_stringRel va vb ∗
    src (fill K (lev vb)) ⊢
    SEQ (Lev slen g va) ⟨⟨v, ∃ m: nat, ⌜v = #m⌝ ∗ $ c ∗ src (fill K #m) ∗ □ (∀ vb', pair_imm_stringRel va vb' -∗ eval (lev vb') #m) ⟩⟩.
  Proof.
  iIntros "[#Hstrlen [#IH [HPre Hsrc]]] Hna".
  iDestruct "HPre" as (v1a v2a v1b v2b Heq1 Heq2) "(Hs1&Hs2)". subst.
  iDestruct "Hs1" as (s1) "#Hinv1".
  iDestruct "Hs2" as (s2) "#Hinv2".
  iApply (rwp_take_step with "[-Hsrc] [Hsrc]"); first done; last first.
  { iApply (step_inv_alloc c with "[] [$Hsrc]").
    iSplitL.
    { iApply exec_src_update; eauto. eapply exec_frame. apply lev_Lev. }
    iIntros "H". iExists _. iFrame. iPureIntro.
    rewrite /Lev/lev. intros Heq%fill_inj. congruence. }
  iIntros "(Hsrc&$)".  iApply rswp_do_step. iNext. rewrite /Lev.
  wp_pures.
  iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
  iMod (stringRel_inv_acc with "Hinv2") as "Hstr2".
  destruct s1 as [| n1 s1].
  {
    iDestruct "Hstr1" as (l1a l1b (->&->)) "(Hl1a&Hl1b)".
    iDestruct "Hstr2" as (l2a l2b (->&->)) "(Hl2a&Hl2b)".
    iDestruct "Hl1a" as (q1a) "Hl1a".
    iDestruct "Hl1b" as (q1b) "Hl1b".
    do 6 src_pure _ in "Hsrc".
    src_load in "Hsrc".
    do 4 src_pure _ in "Hsrc".
    iDestruct ("Hstrlen" $! _ _ O with "[] [$Hsrc]") as "Hstr1".
    { rewrite /imm_stringRel. iExists _; eauto. }
    wp_load. wp_pures. wp_pure _; first solve_vals_compare_safe. wp_pures.
    iApply (rwp_wand with "[Hstr1 Hna]").
    { wp_apply ("Hstr1" with "[$]"). }
    iIntros (v) "(Hna&H)".
    iDestruct "H" as (? (r1&Heq1&Heq2)) "(_&Hsrc&#Heval1)".
    iFrame.
    subst. wp_pures.
    simpl fill. iExists _. iSplit; first eauto. iFrame.
    iModIntro. rewrite /eval. iIntros (vb') "#HPre". iIntros (K') "H".
    iDestruct "HPre" as (v1a v2a v1b v2b Heq1 Heq2) "(Hs1&Hs2)". subst.
    symmetry in Heq1. inversion_clear Heq1. subst.
    iDestruct "Hs1" as (s1') "#Hinv1'".
    iDestruct "Hs2" as (s2') "#Hinv2'".
    iApply fupd_src_update.
    iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
    iMod (stringRel_inv_acc with "Hinv2") as "Hstr2".
    iMod (stringRel_inv_acc with "Hinv1'") as "Hstr1'".
    iMod (stringRel_inv_acc with "Hinv2'") as "Hstr2'".
    iDestruct (stringRel_is_functional with "Hstr1' Hstr1") as %->.
    iDestruct (stringRel_is_functional with "Hstr2' Hstr2") as %->.
    iClear "Hstr1 Hstr2".
    iRename "Hstr1'" into "Hstr1".
    iRename "Hstr2'" into "Hstr2".
    iDestruct "Hstr1" as (?? (->&->)) "(Hl1a&Hl1b)".
    iDestruct "Hstr2" as (?? (->&->)) "(Hl2a&Hl2b)".
    iDestruct "Hl1a" as (q1a') "Hl1a".
    iDestruct "Hl1b" as (q1b') "Hl1b".
    iModIntro.
    rewrite /Lev/lev/lev_template.
    do 12 src_pure _ in "H".
    src_load in "H".
    do 4 src_pure _ in "H".
    iApply src_update_weak_src_update.
    iDestruct ("Heval1" with "[]") as (v') "(Heval1'&Hrel)"; last first.
    { iDestruct "Hrel" as %[? (->&->)]. iApply "Heval1'". eauto. }
    rewrite /imm_stringRel. eauto.
  }
  iDestruct "Hstr1" as (l1a l1b (->&->)) "(Hl1a&Hl1b)".
  iDestruct "Hstr2" as (l2a l2b (->&->)) "(Hl2a&Hl2b)".
  simpl string_is.
  iDestruct "Hl1a" as (H1neq0) "(Hpts1a&Hl1a)".
  iDestruct "Hpts1a" as (?) "Hpts1a".
  wp_load. wp_pures. wp_pure _; first solve_vals_compare_safe.
  rewrite bool_decide_false //; last first.
  { intros Heq. inversion Heq. lia. }
  wp_pures.
  destruct s2 as [| n2 s2].
  {
    simpl src_string_is.
    iDestruct "Hl2a" as (q2a) "Hl2a".
    iDestruct "Hl1b" as (H1neq0') "(Hpts1b&Hl1b)".
    iDestruct "Hpts1b" as (?) "Hpts1b".
    wp_load. wp_pures. wp_pure _; first solve_vals_compare_safe.
    wp_pure _.
    do 6 src_pure _ in "Hsrc".
    src_load in "Hsrc".
    do 3 src_pure _ in "Hsrc".
    rewrite bool_decide_false //; last first.
    { intros Heq. inversion Heq. lia. }
    do 1 src_pure _ in "Hsrc".
    iDestruct "Hl2b" as (q2b) "Hl2b".
    src_load in "Hsrc".
    do 4 src_pure _ in "Hsrc".
    iDestruct ("Hstrlen" $! _ _ O with "[] [$Hsrc]") as "Hstr2".
    { rewrite /imm_stringRel. iExists _; eauto. }
    iApply (rwp_wand with "[Hstr2 Hna]").
    { wp_apply ("Hstr2" with "[$]"). }
    iIntros (v) "(Hna&H)".
    iDestruct "H" as (? (r1&Heq1&Heq2)) "(_&Hsrc&#Heval1)".
    iFrame.
    subst. wp_pures.
    simpl fill. iExists _. iSplit; first eauto. iFrame.
    iModIntro. rewrite /eval. iIntros (vb') "#HPre". iIntros (K') "H".
    iDestruct "HPre" as (v1a v2a v1b v2b Heq1 Heq2) "(Hs1&Hs2)". subst.
    symmetry in Heq1. inversion_clear Heq1. subst.
    iDestruct "Hs1" as (s1') "#Hinv1'".
    iDestruct "Hs2" as (s2') "#Hinv2'".
    iApply fupd_src_update.
    iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
    iMod (stringRel_inv_acc with "Hinv2") as "Hstr2".
    iMod (stringRel_inv_acc with "Hinv1'") as "Hstr1'".
    iMod (stringRel_inv_acc with "Hinv2'") as "Hstr2'".
    iDestruct (stringRel_is_functional with "Hstr1' Hstr1") as %->.
    iDestruct (stringRel_is_functional with "Hstr2' Hstr2") as %->.
    iClear "Hstr1 Hstr2".
    iRename "Hstr1'" into "Hstr1".
    iRename "Hstr2'" into "Hstr2".
    iDestruct "Hstr1" as (?? (->&->)) "(Hl1a&Hl1b)".
    iDestruct "Hstr2" as (?? (->&->)) "(Hl2a&Hl2b)".
    simpl src_string_is.
    iDestruct "Hl1b" as (H1neq0'') "(Hpts1b&Hl1b)".
    iDestruct "Hpts1b" as (?) "Hpts1b".
    rewrite /Lev/lev/lev_template.
    iModIntro.
    do 12 src_pure _ in "H".
    src_load in "H".
    do 3 src_pure _ in "H".
    rewrite bool_decide_false //; last first.
    { intros Heq. inversion Heq. lia. }
    do 1 src_pure _ in "H".
    iDestruct "Hl2b" as (q2b') "Hl2b".
    src_load in "H".
    do 4 src_pure _ in "H".
    iApply src_update_weak_src_update.
    iDestruct ("Heval1" with "[]") as (v') "(Heval1'&Hrel)"; last first.
    { iDestruct "Hrel" as %[? (->&->)]. iApply "Heval1'". eauto. }
    rewrite /imm_stringRel. eauto.
  }
  simpl string_is.
  iDestruct "Hl2a" as (H2neq0) "(Hpts2a&Hl2a)".
  iDestruct "Hpts2a" as (q2a) "Hpts2a".
  wp_load. wp_pures. wp_pure _; first solve_vals_compare_safe.
  rewrite bool_decide_false //; last first.
  { intros Heq. inversion Heq. lia. }
  wp_pures. wp_pure _; first solve_vals_compare_safe.
  rewrite /tf_implements.
  simpl src_string_is.
  iDestruct "Hl1b" as (H1neq0') "(Hpts1b&Hl1b)".
  iDestruct "Hpts1b" as (?) "Hpts1b".
  iDestruct "Hl2b" as (H2neq0') "(Hpts2b&Hl2b)".
  iDestruct "Hpts2b" as (?) "Hpts2b".
  do 6 src_pure _ in "Hsrc".
  src_load in "Hsrc".
  do 3 src_pure _ in "Hsrc".
  rewrite bool_decide_false //; last first.
  { intros Heq. inversion Heq. lia. }
  do 1 src_pure _ in "Hsrc".
  src_load in "Hsrc".
  do 3 src_pure _ in "Hsrc".
  rewrite bool_decide_false //; last first.
  { intros Heq. inversion Heq. lia. }
  do 2 src_pure _ in "Hsrc".
  iAssert (pair_imm_stringRel (#(l1a +ₗ 1), #(l2a +ₗ 1)) (#(l1b +ₗ 1), #(l2b +ₗ 1))) as "#Hshift_both".
  {
    iExists #(l1a +ₗ 1), #(l2a +ₗ 1), _, _.
    rewrite /imm_stringRel.
    iSplit; first eauto.
    iSplit; first eauto.
    iSplitL "Hinv1".
    { iExists _. iApply inv_stringRel_is_tl. iApply "Hinv1". }
    { iExists _. iApply inv_stringRel_is_tl. iApply "Hinv2". }
  }
  iAssert (pair_imm_stringRel ((#l1a, #(l2a +ₗ 1)))%V ((#l1b, #(l2b +ₗ 1)))%V) as "#Hshift_right".
  {
    iExists #(l1a), #(l2a +ₗ 1), _, _.
    rewrite /imm_stringRel.
    iSplit; first eauto.
    iSplit; first eauto.
    iSplitL "Hinv1".
    { iExists _. iApply "Hinv1". }
    { iExists _. iApply inv_stringRel_is_tl. iApply "Hinv2". }
  }
  iAssert (pair_imm_stringRel (#(l1a +ₗ 1), #l2a) (#(l1b +ₗ 1), #l2b)) as "#Hshift_left".
  {
    iExists #(l1a +ₗ 1), #(l2a), _, _.
    rewrite /imm_stringRel.
    iSplit; first eauto.
    iSplit; first eauto.
    iSplitL "Hinv1".
    { iExists _. iApply inv_stringRel_is_tl. iApply "Hinv1". }
    { iExists _. iApply "Hinv2". }
  }
  case_bool_decide.
  {
    do 2 wp_pure _.
    do 4 src_pure _ in "Hsrc".
    rewrite /tf_implements.
    iSpecialize ("IH" $! (#(l1a +ₗ 1), #(l2a +ₗ 1))%V _ O with "[$] Hsrc [$]").
    iApply (rwp_wand with "[IH]").
    { wp_apply "IH". }
    iIntros (v) "($&H)".
    iDestruct "H" as (? (m&Heq1&Heq2)) "(_&Hsrc&#Heval')".
    subst. iExists m. iSplit; first done.
    iFrame.
    iModIntro. rewrite /eval. iIntros (vb') "#HPre". iIntros (K') "H".
    iDestruct "HPre" as (v1a v2a v1b v2b Heq1 Heq2) "(Hs1&Hs2)". subst.
    symmetry in Heq1. inversion_clear Heq1. subst.
    iDestruct "Hs1" as (s1') "#Hinv1'".
    iDestruct "Hs2" as (s2') "#Hinv2'".
    iApply fupd_src_update.
    iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
    iMod (stringRel_inv_acc with "Hinv2") as "Hstr2".
    iMod (stringRel_inv_acc with "Hinv1'") as "Hstr1'".
    iMod (stringRel_inv_acc with "Hinv2'") as "Hstr2'".
    iDestruct (stringRel_is_functional with "Hstr1' Hstr1") as %->.
    iDestruct (stringRel_is_functional with "Hstr2' Hstr2") as %->.
    iClear "Hstr1 Hstr2".
    iRename "Hstr1'" into "Hstr1".
    iRename "Hstr2'" into "Hstr2".
    iModIntro.
    rewrite /Lev/lev/lev_template.
    do 12 src_pure _ in "H".
    iDestruct "Hstr1" as (?? (Heq1a&Heq1b)) "(Hl1a&Hl1b)".
    iDestruct "Hstr2" as (?? (Heq2a&Heq2b)) "(Hl2a&Hl2b)".
    simpl src_string_is.
    iDestruct "Hl1b" as (H1neq0'') "(Hpts1b&Hl1b)".
    iDestruct "Hpts1b" as (?) "Hpts1b".
    rewrite ?Heq1a ?Heq1b ?Heq2a ?Heq2b.
    src_load in "H".
    do 3 src_pure _ in "H".
    rewrite bool_decide_false //; last first.
    { intros Heq. inversion Heq. lia. }
    do 1 src_pure _ in "H".
    iDestruct "Hl2b" as (H2neq0'') "(Hpts2b&Hl2b)".
    iDestruct "Hpts2b" as (?) "Hpts2b".
    src_load in "H".
    do 3 src_pure _ in "H".
    rewrite bool_decide_false //; last first.
    { intros Heq. inversion Heq. lia. }
    do 2 src_pure _ in "H".
    rewrite bool_decide_true //; [].
    do 4 src_pure _ in "H".
    rewrite -?Heq1a -?Heq1b -?Heq2a -?Heq2b.
    iApply src_update_weak_src_update.
    iDestruct ("Heval'" with "[]") as (v') "(Heval1&Hrel)"; last first.
    { iDestruct "Hrel" as %[? (->&->)]. iApply "Heval1". eauto. }
    {
      iExists _, _, _, _; repeat (iSplit; try iExists _; eauto).
      { iApply inv_stringRel_is_tl. rewrite Heq1b. eauto. }
      { iApply inv_stringRel_is_tl. rewrite Heq2b. eauto. }
    }
  }
  do 3 wp_pure _.
  do 3 src_pure _ in "Hsrc".
  src_bind (lev _) in "Hsrc".
  iDestruct ("IH" $! _ _ O with "Hshift_right Hsrc [$]") as "IH1".
  wp_bind (g _).
  iApply (rwp_wand with "[IH1]").
  { wp_apply "IH1". }
  iIntros (v) "(Hna&H)".
  iDestruct "H" as (? (r1&Heq1&Heq2)) "(_&Hsrc&#Heval1)".
  subst. wp_pures.
  simpl fill.
  do 1 src_pure _ in "Hsrc".

  do 3 src_pure _ in "Hsrc".
  src_bind (lev _) in "Hsrc".
  iDestruct ("IH" $! _ _ O with "Hshift_left Hsrc [$]") as "IH2".
  wp_bind (g _).
  iApply (rwp_wand with "[IH2]").
  { wp_apply "IH2". }
  iIntros (v) "(Hna&H)".
  iDestruct "H" as (? (r2&Heq1&Heq2)) "(_&Hsrc&#Heval2)".
  subst. wp_pures.
  simpl fill.
  do 2 src_pure _ in "Hsrc".

  do 3 src_pure _ in "Hsrc".
  src_bind (lev _) in "Hsrc".
  iDestruct ("IH" $! _ _ O with "Hshift_both Hsrc [$]") as "IH2".
  wp_bind (g _).
  iApply (rwp_wand with "[IH2]").
  { wp_apply "IH2". }
  iIntros (v) "(Hna&H)".
  iDestruct "H" as (? (r3&Heq1&Heq2)) "(_&Hsrc&#Heval3)".
  subst. wp_pures.
  simpl fill.
  do 2 src_pure _ in "Hsrc".

  wp_bind (min3 _ _ _).
  wp_apply (min3_spec with "[//]").
  iIntros "_".
  src_bind (min3 _ _ _) in "Hsrc".
  iDestruct (eval_min3 with "Hsrc") as "Hsrc".
  iApply (rwp_weaken with "[-Hsrc] Hsrc"); first done.
  iIntros "Hsrc".
  simpl fill.
  src_pure _ in "Hsrc".
  wp_pures. iFrame. iExists (1 + (min (min r1 r2) r3)%nat)%nat.
  iSplit.
  { iPureIntro. do 2 f_equal. lia. }
  assert (#(1 + (r1 `min` r2) `min` r3)%nat =
          #(1 + ((r1 `min` r2) `min` r3)%nat)) as ->.
  { do 2 f_equal. lia. }
  iFrame.
  iModIntro. rewrite /eval. iIntros (vb') "#HPre". iIntros (K') "H".
  iDestruct "HPre" as (v1a v2a v1b v2b Heq1 Heq2) "(Hs1&Hs2)". subst.
  symmetry in Heq1. inversion_clear Heq1. subst.
  iDestruct "Hs1" as (s1') "#Hinv1'".
  iDestruct "Hs2" as (s2') "#Hinv2'".
  iApply fupd_src_update.
  iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
  iMod (stringRel_inv_acc with "Hinv2") as "Hstr2".
  iMod (stringRel_inv_acc with "Hinv1'") as "Hstr1'".
  iMod (stringRel_inv_acc with "Hinv2'") as "Hstr2'".
  iDestruct (stringRel_is_functional with "Hstr1' Hstr1") as %->.
  iDestruct (stringRel_is_functional with "Hstr2' Hstr2") as %->.
  iClear "Hstr1 Hstr2".
  iRename "Hstr1'" into "Hstr1".
  iRename "Hstr2'" into "Hstr2".
  iModIntro.
  rewrite /Lev/lev/lev_template.
  do 12 src_pure _ in "H".
  iDestruct "Hstr1" as (?? (Heq1a&Heq1b)) "(Hl1a&Hl1b)".
  iDestruct "Hstr2" as (?? (Heq2a&Heq2b)) "(Hl2a&Hl2b)".
  simpl src_string_is.
  iDestruct "Hl1b" as (H1neq0'') "(Hpts1b&Hl1b)".
  iDestruct "Hpts1b" as (?) "Hpts1b".
  rewrite ?Heq1a ?Heq1b ?Heq2a ?Heq2b.
  src_load in "H".
  do 3 src_pure _ in "H".
  rewrite bool_decide_false //; last first.
  { intros Heq. inversion Heq. lia. }
  do 1 src_pure _ in "H".
  iDestruct "Hl2b" as (H2neq0'') "(Hpts2b&Hl2b)".
  iDestruct "Hpts2b" as (?) "Hpts2b".
  src_load in "H".
  do 3 src_pure _ in "H".
  rewrite bool_decide_false //; last first.
  { intros Heq. inversion Heq. lia. }
  do 2 src_pure _ in "H".
  rewrite bool_decide_false //; [].
  do 1 src_pure _ in "H".
  do 1 src_pure _ in "H".
  do 1 src_pure _ in "H".
  src_bind (_ (#_, #_)%V)%E in "H".
  (* TODO: can't seem to bind this properly otherwise *)
  rewrite fill_cons. simpl ectxi_language.fill_item.
  iApply src_update_weak_src_update.
  iDestruct ("Heval1" with "[]") as (r1') "(Heval1'&Hrel)"; [|
  iDestruct "Hrel" as %[? (Heq1&->)]; iDestruct ("Heval1'" with "H") as "H"].
  {
      iExists _, _, _, _; repeat (iSplit; try iExists _; eauto).
      { iApply inv_stringRel_is_tl. rewrite Heq1b Heq2a. eauto. }
  }
  iApply (src_update_bind with "[$H]").
  iIntros "H".
  simpl.
  do 2 src_pure _ in "H".

  do 2 src_pure _ in "H".
  src_bind (_ (#_, #_)%V)%E in "H".
  (* TODO: can't seem to bind this properly otherwise *)
  rewrite fill_cons. simpl ectxi_language.fill_item.
  iApply src_update_weak_src_update.
  iDestruct ("Heval2" with "[]") as (r2') "(Heval2'&Hrel)"; [|
  iDestruct "Hrel" as %[? (Heq2&->)]; iDestruct ("Heval2'" with "H") as "H"].
  {
      iExists _, _, _, _; repeat (iSplit; try iExists _; eauto).
      { iApply inv_stringRel_is_tl. rewrite Heq1a Heq2b. eauto. }
  }
  iApply (src_update_bind with "[$H]").
  iIntros "H".
  simpl.
  do 2 src_pure _ in "H".

  do 3 src_pure _ in "H".
  src_bind (_ (#_, #_)%V)%E in "H".
  (* TODO: can't seem to bind this properly otherwise *)
  rewrite fill_cons. simpl ectxi_language.fill_item.
  iApply src_update_weak_src_update.
  iDestruct ("Heval3" with "[]") as (r3') "(Heval3'&Hrel)"; [|
    iDestruct "Hrel" as %[? (Heq3&->)]; iDestruct ("Heval3'" with "H") as "H"].
  {
      iExists _, _, _, _; repeat (iSplit; try iExists _; eauto).
      { iApply inv_stringRel_is_tl. rewrite Heq1a Heq2b. eauto. }
      { iApply inv_stringRel_is_tl. rewrite Heq1b Heq2a. eauto. }
  }
  iApply (src_update_bind with "[$H]").
  iIntros "H".
  simpl.
  do 2 src_pure _ in "H".
  rewrite -Heq1 -Heq2 -Heq3.

  src_bind (min3 _ _ _) in "H".
  iDestruct (eval_min3 with "[$]") as "H".
  iApply src_update_weak_src_update.
  iApply (src_update_bind with "[$H]").
  iIntros "H". simpl.
  do 1 src_pure _ in "H".
  iApply weak_src_update_return.
  iApply "H".
  Qed.

  Definition eq_pair : val := (λ: "n1" "n2", BinOp AndOp (Fst "n1" = Fst "n2") (Snd "n1" = Snd "n2")).

  Lemma strlen_sound :
    ⊢ tf_implements imm_stringRel natRel strlen strlen.
  Proof.
    iLöb as "IH".
    iModIntro. iIntros (?? c K) "#HPre Hsrc Hna".
    iDestruct "HPre" as (s) "#Hinv1".
    rewrite {4}/strlen. wp_pure _. rewrite {1}/strlen_template. do 3 wp_pure _.
    iPoseProof (strlen_fundamental_core strlen c K _ with "[Hsrc IH] Hna") as "H".
    { iFrame "Hsrc IH". iExists _. eauto. }
    iApply (rwp_wand with "H").
    iIntros (v) "($&H)".
    iDestruct "H" as (m ->) "(Hsrc&Hc&#Hexec)". iExists _. iFrame.
    iSplitR; first eauto.
    iModIntro. iIntros (x) "#Hrel". iExists #m. iSplit; last eauto.
    iModIntro. iApply "Hexec". eauto.
  Qed.

  Lemma strlen_template_sound g:
    ▷ tf_implements imm_stringRel natRel g strlen ⊢
      SEQ (strlen_template g) ⟨⟨h, tf_implements imm_stringRel natRel h strlen⟩⟩.
  Proof.
    iIntros "#IH Hna". rewrite /strlen_template. wp_pures. iFrame.
    iModIntro; iIntros (? ? c K) "HPre Hsrc Hna".
    wp_pure _.
    iDestruct "HPre" as (s1) "#Hinv1".
    iPoseProof (strlen_fundamental_core g c K _ with "[$Hsrc $IH] Hna") as "H".
    { iExists _. repeat iSplit; try iExists _; eauto. }
    rewrite /Strlen.
    iApply (rwp_wand with "H").
    iIntros (v) "($&H)".
    iDestruct "H" as (m ->) "(Hsrc&Hc&#Hexec)". iExists _. iFrame.
    iSplitR; first eauto.
    iModIntro. iIntros (x) "#Hrel". iExists #m. iSplit; last eauto.
    iModIntro. iApply "Hexec". eauto.
  Qed.

  Lemma lev_sound:
    ⊢ tf_implements pair_imm_stringRel natRel lev lev.
  Proof.
    iLöb as "IH".
    iModIntro. iIntros (v v' c K) "#HPre Hsrc Hna".
    iDestruct "HPre" as (v1a v2a v1b v2b Heq1 Heq2) "(Hs1&Hs2)". subst.
    iDestruct "Hs1" as (s1) "#Hinv1".
    iDestruct "Hs2" as (s2) "#Hinv2".
    rewrite {4}/lev. wp_pure _. rewrite {1}/lev_template. do 3 wp_pure _.
    iPoseProof (lev_fundamental_core lev strlen c K (v1a, v2a)%V with "[Hsrc IH] Hna") as "H".
    { iFrame "Hsrc". iSplitL.
      { iNext. iApply strlen_sound. }
      iFrame "IH".
      { iExists _, _, _, _. repeat iSplit; try iExists _; eauto. }
    }
    rewrite /Lev/lev.
    do 2 wp_pure _.
    iApply (rwp_wand with "H").
    iIntros (v) "($&H)".
    iDestruct "H" as (m ->) "(Hsrc&Hc&#Hexec)". iExists _. iFrame.
    iSplitR; first eauto.
    iModIntro. iIntros (x) "#Hrel". iExists #m. iSplit; last eauto.
    iModIntro. iApply "Hexec". eauto.
  Qed.

  Lemma lev_template'_sound g slen:
    ▷ tf_implements imm_stringRel natRel slen strlen ∗
    ▷ tf_implements pair_imm_stringRel natRel g lev ⊢
      SEQ (lev_template' slen g) ⟨⟨h, tf_implements pair_imm_stringRel natRel h lev⟩⟩.
  Proof.
    iIntros "[#Hslen #IH] Hna". rewrite /lev_template'. wp_pures. iFrame.
    iModIntro; iIntros (n n' c K) "HPre Hsrc Hna".
    wp_pure _.
    iDestruct "HPre" as (v1a v2a v1b v2b Heq1 Heq2) "(Hs1&Hs2)". subst.
    iDestruct "Hs1" as (s1) "#Hinv1".
    iDestruct "Hs2" as (s2) "#Hinv2".
    iPoseProof (lev_fundamental_core g slen c K (v1a, v2a)%V with "[$Hslen $Hsrc $IH] Hna") as "H".
    { iExists _, _, _, _. repeat iSplit; try iExists _; eauto. }
    rewrite /Lev.
    iApply (rwp_wand with "H").
    iIntros (v) "($&H)".
    iDestruct "H" as (m ->) "(Hsrc&Hc&#Hexec)". iExists _. iFrame.
    iSplitR; first eauto.
    iModIntro. iIntros (x) "#Hrel". iExists #m. iSplit; last eauto.
    iModIntro. iApply "Hexec". eauto.
  Qed.

  (* memoized versions *)
  Context `{Sync: !inG Σ (authR (optionUR (exclR (gmapO val (valO SI)))))}.
  Context `{Fin: FiniteBoundedExistential SI}.

  Lemma lev_memoized:
    $ (1%nat) ⊢ SEQ (memoize eq_pair lev) ⟨⟨ h, tf_implements pair_imm_stringRel natRel h lev ⟩⟩.
  Proof using Sync Fin.
    (* XXX: the iApply fails over typeclass resolution (?) if we don't do iStartProof *)
    iStartProof. iIntros "Hc".
    iApply (tf_memoize_spec _ _ (λ x, ∃ (l1 l2: loc), ⌜ x = (#l1, #l2)%V ⌝)%I (λ x1 x2, ⌜ x1 = x2 ⌝)%I);
      [| | iSplit].
    - iIntros (??) "HPre".
      iDestruct "HPre" as (v1a v2a v1b v2b Heq1 Heq2) "(Hs1&Hs2)". subst.
      iDestruct "Hs1" as (s1) "#Hinv1".
      iDestruct "Hs2" as (s2) "#Hinv2".
      iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
      iMod (stringRel_inv_acc with "Hinv2") as "Hstr2".
      iDestruct "Hstr1" as (?? (->&->)) "(Hl1a&Hl1b)".
      iDestruct "Hstr2" as (?? (->&->)) "(Hl2a&Hl2b)".
      eauto.
    - iIntros (??? ->); auto.
    - rewrite /eqfun.  iIntros (??). iModIntro. iIntros (Φ) "(H1&H2) H".
      iDestruct "H1" as %[l1 [l2 ->]].
      iDestruct "H2" as %[l1' [l2' ->]].
      rewrite /eq_pair.
      wp_pures.
      wp_pure _; first solve_vals_compare_safe.
      wp_pure _.
      case_bool_decide;
       (wp_pures; wp_pure _; first solve_vals_compare_safe;
        case_bool_decide; (wp_pures; iApply "H"; iSplitL; [| iSplitL]; eauto; iPureIntro; congruence)).
    - iFrame. iApply lev_sound.
  Qed.

  Lemma lev_deep_memoized:
    $ (1%nat) ∗ $ (1%nat) ⊢
      SEQ (let: "strlen" := mem_rec eq_heaplang strlen_template in
                 mem_rec eq_pair (lev_template "strlen"))
      ⟨⟨ h, tf_implements pair_imm_stringRel natRel h lev ⟩⟩.
  Proof using Sync Fin.
    iStartProof. iIntros "(Hc1&Hc2) Hna".
    wp_bind (mem_rec _ _).
    iPoseProof (tf_mem_rec_spec imm_stringRel natRel
                                (λ x, ∃ l1 : loc, ⌜ x = #l1%V ⌝)%I (λ x1 x2, ⌜ x1 = x2 ⌝)%I with "[Hc1] [$Hna]")
    as "IH"; last (iApply (rwp_wand with "IH")).
    { iIntros (??) "HPre". iDestruct "HPre" as (s1) "#Hinv1".
      iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
      iDestruct "Hstr1" as (?? (->&->)) "(Hl1a&Hl1b)". eauto. }
    { iIntros (??? ->); auto. }
    {  iSplit.
      { rewrite /eqfun.  iIntros (??). iModIntro. iIntros (Φ) "(H1&H2) H".
        iDestruct "H1" as %[l1 ->].
        iDestruct "H2" as %[l1' ->].
        rewrite /eq_heaplang.
        wp_pures.
        wp_pure _; first solve_vals_compare_safe.
        case_bool_decide; eauto; iApply "H"; eauto. }
      iFrame.
      iModIntro. iIntros.
      iApply strlen_template_sound. eauto.
    }
    iIntros (h) "(Hna&#Himpl)".
    wp_pures.
    rewrite /lev_template. wp_pure _. wp_pure _.
    iApply (tf_mem_rec_spec _ _ (λ x, ∃ (l1 l2: loc), ⌜ x = (#l1, #l2)%V ⌝)%I (λ x1 x2, ⌜ x1 = x2 ⌝)%I with "[Hc2] [$Hna]"); [| | iSplit].
    - iIntros (??) "HPre".
      iDestruct "HPre" as (v1a v2a v1b v2b Heq1 Heq2) "(Hs1&Hs2)". subst.
      iDestruct "Hs1" as (s1) "#Hinv1".
      iDestruct "Hs2" as (s2) "#Hinv2".
      iMod (stringRel_inv_acc with "Hinv1") as "Hstr1".
      iMod (stringRel_inv_acc with "Hinv2") as "Hstr2".
      iDestruct "Hstr1" as (?? (->&->)) "(Hl1a&Hl1b)".
      iDestruct "Hstr2" as (?? (->&->)) "(Hl2a&Hl2b)".
      eauto.
    - iIntros (??? ->); auto.
    - rewrite /eqfun.  iIntros (??). iModIntro. iIntros (Φ) "(H1&H2) H".
      iDestruct "H1" as %[l1 [l2 ->]].
      iDestruct "H2" as %[l1' [l2' ->]].
      rewrite /eq_pair.
      wp_pures.
      wp_pure _; first solve_vals_compare_safe.
      wp_pure _.
      case_bool_decide;
       (wp_pures; wp_pure _; first solve_vals_compare_safe;
        case_bool_decide; (wp_pures; iApply "H"; iSplitL; [| iSplitL]; eauto; iPureIntro; congruence)).
    - iFrame. iModIntro. iIntros (g) "H".
      iPoseProof (lev_template'_sound with "[H]") as "H".
      { iSplitR.
        * iApply "Himpl".
        * iApply "H".
      }
      iApply "H".
  Qed.
End levenshtein.

