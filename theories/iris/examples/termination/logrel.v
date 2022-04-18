
From iris.program_logic.refinement Require Export seq_weakestpre.
From iris.base_logic.lib Require Export invariants na_invariants.
From iris.heap_lang Require Export lang lifting.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation metatheory.
From iris.algebra Require Import auth.
From iris.algebra.ordinals Require Import arithmetic.
Set Default Proof Using "Type".



Section token_ra.
  Context {SI: indexT} {Σ: gFunctors SI} `{!inG Σ (authR (unitUR SI))}.

  Definition tok γ := own γ (● ()).

  Lemma tok_alloc: ⊢ (|==> ∃ γ, tok γ)%I.
  Proof.
    iStartProof. iMod (own_alloc (● ())); auto.
    by apply auth_auth_valid.
  Qed.

  Lemma tok_unique γ: tok γ ∗ tok γ ⊢ False.
  Proof.
    rewrite /tok -own_op own_valid -auth_auth_frac_op uPred.discrete_valid.
    iIntros (Htok). apply ->(@auth_auth_frac_valid SI) in Htok.
    destruct Htok as [Htok _]. apply ->(@frac_valid' SI) in Htok.
    exfalso. by eapply Qp_not_plus_q_ge_1.
  Qed.

End token_ra.




(* the heap values for empty, value, and computation *)
Definition div : expr := (rec: "f" "x" := "f" "x") #().
Definition E : expr := InjL #().
Definition V (e: expr): expr := InjR (InjL e).
Definition C (e: expr): expr := InjR (InjR e).
Definition EV : val := InjLV #().
Definition VV (v: val): val := InjRV (InjLV v).
Definition CV (v: val): val := InjRV (InjRV v).
Definition caseof : val :=
  λ: "e" "e_empty" "e_val" "e_cont",
  match: "e" with
    InjL <> => "e_empty" #()
  | InjR "x" =>
    match: "x" with
    InjL "v" => "e_val" "v"
    | InjR "f" => "e_cont" "f"
    end
  end.
Notation "'case' e 'of' 'E' => e1 | 'V' v => e2 | 'C' c => e3 'end'" := (caseof e (λ: <>, e1)%E (λ: v, e2)%E (λ: c, e3)%E).

Definition letpair : val :=
  λ: "p" "f", "f" (Fst "p") (Snd "p").

Notation "'let:' ( x , y ) := p 'in' e" := (letpair p (λ: x y, e)%E) (at level 200, x at level 1, y at level 1, p, e at level 200, format "'[' 'let:'  ( x , y )  :=  '[' p ']'  'in'  '/' e ']'") : expr_scope.

Definition iter : val :=
  rec: "iter" "s" := λ: "n" "f", if: "n" = #0 then "s" else "iter" ("f" "s") ("n" - #1) "f".

Definition chan : val :=
  λ: <>, let: "c" := ref E in ("c", "c").

Definition put : val :=
  λ: "p",
  let: "c" := Fst "p" in
  let: "v" := Snd "p" in
  case ! "c" of
    E => "c" <- V "v"
  | V <> => div
  | C "f" => "c" <- E;; "f" "v"
  end.

Definition get : val :=
  λ: "p",
  let: "c" := Fst "p" in
  let: "f" := Snd "p" in
  case ! "c" of
    E => "c" <- C "f"
  | V "v" => "c" <- E;; "f" "v"
  | C <> => div
  end.

Section semantic_model.
  Context {SI} {Σ: gFunctors SI} `{Heap: !heapG Σ} `{TimeCredits: !tcG Σ} `{Sequential: !seqG Σ} `{FBI: FiniteBoundedExistential SI} `{Tok: !inG Σ (authR (unitUR SI))}.

  Implicit Types (l r: loc).
  Implicit Types (n: nat).
  Implicit Types (b: bool).
  Implicit Types (e : expr).
  Implicit Types (v f: val).
  Implicit Types (P Q: iProp Σ).
  Implicit Types (Φ Ψ: val → iProp Σ).
  Implicit Types (x y: string).


  Section execution_lemmas.
    Lemma rwp_put_empty l v:
      l ↦ EV ⊢ WP (put (#l, v)%V)%E [{ w, ⌜w = #()⌝ ∗ l ↦ VV v}].
    Proof.
      iIntros "Hl". rewrite /put /caseof. wp_pures. wp_load. wp_pures.
      wp_store. by iFrame.
    Qed.

    Lemma rwp_put_cont l f v Φ:
      l ↦ CV f ∗ WP f v [{ w, Φ w }] ⊢ WP (put (#l, v)%V)%E [{ w, Φ w ∗ l ↦ EV}].
    Proof.
      iIntros "[Hl Hwp]". rewrite /put /caseof. wp_pures. wp_load. wp_pures.
      wp_store. by iFrame "Hl".
    Qed.

    Lemma rwp_get_empty l f:
      l ↦ EV ⊢ WP (get (#l, f)%V)%E [{ w, ⌜w = #()⌝ ∗ l ↦ CV f}].
    Proof.
      iIntros "Hl". rewrite /get /caseof. wp_pures. wp_load. wp_pures.
      wp_store. by iFrame.
    Qed.

    Lemma rwp_get_val l f v Φ:
      l ↦ VV v ∗ WP f v [{ w, Φ w }] ⊢ WP (get (#l, f)%V)%E [{ w, Φ w ∗ l ↦ EV}].
    Proof.
      iIntros "[Hl Hwp]". rewrite /get /caseof. wp_pures. wp_load. wp_pures.
      wp_store. by iFrame "Hl".
    Qed.

    Lemma rwp_chan :
      ⊢ (WP (chan #())%E [{ v, ∃ l, ⌜v = (#l, #l)%V⌝ ∗ l ↦ EV}])%I.
    Proof.
      iStartProof. rewrite /chan. wp_pures. wp_alloc l as "Hl".
      wp_pures. eauto.
    Qed.
  End execution_lemmas.


  Section closed_lemmas.
  (* the channel invariant *)
  Definition ch_inv  γget γput l A :=
    (l ↦ EV ∨ (∃ v, l ↦ VV v ∗ tok γput  ∗ A v) ∨ (∃ f, l ↦ CV f ∗ tok γget ∗ ∀ v, A v -∗ SEQ f v [{ v, ⌜v = #()⌝ }]))%I.

  (* we have a linear type system *)
  Definition lN := nroot .@ "type".
  Definition ltype := val -d> iProp Σ.

  Implicit Types (A B C: ltype).

  (* type interpretations *)
  Definition lunit : ltype := λ v, (⌜v = #()⌝)%I.
  Definition lbool : ltype := λ v, (∃ b, ⌜v = #b⌝)%I.
  Definition lnat : ltype := λ v, (∃ n, ⌜v = #n⌝)%I.
  Definition lget A : ltype := λ v, (∃ l γget γput, ⌜v = #l⌝ ∗ tok γget ∗ se_inv (lN .@ l) (ch_inv γget γput l A) ∗ $ one)%I.
  Definition lput A : ltype := λ v, (∃ l γget γput, ⌜v = #l⌝ ∗ tok γput ∗ se_inv (lN .@ l) (ch_inv γget γput l A) ∗ $ one)%I.
  Definition ltensor A B : ltype := λ v, (∃ v1 v2, ⌜v = (v1, v2)%V⌝ ∗ A v1 ∗ B v2)%I.
  Definition larr A B : ltype := λ f, (∀ v, A v -∗ SEQ f v [{ v, B v }])%I.

  Lemma closed_unit_intro: (SEQ #() [{ v, lunit v }])%I.
  Proof.
    iApply seq_value. by rewrite /lunit.
  Qed.

  Lemma closed_unit_elim e1 e2 Φ: (SEQ e1 [{ v, lunit v}] ∗ SEQ e2 [{ v, Φ v }] ⊢ SEQ e1;;e2 [{ v, Φ v }])%I.
  Proof.
    iIntros "[He He2] Hna". wp_bind e1.
    iMod ("He" with "Hna") as "_". iIntros (v) "[Hna ->] !>".
    wp_pures. by iApply "He2".
  Qed.

  Lemma closed_bool_intro (b: bool): (SEQ #b [{ v, lbool v }])%I.
  Proof.
    iApply seq_value. rewrite /lbool; eauto.
  Qed.

  Lemma closed_bool_elim e e_1 e_2 A P: (SEQ e [{ v, lbool v}] ∗ (P -∗ SEQ e_1 [{ v, A v}]) ∗ (P -∗ SEQ e_2 [{ v, A v}]) ∗ P) ⊢ (SEQ (if: e then e_1 else e_2) [{ v, A v}])%I.
  Proof.
    iIntros "(He & H1 & H2 & P) Hna". wp_bind e.
    iMod ("He" with "Hna") as "_"; iIntros (v) "[Hna Hb] !>"; iDestruct "Hb" as ([]) "->".
    - wp_pures. iApply ("H1" with "P Hna").
    - wp_pures. iApply ("H2" with "P Hna").
  Qed.

  Lemma closed_nat_intro n: (SEQ #n [{ v, lnat v }])%I.
  Proof.
    iApply seq_value. rewrite /lnat; eauto.
  Qed.

  Lemma closed_nat_add e1 e2: (SEQ e1 [{ v, lnat v }] ∗ SEQ e2 [{ v, lnat v }] ⊢ SEQ (e1 + e2) [{ v, lnat v}])%I.
  Proof.
    iIntros "(H1 & H2) Hna".
    wp_bind e2. iMod ("H2" with "Hna") as "_"; iIntros (v2) "[Hna Hv2] !>"; iDestruct "Hv2" as (n2) "->".
    wp_bind e1. iMod ("H1" with "Hna") as "_"; iIntros (v1) "[Hna Hv1] !>"; iDestruct "Hv1" as (n1) "->".
    wp_pures. iFrame. rewrite /lnat; iExists (n1 + n2)%nat. iPureIntro. do 2 f_equal.
    lia.
  Qed.

  Lemma closed_nat_iter_n n s f α A: (SEQ s [{ v, A v }] ∗ (□ $ α -∗ ∀ v, A v -∗ SEQ f v [{ w, A w }]) ∗ $ (natmul n α) ⊢ SEQ (iter s #n f) [{ v, A v}])%I.
  Proof.
    iIntros "(H1 & #H2 & Hc) Hna". iInduction n as [|n] "IH" forall (s); simpl.
    all: wp_bind s; iMod ("H1" with "Hna") as "_"; iIntros (v) "[Hna Hv] !>".
    - rewrite /iter. wp_pures. replace (#0%nat) with (#0) by ((do 2 f_equal); lia).
      wp_pure _; first naive_solver. wp_pures. by iFrame.
    - rewrite tc_split. iDestruct "Hc" as "[Hα Hc]".
      rewrite /iter. wp_pures. wp_pure _; first naive_solver.
      wp_pures. replace (S n - 1) with (n: Z) by lia.
      iApply ("IH" with "[Hα Hv] Hc Hna"). iApply ("H2" with "Hα Hv").
  Qed.


  Lemma closed_nat_iter e1 e2 f α A: (SEQ e1 [{ v, lnat v }] ∗ SEQ e2 [{ v, A v }] ∗ (□ $ α -∗ ∀ v, A v -∗ SEQ f v [{ w, A w }]) ∗ $ (omul α) ⊢ SEQ (iter e2 e1 f) [{ v, A v}])%I.
  Proof.
    iIntros "(H1 & H2 & H3 & Hc) Hna".
    wp_bind e1. iMod ("H1" with "Hna") as "_"; iIntros (v) "[Hna Hv] !>"; iDestruct "Hv" as (n) "->".
    iApply (tc_weaken (omul α) (natmul n α) with "[H2 H3 Hna $Hc]"); auto.
    { eapply (ord_stepindex.limit_upper_bound (λ n, natmul n α)). }
    iIntros "Hα". iApply (closed_nat_iter_n with "[$H2 $H3 $Hα] Hna").
  Qed.

  Lemma closed_fun_intro x e A B: (∀ v, A v -∗ SEQ (subst x v e) [{ w, B w}] ) ⊢ (SEQ (λ: x, e) [{ v, larr A B v}])%I.
  Proof.
    iIntros "H Hna". wp_pures. iFrame. iIntros (v) "Hv Hna". wp_pures.
    by iApply ("H" with "Hv Hna").
  Qed.

  Lemma closed_fun_elim e_1 e_2 A B: (SEQ e_1 [{ v, larr A B v}] ∗ SEQ e_2 [{ v, A v }]) ⊢ (SEQ (e_1 e_2) [{ v, B v}])%I.
  Proof.
    iIntros "(H1 & H2) Hna".
    wp_bind e_2. iMod ("H2" with "Hna") as "_"; iIntros (v) "[Hna HA] !>".
    wp_bind e_1. iMod ("H1" with "Hna") as "_"; iIntros (f) "[Hna HAB] !>".
    iApply ("HAB" with "HA Hna").
  Qed.

  Lemma closed_tensor_intro e_1 e_2 A B: (SEQ e_1 [{ v, A v}] ∗ SEQ e_2 [{ v, B v }]) ⊢ (SEQ (e_1, e_2) [{ v, ltensor A B v}])%I.
  Proof.
    iIntros "(H1 & H2) Hna".
    wp_bind e_2. iMod ("H2" with "Hna") as "_"; iIntros (v2) "[Hna HB] !>".
    wp_bind e_1. iMod ("H1" with "Hna") as "_"; iIntros (v1) "[Hna HA] !>".
    wp_pures. iFrame. iExists v1, v2; by iFrame.
  Qed.

  Lemma closed_tensor_elim x y e1 e2 A B C: x ≠ y → (SEQ e1 [{ v, ltensor A B v }]) ∗ (∀ v1 v2, A v1 -∗ B v2 -∗ SEQ (subst y v2 (subst x v1 e2)) [{ w, C w}]) ⊢ (SEQ (let: (x, y) := e1 in e2) [{ v, C v}])%I.
  Proof.
    iIntros (Hneq) "[H1 H2] Hna". wp_pures. wp_bind e1.
    iMod ("H1" with "Hna") as "_". iIntros (p) "[Hna Hp] !>".
    iDestruct "Hp" as (v1 v2) "(-> & Hv1 & Hv2)".
    rewrite /letpair. wp_pures.
    destruct decide as [H|H].
    - iApply ("H2" with "Hv1 Hv2 Hna").
    - exfalso. apply H; split; auto. by injection 1.
  Qed.


  Lemma closed_get e1 e2 A: SEQ e1 [{ v, lget A v}] ∗ SEQ e2 [{ f, larr A lunit f}] ⊢ SEQ (get (e1, e2)) [{ v, lunit v}].
  Proof using FBI Heap SI Sequential TimeCredits Σ.
    iIntros "[H1 H2] Hna".
    wp_bind e2. iMod ("H2" with "Hna") as "_"; iIntros (f) "[Hna Hf] !>".
    wp_bind e1. iMod ("H1" with "Hna") as "_"; iIntros (?) "[Hna Hloc] !>"; iDestruct "Hloc" as (l γget γput) "(-> & Hget & #I & Hone)".
    iMod (na_inv_acc_open with "I Hna") as "P"; auto.
    iApply (tcwp_burn_credit with "Hone"); first done. iNext. wp_pures. (* we use the step from expressions to values here conventiently *)
    rewrite -tcwp_rwp.
    iDestruct "P" as "([HI|[HI|HI]] & Hna & Hclose)".
    - iMod (rwp_get_empty with "HI") as "_". iIntros (?) "(-> & Hl)".
      iMod ("Hclose" with "[Hf Hl Hget $Hna]") as "Hna".
      { iNext. iRight. iRight. iExists f. iFrame. }
      iModIntro. iFrame. eauto.
    - iDestruct "HI" as (v) "[Hl [Hput Hv]]".
      iSpecialize ("Hf" with "Hv").
      (* we need to close the invariant after the value has been updated before we execute f, since f assumes all invariants *)
      rewrite /get. wp_pures. wp_load. rewrite /caseof. wp_pures.
      wp_store. iApply fupd_rwp.
      iMod ("Hclose" with "[Hl $Hna]") as "Hna".
      { iNext. by iLeft. }
      iApply ("Hf" with "Hna").
    - iDestruct "HI" as (f') "[_ [Hget' _]]".
      iExFalso. iApply (tok_unique with "[$Hget $Hget']").
  Qed.

  Lemma closed_put e1 e2 A: SEQ e1 [{ v, lput A v}] ∗ SEQ e2 [{ v, A v}] ⊢ SEQ (put (e1, e2)) [{ v, lunit v}].
  Proof using FBI Heap SI Sequential TimeCredits Σ.
    iIntros "[H1 H2] Hna".
    wp_bind e2. iMod ("H2" with "Hna") as "_"; iIntros (v) "[Hna Hv] !>".
    wp_bind e1. iMod ("H1" with "Hna") as "_"; iIntros (?) "[Hna Hloc] !>"; iDestruct "Hloc" as (l γget γput) "(-> & Hput & #I & Hone)".
    iMod (na_inv_acc_open with "I Hna") as "P"; auto.
    iApply (tcwp_burn_credit with "Hone"); first done. iNext. wp_pures. (* we use the step from expressions to values here conventiently *)
    rewrite -tcwp_rwp.
    iDestruct "P" as "([HI|[HI|HI]] & Hna & Hclose)".
    - iMod (rwp_put_empty with "HI") as "_". iIntros (?) "(-> & Hl)".
      iMod ("Hclose" with "[Hv Hl Hput $Hna]") as "Hna".
      { iNext. iRight. iLeft. iExists v. iFrame. }
      iModIntro. by iFrame.
    - iDestruct "HI" as (v') "[Hl [Hput' _]]".
      iExFalso. iApply (tok_unique with "[$Hput $Hput']").
    - iDestruct "HI" as (f) "[Hl [Hget Hf]]".
      iSpecialize ("Hf" with "Hv").
      (* we need to close the invariant after the value has been updated before we execute f, since f assumes all invariants *)
      rewrite /put. wp_pures. wp_load. rewrite /caseof. wp_pures.
      wp_store. iApply fupd_rwp.
      iMod ("Hclose" with "[Hl $Hna]") as "Hna".
      { iNext. by iLeft. }
      iApply ("Hf" with "Hna").
  Qed.

  Lemma closed_chan A: $ one ∗ $ one ⊢ SEQ (chan #()) [{ v, ltensor (lget A) (lput A) v}].
  Proof.
    iIntros "[Hone Hone'] Hna".
    iMod (rwp_chan) as "_". iIntros (v) "Hv". iDestruct "Hv" as (l) "[-> Hl]".
    iMod (tok_alloc) as (γget) "Hget".
    iMod (tok_alloc) as (γput) "Hput".
    iMod (na_inv_alloc seqG_name _  (lN .@ l) (ch_inv γget γput l A)  with "[Hl]") as "#I".
    { iNext. by iLeft. }
    iModIntro; rewrite /ltensor /lget /lput; iFrame.
    iExists #l, #l; iSplit; auto.
    iSplitL "Hget"; iExists l, γget, γput; iFrame; eauto.
  Qed.

  End closed_lemmas.

  Section simple_logical_relation.
  (* The semantic typing judgment *)
  Implicit Types (Γ Δ: gmap string ltype).
  Implicit Types (θ τ: gmap string val).

  Definition env_ltyped Γ θ: iProp Σ := ([∗ map] x ↦ A ∈ Γ, ∃ v, ⌜θ !! x = Some v⌝ ∗ A v)%I.
  Definition ltyped Γ e A := ⊢ (∃ α, $ α -∗ ∀ θ, env_ltyped Γ θ -∗ SEQ subst_map θ e [{ v, A v }])%I.
  Notation "Γ ⊨ e : A" := (ltyped Γ e A) (at level 100, e at next level, A at level 200) : bi_scope.

  Lemma env_ltyped_split Γ Δ θ: Γ ##ₘ Δ → env_ltyped (Γ ∪ Δ) θ ⊢ env_ltyped Γ θ ∗ env_ltyped Δ θ.
  Proof.
    intros H. rewrite /env_ltyped. by rewrite big_sepM_union.
  Qed.

  Lemma env_ltyped_empty θ: ⊢ (env_ltyped ∅ θ).
  Proof.
    iStartProof. by rewrite /env_ltyped big_sepM_empty.
  Qed.

  Lemma env_ltyped_insert Γ θ A v x: env_ltyped Γ θ ∗ A v ⊢ env_ltyped (<[x:=A]> Γ) (<[x:=v]> θ).
  Proof.
    iIntros "[HΓ HA]". destruct (Γ !! x) eqn: Hx.
    - rewrite -[<[x:=A]> Γ]insert_delete. iApply (big_sepM_insert_2 with "[HA] [HΓ]"); simpl.
      + iExists v. iFrame. iPureIntro. apply lookup_insert.
      + rewrite /env_ltyped.
        rewrite big_sepM_delete; last apply Hx.
        iDestruct "HΓ" as "[_ HΓ]". iApply (big_sepM_mono with "HΓ").
        iIntros (y B Hy) "Hv"; simpl. iDestruct "Hv" as (w) "[% B]".
        iExists w. iFrame. iPureIntro.
        rewrite lookup_insert_ne; auto.
        intros ->. rewrite lookup_delete in Hy. discriminate.
    - iApply (big_sepM_insert_2 with "[HA] [HΓ]"); simpl.
      + iExists v. iFrame. iPureIntro. apply lookup_insert.
      + rewrite /env_ltyped. iApply (big_sepM_mono with "HΓ").
        iIntros (y B Hy) "Hv"; simpl. iDestruct "Hv" as (w) "[% B]".
        iExists w. iFrame. iPureIntro.
        rewrite lookup_insert_ne; auto.
        intros ->. rewrite Hy in Hx. discriminate.
  Qed.

  Lemma env_ltyped_weaken x A Γ θ: Γ !! x = None → env_ltyped (<[x:=A]> Γ) θ ⊢ env_ltyped Γ θ.
  Proof.
    intros Hx. rewrite insert_union_singleton_l. iIntros "H".
    iPoseProof (env_ltyped_split with "H") as "[_ $]".
    apply map_disjoint_insert_l_2, map_disjoint_empty_l; auto.
  Qed.

  (* the typing rules *)
  Lemma variable x A: ({[ x := A ]} ⊨ x : A)%I.
  Proof.
    iExists ord_stepindex.zero. iIntros "_".
    iIntros (θ) "HΓ". rewrite /env_ltyped.
    iPoseProof (big_sepM_lookup _ _ x A with "HΓ") as "Hx"; first eapply lookup_insert.
    simpl; iDestruct "Hx" as (v) "(-> & HA)".
    by iApply seq_value.
  Qed.

  Lemma weaken x Γ e A B: Γ !! x = None → (Γ ⊨ e : B)%I → (<[ x := A ]> Γ ⊨ e : B)%I.
  Proof.
    intros Hx He. iDestruct He as (α) "He".
    iExists α. iIntros "Hα". iIntros (θ) "Hθ".
    iApply ("He" with "Hα"). by iApply (env_ltyped_weaken with "Hθ").
  Qed.

  Lemma unit_intro: (∅ ⊨ #() : lunit)%I.
  Proof.
    iExists ord_stepindex.zero. iIntros "_".
    iIntros (θ) "HΓ"; simpl. iApply closed_unit_intro.
  Qed.

  Lemma unit_elim Γ Δ e e' A: Γ ##ₘ Δ → (Γ ⊨ e : lunit)%I → (Δ ⊨ e' : A)%I → (Γ ∪ Δ ⊨ (e ;; e'): A)%I.
  Proof.
    intros Hdis He He'. iDestruct He as (α_e) "He". iDestruct He' as (α_e') "He'".
    iExists (α_e ⊕ α_e'). rewrite tc_split. iIntros "[α_e α_e']".
    iIntros (θ). rewrite env_ltyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("He" with "α_e HΓ"). iSpecialize ("He'" with "α_e' HΔ").
    simpl; iApply (closed_unit_elim with "[$He $He']").
  Qed.

  Lemma bool_intro b: (∅ ⊨ #b : lbool)%I.
  Proof.
    iExists ord_stepindex.zero. iIntros "_".
    iIntros (θ) "HΓ"; simpl. iApply closed_bool_intro.
  Qed.

  Lemma bool_elim Γ Δ e e_1 e_2 A: Γ ##ₘ Δ → (Γ ⊨ e : lbool)%I → (Δ ⊨ e_1 : A)%I  → (Δ ⊨ e_2 : A)%I → (Γ ∪ Δ ⊨ (if: e then e_1 else e_2): A)%I.
  Proof.
    intros Hdis He H1 H2. iDestruct He as (α_e) "He". iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_e ⊕ α_1 ⊕ α_2). rewrite !tc_split. iIntros "[[α_e α_1] α_2]".
    iIntros (θ). rewrite env_ltyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("He" with "α_e HΓ"). simpl.
    iApply (closed_bool_elim _ _ _ _ (env_ltyped Δ θ)); iFrame.
    iSplitL "H1 α_1".
    - iApply ("H1" with "α_1").
    - iApply ("H2" with "α_2").
  Qed.

  Lemma nat_intro n: (∅ ⊨ #n : lnat)%I.
  Proof.
    iExists ord_stepindex.zero. iIntros "_".
    iIntros (θ) "HΓ"; simpl. iApply closed_nat_intro.
  Qed.

  Lemma nat_plus e1 e2 Γ Δ: Γ ##ₘ Δ → (Γ ⊨ e1 : lnat)%I → (Δ ⊨ e2 : lnat)%I → (Γ ∪ Δ ⊨ e1 + e2 : lnat)%I.
  Proof.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (θ). rewrite env_ltyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 HΓ"). iSpecialize ("H2" with "α_2 HΔ").
    simpl; iApply (closed_nat_add with "[$H1 $H2]").
  Qed.

  Lemma nat_elim e e_0 e_S x A Γ Δ: Γ ##ₘ Δ → (Γ ⊨ e : lnat)%I → (Δ ⊨ e_0 : A)%I → ({[ x := A ]} ⊨ e_S : A)%I → (Γ ∪ Δ ⊨ iter e_0 e (λ: x, e_S)%V : A)%I.
  Proof.
    intros Hdis He H0 HS.
    iDestruct He as (α_e) "He". iDestruct H0 as (α_0) "H0". iDestruct HS as (α_S) "HS".
    iExists (α_e ⊕ α_0 ⊕ omul α_S). rewrite !tc_split. iIntros "[[α_e α_0] α_S]".
    iIntros (θ). rewrite env_ltyped_split; auto. iIntros "[HΓ HΔ]". simpl.
    iSpecialize ("He" with "α_e HΓ"). iSpecialize ("H0" with "α_0 HΔ").
    simpl; iApply (closed_nat_iter _ _ _ α_S with "[$He $H0 $α_S]").
    iModIntro. iIntros "α_S". iIntros (v) "Hv".
    iIntros "Hna". wp_pures.
    replace e_S with (subst_map (delete x ∅) e_S) at 1; last by rewrite delete_empty subst_map_empty.
    rewrite -subst_map_insert. iApply ("HS" with "α_S [Hv] Hna").
    iApply env_ltyped_insert; iFrame.
    iApply env_ltyped_empty.
  Qed.

  Lemma fun_intro Γ x e A B: ((<[x:=A]> Γ) ⊨ e : B)%I → (Γ ⊨ (λ: x, e) : larr A B)%I.
  Proof.
    intros He. iDestruct He as (α_e) "He". iExists α_e.
    iIntros "α_e". iSpecialize ("He" with "α_e").
    iIntros (θ) "HΓ". simpl.  iApply (closed_fun_intro).
    iIntros (v) "Hv". rewrite -subst_map_insert. iApply ("He" with "[HΓ Hv]").
    iApply (env_ltyped_insert with "[$HΓ Hv]"); first done.
  Qed.

  Lemma fun_elim Γ Δ e1 e2 A B: Γ ##ₘ Δ → (Γ ⊨ e1 : larr A B)%I → (Δ ⊨ e2 : A)%I → (Γ ∪ Δ ⊨ (e1 e2): B)%I.
  Proof.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (θ). rewrite env_ltyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 HΓ"). iSpecialize ("H2" with "α_2 HΔ").
    simpl; iApply (closed_fun_elim with "[$H1 $H2]").
  Qed.

  Lemma tensor_intro Γ Δ e1 e2 A B: Γ ##ₘ Δ → (Γ ⊨ e1 : A)%I → (Δ ⊨ e2 : B)%I → (Γ ∪ Δ ⊨ (e1, e2): ltensor A B)%I.
  Proof.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (θ). rewrite env_ltyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 HΓ"). iSpecialize ("H2" with "α_2 HΔ").
    iApply (closed_tensor_intro with "[$H1 $H2]").
  Qed.

  Lemma tensor_elim Γ Δ x y e1 e2 A B C: x ≠ y → Γ ##ₘ Δ → (Γ ⊨ e1 : ltensor A B)%I → ((<[x := A]> (<[y := B]> Δ)) ⊨ e2 : C)%I → (Γ ∪ Δ ⊨ (let: (x, y) := e1 in e2) : C)%I.
  Proof.
    intros Hne Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (θ). rewrite env_ltyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 HΓ"). simpl. iApply (closed_tensor_elim with "[$H1 HΔ α_2]"); auto.
    iIntros (v1 v2) "Hv1 Hv2".
    rewrite delete_commute -subst_map_insert -delete_insert_ne; auto.
    rewrite -subst_map_insert. iApply ("H2" with "α_2").
    rewrite insert_commute; auto.
    do 2 (iApply env_ltyped_insert; iFrame).
  Qed.

  Lemma chan_alloc A: (∅ ⊨ chan #() : ltensor (lget A) (lput A))%I.
  Proof.
    iExists (one ⊕ one). rewrite tc_split. iIntros "Hcred".
    iIntros (θ) "_"; simpl. iApply (closed_chan A with "Hcred").
  Qed.

  Lemma chan_get Γ Δ e1 e2 A: Γ ##ₘ Δ → (Γ ⊨ e1 : lget A)%I → (Δ ⊨ e2 : larr A lunit)%I → (Γ ∪ Δ ⊨ get (e1, e2)%E: lunit)%I.
  Proof using FBI Heap SI Sequential TimeCredits Σ.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (θ). rewrite env_ltyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 HΓ"). iSpecialize ("H2" with "α_2 HΔ").
    simpl; iApply (closed_get with "[$H1 $H2]").
  Qed.

  Lemma chan_put Γ Δ e1 e2 A: Γ ##ₘ Δ → (Γ ⊨ e1 : lput A)%I → (Δ ⊨ e2 : A)%I → (Γ ∪ Δ ⊨ put (e1, e2)%E: lunit)%I.
  Proof using FBI Heap SI Sequential TimeCredits Σ.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (θ). rewrite env_ltyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 HΓ"). iSpecialize ("H2" with "α_2 HΔ").
    simpl; iApply (closed_put with "[$H1 $H2]").
  Qed.

  End simple_logical_relation.

  Section polymorphic_logical_relation.
  (* The semantic typing judgment *)
  Implicit Types (Ω: gset string) (* the type variables *).
  Implicit Types (δ: gmap string ltype) (* the instantiation of the type variables *).
  Definition lptype := gmap string ltype -d> ltype.

  Implicit Types (Π Ξ: gmap string lptype). (* the variables, given an instantiation of the type variables *)
  Implicit Types (T U: lptype). (* the types *)
  Implicit Types (θ τ: gmap string val).

  Definition subst_cons δ X A := <[X := A]> δ.
  Definition subst_ty (T: lptype) (X: string) U : lptype := λ δ, T (subst_cons δ X (U δ)).
  Definition well_formed Ω δ : iProp Σ := (⌜Ω ≡ dom (gset string) δ⌝)%I.
  Definition well_formed_type Ω T : Prop := (∀ δ δ', (∀ X, X ∈ Ω → δ !! X = δ' !! X) → T δ = T δ').
  Definition well_formed_ctx Ω Π : Prop := (∀ x T, Π !! x = Some T → well_formed_type Ω T).
  Definition env_lptyped Π δ θ : iProp Σ := (env_ltyped (fmap (λ T, T δ) Π) θ)%I.
  Definition lptyped Ω Π e T := ⊢ (∃ α, $ α -∗ ∀ δ, well_formed Ω δ -∗ ∀ θ, env_lptyped Π δ θ -∗ SEQ subst_map θ e [{ v, (T δ) v }])%I.
  Notation "Ω ; Π ⊨ e : T" := (lptyped Ω Π e T) (at level 100, Π at next level, e at next level, T at level 200) : bi_scope.

  (* Notation for well-formedness *)
  Class is_wf (A B: Type) := Is_wf: A → B → Prop.
  Notation "A ⊨ B" := (Is_wf A B) (at level 100, B at level 200).
  Instance: is_wf (gset string) (lptype) := well_formed_type.
  Instance: is_wf (gset string) (gmap string lptype) := well_formed_ctx.

  Definition lpunit : lptype := λ _, lunit.
  Definition lpbool : lptype := λ _, lbool.
  Definition lpnat : lptype := λ _, lnat.
  Definition lpget T : lptype := λ δ, lget (T δ).
  Definition lpput T : lptype := λ δ, lput (T δ).
  Definition lptensor T U : lptype := λ δ, ltensor (T δ) (U δ).
  Definition lparr T U : lptype := λ δ, larr (T δ) (U δ).
  Definition lpforall X (T: lptype) : lptype := λ δ f, (∀ U, SEQ (f #()) [{ u, (subst_ty T X U) δ u }])%I.
  Definition lpexists X (T: lptype) : lptype := λ δ v, (∃ U, (subst_ty T X U) δ v)%I.

  Definition tlam e : expr := λ: <>, e.
  Definition tapp e : expr := e #().
  Definition pack e : expr := e.
  Definition unpack e x e' : expr := (λ: x, e') e.

  Lemma well_formed_empty:
    True ⊢ well_formed ∅ ∅.
  Proof using SI Σ.
    iIntros (Heq). iPureIntro.
    by rewrite dom_empty.
  Qed.


  Lemma well_formed_insert Ω δ X A:
    well_formed Ω δ ⊢ well_formed ({[X]} ∪ Ω) (subst_cons δ X A).
  Proof using SI Σ.
    iIntros (Heq). iPureIntro.
    by rewrite dom_insert Heq.
  Qed.

  Lemma env_lptyped_split Π Ξ δ θ: Π ##ₘ Ξ → env_lptyped (Π ∪ Ξ) δ θ ⊢ env_lptyped Π δ θ ∗ env_lptyped Ξ δ θ.
  Proof.
    intros H. rewrite /env_lptyped /env_ltyped !big_sepM_fmap big_sepM_union; auto.
  Qed.

  Lemma env_lptyped_empty δ θ: sbi_emp_valid (env_lptyped ∅ δ θ).
  Proof.
    iStartProof. by rewrite /env_lptyped /env_ltyped !big_sepM_fmap big_sepM_empty.
  Qed.

  Lemma env_lptyped_insert Π δ θ T v x: env_lptyped Π δ θ ∗ T δ v ⊢ env_lptyped (<[x:=T]> Π) δ (<[x:=v]> θ).
  Proof.
    rewrite /env_lptyped fmap_insert. eapply env_ltyped_insert.
  Qed.

  Lemma env_lptyped_weaken x T Π θ δ: Π !! x = None → env_lptyped (<[x:=T]> Π) δ θ ⊢ env_lptyped Π δ θ.
  Proof.
    intros Hx. rewrite /env_lptyped fmap_insert env_ltyped_weaken //= lookup_fmap Hx //=.
  Qed.

  Lemma env_lptyped_update_type_map Ω Π T δ X θ:
    (Ω ⊨ Π) → (X ∉ Ω) → env_lptyped Π δ θ ⊢ env_lptyped Π (subst_cons δ X (T δ)) θ.
  Proof using SI Σ.
    clear FBI. intros Hwf HX. rewrite /env_lptyped /env_ltyped !big_opM_fmap.
    iIntros "Hθ". iApply (big_sepM_mono with "Hθ").
    iIntros (Y B HYB) "H". iDestruct "H" as (v) "[% B]".
    iExists v; iSplit; auto.
    feed pose proof (Hwf _ _ HYB δ (<[X:=T δ]> δ)) as HB.
    { intros Z Hx'. assert (X ≠ Z) by  set_solver. by rewrite lookup_insert_ne. }
    by erewrite HB.
  Qed.


  (* the typing rules *)
  Lemma poly_variable Ω x T: (Ω; {[ x := T ]} ⊨ x : T)%I.
  Proof.
    iExists ord_stepindex.zero. iIntros "_".
    iIntros (δ) "%". iIntros (θ) "HΓ". rewrite /env_lptyped /env_ltyped big_opM_fmap.
    iPoseProof (big_sepM_lookup _ _ x T with "HΓ") as "Hx"; first eapply lookup_insert.
    simpl; iDestruct "Hx" as (v) "(-> & HA)".
    by iApply seq_value.
  Qed.

  Lemma poly_weaken x Ω Π e T U: Π !! x = None → (Ω; Π ⊨ e : U)%I → (Ω; (<[ x := T ]> Π) ⊨ e : U)%I.
  Proof.
    intros Hx He. iDestruct He as (α) "He".
    iExists α. iIntros "Hα". iIntros (δ) "Hδ". iIntros (θ) "Hθ".
    iApply ("He" with "Hα Hδ"). by iApply (env_lptyped_weaken with "Hθ").
  Qed.

  Lemma poly_unit_intro Ω: (Ω; ∅ ⊨ #() : lpunit)%I.
  Proof.
    iExists ord_stepindex.zero. iIntros "_".
    iIntros (δ) "Hδ". iIntros (θ) "HΓ"; simpl. iApply closed_unit_intro.
  Qed.

  Lemma poly_unit_elim Ω Π Ξ e e' T: Π ##ₘ Ξ → (Ω; Π ⊨ e : lpunit)%I → (Ω; Ξ ⊨ e' : T)%I → (Ω; Π ∪ Ξ ⊨ (e ;; e'): T)%I.
  Proof.
    intros Hdis He He'. iDestruct He as (α_e) "He". iDestruct He' as (α_e') "He'".
    iExists (α_e ⊕ α_e'). rewrite tc_split. iIntros "[α_e α_e']".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("He" with "α_e Hδ HΓ"). iSpecialize ("He'" with "α_e' Hδ HΔ").
    simpl; iApply (closed_unit_elim with "[$He $He']").
  Qed.

  Lemma poly_bool_intro Ω b: (Ω; ∅ ⊨ #b : lpbool)%I.
  Proof.
    iExists ord_stepindex.zero. iIntros "_".
    iIntros (δ) "#Hδ". iIntros (θ) "HΓ"; simpl. iApply closed_bool_intro.
  Qed.

  Lemma poly_bool_elim Ω Π Ξ e e_1 e_2 T:
    Π ##ₘ Ξ
    → (Ω; Π ⊨ e : lpbool)%I
    → (Ω; Ξ ⊨ e_1 : T)%I
    → (Ω; Ξ ⊨ e_2 : T)%I
    → (Ω; (Π ∪ Ξ) ⊨ (if: e then e_1 else e_2): T)%I.
  Proof.
    intros Hdis He H1 H2. iDestruct He as (α_e) "He". iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_e ⊕ α_1 ⊕ α_2). rewrite !tc_split. iIntros "[[α_e α_1] α_2]".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("He" with "α_e Hδ HΓ"). simpl.
    iApply (closed_bool_elim _ _ _ _ (env_lptyped Ξ δ θ)); iFrame.
    iSplitL "H1 α_1".
    - iApply ("H1" with "α_1 Hδ").
    - iApply ("H2" with "α_2 Hδ").
  Qed.

  Lemma poly_nat_intro Ω n: (Ω; ∅ ⊨ #n : lpnat)%I.
  Proof.
    iExists ord_stepindex.zero. iIntros "_".
    iIntros (δ) "#Hδ". iIntros (θ) "HΓ"; simpl. iApply closed_nat_intro.
  Qed.

  Lemma poly_nat_plus Ω e1 e2 Π Ξ: Π ##ₘ Ξ → (Ω; Π ⊨ e1 : lpnat)%I → (Ω; Ξ ⊨ e2 : lpnat)%I → (Ω; Π ∪ Ξ ⊨ e1 + e2 : lpnat)%I.
  Proof.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 Hδ HΓ"). iSpecialize ("H2" with "α_2 Hδ HΔ").
    simpl; iApply (closed_nat_add with "[$H1 $H2]").
  Qed.

  Lemma poly_nat_elim Ω e e_0 e_S x T Π Ξ:
    Π ##ₘ Ξ
    → (Ω; Π ⊨ e : lpnat)%I
    → (Ω; Ξ ⊨ e_0 : T)%I
    → (Ω; {[ x := T ]} ⊨ e_S : T)%I
    → (Ω; Π ∪ Ξ ⊨ iter e_0 e (λ: x, e_S)%V : T)%I.
  Proof.
    intros Hdis He H0 HS.
    iDestruct He as (α_e) "He". iDestruct H0 as (α_0) "H0". iDestruct HS as (α_S) "HS".
    iExists (α_e ⊕ α_0 ⊕ omul α_S). rewrite !tc_split. iIntros "[[α_e α_0] α_S]".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split; auto. iIntros "[HΓ HΔ]". simpl.
    iSpecialize ("He" with "α_e Hδ HΓ"). iSpecialize ("H0" with "α_0 Hδ HΔ").
    simpl; iApply (closed_nat_iter _ _ _ α_S with "[$He $H0 $α_S]").
    iModIntro. iIntros "α_S". iIntros (v) "Hv".
    iIntros "Hna". wp_pures.
    replace e_S with (subst_map (delete x ∅) e_S) at 1; last by rewrite delete_empty subst_map_empty.
    rewrite -subst_map_insert. iApply ("HS" with "α_S Hδ [Hv] Hna").
    iApply env_lptyped_insert; iFrame.
    iApply env_lptyped_empty.
  Qed.

  Lemma poly_fun_intro Ω Π x e T U:
    (Ω; (<[x:=T]> Π) ⊨ e : U)%I
    → (Ω; Π ⊨ (λ: x, e) : lparr T U)%I.
  Proof.
    intros He. iDestruct He as (α_e) "He". iExists α_e.
    iIntros "α_e". iSpecialize ("He" with "α_e").
    iIntros (δ) "#Hδ". iIntros (θ) "HΓ". simpl.  iApply (closed_fun_intro).
    iIntros (v) "Hv". rewrite -subst_map_insert. iApply ("He" with "Hδ [HΓ Hv]").
    iApply (env_lptyped_insert with "[$HΓ Hv]"); first done.
  Qed.

  Lemma poly_fun_elim Ω Π Ξ e1 e2 T U:
    Π ##ₘ Ξ
    → (Ω; Π ⊨ e1 : lparr T U)%I
    → (Ω; Ξ ⊨ e2 : T)%I
    → (Ω; Π ∪ Ξ ⊨ (e1 e2): U)%I.
  Proof.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 Hδ HΓ"). iSpecialize ("H2" with "α_2 Hδ HΔ").
    simpl; iApply (closed_fun_elim with "[$H1 $H2]").
  Qed.

  Lemma poly_tensor_intro Ω Π Ξ e1 e2 T U:
    Π ##ₘ Ξ
    → (Ω; Π ⊨ e1 : T)%I
    → (Ω; Ξ ⊨ e2 : U)%I
    → (Ω; Π ∪ Ξ ⊨ (e1, e2): lptensor T U)%I.
  Proof.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 Hδ HΓ"). iSpecialize ("H2" with "α_2 Hδ HΔ").
    iApply (closed_tensor_intro with "[$H1 $H2]").
  Qed.

  Lemma poly_tensor_elim Ω Π Ξ x y e1 e2 T1 T2 U:
    x ≠ y
    → Π ##ₘ Ξ
    → (Ω; Π ⊨ e1 : lptensor T1 T2)%I
    → (Ω; (<[x := T1]> (<[y := T2]> Ξ)) ⊨ e2 : U)%I
    → (Ω; Π ∪ Ξ ⊨ (let: (x, y) := e1 in e2) : U)%I.
  Proof.
    intros Hne Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 Hδ HΓ"). simpl. iApply (closed_tensor_elim with "[$H1 HΔ α_2]"); auto.
    iIntros (v1 v2) "Hv1 Hv2".
    rewrite delete_commute -subst_map_insert -delete_insert_ne; auto.
    rewrite -subst_map_insert. iApply ("H2" with "α_2 Hδ").
    rewrite insert_commute; auto.
    do 2 (iApply env_lptyped_insert; iFrame).
  Qed.

  Lemma poly_chan_alloc Ω T: (Ω; ∅ ⊨ chan #() : lptensor (lpget T) (lpput T))%I.
  Proof.
    iExists (one ⊕ one). rewrite tc_split. iIntros "Hcred".
    iIntros (δ) "#Hδ". iIntros (θ) "_"; simpl. iApply (closed_chan (T δ) with "Hcred").
  Qed.

  Lemma poly_chan_get Ω Π Ξ e1 e2 T:
    Π ##ₘ Ξ
    → (Ω; Π ⊨ e1 : lpget T)%I
    → (Ω; Ξ ⊨ e2 : lparr T lpunit)%I
    → (Ω; Π ∪ Ξ ⊨ get (e1, e2)%E: lpunit)%I.
  Proof using FBI Heap SI Sequential TimeCredits Σ.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 Hδ HΓ"). iSpecialize ("H2" with "α_2 Hδ HΔ").
    simpl; iApply (closed_get with "[$H1 $H2]").
  Qed.

  Lemma poly_chan_put Ω Π Ξ e1 e2 T:
    Π ##ₘ Ξ
    → (Ω; Π ⊨ e1 : lpput T)%I
    → (Ω; Ξ ⊨ e2 : T)%I
    → (Ω; Π ∪ Ξ ⊨ put (e1, e2)%E: lpunit)%I.
  Proof using FBI Heap SI Sequential TimeCredits Σ.
    intros Hdis H1 H2. iDestruct H1 as (α_1) "H1". iDestruct H2 as (α_2) "H2".
    iExists (α_1 ⊕ α_2). rewrite tc_split. iIntros "[α_1 α_2]".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split; auto. iIntros "[HΓ HΔ]".
    iSpecialize ("H1" with "α_1 Hδ HΓ"). iSpecialize ("H2" with "α_2 Hδ HΔ").
    simpl; iApply (closed_put with "[$H1 $H2]").
  Qed.


  Lemma poly_forall_intro Ω X Π e T:
    (Ω ⊨ Π) → X ∉ Ω → (({[X]} ∪ Ω); Π ⊨ e : T)%I → (Ω; Π ⊨ tlam e : lpforall X T)%I.
  Proof using FBI Heap SI Sequential TimeCredits Σ.
    intros Hwf Hx He.
    iDestruct He as (α_e) "He". iExists α_e.
    iIntros "Ha". iSpecialize ("He" with "Ha").
    iIntros (δ) "Hδ". iIntros (θ) "Hθ". simpl.
    iIntros "Hna". wp_pures. iFrame.
    unfold lpforall. iIntros (U) "Hna".
    wp_pures. unfold subst_ty. iApply ("He" with "[Hδ] [Hθ] Hna").
    - by iApply well_formed_insert.
    - iApply (env_lptyped_update_type_map with "Hθ"); eauto.
  Qed.

  (* For the compatibility lemma, we do not need well-formedness of U. It's only needed for type preservation. *)
  Lemma poly_forall_elim Ω X Π e T U:
    (* Ω ⊨ U → *) (Ω; Π ⊨ e : lpforall X T)%I → (Ω; Π ⊨ tapp e : subst_ty T X U)%I.
  Proof.
    intros He.
    iDestruct He as (α_e) "He". iExists α_e.
    iIntros "Ha". iSpecialize ("He" with "Ha").
    iIntros (δ) "Hδ". iIntros (θ) "Hθ". simpl.
    iIntros "Hna". wp_bind (subst_map _ e).
    iMod ("He" with "Hδ Hθ Hna") as "_".
    iIntros (v) "[Hna Hf] !>". rewrite /lpforall.
    by iApply "Hf".
  Qed.

  (* Well-formedness assumptions needed for type preservation but not for the compatibility lemma.*)
  Lemma poly_exists_intro Ω X Π e T U:
    (Ω; Π ⊨ e : subst_ty T X U)%I → (Ω; Π ⊨ pack e : lpexists X T)%I.
  Proof using FBI Heap SI Sequential TimeCredits Σ.
    intros He.
    iDestruct He as (α_e) "He". iExists α_e.
    iIntros "Ha". iSpecialize ("He" with "Ha").
    iIntros (δ) "Hδ". iIntros (θ) "Hθ".
    iIntros "Hna". iMod ("He" with "Hδ Hθ Hna") as "_".
    iIntros (v) "[$ HT] !>". by iExists U.
  Qed.

  Lemma poly_exists_elim Ω X Π Ξ x e e2 T U:
    X ∉ Ω
    → (Ω ⊨ Ξ)
    → (Ω ⊨ U)
    → Π ##ₘ Ξ
    → (Ω; Π ⊨ e : lpexists X T)%I
    → ({[X]} ∪ Ω; <[x := T ]> Ξ ⊨ e2 : U)%I
    → (Ω; Π ∪ Ξ ⊨ unpack e x e2 : U)%I.
  Proof using FBI Heap SI Sequential TimeCredits Σ.
    intros Hx Hwf HwfU Hdis He He2.
    iDestruct He as (α_e) "He". iDestruct He2 as (α_2) "H2".
    iExists (α_e ⊕ α_2). rewrite tc_split. iIntros "[α_e α_2]".
    iIntros (δ) "#Hδ". iIntros (θ). rewrite env_lptyped_split //=.
    iIntros "[HΓ HΞ] Hna".
    wp_bind (subst_map _ e). iMod ("He" with "α_e Hδ HΓ Hna") as "_".
    iIntros (v) "[Hna Hv] !>". iDestruct "Hv" as (T') "Hv".
    wp_pures. rewrite -subst_map_insert.
    iMod ("H2" with "α_2 [Hδ] [HΞ Hv] Hna") as "_".
    - by iApply well_formed_insert.
    - iApply env_lptyped_insert; iFrame.
      iApply (env_lptyped_update_type_map with "HΞ"); eauto.
    - feed pose proof (HwfU δ (<[X := (T' δ)]> δ)).
      { intros Z Hx'. assert (X ≠ Z) by set_solver. by rewrite lookup_insert_ne. }
      iIntros (w) "[$ HU] !>". by rewrite -H.
  Qed.

End polymorphic_logical_relation.

End semantic_model.

From iris.examples.termination Require Import adequacy.
Section adequacy.

  Context {SI} `{C: Classical}  {Σ: gFunctors SI} {Hlarge: LargeIndex SI}.
  Context `{Hpre: !heapPreG Σ} `{Hna: !na_invG Σ} `{Htc: !inG Σ (authR (ordA SI))}.

  Theorem simple_logrel_adequacy (e: expr) σ A:
    (∀ `{heapG SI Σ} `{!seqG Σ} `{!auth_sourceG Σ (ordA SI)},
      ltyped ∅ e A
    ) →
    sn erased_step ([e], σ).
  Proof using Hlarge C Σ Hpre Hna Htc.
    intros Htyped.
    eapply heap_lang_ref_adequacy.
    intros ???. iIntros "_".
    iPoseProof (Htyped) as (α) "H".
    iExists α. iIntros "Hα". iSpecialize ("H" with "Hα").
    iPoseProof (env_ltyped_empty ∅) as "Henv". iSpecialize ("H" with "Henv").
    rewrite subst_map_empty. iIntros "Hna". iMod ("H" with "Hna"); eauto.
    by iIntros (v) "[$ _]".
  Qed.

  Theorem logrel_adequacy (e: expr) σ A:
    (∀ `{heapG SI Σ} `{!seqG Σ} `{!auth_sourceG Σ (ordA SI)},
      lptyped ∅ ∅ e A
    ) →
    sn erased_step ([e], σ).
  Proof using Hlarge C Σ Hpre Hna Htc.
    intros Htyped.
    eapply heap_lang_ref_adequacy.
    intros ???. iIntros "_".
    iPoseProof (Htyped) as (α) "H".
    iExists α. iIntros "Hα". iSpecialize ("H" with "Hα").
    iPoseProof (well_formed_empty with "[//]") as "Hctx".
    iPoseProof (env_lptyped_empty ∅ ∅) as "Henv".
    iSpecialize ("H" with "Hctx Henv").
    rewrite subst_map_empty. iIntros "Hna". iMod ("H" with "Hna"); eauto.
    by iIntros (v) "[$ _]".
  Qed.

End adequacy.

Section ordinals. 
  Context `{C: Classical}  {Σ: gFunctors ordI}.
  Context `{Hpre: !heapPreG Σ} `{Hna: !na_invG Σ} `{Htc: !inG Σ (authR (ordA ordI))}.

  Theorem simple_logrel_adequacy_ord (e: expr) σ A:
    (∀ `{heapG ordI Σ} `{!seqG Σ} `{!auth_sourceG Σ (ordA ordI)},
      ltyped ∅ e A
    ) →
    sn erased_step ([e], σ).
  Proof using C Σ Hpre Hna Htc.
    intros Htyped.
    eapply heap_lang_ref_adequacy.
    intros ???. iIntros "_".
    iPoseProof (Htyped) as (α) "H".
    iExists α. iIntros "Hα". iSpecialize ("H" with "Hα").
    iPoseProof (env_ltyped_empty ∅) as "Henv". iSpecialize ("H" with "Henv").
    rewrite subst_map_empty. iIntros "Hna". iMod ("H" with "Hna"); eauto.
    by iIntros (v) "[$ _]".
  Qed.

  Theorem logrel_adequacy_ord (e: expr) σ A:
    (∀ `{heapG ordI Σ} `{!seqG Σ} `{!auth_sourceG Σ (ordA ordI)},
      lptyped ∅ ∅ e A
    ) →
    sn erased_step ([e], σ).
  Proof using C Σ Hpre Hna Htc.
    intros Htyped.
    eapply heap_lang_ref_adequacy.
    intros ???. iIntros "_".
    iPoseProof (Htyped) as (α) "H".
    iExists α. iIntros "Hα". iSpecialize ("H" with "Hα").
    iPoseProof (well_formed_empty with "[//]") as "Hctx".
    iPoseProof (env_lptyped_empty ∅ ∅) as "Henv".
    iSpecialize ("H" with "Hctx Henv").
    rewrite subst_map_empty. iIntros "Hna". iMod ("H" with "Hna"); eauto.
    by iIntros (v) "[$ _]".
  Qed.

End ordinals.

