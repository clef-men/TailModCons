From iris.algebra Require Export stepindex  base.
Set Default Proof Using "Type".
Set Primitive Projections.

(** This files defines (a shallow embedding of) the category of OFEs:
    Ordered families of equivalences. This is a cartesian closed
    category, and mathematically speaking, the entire development lives
    in this category. However, we will generally prefer to work with raw
    Coq functions plus some registered Proper instances for non-expansiveness.
    This makes writing such functions much easier. It turns out that it many
    cases, we do not even need non-expansiveness.
*)

(** Unbundeled version *)
Class Dist (SI: indexT) A := dist : SI → relation A.

Instance: Params (@dist) 4 := {}.
Notation "x ≡{ α }≡ y" := (dist α x y)
  (at level 70, α at next level, format "x  ≡{ α }≡  y").
Notation "x ≡{ α }@{ A }≡ y" := (dist (A:=A) α x y)
  (at level 70, α at next level, only parsing).

Hint Extern 0 (_ ≡{_}≡ _) => reflexivity : core.
Hint Extern 0 (_ ≡{_}≡ _) => symmetry; assumption : core.
Notation NonExpansive f := (∀ α, Proper (dist α ==> dist α) f).
Notation NonExpansive2 f := (∀ α, Proper (dist α ==> dist α ==> dist α) f).

Lemma ne_apply {SI: indexT} `{Dist SI A} `{Dist SI B} {f: A → B} `{NonExpansive f}  (α: SI):
  Proper (dist (A:=A) α ==> dist (A:=B) α) f.
Proof. typeclasses eauto. Qed.

Tactic Notation "ofe_subst" ident(x) :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?SI ?A ?d ?α x _ |- _ => setoid_subst_aux (@dist SI A d α) x
  | H:@dist ?SI ?A ?d ?α _ x |- _ => symmetry in H; setoid_subst_aux (@dist SI A d α) x
  end.
Tactic Notation "ofe_subst" :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?SI ?A ?d ?α ?x _ |- _ => setoid_subst_aux (@dist SI A d α) x
  | H:@dist ?SI ?A ?d ?α _ ?x |- _ => symmetry in H;setoid_subst_aux (@dist SI A d α) x
  end.

Record OfeMixin (SI: indexT) A `{Equiv A, Dist SI A} := {
  mixin_equiv_dist x y : x ≡ y ↔ ∀ (α: SI), x ≡{α}≡ y;
  mixin_dist_equivalence (α : SI): Equivalence (dist α);
  mixin_dist_mono (α β: SI) x y : x ≡{α}≡ y → β ≺ α → x ≡{β}≡ y
}.


(** Bundeled version *)
Structure ofeT (SI: indexT) := OfeT {
  ofe_car :> Type;
  ofe_equiv : Equiv ofe_car;
  ofe_dist : Dist SI ofe_car;
  ofe_mixin : OfeMixin SI ofe_car
}.
Arguments OfeT {_} _ {_ _} _.
Add Printing Constructor ofeT.
Hint Extern 0 (Equiv _) => eapply (@ofe_equiv _ _) : typeclass_instances.
Hint Extern 0 (Dist _ _) => eapply (@ofe_dist _ _) : typeclass_instances.
Arguments ofe_car : simpl never.
Arguments ofe_equiv : simpl never.
Arguments ofe_dist : simpl never.
Arguments ofe_mixin : simpl never.

(** When declaring instances of subclasses of OFE (like CMRAs and unital CMRAs)
we need Coq to *infer* the canonical OFE instance of a given type and take the
mixin out of it. This makes sure we do not use two different OFE instances in
different places (see for example the constructors [CmraT] and [UcmraT] in the
file [cmra.v].)

In order to infer the OFE instance, we use the definition [ofe_mixin_of'] which
is inspired by the [clone] trick in ssreflect. It works as follows, when type
checking [@ofe_mixin_of' A ?Ac id] Coq faces a unification problem:

  ofe_car ?Ac  ~  A

which will resolve [?Ac] to the canonical OFE instance corresponding to [A]. The
definition [@ofe_mixin_of' A ?Ac id] will then provide the corresponding mixin.
Note that type checking of [ofe_mixin_of' A id] will fail when [A] does not have
a canonical OFE instance.

The notation [ofe_mixin_of A] that we define on top of [ofe_mixin_of' A id]
hides the [id] and normalizes the mixin to head normal form. The latter is to
ensure that we do not end up with redundant canonical projections to the mixin,
i.e. them all being of the shape [ofe_mixin_of' A id]. *)
Definition ofe_mixin_of' SI A {Ac : ofeT SI} (f : Ac → A) : OfeMixin SI Ac := ofe_mixin SI Ac.
Notation ofe_mixin_of SI A :=
  ltac:(let H := eval hnf in (ofe_mixin_of' SI A id) in exact H) (only parsing).


(** Lifting properties from the mixin *)
Section ofe_mixin.
  Context {SI} {A : ofeT SI}.
  Implicit Types x y : A.
  Lemma equiv_dist x y : x ≡ y ↔ ∀ (α: SI), x ≡{α}≡ y.
  Proof. apply (mixin_equiv_dist _ _ (ofe_mixin SI A)). Qed.
  Global Instance dist_equivalence α : Equivalence (@dist SI A _ α).
  Proof. apply (mixin_dist_equivalence _ _ (ofe_mixin SI A)). Qed.
  Lemma dist_mono (α β: SI) x y : x ≡{α}≡ y → β ≺ α → x ≡{β}≡ y.
  Proof. apply (mixin_dist_mono _ _ (ofe_mixin SI A)). Qed.
  Lemma dist_mono' (α β: SI) x y : x ≡{α}≡ y → β ⪯ α → x ≡{β}≡ y.
  Proof. intros H [-> | Hβ]; [auto | by eapply dist_mono]. Qed.
End ofe_mixin.


Hint Extern 1 (_ ≡{_}≡ _) => apply equiv_dist; assumption : core.

(** Discrete OFEs and discrete OFE elements *)
Class Discrete {SI: indexT} {A : ofeT SI} (x : A) := discrete y : x ≡{zero}≡ y → x ≡ y.
Arguments discrete {_ _} _ {_} _ _.
Hint Mode Discrete - + ! : typeclass_instances.
Instance: Params (@Discrete) 2 := {}.

Class OfeDiscrete {SI: indexT} (A : ofeT SI) := ofe_discrete_discrete (x : A) :> Discrete x.
Hint Mode OfeDiscrete - ! : typeclass_instances.

(** OFEs with a completion *)
Record chain {SI: indexT} (A : ofeT SI) := mkchain
  {
    chain_car :> SI → A;
    chain_cauchy : ∀ α β, α ⪯ β → chain_car β ≡{α}≡ chain_car α
  }.

Record bchain {SI: indexT} (A : ofeT SI) (α: SI) := mkbchain
  {
    bchain_car :>  ∀ β, β ≺ α → A;
    bchain_cauchy : ∀ β γ, β ⪯ γ → ∀ Hβ Hγ, bchain_car γ Hγ ≡{β}≡ bchain_car β Hβ
  }.

Program Definition chain_map  {SI: indexT} {A B : ofeT SI} (f : A → B) `{NonExpansive f} (c: chain A) : chain B :=
  {| chain_car α := f (c α) |}.
Next Obligation. by intros SI A B f Hf c n i ?; apply Hf, chain_cauchy. Qed.

Program Definition bchain_map  {SI: indexT} {A B : ofeT SI} (f : A → B) `{NonExpansive f} {α} (c: bchain A α) : bchain B α :=
  {| bchain_car β Hβ := f (c β Hβ) |}.
Next Obligation. by intros SI A B f Hf α c β γ ? Hβ Hγ; apply Hf, bchain_cauchy. Qed.

(* simplify rewriting: *)
Lemma chain_cauchy' {SI: indexT} {A: ofeT SI} (c: chain A) α β: α ⪯ β → c β ≡{α}≡ c α.
Proof. eapply chain_cauchy. Qed.
Lemma bchain_cauchy' {SI: indexT} {A: ofeT SI} α (c: bchain A α) β γ Hβ Hγ: β ⪯ γ → c γ Hγ ≡{β}≡ c β Hβ.
Proof. intros; by eapply bchain_cauchy. Qed.


Class Cofe {SI: indexT} (A : ofeT SI) :=
  {
    compl : chain A → A;
    bcompl {α}: zero ≺ α → bchain A α → A;
    conv_compl α c: compl c ≡{α}≡ c α;
    conv_bcompl α Hα (c: bchain A α) β Hβ: bcompl Hα c ≡{β}≡ c β Hβ;
    bcompl_ne {α Hα} (c d: bchain A α) β: (∀ γ (Hγ: γ ≺ α), c γ Hγ ≡{β}≡ d γ Hγ) → bcompl Hα c ≡{β}≡ bcompl Hα d
  }.
Arguments compl : simpl never.
Arguments bcompl : simpl never.
Hint Mode Cofe - ! : typeclass_instances.

Lemma chain_conv_compl {SI: indexT} `{Cofe SI A} (c: chain A) α : compl c ≡{α}≡ c α.
Proof. rewrite conv_compl; eauto using chain_cauchy. Qed.

Lemma bchain_conv_bcompl {SI: indexT}  `{Cofe SI A} α Hα (c: bchain A α) β Hβ: bcompl Hα c ≡{β}≡ c β Hβ.
Proof. rewrite conv_bcompl; eauto using bchain_cauchy. Qed.

Lemma compl_chain_map {SI: indexT} `{Cofe SI A, Cofe SI B} (f : A → B) (c: chain A) `(NonExpansive f) :
  compl (chain_map f c) ≡ f (compl c).
Proof. apply equiv_dist=>α. by rewrite !chain_conv_compl. Qed.

(* constant chains *)
Program Definition chain_const {SI: indexT} {A : ofeT SI} (a : A) : chain A := {| chain_car α := a |}.
Next Obligation. by intros ??????. Qed.

Lemma compl_chain_const {I: indexT} {A : ofeT I} `{!Cofe A} (a : A) :
  compl (chain_const a) ≡ a.
Proof. apply equiv_dist=>α. by rewrite chain_conv_compl. Qed.

Program Definition bchain_const {SI : indexT} {A : ofeT SI} (a : A) α : bchain A α :=
  {| bchain_car β _ := a |}.
Next Obligation.
  by intros ????????.
Qed.

Lemma bcompl_bchain_const {I: indexT} {A : ofeT I} `{!Cofe A} (a : A) (α : I) Hα:
  ∀ γ, γ ≺ α → bcompl Hα (bchain_const a α) ≡{γ}≡ a.
Proof.
  intros γ Hγ. by unshelve rewrite bchain_conv_bcompl.
Qed.

(** General properties *)
Section ofe.
  Context {SI: indexT} {A : ofeT SI}.
  Implicit Types x y : A.
  Global Instance ofe_equivalence : Equivalence ((≡) : relation A).
  Proof.
    split.
    - by intros x; rewrite equiv_dist.
    - by intros x y; rewrite !equiv_dist.
    - by intros x y z; rewrite !equiv_dist; intros; trans y.
  Qed.
  Global Instance dist_ne α : Proper (dist α ==> dist α ==> iff) (@dist SI A _ α).
  Proof.
    intros x1 x2 ? y1 y2 ?; split; intros.
    - by trans x1; [|trans y1].
    - by trans x2; [|trans y2].
  Qed.
  Global Instance dist_proper α : Proper ((≡) ==> (≡) ==> iff) (@dist SI A _ α).
  Proof.
    by move => x1 x2 /equiv_dist Hx y1 y2 /equiv_dist Hy; rewrite (Hx α) (Hy α).
  Qed.
  Global Instance dist_proper_2 α x : Proper ((≡) ==> iff) (dist α x).
  Proof. by apply dist_proper. Qed.
  Global Instance Discrete_proper : Proper ((≡) ==> iff) (@Discrete SI A).
  Proof. intros x y Hxy. rewrite /Discrete. by setoid_rewrite Hxy. Qed.

  Lemma dist_le α α' x y : x ≡{α}≡ y → α' ⪯ α → x ≡{α'}≡ y.
  Proof. destruct 2; eauto using dist_mono; congruence. Qed.
  Lemma dist_le' α α' x y : α' ⪯ α → x ≡{α}≡ y → x ≡{α'}≡ y.
  Proof. intros; eauto using dist_le. Qed.
  Instance ne_proper {B : ofeT SI} (f : A → B) `{!NonExpansive f} :
    Proper ((≡) ==> (≡)) f | 100.
  Proof. by intros x1 x2; rewrite !equiv_dist; intros Hx n; rewrite (Hx n). Qed.
  Instance ne_proper_2 {B C : ofeT SI} (f : A → B → C) `{!NonExpansive2 f} :
    Proper ((≡) ==> (≡) ==> (≡)) f | 100.
  Proof.
     unfold Proper, respectful; setoid_rewrite equiv_dist.
     by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
  Qed.

  Lemma conv_compl' `{Cofe SI A} (α β: SI) (c: chain A) : α ⪯ β → compl c ≡{α}≡ c β.
  Proof.
    transitivity (c α); first by apply chain_conv_compl. symmetry. by rewrite chain_cauchy.
  Qed.

  Lemma discrete_iff α (x : A) `{!Discrete x} y : x ≡ y ↔ x ≡{α}≡ y.
  Proof.
    split; intros; auto. apply (discrete _), dist_le with α; auto.
  Qed.
  Lemma discrete_iff_0 α (x : A) `{!Discrete x} y : x ≡{zero}≡ y ↔ x ≡{α}≡ y.
  Proof. by rewrite -!discrete_iff. Qed.
End ofe.

(** Contractive functions *)
Definition dist_later {SI: indexT} `{Dist SI A} (α : SI) (x y : A) : Prop :=
  ∀ β, β ≺ α → x ≡{β}≡ y.

Arguments dist_later _ _ _ !_ _ _ /.

Global Instance dist_later_equivalence {SI} (A : ofeT SI) α : Equivalence (@dist_later SI A _ α).
Proof.
  split.
  - now intros ???.
  - unfold dist_later; intros ?? H ??; now rewrite H.
  - unfold dist_later; intros ??? H1 H2 ??; now rewrite H1 ?H2.
Qed.

Lemma dist_dist_later {SI: indexT} {A : ofeT SI} α (x y : A) : dist α x y → dist_later α x y.
Proof. intros Heq ??; eapply dist_mono; eauto. Qed.

Lemma dist_later_dist {SI: indexT} {A : ofeT SI} α β (x y : A) : β ≺ α → dist_later α x y → dist β x y.
Proof. intros ? H; by apply H.  Qed.

Lemma dist_later_zero {SI: indexT} {A : ofeT SI} (x y : A): dist_later zero x y.
Proof. intros ? [] % index_lt_zero_is_normal. Qed.

Global Instance ne_dist_later {SI: indexT} {A B : ofeT SI} (f : A → B) :
  NonExpansive f → ∀ (α: SI), Proper (dist_later α ==> dist_later α) f.
Proof. intros Hf ??????; by eapply Hf, H. Qed.

Global Instance ne2_dist_later_l {SI} {A B C: ofeT SI} (f : A → B → C) :
  NonExpansive2 f → ∀ α, Proper (dist_later α ==> dist α ==> dist_later α) f.
Proof. intros H α a b H1 c d H2 β Hβ. apply H; by eauto using dist_mono. Qed.
Global Instance ne2_dist_later_r {SI} {A B C: ofeT SI} (f : A → B → C) :
  NonExpansive2 f → ∀ α, Proper (dist α ==> dist_later α ==> dist_later α) f.
Proof. intros H α a b H1 c d H2 β Hβ. apply H; by eauto using dist_mono. Qed.


Notation Contractive f := (∀ α, Proper (dist_later α ==> dist α) f).

Instance const_contractive {I: indexT} {A B : ofeT I} (x : A) : Contractive (@const A B x).
Proof. by intros α y1 y2. Qed.

Section contractive.
  Local Set Default Proof Using "Type*".
  Context {SI: indexT} {A B : ofeT SI} (f : A → B) `{!Contractive f}.
  Implicit Types x y : A.

  Lemma contractive_0 x y : f x ≡{zero}≡ f y.
  Proof. by apply (_ : Contractive f), dist_later_zero. Qed.
  Lemma contractive_mono α x y : dist_later α x y → f x ≡{α}≡ f y.
  Proof. by apply (_ : Contractive f). Qed.

  Global Instance contractive_ne : NonExpansive f | 100.
  Proof.
    intros n x y ?; eapply dist_mono with (α := succ n).
    2: eapply index_succ_greater.
    eapply contractive_mono.
    intros ??. eapply dist_le; eauto.
  Qed.

  Global Instance contractive_proper : Proper ((≡) ==> (≡)) f | 100.
  Proof. apply (ne_proper _). Qed.
End contractive.

Ltac f_contractive :=
  match goal with
  | |- ?f _ ≡{_}≡ ?f _ => simple apply (_ : Proper (dist_later _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (dist_later _ ==> _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (_ ==> dist_later _ ==> _) f)
  | |- dist_later _ (?f _) (?f _) => simple apply (_ : Proper (dist_later _ ==> dist_later _) f)
  | |- dist_later _ (?f _ _) (?f _ _) => simple apply (_ : Proper (dist_later _ ==> _ ==> dist_later _) f)
  | |- dist_later _ (?f _ _) (?f _ _) => simple apply (_ : Proper (_ ==> dist_later _ ==> dist_later _) f)
  end;
  try simple apply reflexivity.

(* FIXME: the last clause is a hacky addition since the approach for dealing this from finite Iris (destructing the index) cannot be directly translated.
  we might want to look for a smarter solution. *)
Ltac solve_contractive :=
  solve_proper_core ltac:(fun _ => first [f_contractive | f_equiv |
      try match goal with
        | H : @dist_later _ ?A _ _ ?x ?y |- ?x ≡{_}≡ ?y =>
            by (apply H; eauto 3 with index)
      end]).

(* without smoothness, we only get uniqueness at ≺ α *)
Lemma cofe_bcompl_weakly_unique {SI : indexT} (A : ofeT SI) (HA : Cofe A) (α: SI) Hα (c d : bchain A α):
 (∀ γ (Hγ : γ ≺ α), c γ Hγ ≡{γ}≡ d γ Hγ) → dist_later α (bcompl Hα c) (bcompl Hα d).
Proof.
  intros H γ Hγ. unshelve rewrite !conv_bcompl; [assumption | assumption | apply H].
Qed.

(** Limit preserving predicates *)
Class LimitPreserving {SI: indexT} `{Cofe SI A} (P : A → Prop) : Prop :=
  limit_preserving (c: chain A) : (∀ α, P (c α)) → P (compl c).
Hint Mode LimitPreserving - + + ! : typeclass_instances.

Section limit_preserving.
  Context {SI: indexT} `{Cofe SI A}.
  (* These are not instances as they will never fire automatically...
     but they can still be helpful in proving things to be limit preserving. *)

  Lemma limit_preserving_ext (P Q : A → Prop) :
    (∀ x, P x ↔ Q x) → LimitPreserving P → LimitPreserving Q.
  Proof. intros HP Hlimit c ?. apply HP, Hlimit; eauto=> n. by apply HP. Qed.

  Global Instance limit_preserving_const (P : Prop) : LimitPreserving (λ _ : A, P).
  Proof. intros c HP. apply (HP zero). Qed.

  Lemma limit_preserving_discrete (P : A → Prop) :
    Proper (dist zero ==> impl) P → LimitPreserving P.
  Proof. intros PH c HP. by rewrite (conv_compl zero c). Qed.

  Lemma limit_preserving_and (P1 P2 : A → Prop) :
    LimitPreserving P1 → LimitPreserving P2 →
    LimitPreserving (λ x, P1 x ∧ P2 x).
  Proof. intros Hlim1 Hlim2 c HC. split. apply Hlim1; apply HC. apply Hlim2; apply HC. Qed.

  Lemma limit_preserving_impl (P1 P2 : A → Prop) :
    Proper (dist zero ==> impl) P1 → LimitPreserving P2 →
    LimitPreserving (λ x, P1 x → P2 x).
  Proof.
    intros Hlim1 Hlim2 c HP HP1. apply Hlim2; eauto; intros n; apply HP.
    eapply Hlim1, HP1. apply dist_le with n; last eapply index_zero_minimum.
    apply (conv_compl n c); eauto.
  Qed.

  Lemma limit_preserving_forall {B} (P : B → A → Prop) :
    (∀ y, LimitPreserving (P y)) →
    LimitPreserving (λ x, ∀ y, P y x).
  Proof. intros Hlim c HC y. by apply Hlim. Qed.
End limit_preserving.


(** Bounded limit preserving predicates *)
Class BoundedLimitPreserving {SI: indexT} `{Cofe SI A} (P : A → Prop) : Prop :=
  bounded_limit_preserving α Hα (c: bchain A α) : (∀ β Hβ, P (c β Hβ)) → P (bcompl Hα c).
Hint Mode BoundedLimitPreserving - + + ! : typeclass_instances.

Section bounded_limit_preserving.
  Context {SI: indexT} `{Cofe SI A}.
  (* These are not instances as they will never fire automatically...
     but they can still be helpful in proving things to be limit preserving. *)

  Lemma bounded_limit_preserving_ext (P Q : A → Prop) :
    (∀ x, P x ↔ Q x) → BoundedLimitPreserving P → BoundedLimitPreserving Q.
  Proof. intros HP Hlimit α Hα c HC. apply HP, Hlimit; eauto=> β Hβ. by apply HP. Qed.

  Global Instance bounded_limit_preserving_const (P : Prop) : P → BoundedLimitPreserving (λ _: A, P).
  Proof. intros c HP ?; eauto. Qed.


  Lemma bounded_limit_preserving_and (P1 P2 : A → Prop) :
    BoundedLimitPreserving P1 → BoundedLimitPreserving P2 →
    BoundedLimitPreserving (λ x, P1 x ∧ P2 x).
  Proof. intros Hlim1 Hlim2 α c Hα HC. split. apply Hlim1; apply HC. apply Hlim2; apply HC. Qed.


  Lemma bounded_limit_preserving_forall {B} (P : B → A → Prop) :
    (∀ y, BoundedLimitPreserving (P y)) →
    BoundedLimitPreserving (λ x, ∀ y, P y x).
  Proof. intros Hlim c ? ? ? y. by apply Hlim. Qed.
End bounded_limit_preserving.


(** Fixpoint *)
Section fixpoint.

  Context {SI: indexT} `{Cofe SI A} (f: A → A) `{C: Contractive f} `{In: Inhabited A}.

  Record is_bounded_fixpoint_chain α (ch : ∀ β, β ≺ α -> A) := mk_is_bounded_fixpoint_chain
    {
      ch_cauchy : ∀ β γ, β ⪯ γ -> ∀ (Hβ : β ≺ α) (Hγ : γ ≺ α), ch γ Hγ ≡{β}≡ ch β Hβ;
      is_fp : forall Hα, dist_later α (f (bcompl Hα (mkbchain SI A α ch ch_cauchy))) (bcompl Hα (mkbchain SI A α ch ch_cauchy));
    }.

  Definition bounded_fixpoint_chain α := {ch : ∀ β, β ≺ α -> A & is_bounded_fixpoint_chain α ch}.
  Program Definition mk_bounded_fixpoint_chain α (ch : bchain A α) (fp : ∀ Hα, dist_later α (f (bcompl Hα ch)) (bcompl Hα ch)) :=
    existT (bchain_car A α ch) (mk_is_bounded_fixpoint_chain α (bchain_car A α ch) _ _).
  Next Obligation. intros α ch _. apply ch. Defined.
  Next Obligation. intros α ch fp Hα. cbn. apply fp. Defined.

  Definition get_chain α (bfc : bounded_fixpoint_chain α) := mkbchain SI A α (projT1 bfc) (@ch_cauchy α (projT1 bfc) (projT2 bfc)).
  Coercion get_chain : bounded_fixpoint_chain >-> bchain.

  Program Definition cast {α} (c: bounded_fixpoint_chain α) β (Hβ: β ⪯ α): bounded_fixpoint_chain β :=
    mk_bounded_fixpoint_chain β (mkbchain SI A β (λ γ Hγ, projT1 c γ _) _) _.
  Next Obligation. intros ??????; eauto using index_lt_le_trans. Qed.
  Next Obligation.
    intros α c β Hβ γ1 γ2 Hγ Hγ1 Hγ2; simpl.
    specialize (bchain_cauchy' α c); eauto.
  Qed.
  Next Obligation.
    intros α c β Hβ Hα γ Hγ; simpl. unshelve rewrite !bchain_conv_bcompl; simpl; eauto.
    specialize (@bchain_conv_bcompl SI A _ α ltac:(eauto using index_lt_le_trans) c) as Hx. cbn in Hx. rewrite -Hx.
    eapply is_fp. eauto using index_lt_le_trans.
  Qed.

  Lemma cast_chain α (Hα: zero ≺ α) β (Hβ: zero ≺ β) (Hβα: β ⪯ α) (c: bounded_fixpoint_chain α):
      dist_later β (bcompl Hβ (cast c β Hβα)) (bcompl Hα c).
  Proof.
    intros γ Hγ. unshelve rewrite !bchain_conv_bcompl; eauto using index_lt_le_trans.
    simpl. specialize (bchain_cauchy' α c); eauto.
  Qed.

  Lemma fp_chain_is_fp α (ch : bounded_fixpoint_chain α) (Hα : zero ≺ α): dist_later α (f (bcompl Hα ch)) (bcompl Hα ch).
  Proof.
    destruct ch as (ch & (cauchy & fp)). apply fp.
  Qed.

  Lemma bounded_fixpoint_chain_unique α (Hα: zero ≺ α) (c: bounded_fixpoint_chain α) β (Hβ: zero ≺ β) (Hβα: β ⪯ α) (d: bounded_fixpoint_chain β) :
    dist_later β (bcompl Hα c) (bcompl Hβ d).
  Proof using A C H SI f.
  revert Hβα d. induction (index_lt_wf SI β) as [β _ IH]. intros Hβα d γ Hγ.
  rewrite -(fp_chain_is_fp _ d Hβ γ Hγ). rewrite -(fp_chain_is_fp _ c Hα γ _); eauto using index_lt_le_trans.
  destruct (index_is_zero γ) as [->|NT].
  - by apply contractive_0.
  - eapply contractive_mono; eauto.
    assert (γ ⪯ β) as Hγβ by eauto.
    pose (e := cast d γ Hγβ).
    transitivity (bcompl NT e).
    + eapply IH; eauto using index_lt_le_trans.
    + apply cast_chain.
  Qed.


  Section inductive_step.


    Local Definition patch_base_case {α: SI} (g: zero ≺ α → A) : A :=
      match index_is_zero α with
      | left H => inhabitant
      | right NT => g NT
      end.

    Program Definition bfpc : ∀ (α: SI), bounded_fixpoint_chain α :=
      index_cumulative_rec (fun _ => A) is_bounded_fixpoint_chain
        (fun α IH => f (patch_base_case (fun NT => bcompl NT (get_chain α IH)))) _.
    Next Obligation.
      intros α G. cbn in *. unshelve econstructor; first last.
      - intros Hα β Hβ; simpl. unshelve rewrite bchain_conv_bcompl; simpl; eauto.
        unfold patch_base_case. destruct index_is_zero; subst.
        + by eapply contractive_0.
        + apply contractive_mono; eauto. by eapply is_fp.
      - intros β γ Hle Hβ Hγ. unfold patch_base_case.
        repeat destruct index_is_zero; eauto; subst.
        + destruct Hle; subst; by exfalso; eapply index_lt_zero_is_normal.
        + by eapply contractive_0.
        + apply contractive_mono; eauto. apply bounded_fixpoint_chain_unique, Hle.
    Qed.
  End inductive_step.

  Program Definition fixpoint_chain: chain A := mkchain _ _  (λ α, f (patch_base_case (λ Hα, bcompl Hα (get_chain α (bfpc α))))) _.
  Next Obligation.
    intros β α Hαβ; simpl. unfold patch_base_case. repeat destruct index_is_zero; eauto; subst.
    - destruct Hαβ; subst; by exfalso; eapply index_lt_zero_is_normal.
    - subst. by eapply contractive_0.
    - apply contractive_mono; eauto. apply bounded_fixpoint_chain_unique; eauto using is_fp.
  Qed.

  Program Definition fixpoint_def  : A := compl fixpoint_chain.
  Definition fixpoint_aux : seal (@fixpoint_def). by eexists. Qed.
  Definition fixpoint := fixpoint_aux.(unseal).
  Definition fixpoint_eq : @fixpoint = @fixpoint_def := fixpoint_aux.(seal_eq).

  Lemma fixpoint_unfold :
    fixpoint ≡ f (fixpoint).
  Proof.
    apply equiv_dist=>α.
    rewrite fixpoint_eq /fixpoint_def; cbn.
    erewrite !conv_compl. unfold fixpoint_chain; simpl.
    unfold patch_base_case; destruct index_is_zero; subst.
    - by apply contractive_0.
    - eapply contractive_mono; eauto.  symmetry. eapply is_fp.
  Qed.

End fixpoint.

Section fixpoint.
  Context {SI: indexT} `{Cofe SI A} (f : A → A) `{!Contractive f} `{Inhabited A}.

  Lemma fixpoint_unique (x : A) : x ≡ f x → x ≡ fixpoint f.
  Proof.
    rewrite !equiv_dist=> Hx α. induction (index_lt_wf SI α) as [α _ IH].
    rewrite Hx fixpoint_unfold. eapply contractive_mono; eauto.
  Qed.

  Lemma fixpoint_ne (g : A → A) `{!Contractive g} α :
    (∀ z, f z ≡{α}≡ g z) → fixpoint f ≡{α}≡ fixpoint g.
  Proof.
    intros Hfg. induction (index_lt_wf SI α) as [α _ IH].
    do 2 (rewrite fixpoint_unfold; symmetry). etransitivity. eapply Hfg.
    eapply contractive_mono; eauto.
    intros ??; eapply IH; eauto.
    intros; eapply dist_le', Hfg; eauto.
  Qed.

  Lemma fixpoint_proper (g : A → A) `{!Contractive  g} :
    (∀ x, f x ≡ g x) → fixpoint f ≡ fixpoint g.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_ne. Qed.

  Lemma fixpoint_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) →
    (∀ x, P x → P (f x)) →
    LimitPreserving P →
    BoundedLimitPreserving P →
    P (fixpoint f).
  Proof.
    intros Pr [x Hx] Hincr Hlim Hblim.
    eapply Pr.
    { eapply fixpoint_unique, (@fixpoint_unfold SI A _ f _ {| inhabitant := x |}). }
    rewrite fixpoint_eq /fixpoint_def.
    eapply Hlim. intros β; simpl.
    apply Hincr. 
    rewrite /bfpc. apply index_cumulative_rec_unfold.  
    intros γ succs H1. 
    unfold patch_base_case at 1. destruct index_is_zero; subst. 
    - apply Hx.
    - eapply Hblim. intros. rewrite index_cumulative_rec_dep_step; cbn. apply Hincr, H1.
  Qed.
End fixpoint.


(** Fixpoint of f when f^k is contractive. **)
Definition fixpointK `{Cofe SI A, Inhabited A} k (f : A → A)
  `{!Contractive (Nat.iter k f)} := fixpoint (Nat.iter k f).

Section fixpointK.
  Local Set Default Proof Using "Type*".
  Context `{Cofe SI A, Inhabited A} (f : A → A) (k : nat).
  Context {f_contractive : Contractive (Nat.iter k f)} {f_ne : NonExpansive f}.
  (* Note than f_ne is crucial here:  there are functions f such that f^2 is contractive,
     but f is not non-expansive.
     Consider for example f: SPred → SPred (where SPred is "downclosed sets of natural numbers").
     Define f (using informative excluded middle) as follows:
     f(N) = N  (where N is the set of all natural numbers)
     f({0, ..., n}) = {0, ... n-1}  if n is even (so n-1 is at least -1, in which case we return the empty set)
     f({0, ..., n}) = {0, ..., n+2} if n is odd
     In other words, if we consider elements of SPred as ordinals, then we decreaste odd finite
     ordinals by 1 and increase even finite ordinals by 2.
     f is not non-expansive:  Consider f({0}) = ∅ and f({0,1}) = f({0,1,2,3}).
     The arguments are clearly 0-equal, but the results are not.

     Now consider g := f^2. We have
     g(N) = N
     g({0, ..., n}) = {0, ... n+1}  if n is even
     g({0, ..., n}) = {0, ..., n+4} if n is odd
     g is contractive.  All outputs contain 0, so they are all 0-equal.
     Now consider two n-equal inputs. We have to show that the outputs are n+1-equal.
     Either they both do not contain n in which case they have to be fully equal and
     hence so are the results.  Or else they both contain n, so the results will
     both contain n+1, so the results are n+1-equal.
   *)

  Let f_proper : Proper ((≡) ==> (≡)) f := ne_proper f.
  Local Existing Instance f_proper.

  Lemma fixpointK_unfold : fixpointK k f ≡ f (fixpointK k f).
  Proof.
    symmetry. rewrite /fixpointK. apply fixpoint_unique.
    by rewrite -Nat_iter_S_r Nat_iter_S -fixpoint_unfold.
  Qed.

  Lemma fixpointK_unique (x : A) : x ≡ f x → x ≡ fixpointK k f.
  Proof.
    intros Hf. apply fixpoint_unique. clear f_contractive.
    induction k as [|k' IH]=> //=. by rewrite -IH.
  Qed.

  Section fixpointK_ne.
    Context (g : A → A) `{g_contractive : !Contractive (Nat.iter k g)}.
    Context {g_ne : NonExpansive g}.

    Lemma fixpointK_ne n : (∀ z, f z ≡{n}≡ g z) → fixpointK k f ≡{n}≡ fixpointK k g.
    Proof.
      rewrite /fixpointK=> Hfg /=. apply fixpoint_ne=> z.
      clear f_contractive g_contractive.
      induction k as [|k' IH]=> //=. by rewrite IH Hfg.
    Qed.

    Lemma fixpointK_proper : (∀ z, f z ≡ g z) → fixpointK k f ≡ fixpointK k g.
    Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpointK_ne. Qed.
  End fixpointK_ne.

  Lemma fixpointK_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) → (∀ x, P x → P (f x)) →
    LimitPreserving P →
    BoundedLimitPreserving P →
    P (fixpointK k f).
  Proof.
    intros. rewrite /fixpointK. apply fixpoint_ind; eauto.
    intros; apply Nat_iter_ind; auto.
  Qed.
End fixpointK.

(** Mutual fixpoints *)
Section fixpointAB.
  Local Unset Default Proof Using.

  Context {SI} `{Cofe SI A, Cofe SI B, !Inhabited A, !Inhabited B}.
  Context (fA : A → B → A).
  Context (fB : A → B → B).
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.

  Local Definition fixpoint_AB (x : A) : B := fixpoint (fB x).
  Local Instance fixpoint_AB_contractive : Contractive fixpoint_AB.
  Proof.
    intros n x x' Hx; rewrite /fixpoint_AB.
    apply fixpoint_ne=> y. solve_contractive.
  Qed.

  Local Definition fixpoint_AA (x : A) : A := fA x (fixpoint_AB x).
  Local Instance fixpoint_AA_contractive : Contractive fixpoint_AA.
  Proof. solve_contractive. Qed.

  Definition fixpoint_A : A := fixpoint fixpoint_AA.
  Definition fixpoint_B : B := fixpoint_AB fixpoint_A.

  Lemma fixpoint_A_unfold : fA fixpoint_A fixpoint_B ≡ fixpoint_A.
  Proof. by rewrite {2}/fixpoint_A (fixpoint_unfold _). Qed.
  Lemma fixpoint_B_unfold : fB fixpoint_A fixpoint_B ≡ fixpoint_B.
  Proof. by rewrite {2}/fixpoint_B /fixpoint_AB (fixpoint_unfold _). Qed.

  Instance: Proper ((≡) ==> (≡) ==> (≡)) fA.
  Proof.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; eauto using dist_dist_later.
  Qed.
  Instance: Proper ((≡) ==> (≡) ==> (≡)) fB.
  Proof.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; auto using dist_dist_later.
  Qed.

  Lemma fixpoint_A_unique p q : fA p q ≡ p → fB p q ≡ q → p ≡ fixpoint_A.
  Proof.
    intros HfA HfB. rewrite -HfA. apply fixpoint_unique. rewrite /fixpoint_AA.
    f_equiv=> //. apply fixpoint_unique. by rewrite HfA HfB.
  Qed.
  Lemma fixpoint_B_unique p q : fA p q ≡ p → fB p q ≡ q → q ≡ fixpoint_B.
  Proof. intros. apply fixpoint_unique. by rewrite -fixpoint_A_unique. Qed.
End fixpointAB.

Section fixpointAB_ne.
  Context {SI} `{Cofe SI A, Cofe SI B, !Inhabited A, !Inhabited B}.
  Context (fA fA' : A → B → A).
  Context (fB fB' : A → B → B).
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA'}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB'}.

  Lemma fixpoint_A_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_A fA fB ≡{n}≡ fixpoint_A fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z.
    rewrite /fixpoint_AA /fixpoint_AB HfA. f_equiv. by apply fixpoint_ne.
  Qed.
  Lemma fixpoint_B_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_B fA fB ≡{n}≡ fixpoint_B fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z. rewrite HfB. f_contractive.
    eapply dist_dist_later, fixpoint_A_ne; auto.
  Qed.

  Lemma fixpoint_A_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_A fA fB ≡ fixpoint_A fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_A_ne. Qed.
  Lemma fixpoint_B_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_B fA fB ≡ fixpoint_B fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_B_ne. Qed.
End fixpointAB_ne.


(** Non-expansive function space *)
Record ofe_mor {I: indexT} (A B : ofeT I) : Type := OfeMor {
  ofe_mor_car :> A → B;
  ofe_mor_ne : NonExpansive  ofe_mor_car
}.
Arguments OfeMor {_ _ _} _ {_}.
Add Printing Constructor ofe_mor.
Existing Instance ofe_mor_ne.

Notation "'λne' x .. y , t" :=
  (@OfeMor _ _ _ (λ x, .. (@OfeMor _ _ _ (λ y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).

Section ofe_mor.
  Context {SI: indexT} {A B : ofeT SI}.
  Global Instance ofe_mor_proper (f : ofe_mor A B) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper, ofe_mor_ne. Qed.
  Instance ofe_mor_equiv : Equiv (ofe_mor A B) := λ f g, ∀ x, f x ≡ g x.
  Instance ofe_mor_dist : Dist SI (ofe_mor A B) := λ α f g, ∀ x, f x ≡{α}≡ g x.
  Definition ofe_mor_ofe_mixin : OfeMixin SI (ofe_mor A B).
  Proof.
    split.
    - intros f g; split; [intros Hfg α l; apply equiv_dist, Hfg|].
      intros Hfg l; apply equiv_dist=> α; apply Hfg.
    - intros α; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - intros α β f g ? x ?; by eapply dist_mono.
  Qed.
  Canonical Structure ofe_morO := OfeT (ofe_mor A B) ofe_mor_ofe_mixin.

  Program Definition ofe_mor_chain (c : chain ofe_morO)
    (x : A) : chain B := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy' c). Qed.
  Program Definition ofe_mor_compl `{Cofe SI B} : chain ofe_morO → ofe_morO := λ c,
    {| ofe_mor_car x := compl (ofe_mor_chain c x) |}.
  Next Obligation.
    intros ? c n x y Hx. by rewrite (conv_compl n (ofe_mor_chain c x))
      (conv_compl n (ofe_mor_chain c y)) /= Hx.
  Qed.

  Program Definition ofe_mor_bchain {α} (c : bchain ofe_morO α) (x : A) : bchain B α :=
    {| bchain_car n Hn := c n Hn x |}.
  Next Obligation. intros α c x n Hn i ??. by apply (bchain_cauchy' α c). Qed.
  Program Definition ofe_mor_bcompl `{Cofe SI B} α : zero ≺ α → bchain ofe_morO α → ofe_morO := λ Hα c,
    {| ofe_mor_car x := bcompl Hα (ofe_mor_bchain c x) |}.
  Next Obligation.
    intros ? α Hα c n x y Hx. eapply bcompl_ne.
    by intros; unfold ofe_mor_bchain; simpl; rewrite Hx.
  Qed.


  Global Program Instance ofe_mor_cofe `{Cofe SI B} : Cofe  ofe_morO :=
    {| compl := ofe_mor_compl; bcompl := ofe_mor_bcompl |}.
  Next Obligation.
    intros ? α c x; cbn. rewrite conv_compl //=.
  Qed.
  Next Obligation.
    intros ? α c β Hβ H x; cbn. rewrite (conv_bcompl α) //=.
  Qed.
  Next Obligation.
    move=> ? α Hα c d β Heq x //=. eapply bcompl_ne.
    intros γ Hγ; eapply Heq.
  Qed.

  Global Instance ofe_mor_car_ne :
    NonExpansive2 (@ofe_mor_car SI A B).
  Proof. intros n f g Hfg x y Hx; rewrite Hx; apply Hfg. Qed.
  Global Instance ofe_mor_car_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@ofe_mor_car SI A B) := ne_proper_2 _.
  Lemma ofe_mor_ext (f g : ofe_mor A B) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.

  Lemma ofe_mor_f_equal (f : ofe_mor A B) x y : x ≡ y → f x ≡ f y.
  Proof. intros H. by rewrite H. Qed.
  Lemma ofe_mor_f_equal_dist (f : ofe_mor A B) x y α : x ≡{α}≡ y → f x ≡{α}≡ f y.
  Proof. intros H. by rewrite H. Qed.
End ofe_mor.


Arguments ofe_morO : clear implicits.
Notation "A -n> B" :=
  (ofe_morO _ A B) (at level 99, B at level 200, right associativity).
Instance ofe_mor_inhabited {SI: indexT} {A B : ofeT SI} `{Inhabited B} :
  Inhabited (A -n> B) := populate (λne _, inhabitant).


(** Identity and composition and constant function *)
Definition cid {SI} {A: ofeT SI} : A -n> A := OfeMor id.
Instance: Params (@cid) 2 := {}.
Definition cconst {SI} {A B : ofeT SI} (x : B) : A -n> B := OfeMor (const x).
Instance: Params (@cconst) 3 := {}.

Definition ccompose {SI: indexT} {A B C: ofeT SI}
  (f : B -n> C) (g : A -n> B) : A -n> C := OfeMor (f ∘ g).
Instance: Params (@ccompose) 4 := {}.

Infix "◎" := ccompose (at level 40, left associativity).
Global Instance ccompose_ne SI {A B C: ofeT SI} :
  NonExpansive2 (@ccompose SI A B C).
Proof. intros n ?? Hf g1 g2 Hg x. rewrite /= (Hg x) (Hf (g2 x)) //. Qed.

Lemma ccompose_assoc {SI : indexT} {A B C D : ofeT SI} (f : C -n> D) (g : B -n> C) (h : A -n> B) :
  (f ◎ g) ◎ h ≡ f ◎ (g ◎ h).
Proof. intros x. by cbn. Qed.

Lemma ccompose_cid_l {SI : indexT} {A B : ofeT SI} (f : A -n> B ) : cid ◎ f ≡ f.
Proof. intros x. by cbn. Qed.

Lemma ccompose_cid_r {SI : indexT} {A B : ofeT SI} (f : A -n> B ) :  f ◎ cid ≡ f.
Proof. intros x. by cbn. Qed.

(* Function space maps *)
Definition ofe_mor_map {SI: indexT} {A A' B B': ofeT SI} (f : A' -n> A) (g : B -n> B')
  (h : A -n> B) : A' -n> B' := g ◎ h ◎ f.
Instance ofe_mor_map_ne SI {A A' B B': ofeT SI} α :
  Proper (dist α ==> dist α ==> dist α ==> dist α) (@ofe_mor_map SI A A' B B').
Proof. intros ??? ??? ???. by repeat apply ccompose_ne. Qed.

Definition ofe_morO_map {SI: indexT} {A A' B B': ofeT SI} (f : A' -n> A) (g : B -n> B') :
  (A -n> B) -n> (A' -n>  B') := OfeMor (ofe_mor_map f g).
Instance ofe_morO_map_ne {SI: indexT} {A A' B B': ofeT SI} :
  NonExpansive2 (@ofe_morO_map SI A A' B B').
Proof.
  intros n f f' Hf g g' Hg ?. rewrite /= /ofe_mor_map.
  by repeat apply ccompose_ne.
Qed.

(** unit *)
Section unit.
  Context {SI: indexT}.
  Instance unit_dist k : Dist k () := λ _ _ _, True.
  Definition unit_ofe_mixin : OfeMixin SI ().
  Proof. by repeat split. Qed.
  Canonical Structure unitO : ofeT SI := OfeT () unit_ofe_mixin.

  Global Program Instance unit_cofe : Cofe  unitO  := { compl x := () }.
  Solve All Obligations with by repeat split.

  Global Instance unit_ofe_discrete : OfeDiscrete unitO.
  Proof. done. Qed.
End unit.
Arguments unitO : clear implicits.




(** Product *)
Section product.
  Context {SI: indexT} {A B : ofeT SI}.

  Instance prod_dist : Dist SI (A * B) := λ n, prod_relation (dist n) (dist n).
  Global Instance pair_ne :
    NonExpansive2 (@pair A B) := _.
  Global Instance fst_ne : NonExpansive  (@fst A B) := _.
  Global Instance snd_ne : NonExpansive  (@snd A B) := _.
  Definition prod_ofe_mixin : OfeMixin SI (A * B).
  Proof.
    split.
    - intros x y; unfold dist, prod_dist, equiv, prod_equiv, prod_relation.
      rewrite !equiv_dist; naive_solver.
    - apply _.
    - by intros α β [x1 y1] [x2 y2] [??]; split; eapply dist_mono.
  Qed.
  Canonical Structure prodO : ofeT SI := OfeT (A * B) prod_ofe_mixin.

  Global Program Instance prod_cofe `{Cofe SI A, Cofe SI B} : Cofe prodO :=
    { compl c := (compl (chain_map fst c), compl (chain_map snd c));
      bcompl α Hα c := (bcompl Hα (bchain_map fst c), bcompl Hα (bchain_map snd c)) }.
  Next Obligation.
    repeat split; cbn; by rewrite conv_compl.
  Qed.
  Next Obligation.
    repeat split; cbn; by rewrite conv_bcompl; simpl.
  Qed.
  Next Obligation.
    intros; cbn; split; cbn; eapply bcompl_ne; intros; simpl; eapply ne_apply; eauto.
  Qed.


  Global Instance prod_discrete (x : A * B) :
    Discrete (x.1) → Discrete (x.2) → Discrete x.
  Proof. by intros ???[??]; split; apply (discrete _). Qed.
  Global Instance prod_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete prodO.
  Proof. intros ?? [??]; apply _. Qed.
End product.

Arguments prodO {_} _ _.
Typeclasses Opaque prod_dist.

Instance prod_map_ne {SI: indexT} {A A' B B' : ofeT SI} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@prod_map A A' B B').
Proof. by intros f f' Hf g g' Hg ?? [??]; split; [apply Hf|apply Hg]. Qed.
Definition prodO_map {SI: indexT} {A A' B B': ofeT SI} (f : A -n> A') (g : B -n> B') :
  prodO A B -n> prodO A' B' := OfeMor (prod_map f g).
Instance prodO_map_ne {SI: indexT} {A A' B B': ofeT SI} :
  NonExpansive2 (@prodO_map SI A A' B B').
Proof. intros n f f' Hf g g' Hg [??]; split; [apply Hf|apply Hg]. Qed.

(** Functors *)
Record oFunctor {SI} := OFunctor {
  oFunctor_car : ∀ A B, ofeT SI;
  oFunctor_map  {A1 A2 B1 B2}:
    ((A2 -n> A1) * (B1 -n> B2)) → oFunctor_car A1 B1 -n> oFunctor_car A2 B2;
  oFunctor_ne {A1 A2 B1 B2}:
    NonExpansive  (@oFunctor_map A1 A2 B1 B2);
  oFunctor_id {A B} (x : oFunctor_car A B) :
    oFunctor_map (cid,cid) x ≡ x;
  oFunctor_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    oFunctor_map (f◎g, g'◎f') x ≡ oFunctor_map (g,g') (oFunctor_map (f,f') x)
}.
Existing Instance oFunctor_ne.
Instance: Params (@oFunctor_map) 6 := {}.
Arguments oFunctor : clear implicits.


Delimit Scope oFunctor_scope with OF.
Bind Scope oFunctor_scope with oFunctor.

Class oFunctorContractive {I: indexT} (F : oFunctor I) :=
  oFunctor_contractive `{A1 : ofeT I} `{A2 : ofeT I} `{B1 : ofeT I} `{B2 : ofeT I} :>
    Contractive  (@oFunctor_map I F A1 A2 B1 B2).
Hint Mode oFunctorContractive - ! : typeclass_instances.

Definition oFunctor_diag {SI: indexT} (F: oFunctor SI) (A: ofeT SI) : ofeT SI := oFunctor_car F A A.
Coercion oFunctor_diag : oFunctor >-> Funclass.

Program Definition constOF {SI} (B : ofeT SI) : oFunctor SI :=
  {| oFunctor_car A1 A2 := B; oFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion constOF : ofeT >-> oFunctor.

Instance constOF_Contractive {SI}  B : @oFunctorContractive SI (constOF B).
Proof. rewrite /oFunctorContractive; apply _. Qed.

Program Definition idOF SI : oFunctor SI :=
  {| oFunctor_car A1 A2 := A2; oFunctor_map A1 A2 B1 B2 f := f.2 |}.
Solve Obligations with done.
Notation "∙" := idOF : oFunctor_scope.

Program Definition prodOF {SI} (F1 F2 : oFunctor SI) : oFunctor SI := {|
  oFunctor_car A B := prodO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map A1 A2 B1 B2 fg :=
    prodO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros k ?? A1 A2 B1 B2 n ???; by apply prodO_map_ne; apply oFunctor_ne.
Qed.
Next Obligation. by intros k F1 F2 A B [??]; rewrite /= !oFunctor_id. Qed.
Next Obligation.
  intros k F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !oFunctor_compose.
Qed.
Notation "F1 * F2" := (prodOF F1%OF F2%OF) : oFunctor_scope.

Instance prodOF_Contractive {SI} {F1 F2 : ofeT SI}:
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (prodOF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply prodO_map_ne; apply oFunctor_contractive.
Qed.

Program Definition ofe_morOF {SI: indexT} (F1 F2 : oFunctor SI) : oFunctor SI := {|
  oFunctor_car A B := oFunctor_car F1 B A -n> oFunctor_car F2 A B;
  oFunctor_map A1 A2 B1 B2 fg :=
    ofe_morO_map (oFunctor_map F1 (fg.2, fg.1)) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros k F1 F2 A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply oFunctor_ne; split; by apply Hfg.
Qed.
Next Obligation.
  intros k F1 F2 A B [f ?] ?; simpl. rewrite /= !oFunctor_id.
  apply (ne_proper f). apply oFunctor_id.
Qed.
Next Obligation.
  intros k F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [h ?] ?; simpl in *.
  rewrite -!oFunctor_compose. do 2 apply (ne_proper _). apply oFunctor_compose.
Qed.
Notation "F1 -n> F2" := (ofe_morOF F1%OF F2%OF) : oFunctor_scope.

Instance ofe_morOF_Contractive {I: indexT}  (F1 F2 : oFunctor I):
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (ofe_morOF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply oFunctor_contractive; unfold dist_later; intros; split; cbn; eauto.
  all: destruct (Hfg β); auto.
Qed.


(** Sum *)

Section sum.
  Context {SI: indexT} {A B : ofeT SI}.

  Instance sum_dist : Dist SI (A + B) := λ n, sum_relation (dist n) (dist n).


  Global Instance inl_ne : NonExpansive (@inl A B) := _.
  Global Instance inr_ne : NonExpansive (@inr A B) := _.
  Global Instance inl_ne_inj : Inj (dist n) (dist n) (@inl A B) := _.
  Global Instance inr_ne_inj : Inj (dist n) (dist n) (@inr A B) := _.

  Definition sum_ofe_mixin : OfeMixin SI (A + B).
  Proof.
    split.
    - intros x y; split=> Hx.
      + destruct Hx=> n; constructor; by apply equiv_dist.
      + destruct (Hx zero); constructor; apply equiv_dist=> n; by apply (inj _).
    - apply _.
    - destruct 1; constructor; eapply dist_mono; eauto.
  Qed.

  Canonical Structure sumO : ofeT SI := OfeT (A + B) sum_ofe_mixin.

  Program Definition inl_chain (c : chain sumO) (a : A) : chain A :=
    {| chain_car n := match c n return _ with inl a' => a' | _ => a end |}.
  Next Obligation. intros c a n i ?; simpl. by destruct (chain_cauchy' c n i). Qed.
  Program Definition inr_chain (c : chain sumO) (b : B) : chain B :=
    {| chain_car n := match c n return _ with inr b' => b' | _ => b end |}.
  Next Obligation. intros c b n i ?; simpl. by destruct (chain_cauchy' c n i). Qed.
  Definition sum_compl `{Cofe SI A, Cofe SI B} : chain sumO → sumO := λ c,
    match c zero with
    | inl a => inl (compl (inl_chain c a))
    | inr b => inr (compl (inr_chain c b))
    end.

  Program Definition inl_bchain {α} (c : bchain sumO α) (a : A) : bchain A α :=
    {| bchain_car n Hn := match c n Hn return _ with inl a' => a' | _ => a end |}.
  Next Obligation. intros α c a β γ ? Hβ Hγ; simpl. by destruct (bchain_cauchy' α c β γ Hβ Hγ). Qed.
  Program Definition inr_bchain {α} (c : bchain sumO α) (b : B) : bchain B α :=
    {| bchain_car n Hn := match c n Hn return _ with inr b' => b' | _ => b end |}.
  Next Obligation. intros α c b β γ ? Hβ Hγ; simpl. by destruct (bchain_cauchy' α c β γ Hβ Hγ). Qed.
  Definition sum_bcompl `{Cofe SI A, Cofe SI B} α : zero ≺ α → bchain sumO α → sumO :=
    λ Hα c,
    match c zero Hα with
    | inl a => inl (bcompl Hα (inl_bchain c a))
    | inr b => inr (bcompl Hα (inr_bchain c b))
    end.

  Global Program Instance sum_cofe `{Cofe SI A, Cofe SI B} : Cofe  sumO :=
    { compl := sum_compl; bcompl := sum_bcompl }.
  Next Obligation.
    intros ?? n c; rewrite /compl /sum_compl.
    feed inversion (chain_cauchy' c zero n).
    - apply index_zero_minimum.
    - rewrite (conv_compl n (inl_chain c _)) /=. destruct (c n); naive_solver.
    - rewrite (conv_compl n (inr_chain c _)) /=. destruct (c n); naive_solver.
  Qed.
  Next Obligation.
    intros ?? α Hα c β Hβ. rewrite /sum_bcompl.
    feed inversion (bchain_cauchy' α c zero β Hα Hβ).
    - apply index_zero_minimum.
    - rewrite (conv_bcompl α _ _ _ Hβ) /=. destruct (c β _); naive_solver.
    - rewrite (conv_bcompl α _ _ _ Hβ) /=. destruct (c β _); naive_solver.
  Qed.
  Next Obligation.
    intros ?????? β H1. unfold sum_bcompl.
    destruct (H1 zero Hα); simpl; rewrite bcompl_ne; eauto.
    all: intros γ Hγ; simpl; destruct (H1 γ Hγ); eauto.
  Qed.

  Global Instance inl_discrete (x : A) : Discrete x → Discrete (inl x).
  Proof. inversion_clear 2; constructor; by apply (discrete _). Qed.
  Global Instance inr_discrete (y : B) : Discrete y → Discrete (inr y).
  Proof. inversion_clear 2; constructor; by apply (discrete _). Qed.
  Global Instance sum_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete sumO.
  Proof. intros ?? [?|?]; apply _. Qed.
End sum.

Arguments sumO {_} _ _.
Typeclasses Opaque sum_dist.

Instance sum_map_ne {SI: indexT} {A A' B B' : ofeT SI} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@sum_map A A' B B').
Proof.
  intros f f' Hf g g' Hg ??; destruct 1; constructor; [by apply Hf|by apply Hg].
Qed.
Definition sumO_map {SI: indexT} {A A' B B': ofeT SI} (f : A -n> A') (g : B -n> B') :
  sumO A B -n> sumO A' B' := OfeMor (sum_map f g).
Instance sumO_map_ne {SI} {A A' B B'} :
  NonExpansive2 (@sumO_map SI A A' B B').
Proof. intros n f f' Hf g g' Hg [?|?]; constructor; [apply Hf|apply Hg]. Qed.

Program Definition sumOF {SI: indexT} (F1 F2 : oFunctor SI) : oFunctor SI := {|
  oFunctor_car A B := sumO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map A1 A2 B1 B2 fg :=
    sumO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros ??? A1 A2 B1 B2 n ???; by apply sumO_map_ne; apply oFunctor_ne.
Qed.
Next Obligation. by intros ? F1 F2 A B [?|?]; rewrite /= !oFunctor_id. Qed.
Next Obligation.
  intros ? F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [?|?]; simpl;
    by rewrite !oFunctor_compose.
Qed.
Notation "F1 + F2" := (sumOF F1%OF F2%OF) : oFunctor_scope.

Instance sumOF_contractive {SI: indexT} (F1 F2 : oFunctor SI):
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (sumOF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply sumO_map_ne; apply oFunctor_contractive.
Qed.


(** Discrete OFE *)
Section discrete_ofe.
  Context {SI: indexT} {A: Type} `{Equiv A}  (Heq : @Equivalence A (≡)).

  Instance discrete_dist : Dist SI A := λ n x y, x ≡ y.
  Definition discrete_ofe_mixin : OfeMixin SI A.
  Proof using Type*.
    split.
    - intros x y; split; [done|intros Hn; apply (Hn zero)].
    - done.
    - done.
  Qed.

  Global Instance discrete_ofe_discrete : OfeDiscrete (OfeT A discrete_ofe_mixin).
  Proof. by intros x y. Qed.

  Global Program Instance discrete_cofe : Cofe  (OfeT A discrete_ofe_mixin) :=
    { compl c := c zero;
      bcompl α Hα c := c zero Hα
    }.
  Next Obligation.
    intros α c; simpl.
    symmetry; apply (chain_cauchy' c zero α).
    eapply index_zero_minimum.
  Qed.
  Next Obligation.
    intros α Hα c; simpl.
    symmetry; apply (bchain_cauchy' α c zero β).
    eapply index_zero_minimum.
  Qed.
  Next Obligation.
    intros; simpl; eauto.
  Qed.

End discrete_ofe.

Notation discreteO SI A := (OfeT A (discrete_ofe_mixin _): ofeT SI).
Notation leibnizO SI A := (OfeT A (@discrete_ofe_mixin SI _ equivL _): ofeT SI).

(** In order to define a discrete CMRA with carrier [A] (in the file [cmra.v])
we need to determine the [Equivalence A] proof that was used to construct the
OFE instance of [A] (note that this proof is not the same as the one we obtain
via [ofe_equivalence]).

We obtain the proof of [Equivalence A] by inferring the canonical OFE mixin
using [ofe_mixin_of A], and then check whether it is indeed a discrete OFE. This
will fail if no OFE, or an OFE other than the discrete OFE, was registered. *)
Notation discrete_ofe_equivalence_of SI A := ltac:(
  match constr:(ofe_mixin_of SI A) with
  | discrete_ofe_mixin ?H => exact H
  end) (only parsing).

Instance leibnizO_leibniz A {SI} : LeibnizEquiv (leibnizO SI A : ofeT SI).
Proof. by intros x y. Qed.

Canonical Structure boolO SI : ofeT SI := leibnizO SI bool.
Canonical Structure natO SI : ofeT SI := leibnizO SI nat.
Canonical Structure positiveO SI : ofeT SI := leibnizO SI positive.
Canonical Structure NO SI : ofeT SI := leibnizO SI N.
Canonical Structure ZO SI : ofeT SI := leibnizO SI Z.

(* Option *)
Section option.
  Context {SI: indexT} {A : ofeT SI}.

  Instance option_dist : Dist SI (option A) := λ α, option_Forall2 (dist α).
  Lemma dist_option_Forall2 α mx my : mx ≡{α}≡ my ↔ option_Forall2 (dist α) mx my.
  Proof. done. Qed.

  Definition option_ofe_mixin : OfeMixin SI (option A).
  Proof.
    split.
    - intros mx my; split; [by destruct 1; constructor; apply equiv_dist|].
      intros Hxy; destruct (Hxy zero); constructor; apply equiv_dist.
      by intros α; feed inversion (Hxy α).
    - apply _.
    - destruct 1; constructor; eapply dist_le; eauto.
  Qed.
  Canonical Structure optionO := OfeT (option A) option_ofe_mixin.


  Global Instance Some_ne : NonExpansive (@Some A).
  Proof. intros ????. by econstructor. Qed.
  Global Instance Some_ne_inj : Inj (dist n) (dist n) (@Some A).
  Proof. intros ??? H. by inversion H. Qed.

  Program Definition option_chain (c : chain optionO) (x : A) : chain A :=
    {| chain_car n := default x (c n) |}.
  Next Obligation. intros c x n i ?; simpl. by destruct (chain_cauchy' c n i). Qed.
  Definition option_compl `{Cofe SI A} : (chain optionO) → optionO := λ c,
    match c zero with Some x => Some (compl (option_chain c x)) | None => None end.

  Program Definition option_bchain α (c : bchain optionO α) (x : A) : bchain A α :=
    {| bchain_car n Hn := default x (c n Hn) |}.
  Next Obligation. intros α c x β γ ? Hβ Hγ; simpl. by destruct (bchain_cauchy' α c β γ Hβ Hγ). Qed.
  Definition option_bcompl `{Cofe SI A} α (Hα: zero ≺ α): (bchain optionO α) → optionO := λ c,
    match c zero Hα with Some x => Some (bcompl Hα (option_bchain α c x)) | None => None end.

  Global Program Instance option_cofe `{Cofe SI A} : Cofe optionO :=
    { compl := option_compl; bcompl := option_bcompl }.
  Next Obligation.
    intros ? n c; rewrite /compl /option_compl.
    feed inversion (chain_cauchy' c zero n); auto using index_zero_minimum.
    constructor. rewrite (conv_compl n (option_chain c _)) /=.
    destruct (c n); naive_solver.
  Qed.
  Next Obligation.
    intros ? α Hα c β Hβ; rewrite /bcompl /option_bcompl.
    feed inversion (bchain_cauchy' α c zero β Hα Hβ); auto using index_zero_minimum.
    constructor. unshelve rewrite conv_bcompl; eauto; simpl.
    destruct (c β Hβ); naive_solver.
  Qed.
  Next Obligation.
    intros ? α Hα c d β Hc; rewrite /bcompl /option_bcompl.
    destruct (Hc zero Hα); auto. rewrite bcompl_ne; eauto.
    intros γ Hγ; simpl. destruct (Hc γ Hγ); eauto.
  Qed.

  Global Instance option_ofe_discrete : OfeDiscrete A → OfeDiscrete optionO.
  Proof. destruct 2; constructor; by apply (discrete _). Qed.

  Global Instance is_Some_ne n : Proper (dist n ==> iff) (@is_Some A).
  Proof. destruct 1; split; eauto. Qed.
  Global Instance from_option_ne {B} (R : relation B) (f : A → B) n :
    Proper (dist n ==> R) f → Proper (R ==> dist n ==> R) (from_option f).
  Proof. destruct 3; simpl; auto. Qed.

  Global Instance None_discrete : Discrete (@None A).
  Proof. inversion_clear 1; constructor. Qed.
  Global Instance Some_discrete x : Discrete x → Discrete (Some x).
  Proof. by intros ?; inversion_clear 1; constructor; apply discrete. Qed.

  Lemma dist_None α mx : mx ≡{α}≡ None ↔ mx = None.
  Proof. split; [by inversion_clear 1|by intros ->]. Qed.
  Lemma dist_Some α x y : Some x ≡{α}≡ Some y ↔ x ≡{α}≡ y.
  Proof. split; [by inversion_clear 1 | by intros ->]. Qed.
  Lemma dist_Some_inv_l α mx my x :
    mx ≡{α}≡ my → mx = Some x → ∃ y, my = Some y ∧ x ≡{α}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_r α mx my y :
    mx ≡{α}≡ my → my = Some y → ∃ x, mx = Some x ∧ x ≡{α}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_l' α my x : Some x ≡{α}≡ my → ∃ x', Some x' = my ∧ x ≡{α}≡ x'.
  Proof. intros ?%(dist_Some_inv_l _ _ _ x); naive_solver. Qed.
  Lemma dist_Some_inv_r' α mx y : mx ≡{α}≡ Some y → ∃ y', mx = Some y' ∧ y ≡{α}≡ y'.
  Proof. intros ?%(dist_Some_inv_r _ _ _ y); naive_solver. Qed.
End option.

Typeclasses Opaque option_dist.
Arguments optionO {_} _.

Instance option_fmap_ne {SI} {A B : ofeT SI} α:
  Proper ((dist α ==> dist α) ==> dist α ==> dist α) (@fmap option _ A B).
Proof. intros f f' Hf ?? []; constructor; auto. Qed.
Instance option_mbind_ne {SI} {A B : ofeT SI} α:
  Proper ((dist α ==> dist α) ==> dist α ==> dist α) (@mbind option _ A B).
Proof. destruct 2; simpl; auto. Qed.
Instance option_mjoin_ne {SI} {A : ofeT SI} α:
  Proper (dist α ==> dist α) (@mjoin option _ A).
Proof. destruct 1 as [?? []|]; simpl; by constructor. Qed.

Definition optionO_map {SI} {A B: ofeT SI} (f : A -n> B) : optionO A -n> optionO B :=
  OfeMor (fmap f : optionO A → optionO B).
Instance optionO_map_ne {SI} (A B: ofeT SI) : NonExpansive (@optionO_map _ A B).
Proof. by intros n f f' Hf []; constructor; apply Hf. Qed.

Program Definition optionOF {SI: indexT} (F : oFunctor SI) : oFunctor SI := {|
  oFunctor_car A B := optionO (oFunctor_car F A B);
  oFunctor_map A1 A2 B1 B2 fg := optionO_map (oFunctor_map F fg)
|}.
Next Obligation.
  by intros SI F A1 A2 B1 B2 n f g Hfg; apply optionO_map_ne, oFunctor_ne.
Qed.
Next Obligation.
  intros SI F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply oFunctor_id.
Qed.
Next Obligation.
  intros SI F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply oFunctor_compose.
Qed.

Instance optionOF_contractive {SI} (F : oFunctor SI):
  oFunctorContractive F → oFunctorContractive (optionOF F).
Proof.
  by intros ? ? A1 A2 B1 B2 n f g Hfg; apply optionO_map_ne, oFunctor_contractive.
Qed.

(** Later *)
(** Note that the projection [later_car] is not non-expansive (see also the
lemma [later_car_anti_contractive] below), so it cannot be used in the logic.
If you need to get a witness out, you should use the lemma [Next_uninj]
instead. *)
Record later (A : Type) : Type := Next { later_car : A }.
Add Printing Constructor later.
Arguments Next {_} _.
Arguments later_car {_} _.
Instance: Params (@Next) 1 := {}.



Section later.
  Context {SI: indexT} {A : ofeT SI}.
  Instance later_equiv : Equiv (later A) := λ x y, later_car x ≡ later_car y.
  Instance later_dist : Dist SI (later A) := λ α x y,
    dist_later α (later_car x) (later_car y).
  Definition later_ofe_mixin : OfeMixin SI (later A).
  Proof.
    split.
    - intros x y; unfold equiv, later_equiv; rewrite !equiv_dist.
      split; first by intros Hxy α β Hβ.
      intros H α; eapply (H (succ α)). by eapply index_succ_iff.
    - split; rewrite /dist /later_dist.
      + by intros [x].
      + by intros [x] [y].
      + by intros [x] [y] [z] ??; trans y.
    - intros α β [x] [y] H ? γ Hγ. eapply H; by transitivity β.
  Qed.
  Canonical Structure laterO : ofeT SI := OfeT (later A) later_ofe_mixin.

  Lemma later_car_bounded_expansive (a b : laterO) α: a ≡{succ α}≡ b → later_car a ≡{α}≡ later_car b.
  Proof.
    intros H. destruct a as [a], b as [b]; cbn in *. apply (H α (index_succ_greater _)).
  Qed.

  Lemma later_dist_unfold (a b : laterO) α : a ≡{α}≡ b ↔ dist_later α (later_car a) (later_car b).
  Proof. tauto. Qed.

  Program Definition later_chain (c : chain laterO) : chain A :=
    {| chain_car n := later_car (c (succ n)) |}.
  Next Obligation.
    intros c n i ?; apply (chain_cauchy' c (succ n)); eauto with index.
  Qed.

  Program Definition later_limit_bchain {α} (c : bchain laterO α) (islim: ∀ β, β ≺ α → succ β ≺ α) : bchain A α :=
    {| bchain_car β Hβ := later_car (c (succ β) (islim β Hβ)) |}.
  Next Obligation.
    intros α c islim β γ ? Hβ Hγ; apply (bchain_cauchy' α c (succ β) (succ γ)); eauto with index.
  Qed.


  Global Instance Next_contractive : Contractive  (@Next A).
  Proof. by intros α x y. Qed.

  Global Program Instance later_cofe `{Cofe SI A} : Cofe laterO :=
    { compl c := Next (compl (later_chain c));
      bcompl α Hα c :=
        match index_dec_limit α with
        | inl (exist _ β H) => c β (index_succ_greater' _ _ H)
        | inr islim => Next (bcompl Hα (later_limit_bchain c islim))
        end
    }.
  Next Obligation.
    intros ? α c β Hβ; simpl. rewrite conv_compl /=.
    symmetry; apply (chain_cauchy' c (succ β) α); eauto with index.
  Qed.
  Next Obligation.
    intros ? α Hα c β Hβ; simpl; destruct index_dec_limit as [[γ ?]|islim]; subst.
    - by eapply bchain_cauchy, index_succ_iff.
    - intros γ Hγ; simpl. unshelve rewrite conv_bcompl; simpl.
      eauto using index_lt_le_trans. symmetry. eapply (bchain_cauchy' α c (succ γ)); eauto with index.
  Qed.
  Next Obligation.
    intros ? α Hα c d β H; simpl; destruct index_dec_limit as [[γ ->]|islim]; eauto.
    intros γ Hγ; simpl; eapply bcompl_ne; intros δ Hδ; simpl; by eapply H.
  Qed.

  Global Instance Later_inj n : Inj (dist_later n) (dist n) (@Next A).
  Proof. by intros x y H. Qed.

  Lemma Next_uninj x : ∃ a, x ≡ Next a.
  Proof. by exists (later_car x). Qed.
  Instance later_car_anti_contractive n :
    Proper (dist n ==> dist_later n) later_car.
  Proof. move=> [x] [y] /= Hxy. done. Qed.

  (* f is contractive iff it can factor into `Next` and a non-expansive function. *)
  Lemma contractive_alt {B : ofeT SI} (f : A → B) :
    Contractive  f ↔ ∃ g : later A → B, NonExpansive  g ∧ ∀ x, f x ≡ g (Next x).
  Proof.
    split.
    - intros Hf. exists (f ∘ later_car); split=> // n x y ?. by eapply ne_apply.
    - intros (g&Hg&Hf) n x y Hxy. rewrite !Hf. by apply Hg.
  Qed.
End later.

Arguments laterO {_} _.

Definition later_map {A B} (f : A → B) (x : later A) : later B :=
  Next (f (later_car x)).
Instance later_map_ne {I: indexT} {A B : ofeT I} (f : A → B) n :
  Proper (dist_later n ==> dist_later n) f →
  Proper (dist n ==> dist n) (later_map f) | 0.
Proof. intros P [x] [y] H; rewrite /later_map //=.
       intros α Hα; apply P, Hα. apply H.
Qed.

Instance later_map_ne' {SI: indexT} {A B : ofeT SI} (f : A → B) `{NonExpansive  f} : NonExpansive  (later_map f).
Proof. intros ?[x][y]H. unfold later_map; simpl.
       intros ??; cbn. by eapply ne_apply, H.
Qed.

Lemma later_map_id {A} (x : later A) : later_map id x = x.
Proof. by destruct x. Qed.
Lemma later_map_compose {A B C} (f : A → B) (g : B → C) (x : later A) :
  later_map (g ∘ f) x = later_map g (later_map f x).
Proof. by destruct x. Qed.
Lemma later_map_ext {SI: indexT} {A B : ofeT SI} (f g : A → B) x :
  (∀ x, f x ≡ g x) → later_map f x ≡ later_map g x.
Proof. destruct x; intros Hf; apply Hf. Qed.
Definition laterO_map {SI: indexT} {A B: ofeT SI} (f : A -n> B) : laterO A -n> laterO B :=
  OfeMor (later_map f).
Instance laterO_map_contractive {SI: indexT} (A B : ofeT SI) : Contractive  (@laterO_map SI A B).
Proof. intros α f g ? [x] ??; simpl. by apply H. Qed.

Program Definition laterOF {SI: indexT} (F : oFunctor SI) : oFunctor SI := {|
  oFunctor_car A B := laterO (oFunctor_car F A B);
  oFunctor_map A1 A2 B1 B2 fg := laterO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros k F A1 A2 B1 B2 n fg fg' ?.
  by apply (contractive_ne laterO_map), oFunctor_ne.
Qed.
Next Obligation.
  intros k F A B x; simpl. rewrite -{2}(later_map_id x).
  apply later_map_ext=>y. by rewrite oFunctor_id.
Qed.
Next Obligation.
  intros k F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -later_map_compose.
  apply later_map_ext=>y; apply oFunctor_compose.
Qed.
Notation "▶ F"  := (laterOF F%OF) (at level 20, right associativity) : oFunctor_scope.

Instance laterOF_contractive {SI: indexT} {F :oFunctor SI} : oFunctorContractive (laterOF F).
Proof.
  intros A1 A2 B1 B2 n fg fg' Hfg. apply laterO_map_contractive.
  intros ???; simpl.  by eapply oFunctor_ne, Hfg.
Qed.


(* Dependently-typed functions over a discrete domain *)
(* We make [discrete_fun] a definition so that we can register it as a canonical
structure. *)
Definition discrete_fun {SI: indexT} {A} (B : A → ofeT SI) := ∀ x : A, B x.

Section discrete_fun.
  Context {SI: indexT} {A : Type} {B : A → ofeT SI}.
  Implicit Types f g : discrete_fun B.

  Instance discrete_fun_equiv : Equiv (discrete_fun B) := λ f g, ∀ x, f x ≡ g x.
  Instance discrete_fun_dist : Dist SI (discrete_fun B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition discrete_fun_ofe_mixin : OfeMixin SI (discrete_fun B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - intros n m f g ? H x. eauto using dist_le.
  Qed.
  Canonical Structure discrete_funO := OfeT (discrete_fun B) discrete_fun_ofe_mixin.

  Program Definition discrete_fun_chain `(c : chain discrete_funO) (x : A) : chain (B x) :=
    {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy' c). Qed.
  Program Definition discrete_fun_bchain {α} `(c : bchain discrete_funO α) (x : A) : bchain (B x) α :=
    {| bchain_car n Hn := c n Hn x |}.
  Next Obligation. intros α c x β γ ? Hβ Hγ. by apply (bchain_cauchy' α c _ _  Hβ Hγ). Qed.


  Global Program Instance discrete_fun_cofe `{∀ x, Cofe (B x)} : Cofe discrete_funO :=
    { compl c x := compl (discrete_fun_chain c x); bcompl α Hα c x := bcompl Hα (discrete_fun_bchain c x) }.
  Next Obligation.
    intros ? α c x. by apply conv_compl.
  Qed.
  Next Obligation.
    intros ? α Hα c β Hβ x. unshelve rewrite conv_bcompl; eauto.
  Qed.
  Next Obligation.
    intros ? α Hα c d β H x. eapply bcompl_ne; intros; simpl; by eapply H.
  Qed.

  Global Instance discrete_fun_inhabited `{∀ x, Inhabited (B x)} : Inhabited discrete_funO :=
    populate (λ _, inhabitant).
  Global Instance discrete_fun_lookup_discrete `{EqDecision A} f x :
    Discrete f → Discrete (f x).
  Proof.
    intros Hf y ?.
    set (g x' := if decide (x = x') is left H then eq_rect _ B y _ H else f x').
    trans (g x).
    { apply Hf=> x'. unfold g. by destruct (decide _) as [[]|]. }
    unfold g. destruct (decide _) as [Hx|]; last done.
    by rewrite (proof_irrel Hx eq_refl).
  Qed.
End discrete_fun.

Arguments discrete_funO {_ _} _.
Notation "A -d> B" :=
  (@discrete_funO _ A (λ _, B)) (at level 99, B at level 200, right associativity).

Definition discrete_fun_map {SI A} {B1 B2 : A → ofeT SI} (f : ∀ x, B1 x → B2 x)
  (g : discrete_fun B1) : discrete_fun B2 := λ x, f _ (g x).

Lemma discrete_fun_map_ext {SI A} {B1 B2 : A → ofeT SI} (f1 f2 : ∀ x, B1 x → B2 x)
  (g : discrete_fun B1) :
  (∀ x, f1 x (g x) ≡ f2 x (g x)) → discrete_fun_map f1 g ≡ discrete_fun_map f2 g.
Proof. done. Qed.
Lemma discrete_fun_map_id {SI A} {B : A → ofeT SI} (g : discrete_fun B) :
  discrete_fun_map (λ _, id) g = g.
Proof. done. Qed.
Lemma discrete_fun_map_compose {SI A} {B1 B2 B3 : A → ofeT SI}
    (f1 : ∀ x, B1 x → B2 x) (f2 : ∀ x, B2 x → B3 x) (g : discrete_fun B1) :
  discrete_fun_map (λ x, f2 x ∘ f1 x) g = discrete_fun_map f2 (discrete_fun_map f1 g).
Proof. done. Qed.

Instance discrete_fun_map_ne {SI A} {B1 B2 : A → ofeT SI} (f : ∀ x, B1 x → B2 x) n :
  (∀ x, Proper (dist n ==> dist n) (f x)) →
  Proper (dist n ==> dist n) (discrete_fun_map f).
Proof. by intros ? y1 y2 Hy x; rewrite /discrete_fun_map (Hy x). Qed.

Definition discrete_funO_map {SI A} {B1 B2 : A → ofeT SI} (f : discrete_fun (λ x, B1 x -n> B2 x)) :
  discrete_funO B1 -n> discrete_funO B2 := OfeMor (discrete_fun_map f).
Instance discrete_funO_map_ne {SI A} {B1 B2 : A → ofeT SI} :
  NonExpansive (@discrete_funO_map SI A B1 B2).
Proof. intros n f1 f2 Hf g x; apply Hf. Qed.

Program Definition discrete_funOF {SI C} (F : C → oFunctor SI) : oFunctor SI := {|
  oFunctor_car A B := discrete_funO (λ c, oFunctor_car (F c) A B);
  oFunctor_map A1 A2 B1 B2 fg := discrete_funO_map (λ c, oFunctor_map (F c) fg)
|}.
Next Obligation.
  intros SI C F A1 A2 B1 B2 n ?? g. by apply discrete_funO_map_ne=>?; apply oFunctor_ne.
Qed.
Next Obligation.
  intros SI C F A B g; simpl. rewrite -{2}(discrete_fun_map_id g).
  apply discrete_fun_map_ext=> y; apply oFunctor_id.
Qed.
Next Obligation.
  intros SI C F A1 A2 A3 B1 B2 B3 f1 f2 f1' f2' g.
  rewrite /= -discrete_fun_map_compose.
  apply discrete_fun_map_ext=>y; apply oFunctor_compose.
Qed.

Notation "T -d> F" := (@discrete_funOF _ T%type (λ _, F%OF)) : oFunctor_scope.

Instance discrete_funOF_contractive {SI C} (F : C → oFunctor SI) :
  (∀ c, oFunctorContractive (F c)) → oFunctorContractive (discrete_funOF F).
Proof.
  intros ? A1 A2 B1 B2 n ?? g.
  by apply discrete_funO_map_ne=>c; apply oFunctor_contractive.
Qed.



(** Constructing isomorphic OFEs *)
Lemma iso_ofe_mixin {SI} {A : ofeT SI} `{Equiv B, Dist SI B} (g : B → A)
  (g_equiv : ∀ y1 y2, y1 ≡ y2 ↔ g y1 ≡ g y2)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2) : OfeMixin SI B.
Proof.
  split.
  - intros y1 y2. rewrite g_equiv. setoid_rewrite g_dist. apply equiv_dist.
  - split.
    + intros y. by apply g_dist.
    + intros y1 y2. by rewrite !g_dist.
    + intros y1 y2 y3. rewrite !g_dist. intros ??; etrans; eauto.
  - intros n m y1 y2. rewrite !g_dist. intros; eapply dist_le; eauto.
Qed.

Section iso_cofe_subtype.
  Context {SI} {A B : ofeT SI} `{Cofe SI A} (P : A → Prop) (f : ∀ x, P x → B) (g : B → A).
  Context (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2).
  Let Hgne : NonExpansive g.
  Proof. intros n y1 y2. apply g_dist. Qed.
  Existing Instance Hgne.
  Context (gf : ∀ x Hx, g (f x Hx) ≡ x).
  Context (Hlimit : ∀ c : chain B, P (compl (chain_map g c))).
  Context (Hblimit : ∀ α (Hα : zero ≺ α) c, P (bcompl Hα (bchain_map g c))).
  Program Definition iso_cofe_subtype : Cofe B :=
    {| compl c := f (compl (chain_map g c)) _; bcompl α Hα c := f (bcompl Hα (bchain_map g c)) _ |}.
  Next Obligation. apply Hlimit. Qed.
  Next Obligation. apply Hblimit. Qed.
  Next Obligation. intros n c; simpl. apply g_dist. by rewrite gf conv_compl. Qed.
  Next Obligation. intros α Hα c β Hβ; simpl. apply g_dist. by unshelve rewrite gf conv_bcompl. Qed.
  Next Obligation. intros α Hα c d β Heq; simpl. apply g_dist. rewrite !gf. apply bcompl_ne. intros ??; simpl; by rewrite Heq. Qed.

End iso_cofe_subtype.

Lemma iso_cofe_subtype' {SI} {A B : ofeT SI} `{Cofe SI A}
  (P : A → Prop) (f : ∀ x, P x → B) (g : B → A)
  (Pg : ∀ y, P (g y))
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x Hx, g (f x Hx) ≡ x)
  (Hlimit : LimitPreserving P)
  (Hblimit : BoundedLimitPreserving P) : Cofe B.
Proof. apply: (iso_cofe_subtype P f g)=> //; eauto. Qed.

Definition iso_cofe {SI} {A B : ofeT SI} `{Cofe SI A} (f : A → B) (g : B → A)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x, g (f x) ≡ x) : Cofe B.
Proof. by apply (iso_cofe_subtype (λ _, True) (λ x _, f x) g). Qed.

(** Sigma *)
Section sigma.
  Context {SI} {A : ofeT SI} {P : A → Prop}.
  Implicit Types x : sig P.

  (* TODO: Find a better place for this Equiv instance. It also
     should not depend on A being an OFE. *)
  Instance sig_equiv : Equiv (sig P) := λ x1 x2, `x1 ≡ `x2.
  Instance sig_dist : Dist SI (sig P) := λ n x1 x2, `x1 ≡{n}≡ `x2.

  Definition sig_equiv_alt x y : x ≡ y ↔ `x ≡ `y := reflexivity _.
  Definition sig_dist_alt n x y : x ≡{n}≡ y ↔ `x ≡{n}≡ `y := reflexivity _.

  Lemma exist_ne n a1 a2 (H1 : P a1) (H2 : P a2) :
    a1 ≡{n}≡ a2 → a1 ↾ H1 ≡{n}≡ a2 ↾ H2.
  Proof. done. Qed.

  Global Instance proj1_sig_ne : NonExpansive (@proj1_sig _ P).
  Proof. by intros n [a Ha] [b Hb] ?. Qed.
  Definition sig_ofe_mixin : OfeMixin SI (sig P).
  Proof. by apply (iso_ofe_mixin proj1_sig). Qed.
  Canonical Structure sigO : ofeT SI := OfeT (sig P) sig_ofe_mixin.

  Global Instance sig_cofe `{Cofe SI A, !LimitPreserving P, !BoundedLimitPreserving P} : Cofe sigO.
  Proof. apply (iso_cofe_subtype' P (exist P) proj1_sig)=> //. by intros []. Qed.

  Global Instance sig_discrete (x : sig P) :  Discrete (`x) → Discrete x.
  Proof. intros ? y. rewrite sig_dist_alt sig_equiv_alt. apply (discrete _). Qed.
  Global Instance sig_ofe_discrete : OfeDiscrete A → OfeDiscrete sigO.
  Proof. intros ??. apply _. Qed.
End sigma.

Arguments sigO {_ _} _.

(** Ofe for [sigT]. The first component must be discrete
    and use Leibniz equality, while the second component might be any OFE. *)
Section sigT.
  Import EqNotations.

  Context {SI} {A : Type} {P : A → ofeT SI}.
  Implicit Types x : sigT P.

  (**
    The distance for [{ a : A & P }] uses Leibniz equality on [A] to
    transport the second components to the same type,
    and then step-indexed distance on the second component.
    Unlike in the topos of trees, with (C)OFEs we cannot use step-indexed equality
    on the first component.
  *)
  Instance sigT_dist : Dist SI (sigT P) := λ n x1 x2,
    ∃ Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 ≡{n}≡ projT2 x2.

  (**
    Usually we'd give a direct definition, and show it equivalent to
    [∀ n, x1 ≡{n}≡ x2] when proving the [equiv_dist] OFE axiom.
    But here the equivalence requires UIP — see [sigT_equiv_eq_alt].
    By defining [equiv] in terms of [dist], we can define an OFE
    without assuming UIP, at the cost of complex reasoning on [equiv].
  *)
  Instance sigT_equiv : Equiv (sigT P) := λ x1 x2,
    ∀ n, x1 ≡{n}≡ x2.

  (** Unfolding lemmas.
      Written with [↔] not [=] to avoid https://github.com/coq/coq/issues/3814. *)
  Definition sigT_equiv_eq x1 x2 : (x1 ≡ x2) ↔ ∀ n, x1 ≡{n}≡ x2 :=
      reflexivity _.

  Definition sigT_dist_eq x1 x2 n : (x1 ≡{n}≡ x2) ↔
    ∃ Heq : projT1 x1 = projT1 x2, (rew Heq in projT2 x1) ≡{n}≡ projT2 x2 :=
      reflexivity _.

  Definition sigT_dist_proj1 n {x y} : x ≡{n}≡ y → projT1 x = projT1 y := proj1_ex.
  Definition sigT_equiv_proj1 {x y} : x ≡ y → projT1 x = projT1 y := λ H, proj1_ex (H zero).

  Definition sigT_ofe_mixin : OfeMixin SI (sigT P).
  Proof.
    split => // n.
    - split; hnf; setoid_rewrite sigT_dist_eq.
      + intros. by exists eq_refl.
      + move => [xa x] [ya y] /=. destruct 1 as [-> Heq].
        by exists eq_refl.
      + move => [xa x] [ya y] [za z] /=.
        destruct 1 as [-> Heq1].
        destruct 1 as [-> Heq2]. exists eq_refl => /=. by trans y.
    - setoid_rewrite sigT_dist_eq.
      move => β [xa x] [ya y] /=. destruct 1 as [-> Heq].
      exists eq_refl. by eapply dist_dist_later.
  Qed.

  Canonical Structure sigTO : ofeT SI := OfeT (sigT P) sigT_ofe_mixin.

  Lemma sigT_equiv_eq_alt `{!∀ a b : A, ProofIrrel (a = b)} x1 x2 :
    x1 ≡ x2 ↔
    ∃ Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 ≡ projT2 x2.
  Proof.
    setoid_rewrite equiv_dist. setoid_rewrite sigT_dist_eq. split => Heq.
    - move: (Heq zero) => [H0eq1 _].
      exists H0eq1 => n. move: (Heq n) => [] Hneq1.
      by rewrite (proof_irrel H0eq1 Hneq1).
    - move: Heq => [Heq1 Heqn2] n. by exists Heq1.
  Qed.

  (** [projT1] is non-expansive and proper. *)
  Global Instance projT1_ne : NonExpansive (projT1 : sigTO → leibnizO SI A).
  Proof. solve_proper. Qed.

  Global Instance projT1_proper : Proper ((≡) ==> (≡)) (projT1 : sigTO → leibnizO SI A).
  Proof. apply ne_proper, projT1_ne. Qed.

  (** [projT2] is "non-expansive"; the properness lemma [projT2_ne] requires UIP. *)
  Lemma projT2_ne n (x1 x2 : sigTO) (Heq : x1 ≡{n}≡ x2) :
    rew (sigT_dist_proj1 n Heq) in projT2 x1 ≡{n}≡ projT2 x2.
  Proof. by destruct Heq. Qed.

  Lemma projT2_proper `{!∀ a b : A, ProofIrrel (a = b)} (x1 x2 : sigTO) (Heqs : x1 ≡ x2):
    rew (sigT_equiv_proj1 Heqs) in projT2 x1 ≡ projT2 x2.
  Proof.
    move: x1 x2 Heqs => [a1 x1] [a2 x2] Heqs.
    case: (proj1 (sigT_equiv_eq_alt _ _) Heqs) => /=. intros ->.
    rewrite (proof_irrel (sigT_equiv_proj1 Heqs) eq_refl) /=. done.
  Qed.

  (** [existT] is "non-expansive" — general, dependently-typed statement. *)
  Lemma existT_ne n {i1 i2} {v1 : P i1} {v2 : P i2} :
    ∀ (Heq : i1 = i2), (rew f_equal P Heq in v1 ≡{n}≡ v2) →
      existT i1 v1 ≡{n}≡ existT i2 v2.
  Proof. intros ->; simpl. exists eq_refl => /=. done. Qed.

  Lemma existT_proper {i1 i2} {v1 : P i1} {v2 : P i2} :
    ∀ (Heq : i1 = i2), (rew f_equal P Heq in v1 ≡ v2) →
      existT i1 v1 ≡ existT i2 v2.
  Proof. intros Heq Heqv n. apply (existT_ne n Heq), equiv_dist, Heqv. Qed.

  (** [existT] is "non-expansive" — non-dependently-typed version. *)
  Global Instance existT_ne_2 a : NonExpansive (@existT A P a).
  Proof. move => ??? Heq. apply (existT_ne _ eq_refl Heq). Qed.

  Global Instance existT_proper_2 a : Proper ((≡) ==> (≡)) (@existT A P a).
  Proof. apply ne_proper, _. Qed.

  Implicit Types (c : chain sigTO).

  Global Instance sigT_discrete x : Discrete (projT2 x) → Discrete x.
  Proof.
    move: x => [xa x] ? [ya y] [] /=; intros -> => /= Hxy n.
    exists eq_refl => /=. apply equiv_dist, (discrete _), Hxy.
  Qed.

  Global Instance sigT_ofe_discrete : (∀ a, OfeDiscrete (P a)) → OfeDiscrete sigTO.
  Proof. intros ??. apply _. Qed.

  Lemma sigT_chain_const_proj1 c n : projT1 (c n) = projT1 (c zero).
  Proof. refine (sigT_dist_proj1 _ (chain_cauchy' c zero n _)). apply index_zero_minimum. Qed.

  Lemma sigT_bchain_const_proj1 α Hα (c: bchain sigTO α) n Hn:  projT1 (c n Hn) = projT1 (c zero Hα).
  Proof. refine (sigT_dist_proj1 _ (bchain_cauchy' α c zero n _ _ _)). apply index_zero_minimum. Qed.

  (* For this COFE construction we need UIP (Uniqueness of Identity Proofs)
    on [A] (i.e. [∀ x y : A, ProofIrrel (x = y)]. UIP is most commonly obtained
    from decidable equality (by Hedberg’s theorem, see
    [stdpp.proof_irrel.eq_pi]). *)
  Section cofe.
    Context `{!∀ a b : A, ProofIrrel (a = b)} `{!∀ a, Cofe (P a)}.

    Program Definition chain_map_snd c : chain (P (projT1 (c zero))) :=
      {| chain_car n := rew (sigT_chain_const_proj1 c n) in projT2 (c n) |}.
    Next Obligation.
      move => c n i Hle /=.
      (* [Hgoal] is our thesis, up to casts: *)
      case: (chain_cauchy' c n i Hle) => [Heqin Hgoal] /=.
      (* Pretty delicate. We have two casts to [projT1 (c zero)].
        We replace those by one cast. *)
      move: (sigT_chain_const_proj1 c i) (sigT_chain_const_proj1 c n)
        => Heqi0 Heqn0.
      (* Rewrite [projT1 (c zero)] to [projT1 (c n)] in goal and [Heqi0]: *)
      destruct Heqn0.
      by rewrite /= (proof_irrel Heqi0 Heqin).
    Qed.

    Definition sigT_compl : chain sigTO → sigTO :=
      λ c, existT (projT1 (c zero)) (compl (chain_map_snd c)).

    Program Definition bchain_map_snd α Hα (c: bchain sigTO α): bchain (P (projT1 (c zero Hα))) α :=
      {| bchain_car n Hn := rew (sigT_bchain_const_proj1 α Hα c n Hn) in projT2 (c n Hn) |}.
    Next Obligation.
      move => α Hα c β γ Hle Hβ Hγ /=.
      (* [Hgoal] is our thesis, up to casts: *)
      case: (bchain_cauchy' α c β γ Hβ Hγ Hle) => [Heqin Hgoal] /=.
      (* Pretty delicate. We have two casts to [projT1 (c zero)].
        We replace those by one cast. *)
      move: (sigT_bchain_const_proj1 α Hα c β Hβ ) (sigT_bchain_const_proj1 α Hα c γ Hγ)
        => Heqβ0 Heqγ0.
      (* Rewrite [projT1 (c zero)] to [projT1 (c n)] in goal and [Heqi0]: *)
      destruct Heqβ0.
      by rewrite /= (proof_irrel Heqγ0 Heqin).
    Qed.

    Definition sigT_bcompl α (Hα: zero ≺ α) (c: bchain sigTO α): sigTO :=
      existT (projT1 (c zero Hα)) (bcompl Hα (bchain_map_snd α Hα c)).


    Global Program Instance sigT_cofe : Cofe sigTO := { compl := sigT_compl; bcompl := sigT_bcompl }.
    Next Obligation.
      intros n c. rewrite /sigT_compl sigT_dist_eq /=.
      exists (symmetry (sigT_chain_const_proj1 c n)).
      (* Our thesis, up to casts: *)
      pose proof (conv_compl n (chain_map_snd c)) as Hgoal.
      move: (compl (chain_map_snd c)) Hgoal => pc0 /=.
      destruct (sigT_chain_const_proj1 c n); simpl. done.
    Qed.
    Next Obligation.
      intros α Hα c β Hβ. rewrite /sigT_bcompl sigT_dist_eq /=.
      exists (symmetry (sigT_bchain_const_proj1 α Hα c β Hβ)).
      (* Our thesis, up to casts: *)
      pose proof (conv_bcompl α Hα (bchain_map_snd α Hα c) β Hβ) as Hgoal.
      move: (bcompl Hα (bchain_map_snd α Hα c)) Hgoal => pc0 /=.
      destruct (sigT_bchain_const_proj1 α Hα c β Hβ); simpl. done.
    Qed.
    Next Obligation.
      intros α Hα c d β Heq; rewrite /sigT_bcompl sigT_dist_eq /=.
      destruct (Heq zero Hα) as [eq Ht]. exists eq; simpl.
      enough (bcompl Hα (rew [λ x : A, bchain (P x) α] eq in bchain_map_snd α Hα c) ≡{β}≡ bcompl Hα (bchain_map_snd α Hα d)) as Hbcompl.
      { rewrite <-Hbcompl. clear Ht Hbcompl. by destruct eq. }
      apply bcompl_ne; simpl. intros γ Hγ. destruct (Heq γ Hγ) as [eq' H'].
      rewrite <-(@map_subst _ (λ y, bchain (P y) α) P (λ y d, d γ Hγ) _ _ eq); simpl.
      rewrite rew_compose. revert H'.
      move: (sigT_bchain_const_proj1 α Hα d γ Hγ) (eq_trans (sigT_bchain_const_proj1 α Hα c γ Hγ) eq) => e1 e2.
      destruct e1; simpl. intros <-.
      by rewrite /= (proof_irrel e2 eq').
    Qed.
  End cofe.
End sigT.

Arguments sigTO {_ _} _.

Section sigTOF.
  Context {SI: indexT} {A : Type}.

  Program Definition sigT_map {P1 P2 : A → ofeT SI} :
    discrete_funO (λ a, P1 a -n> P2 a) -n>
    sigTO P1 -n> sigTO P2 :=
    λne f xpx, existT _ (f _ (projT2 xpx)).
  Next Obligation.
    move => ?? f n [x px] [y py] [/= Heq]. destruct Heq; simpl.
    exists eq_refl => /=. by f_equiv.
  Qed.
  Next Obligation.
    move => ?? n f g Heq [x px] /=. exists eq_refl => /=. apply Heq.
  Qed.

  Program Definition sigTOF (F : A → oFunctor SI) : oFunctor SI := {|
    oFunctor_car A B := sigTO (λ a, oFunctor_car (F a) A B);
    oFunctor_map A1 A2 B1 B2 fg := sigT_map (λ a, oFunctor_map (F a) fg)
  |}.
  Next Obligation.
    repeat intro. exists eq_refl => /=. solve_proper.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), oFunctor_id.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), oFunctor_compose.
  Qed.

  Global Instance sigTOF_contractive {F} :
    (∀ a, oFunctorContractive (F a)) → oFunctorContractive (sigTOF F).
  Proof.
    repeat intro. apply sigT_map => a. exact: oFunctor_contractive.
  Qed.
End sigTOF.
Arguments sigTOF {_ _} _%OF.

(*
FIXME: Notation disabled because it causes strange conflicts in Coq 8.7.
Enable again once we drop support for that version.
Notation "{ x  &  P }" := (sigTOF (λ x, P%OF)) : oFunctor_scope.
Notation "{ x : A &  P }" := (@sigTOF A%type (λ x, P%OF)) : oFunctor_scope.
<<<<<<< HEAD
*)

(** different notions of limit uniqueness *)
Class BcomplStronglyUnique {SI : indexT} (A : ofeT SI) `{Cofe SI A} :=
 cofe_strongly_unique (α : SI) Hα (c d : bchain A α) :
  (∀ β (Hβ : β ≺ α), c β Hβ ≡{β}≡ d β Hβ) → bcompl Hα c ≡ bcompl Hα d.
Hint Mode BcomplStronglyUnique - + + : typeclass_instances.

Class BcomplUnique {SI : indexT} (A : ofeT SI) `{Cofe SI A} :=
  cofe_unique (α : SI) Hα (c d : bchain A α) :
    (∀ β (Hβ : β ≺ α), c β Hβ ≡{β}≡ d β Hβ) → bcompl Hα c ≡{α}≡ bcompl Hα d.
Hint Mode BcomplUnique - + + : typeclass_instances.

Class BcomplUniqueLim {SI : indexT} (A : ofeT SI) `{Cofe SI A} :=
  cofe_unique_lim (α : SI) (αlim : index_is_limit α) Hα (c d : bchain A α) :
    (∀ β (Hβ : β ≺ α), c β Hβ ≡{β}≡ d β Hβ) → bcompl Hα c ≡{α}≡ bcompl Hα d.
Hint Mode BcomplUniqueLim - + + : typeclass_instances.

Instance unique_unique_lim {SI : indexT} (A : ofeT SI) `{Cofe SI A} (H1 : BcomplUnique A) :
  BcomplUniqueLim A.
Proof. intros α _. apply H1. Qed.

(** OFEs truncated at a stepindex α*)
(* Equality at ordinals above α is fully determined by equality at α *)
Class Truncated {SI : indexT} {A : ofeT SI} (α : SI) (x : A) := truncated y β: α ⪯ β → x ≡{α}≡ y ↔ x ≡{β}≡ y.
Arguments truncated {_ _} _ _ {_ } _ _ _.
Hint Mode Truncated - + ! ! : typeclass_instances.
Instance : Params (@Truncated) 2 := {}.

Class OfeTruncated {SI : indexT} (A : ofeT SI) (α : SI) := ofe_truncated_truncated (x : A) :> Truncated α x.
Hint Mode OfeTruncated - + - : typeclass_instances.
Arguments OfeTruncated {_} _ _.

Lemma ofe_truncated_equiv {SI : indexT} (A : ofeT SI) (α : SI) {H : OfeTruncated A α} :
  ∀ (x y : A), x ≡ y ↔ x ≡{α}≡ y.
Proof.
  intros x y. rewrite equiv_dist. split.
  - intros Hall. by apply Hall.
  - intros Hα β. destruct (index_le_total α β) as [He | He].
    + by apply ofe_truncated_truncated.
    + by eapply dist_mono'.
Qed.

Lemma ofe_truncated_dist {SI : indexT} (A : ofeT SI) (α : SI) {H : OfeTruncated A α}:
  ∀ (x y : A) β, x ≡{β}≡ y ↔ x ≡{index_min β α}≡ y.
Proof.
  intros x y β. split; intros Heq.
  - eapply dist_mono'; [apply Heq | eapply index_min_le_l].
  - unfold index_min in Heq. destruct (index_le_total β α) as [H1 | H1]. 1: apply Heq.
    by eapply H.
Qed.

Instance discrete_is_truncated {SI : indexT} (A : ofeT SI) (α : SI) (H: OfeDiscrete A) : OfeTruncated A α.
Proof.
  intros x y β Hα. split; intros H0.
  all: apply equiv_dist, ofe_discrete_discrete; (eapply dist_mono'; [apply H0 | apply index_zero_minimum]).
Qed.

Instance ofe_mor_truncated {SI: indexT} {A B : ofeT SI} α {H : OfeTruncated B α} : OfeTruncated (A -n> B) α.
Proof.
  intros f g β Hβ. split; intros Heq x.
  - apply ofe_truncated_truncated; auto.
  - rewrite ofe_truncated_truncated; eauto.
Qed.

(** Truncatable OFEs -- an OFE A is truncatable if, for every ordinal α, it admits a truncation [A]_{α} (again an OFE)
  and a bounded isomorphism (equality up to α) between A and [A]_{α}
*)
Definition boundedInverse {SI: indexT} {X1 X2: ofeT SI} (f : X2 -n> X1) (g : X1 -n> X2) (α : SI) :=
  f ◎ g ≡{α}≡ cid ∧ g ◎ f ≡{α}≡ cid.
Lemma boundedInverse_antimono {SI : indexT} {X1 X2 : ofeT SI} (f : X2 -n> X1) (g : X1 -n> X2) (α β : SI) :
  α ⪯ β → boundedInverse f g β → boundedInverse f g α.
Proof. intros Hle [H1 H2]. split; eapply dist_mono'; eauto. Qed.

Class Truncatable {SI : indexT} (A : ofeT SI):=
  {
    ofe_trunc_car (α : SI) : ofeT SI;
    ofe_trunc_truncated (α : SI) : OfeTruncated (ofe_trunc_car α) α;
    ofe_trunc_truncate (α : SI) : A -n> ofe_trunc_car α;
    ofe_trunc_expand (α : SI) : ofe_trunc_car α -n> A;
    ofe_trunc_inverse (α : SI) : boundedInverse (ofe_trunc_truncate α) (ofe_trunc_expand α) α;
  }.
Hint Mode Truncatable - - : typeclass_instances.
Arguments ofe_trunc_car {_ _ _} _.

(* FIXME: when printing, usually A is implicit (inferred from the Truncatable instance) and an underscore is printed.
  can we force Coq to infer & print the implicit argument ?*)
Notation "'[' A ']_{' α '}'" := (@ofe_trunc_car _ A  _ α) (only parsing).
Notation "'⌊' a '⌋_{' α '}'" := (ofe_trunc_truncate α a) (format "'⌊' a '⌋_{' α '}'").
Notation "'⌈' a '⌉_{' α '}'" := (ofe_trunc_expand α a) (format "'⌈' a '⌉_{' α '}'").

Section truncatable_props.
  Context {SI : indexT} {A : ofeT SI} {Htrunc : Truncatable A}.
  Lemma ofe_trunc_truncate_expand_id {α} :
    ofe_trunc_truncate α ◎ ofe_trunc_expand α ≡ cid.
  Proof. intros x. cbn. eapply ofe_truncated_equiv. apply Htrunc. apply ofe_trunc_inverse. Qed.

  Lemma ofe_trunc_expand_truncate_id {α} : ofe_trunc_expand α ◎ ofe_trunc_truncate α ≡{α}≡ cid.
  Proof. apply ofe_trunc_inverse. Qed.

  Global Instance Truncatable_truncated (α : SI) : OfeTruncated (ofe_trunc_car (A := A) α) α
    := (@ofe_trunc_truncated _ A _  α).

  Section truncatable_cofe.
    Context (γ: SI) {Ha : Cofe A}.

    Program Definition trunc_chain (c : chain ([A]_{γ})) : chain A :=
      mkchain _ A (λ α, ofe_trunc_expand γ (c α)) _.
    Next Obligation. intros c α' β Hle. cbn. by rewrite (chain_cauchy _ c α' β Hle). Qed.
    Program Definition trunc_bchain β (c : bchain ([A]_{γ}) β) : bchain A β :=
      mkbchain _ A β (λ γ' Hγ', ofe_trunc_expand γ (c γ' Hγ')) _.
    Next Obligation. intros β c β' γ' Hle Hβ Hγ'. cbn. f_equiv. by apply bchain_cauchy. Qed.

    Global Program Instance Truncatable_cofe : Cofe ([A]_{γ}) :=
      {
        compl c := ⌊compl (trunc_chain c)⌋_{γ};
        bcompl β Hβ c := ⌊bcompl Hβ (trunc_bchain β c)⌋_{γ};
       }.
    Next Obligation.
      intros α' c. cbn.
      rewrite ofe_truncated_dist.
      setoid_rewrite (dist_mono' _ _ _ _ (conv_compl α' _)). 2: apply index_min_le_l.
      cbn. eapply dist_mono'.
      - apply equiv_dist, ofe_trunc_truncate_expand_id.
      - apply index_min_le_r.
    Qed.
    Next Obligation.
      intros α' Hα' c β Hβ. cbn. rewrite ofe_truncated_dist.
      unshelve setoid_rewrite (dist_mono' _ _ _ _ (conv_bcompl _ _ _ β Hβ)). 2: apply index_min_le_l.
      cbn. eapply dist_mono'.
      - apply equiv_dist, ofe_trunc_truncate_expand_id.
      - apply index_min_le_r.
    Qed.
    Next Obligation.
      intros α' Hα' c d β Heq. cbn. f_equiv.
      apply bcompl_ne. intros γ' Hγ'. cbn. by f_equiv.
    Qed.

    Global Instance Truncatable_unique {H : BcomplUnique A}: BcomplUnique ([A]_{γ}).
    Proof.
      intros β Hβ c d Heq. unfold bcompl, Truncatable_cofe.
      f_equiv. apply H. intros β' Hβ'. cbn. apply ofe_mor_ne, Heq.
    Qed.

    Global Instance Truncatable_unique_lim {H : BcomplUniqueLim A}: BcomplUniqueLim ([A]_{γ}).
    Proof.
      intros β Hlim Hβ c d Heq. unfold bcompl, Truncatable_cofe.
      f_equiv. apply H. assumption.
      intros β' Hβ'. cbn. by f_equiv.
    Qed.

    Global Instance Truncatable_strongly_unique {H : BcomplStronglyUnique A}: BcomplStronglyUnique ([A]_{γ}).
    Proof.
      intros β Hβ c d Heq. unfold bcompl, Truncatable_cofe. f_equiv.
      apply H. intros β' Hβ'. cbn. apply ofe_mor_ne, Heq.
    Qed.
  End truncatable_cofe.
End truncatable_props.

Section truncatable.
  Context {SI : indexT} .

  Program Definition trunc_map  {A : ofeT SI} {HtruncA : Truncatable A} {B : ofeT SI} {HtruncB : Truncatable B}
  (α β : SI) : (A -n> B) -n> ([A]_{α} -n> [B]_{β}) := λne f, ofe_trunc_truncate β ◎ f ◎ ofe_trunc_expand α.
  Next Obligation.
    intros A HtrucA B HtruncB α β γ f g Heq.
    apply ccompose_ne; [ |  reflexivity ]. apply ccompose_ne; auto.
  Qed.

  Context {A : ofeT SI} {HtruncA : Truncatable A}.
  Context {B : ofeT SI} {HtruncB : Truncatable B}.
  Lemma trunc_map_inv (f : A -n> B) (g : B -n> A) α β:
    α ⪯ β → boundedInverse f g α → boundedInverse (trunc_map α β f) (trunc_map β α g) α.
  Proof.
    intros Hle [H1 H2]. split; intros x.
    - unfold trunc_map. cbn.
      rewrite ofe_truncated_dist.
      rewrite ofe_mor_ne. 2: { eapply dist_mono'. 2: apply index_min_le_l.
        setoid_rewrite (ofe_trunc_expand_truncate_id _). apply H1.
      }
      cbn. apply equiv_dist, ofe_trunc_truncate_expand_id.
    - cbn. rewrite ofe_mor_ne.
      2: { rewrite ofe_mor_ne. 2: { eapply dist_mono'. setoid_rewrite (ofe_trunc_expand_truncate_id _). cbn. all: eauto. }
        apply H2.
      }
      apply equiv_dist, ofe_trunc_truncate_expand_id.
  Qed.

  Context {C : ofeT SI} {HtruncC : Truncatable C}.
  Lemma trunc_map_compose (f : A -n> B) (g : B -n> C) α β γ :
    trunc_map α β (g ◎ f) ≡{γ}≡ trunc_map γ β g ◎ trunc_map α γ f.
  Proof.
    cbn. setoid_rewrite ccompose_assoc at 2. setoid_rewrite (proj1 (equiv_dist _ _) (ccompose_assoc _ _ _)) at 3.
    setoid_rewrite <- (proj1 (equiv_dist _ _) (ccompose_assoc _ _ _)) at 3.
    setoid_rewrite (dist_mono' _ _ _ _ (ofe_trunc_expand_truncate_id)); [ | auto].
    by intros x.
  Qed.
End truncatable.


(** a more elementary property than Truncatable. Essentially, proto_trunc α chooses a unique representative of each equivalence class of ≡{α}≡ *)
Class ProtoTruncatable {SI : indexT} (A : ofeT SI) :=
  {
    proto_trunc α : A -n> A;
    proto_compat α (x y : A) : x ≡{α}≡ y → proto_trunc α x ≡ proto_trunc α y;
    proto_ne α x : proto_trunc α x ≡{α}≡ x;
  }.
Hint Mode ProtoTruncatable - + : typeclass_instances.

Section strict_is_proto.
  Context {SI : indexT} (A : ofeT SI) `{Cofe SI A} {Hstrong : BcomplStronglyUnique A}.
  Program Instance StronglyUnique_ProtoTruncatable : ProtoTruncatable A :=
  {
    proto_trunc α := λne a, bcompl (α := succ α) _ (bchain_const a (succ α));
  }.
  Next Obligation.
    intros α _. apply index_succ_iff, index_zero_minimum.
  Qed.
  Next Obligation.
    intros α α' x y Heq.
    destruct (index_le_lt_dec α' α) as [Hle | Hlt].
    - unshelve rewrite !conv_bcompl. 1-2: eapply index_succ_iff, Hle. apply Heq.
    - apply equiv_dist. eapply Hstrong. intros β Hβ; cbn.
      eapply dist_mono. exact Heq. eapply index_lt_le_trans. apply Hβ. eauto with index.
  Qed.
  Next Obligation.
    intros α x y Heq. cbn. apply Hstrong. intros β Hβ. cbn. eapply dist_mono'; eauto with index.
  Qed.
  Next Obligation.
    intros α x. cbn. unshelve rewrite conv_bcompl. apply index_succ_greater. reflexivity.
  Qed.
End strict_is_proto.

Section proto.
  Context {SI : indexT} (A : ofeT SI) {Hcofe : Cofe A} {Htrunc : ProtoTruncatable A}.

  (** basic facts about proto truncatability *)
  Fact proto_trunc_idempotent (a : A) α: proto_trunc α (proto_trunc α a) ≡ proto_trunc α a.
  Proof. apply proto_compat. apply proto_ne. Qed.

  Lemma proto_trunc_dist_min (a b : A) α γ : a ≡{index_min α γ}≡ b → proto_trunc α a ≡{γ}≡ proto_trunc α b.
  Proof.
    intros H. unfold index_min in H. destruct (index_le_total α γ) as [Hle | Hgt].
    - eapply equiv_dist, proto_compat, H.
    - apply ofe_mor_ne, H.
  Qed.

  (** we can also get that ProtoTruncatability implies strong uniqueness of limits,
    if we assume the weaker uniqueness of limits*)
  Program Instance strict_cofe' : Cofe A :=
  { compl := @compl SI A _;
    bcompl α Hα c := proto_trunc α (bcompl Hα c) ;
  }.
  Next Obligation. apply conv_compl. Qed.
  Next Obligation.
    intros α Hα c β Hβ. cbn. rewrite (dist_mono _ _ _ _ (proto_ne _ _)). by apply conv_bcompl. apply Hβ.
  Qed.
  Next Obligation.
    intros α Hα c d β Heq. cbn.
    unshelve eapply bcompl_ne in Heq. exact Hα.
    rewrite ofe_mor_ne. 2: apply Heq. reflexivity.
  Qed.

  Instance ProtoTruncatable_StronglyUnique (Hunique : @BcomplUnique _ A Hcofe):
    @BcomplStronglyUnique _ A strict_cofe'.
  Proof.
    intros α Hα c d H1. unfold strict_cofe', bcompl. apply proto_compat.
    unfold BcomplUnique in Hunique. apply (Hunique α Hα c d H1).
  Qed.
End proto.

Section strict_lim.
  (** we can prove that Truncatability implies strong uniqueness of limits given that we have unique limits *)
  Context {SI : indexT} (A : ofeT SI) `{Cofe SI A}
    (Htrunc : Truncatable A) (Hun : ∀ α, BcomplUnique (ofe_trunc_car α)).

  Program Definition strict_bcompl α (Hα : zero ≺ α) (c : bchain A α) :=
    ⌈bcompl Hα (mkbchain SI ([A]_{α}) α (λ β Hβ, ⌊c β Hβ⌋_{α}) _)⌉_{α}.
  Next Obligation.
    intros α Hα c β γ Hβ Hlt Hγ. cbn. apply ofe_mor_ne. by apply bchain_cauchy.
  Qed.

  Program Instance strict_cofe : Cofe A :=
  { compl := @compl SI A _;
    bcompl := strict_bcompl;
  }.
  Next Obligation. apply conv_compl. Qed.
  Next Obligation.
    intros α Hα c β Hβ. unfold strict_bcompl.
    rewrite ofe_mor_ne. 2: { rewrite conv_bcompl. cbn. reflexivity. }
    setoid_rewrite (dist_mono _ _ _ _ (ofe_trunc_expand_truncate_id _)). 2: apply Hβ.
    cbn. reflexivity.
  Qed.
  Next Obligation.
    intros α Hα c d β Heq. unfold strict_bcompl.
    f_equiv. rewrite ofe_truncated_dist.
    apply bcompl_ne. intros γ Hγ. cbn.
    f_equiv. eapply dist_mono'. apply Heq. apply index_min_le_l.
  Qed.

  Instance Truncatable_StronglyUnique : @BcomplStronglyUnique _ A strict_cofe.
  Proof using Hun.
    intros α Hα c d H1. unfold strict_cofe, bcompl. unfold strict_bcompl.
    apply ne_proper. apply _. rewrite ofe_truncated_equiv.
    apply Hun. intros γ Hγ. cbn. f_equiv. apply H1.
  Qed.
End strict_lim.

(** We show that ProtoTruncatable implies Truncatable *)
(* For defining the truncated types, we wrap the OFE A in an inductive in order to not confuse typeclass inference when defining a different equivalence on it. *)
Inductive trunc_truncation {SI : indexT} (A : ofeT SI) (β : SI) := trunc_truncationC (a : A).
Section proto_truncatable.
  Context {SI : indexT} (A : ofeT SI) (Htrunc : ProtoTruncatable A).

  Section trunc_def.
    Context (α : SI).
    Local Definition truncembed (a : trunc_truncation A α): A := match a with trunc_truncationC _ _ a => a end.

    Instance trunc_truncation_equiv : Equiv (trunc_truncation A α) := λ a b, proto_trunc α (truncembed a) ≡ proto_trunc α (truncembed b).
    Lemma trunc_truncation_equiv_unfold a b : a ≡ b ↔ proto_trunc α (truncembed a) ≡ proto_trunc α (truncembed b).
    Proof. tauto. Qed.

    Instance trunc_truncation_dist : Dist SI (trunc_truncation A α) :=
      λ n a b, proto_trunc α (truncembed a) ≡{n}≡ proto_trunc α (truncembed b).

    Lemma trunc_truncation_dist_unfold a b n : a ≡{n}≡ b ↔ proto_trunc α (truncembed a) ≡{n}≡ proto_trunc α (truncembed b).
    Proof. tauto. Qed.

    Definition trunc_truncation_ofe_mixin : OfeMixin SI (trunc_truncation A α).
    Proof.
      split.
      - setoid_rewrite trunc_truncation_dist_unfold. setoid_rewrite trunc_truncation_equiv_unfold.
        intros x y. split; intros H.
        + intros β. by apply equiv_dist.
        + apply equiv_dist. intros γ. apply (H γ).
      - intros α'. unfold dist, trunc_truncation_dist. split; auto.
        intros a b c -> ->. auto.
      - setoid_rewrite trunc_truncation_dist_unfold. intros α' β x y Heq Hlt. eauto using dist_mono.
    Qed.
    Canonical Structure tcar_truncO : ofeT SI := OfeT (trunc_truncation A α) trunc_truncation_ofe_mixin.

    Program Definition tcar_trunc : A -n> tcar_truncO := λne a, trunc_truncationC A α a.
    Next Obligation.
      intros β x y. rewrite trunc_truncation_dist_unfold; cbn. intros Heq.
      by apply ofe_mor_ne.
    Qed.

    Program Definition tcar_embed : tcar_truncO -n> A := λne a, proto_trunc α (truncembed a).
    Next Obligation.
      intros β [x] [y]. rewrite trunc_truncation_dist_unfold; cbn. auto.
    Qed.

    Lemma tcar_trunc_embed_inv : boundedInverse tcar_trunc tcar_embed α.
    Proof.
      split.
      - intros x. rewrite trunc_truncation_dist_unfold. cbn. destruct x. cbn.
        apply equiv_dist. apply proto_trunc_idempotent.
      - intros x. cbn. apply proto_ne.
    Qed.
  End trunc_def.

  Global Program Instance ProtoTruncatable_is_Truncatable : Truncatable A :=
    {
    ofe_trunc_car α := tcar_truncO α;
    ofe_trunc_expand α := tcar_embed α;
    ofe_trunc_truncate α := tcar_trunc α;
    }.
  Next Obligation.
    intros α x y β Hle. split.
    - rewrite !trunc_truncation_dist_unfold. destruct x, y. cbn. intros H. apply equiv_dist. apply proto_compat.
      rewrite <- proto_ne. setoid_rewrite <- proto_ne at 3. apply H.
    - intros H. eapply dist_mono'. apply H. apply Hle.
  Qed.
  Next Obligation.
    intros α. apply tcar_trunc_embed_inv.
  Qed.
  Global Opaque ProtoTruncatable_is_Truncatable.
End proto_truncatable.

(** We can show that every OFE is truncatable and every COFE can be equipped with strongly unique limits, using classical logic with choice. *)
Require Coq.Logic.Epsilon.
Require Coq.Logic.Classical.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Logic.PropExtensionality.
Section classical_truncation.
  Context {SI : indexT}.
  Context (A : ofeT SI).

  (** First we show that we can get a "truncation" operation for arbitrary decidable equivalence relations.
    We later instantiate this with dist and dist_later *)
  Section fix_alpha.
    Context (P : A → A → Prop).
    Import Epsilon.
    Lemma binary_choice (X : Prop) : (X ∨ ~X) → {X} + {~ X}.
    Proof.
      intros H.
      assert (H0: exists (b : bool), if b then X else ¬ X).
      { destruct H as [H | H]. by exists true. by exists false. }
      apply constructive_indefinite_description in H0 as [[] H0]; auto.
    Qed.

    Context (Pdec : ∀ a b, {P a b} + {¬ P a b}).
    Context {P_equiv : Equivalence P}.
    Existing Instance P_equiv.

    Definition choice_fun (a : A) := λ (b : A), if Pdec a b then true else false.

    Import FunctionalExtensionality.
    Lemma choice_fun_ext (a b : A) : P a b → choice_fun a = choice_fun b.
    Proof using P_equiv.
      intros H. apply functional_extensionality.
      intros x. unfold choice_fun.
      destruct (Pdec a x) as [H1 | H1], (Pdec b x) as [H2 | H2]; try reflexivity; exfalso.
      - apply H2. etransitivity. symmetry; exact H. exact H1.
      - apply H1. etransitivity; eauto.
    Qed.

    Lemma choice_fun_exists (a : A) : ∃ b, choice_fun a b = true.
    Proof using P_equiv.
      exists a. unfold choice_fun. destruct Pdec as [ | H1]; [reflexivity | exfalso; apply H1; reflexivity].
    Qed.

    Definition choose_witness (a : A) := proj1_sig (constructive_indefinite_description _ (choice_fun_exists a)).
    Lemma witness_P (a : A) : P a (choose_witness a).
    Proof.
      assert (choice_fun a (choose_witness a) = true).
      { apply (proj2_sig (constructive_indefinite_description _ (choice_fun_exists a))). }
      unfold choice_fun in H.
      destruct Pdec as [H1 | H1]. assumption. congruence.
    Qed.

    Import PropExtensionality.
    Lemma witness_unique (R Q : A → Prop) (H0 : ∃ a, R a) (H1 : ∃ b, Q b) :
      (∀ a, R a ↔ Q a)
      → proj1_sig (constructive_indefinite_description R H0) = proj1_sig (constructive_indefinite_description Q H1).
    Proof.
      intros H.
      assert (H2 : R = Q).
      { apply functional_extensionality. intros x. apply propositional_extensionality, H. }
      subst.
      rewrite (proof_irrelevance _ H0 H1). reflexivity.
    Qed.

    Lemma choose_witness_choice (a b : A) : P a b → choose_witness a = choose_witness b.
    Proof.
      intros H. unfold choose_witness.
      apply witness_unique. intros x.
      apply choice_fun_ext in H. by rewrite H.
    Qed.
  End fix_alpha.

  Import Classical.
  Lemma dec_dist α (x y : A) : { x ≡{α}≡ y} + {~ x ≡{α}≡ y}.
  Proof. apply binary_choice. apply classic. Qed.

  Program Definition trunc (α : SI) := λne a, choose_witness (dist α) (dec_dist α) a.
  Next Obligation.
    intros α β a b Heq.
    destruct (index_le_lt_dec α β) as [H1 | H1].
    - unshelve erewrite (choose_witness_choice _ _ a b _). { eapply dist_mono'; eassumption. }
      reflexivity.
    - rewrite <- (dist_mono _ _ _ _ (witness_P _ _  a)). 2 : assumption.
      rewrite <- (dist_mono _ _ _ _ (witness_P _ _ b)). 2: assumption.
      apply Heq.
  Qed.

  (* classical ProtoTruncatable instance for arbitrary OFEs *)
  Instance classical_proto_trunc : ProtoTruncatable A.
  Proof.
    exists trunc.
    - intros. unfold trunc. cbn. by rewrite (choose_witness_choice _ _  x y H).
    - intros. symmetry. unfold trunc. cbn. apply witness_P.
  Qed.

  (* Now we can use a similar technique to show that any COFE is StronglyUnique *)
  Lemma dec_dist_later α (x y : A) : { dist_later α x y} + {¬ dist_later α x y}.
  Proof. apply binary_choice. apply classic. Qed.

  Program Definition trunc_dist_later (α : SI) := λne a, choose_witness (dist_later α) (dec_dist_later α) a.
  Next Obligation.
    intros α β a b Heq.
    destruct (index_le_lt_dec α β) as [H1 | H1].
    - unshelve erewrite (choose_witness_choice _ _ a b _).
      { intros γ H. eapply dist_mono. apply Heq. eapply index_lt_le_trans; eauto. }
      reflexivity.
    - rewrite <- (@witness_P (dist_later α) _ _ a β H1).
      rewrite <- (@witness_P (dist_later α) _ _ b β H1).
      assumption.
  Qed.

  Lemma trunc_dist_later_eq α a: dist_later α a (trunc_dist_later α a).
  Proof. unfold trunc_dist_later. cbn. apply witness_P. Qed.
  Lemma trunc_dist_later_pre α a b : dist_later α a b → trunc_dist_later α a ≡ trunc_dist_later α b.
  Proof. intros H. unfold trunc_dist_later. cbn. by rewrite (choose_witness_choice _ _ a b H). Qed.

  Context {Hcofe : Cofe A}.

  (* we can prove, under these classical assumptions, that we can always make limits unique *)
  Program Definition classical_strict_bcompl α (Hα : zero ≺ α) (c : bchain A α) :=
    trunc_dist_later α (bcompl Hα c).

  Program Instance classical_strict_cofe : Cofe A :=
  { compl := @compl SI A _;
    bcompl := classical_strict_bcompl;
  }.
  Next Obligation. apply conv_compl. Qed.
  Next Obligation.
    intros α Hα c β Hβ. unfold classical_strict_bcompl.
    rewrite ofe_mor_ne.
    2: { rewrite conv_bcompl. cbn. reflexivity. }
    rewrite <- (trunc_dist_later_eq α (c _ _) β). reflexivity. apply Hβ.
  Qed.
  Next Obligation.
    intros. unfold classical_strict_bcompl.
    destruct (index_le_lt_dec α β) as [H1 | H1].
    - apply ofe_mor_ne. apply bcompl_ne, H.
    - rewrite <- (trunc_dist_later_eq α _ β H1).
      rewrite <- (trunc_dist_later_eq α _ β H1).
      apply bcompl_ne, H.
  Qed.

  Instance classical_StronglyUnique : @BcomplStronglyUnique _ A classical_strict_cofe.
  Proof.
    intros α Hα c d H1. unfold classical_strict_cofe, bcompl. unfold classical_strict_bcompl.
    apply trunc_dist_later_pre. intros β Hβ.
    rewrite !conv_bcompl. apply H1. Unshelve. apply Hβ.
  Qed.
End classical_truncation.
