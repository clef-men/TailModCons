From iris.bi Require Export bi.
From iris.proofmode Require Import base.
From iris.proofmode Require Export modalities.
From stdpp Require Import namespaces.
Set Default Proof Using "Type".
Import bi.

Class FromAssumption {SI} {PROP : bi SI} (p : bool) (P Q : PROP) :=
  from_assumption : □?p P ⊢ Q.
Arguments FromAssumption {_ _} _ _%I _%I : simpl never.
Arguments from_assumption {_ _} _ _%I _%I {_}.
Hint Mode FromAssumption - + + - - : typeclass_instances.

Class KnownLFromAssumption {SI} {PROP : bi SI} (p : bool) (P Q : PROP) :=
  knownl_from_assumption :> FromAssumption p P Q.
Arguments KnownLFromAssumption {_ _} _ _%I _%I : simpl never.
Arguments knownl_from_assumption {_ _} _ _%I _%I {_}.
Hint Mode KnownLFromAssumption - + + ! - : typeclass_instances.

Class KnownRFromAssumption {SI} {PROP : bi SI} (p : bool) (P Q : PROP) :=
  knownr_from_assumption :> FromAssumption p P Q.
Arguments KnownRFromAssumption {_ _} _ _%I _%I : simpl never.
Arguments knownr_from_assumption {_ _} _ _%I _%I {_}.
Hint Mode KnownRFromAssumption - + + - ! : typeclass_instances.

Class IntoPure {SI} {PROP : bi SI} (P : PROP) (φ : Prop) :=
  into_pure : P ⊢ ⌜φ⌝.
Arguments IntoPure {_ _} _%I _%type_scope : simpl never.
Arguments into_pure {_ _} _%I _%type_scope {_}.
Hint Mode IntoPure - + ! - : typeclass_instances.

(* [IntoPureT] is a variant of [IntoPure] with the argument in [Type] to avoid
some shortcoming of unification in Coq's type class search. An example where we
use this workaround is to repair the following instance:

  Global Instance into_exist_and_pure P Q (φ : Prop) :
    IntoPure P φ → IntoExist (P ∧ Q) (λ _ : φ, Q).

Coq is unable to use this instance: [class_apply] -- which is used by type class
search -- fails with the error that it cannot unify [Prop] and [Type]. This is
probably caused because [class_apply] uses an ancient unification algorith. The
[refine] tactic -- which uses a better unification algorithm -- succeeds to
apply the above instance.

Since we do not want to define [Hint Extern] declarations using [refine] for
any instance like [into_exist_and_pure], we factor this out in the class
[IntoPureT]. This way, we only have to declare a [Hint Extern] using [refine]
once, and use [IntoPureT] in any instance like [into_exist_and_pure].

TODO: Report this as a Coq bug, or wait for https://github.com/coq/coq/pull/991
to be finished and merged someday. *)
Class IntoPureT {SI} {PROP : bi SI} (P : PROP) (φ : Type) :=
  into_pureT : ∃ ψ : Prop, φ = ψ ∧ IntoPure P ψ.
Lemma into_pureT_hint {SI} {PROP : bi SI} (P : PROP) (φ : Prop) : IntoPure P φ → IntoPureT P φ.
Proof. by exists φ. Qed.
Hint Extern 0 (IntoPureT _ _) =>
  notypeclasses refine (into_pureT_hint _ _ _) : typeclass_instances.

(** [FromPure a P φ] is used when introducing a pure assertion. It is used by
[iPureIntro] and the [[%]] specialization pattern.

The Boolean [a] specifies whether introduction of [P] needs [emp] in addition
to [φ]. Concretely, for the [iPureIntro] tactic, this means it specifies whether
the spatial context should be empty or not.

Note that the Boolean [a] is not needed for the (dual) [IntoPure] class, because
there we can just ask that [P] is [Affine]. *)
Class FromPure {SI} {PROP : bi SI} (a : bool) (P : PROP) (φ : Prop) :=
  from_pure : <affine>?a ⌜φ⌝ ⊢ P.
Arguments FromPure {_ _} _ _%I _%type_scope : simpl never.
Arguments from_pure {_ _} _ _%I _%type_scope {_}.
Hint Mode FromPure - + - ! - : typeclass_instances.

Class FromPureT {SI} {PROP : bi SI} (a : bool) (P : PROP) (φ : Type) :=
  from_pureT : ∃ ψ : Prop, φ = ψ ∧ FromPure a P ψ.
Lemma from_pureT_hint {SI} {PROP : bi SI} (a : bool) (P : PROP) (φ : Prop) :
  FromPure a P φ → FromPureT a P φ.
Proof. by exists φ. Qed.
Hint Extern 0 (FromPureT _ _ _) =>
  notypeclasses refine (from_pureT_hint _ _ _ _) : typeclass_instances.

Class IntoInternalEq {SI} {PROP : sbi SI} {A : ofeT SI} (P : PROP) (x y : A) :=
  into_internal_eq : P ⊢ x ≡ y.
Arguments IntoInternalEq {_ _ _} _%I _%type_scope _%type_scope : simpl never.
Arguments into_internal_eq {_ _ _} _%I _%type_scope _%type_scope {_}.
Hint Mode IntoInternalEq - + - ! - - : typeclass_instances.

Class IntoPersistent {SI} {PROP : bi SI} (p : bool) (P Q : PROP) :=
  into_persistent : <pers>?p P ⊢ <pers> Q.
Arguments IntoPersistent {_ _} _ _%I _%I : simpl never.
Arguments into_persistent {_ _} _ _%I _%I {_}.
Hint Mode IntoPersistent - + + ! - : typeclass_instances.

(** The [FromModal M P Q] class is used by the [iModIntro] tactic to transform
a goal [P] into a modality [M] and proposition [Q].

The inputs are [P] and [sel] and the outputs are [M] and [Q].

The input [sel] can be used to specify which modality to introduce in case there
are multiple choices to turn [P] into a modality. For example, given [⎡|==> R⎤],
[sel] can be either [|==> ?e] or [⎡ ?e ⎤], which turn it into an update modality
or embedding, respectively. In case there is no need to specify the modality to
introduce, [sel] should be an evar.

For modalities [N] that do not need to augment the proof mode environment, one
can define an instance [FromModal modality_id (N P) P]. Defining such an
instance only imposes the proof obligation [P ⊢ N P]. Examples of such
modalities [N] are [bupd], [fupd], [except_0], [monPred_subjectively] and
[bi_absorbingly]. *)
Class FromModal {SI} {PROP1 PROP2 : bi SI} {A}
    (M : modality PROP1 PROP2) (sel : A) (P : PROP2) (Q : PROP1) :=
  from_modal : M Q ⊢ P.
Arguments FromModal {_ _ _ _} _ _%I _%I _%I : simpl never.
Arguments from_modal {_ _ _ _} _ _ _%I _%I {_}.
Hint Mode FromModal - - + - - - ! - : typeclass_instances.

(** The [FromAffinely P Q] class is used to add an [<affine>] modality to the
proposition [Q].

The input is [Q] and the output is [P]. *)
Class FromAffinely {SI} {PROP : bi SI} (P Q : PROP) :=
  from_affinely : <affine> Q ⊢ P.
Arguments FromAffinely {_ _} _%I _%I : simpl never.
Arguments from_affinely {_ _} _%I _%I {_}.
Hint Mode FromAffinely - + - ! : typeclass_instances.

(** The [IntoAbsorbingly P Q] class is used to add an [<absorb>] modality to
the proposition [Q].

The input is [Q] and the output is [P]. *)
Class IntoAbsorbingly {SI} {PROP : bi SI} (P Q : PROP) :=
  into_absorbingly : P ⊢ <absorb> Q.
Arguments IntoAbsorbingly {_ _} _%I _%I.
Arguments into_absorbingly {_ _} _%I _%I {_}.
Hint Mode IntoAbsorbingly - + - ! : typeclass_instances.

(*
Converting an assumption [R] into a wand [P -∗ Q] is done in three stages:

- Strip modalities and universal quantifiers of [R] until an arrow or a wand
  has been obtained.
- Balance modalities in the arguments [P] and [Q] to match the goal (which used
  for [iApply]) or the premise (when used with [iSpecialize] and a specific
  hypothesis).
- Instantiate the premise of the wand or implication.
*)

Class IntoWand {SI} {PROP : bi SI} (p q : bool) (R P Q : PROP) :=
  into_wand : □?p R ⊢ □?q P -∗ Q.
Arguments IntoWand {_ _} _ _ _%I _%I _%I : simpl never.
Arguments into_wand {_ _} _ _ _%I _%I _%I {_}.
Hint Mode IntoWand - + + + ! - - : typeclass_instances.

Class IntoWand' {SI} {PROP : bi SI} (p q : bool) (R P Q : PROP) :=
  into_wand' : IntoWand p q R P Q.
Arguments IntoWand' {_ _} _ _ _%I _%I _%I : simpl never.
Hint Mode IntoWand' - + + + ! ! - : typeclass_instances.
Hint Mode IntoWand' - + + + ! - ! : typeclass_instances.

Class FromWand {SI} {PROP : bi SI} (P Q1 Q2 : PROP) := from_wand : (Q1 -∗ Q2) ⊢ P.
Arguments FromWand {_ _} _%I _%I _%I : simpl never.
Arguments from_wand {_ _} _%I _%I _%I {_}.
Hint Mode FromWand - + ! - - : typeclass_instances.

Class FromImpl {SI} {PROP : bi SI} (P Q1 Q2 : PROP) := from_impl : (Q1 → Q2) ⊢ P.
Arguments FromImpl {_ _} _%I _%I _%I : simpl never.
Arguments from_impl {_ _} _%I _%I _%I {_}.
Hint Mode FromImpl - + ! - - : typeclass_instances.

Class FromSep {SI} {PROP : bi SI} (P Q1 Q2 : PROP) := from_sep : Q1 ∗ Q2 ⊢ P.
Arguments FromSep {_ _} _%I _%I _%I : simpl never.
Arguments from_sep {_ _} _%I _%I _%I {_}.
Hint Mode FromSep - + ! - - : typeclass_instances.
Hint Mode FromSep - + - ! ! : typeclass_instances. (* For iCombine *)

Class FromAnd {SI} {PROP : bi SI} (P Q1 Q2 : PROP) := from_and : Q1 ∧ Q2 ⊢ P.
Arguments FromAnd {_ _} _%I _%I _%I : simpl never.
Arguments from_and {_ _} _%I _%I _%I {_}.
Hint Mode FromAnd - + ! - - : typeclass_instances.
Hint Mode FromAnd - + - ! ! : typeclass_instances. (* For iCombine *)

Class IntoAnd {SI} {PROP : bi SI} (p : bool) (P Q1 Q2 : PROP) :=
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2).
Arguments IntoAnd {_ _} _ _%I _%I _%I : simpl never.
Arguments into_and {_ _} _ _%I _%I _%I {_}.
Hint Mode IntoAnd - + + ! - - : typeclass_instances.

Class IntoSep {SI} {PROP : bi SI} (P Q1 Q2 : PROP) :=
  into_sep : P ⊢ Q1 ∗ Q2.
Arguments IntoSep {_ _} _%I _%I _%I : simpl never.
Arguments into_sep {_ _} _%I _%I _%I {_}.
Hint Mode IntoSep - + ! - - : typeclass_instances.

Class FromOr {SI} {PROP : bi SI} (P Q1 Q2 : PROP) := from_or : Q1 ∨ Q2 ⊢ P.
Arguments FromOr {_ _} _%I _%I _%I : simpl never.
Arguments from_or {_ _} _%I _%I _%I {_}.
Hint Mode FromOr - + ! - - : typeclass_instances.

Class IntoOr {SI} {PROP : bi SI} (P Q1 Q2 : PROP) := into_or : P ⊢ Q1 ∨ Q2.
Arguments IntoOr {_ _} _%I _%I _%I : simpl never.
Arguments into_or {_ _} _%I _%I _%I {_}.
Hint Mode IntoOr - + ! - - : typeclass_instances.

Class FromExist {SI} {PROP : bi SI} {A} (P : PROP) (Φ : A → PROP) :=
  from_exist : (∃ x, Φ x) ⊢ P.
Arguments FromExist {_ _ _} _%I _%I : simpl never.
Arguments from_exist {_ _ _} _%I _%I {_}.
Hint Mode FromExist - + - ! - : typeclass_instances.

Class IntoExist {SI} {PROP : bi SI} {A} (P : PROP) (Φ : A → PROP) :=
  into_exist : P ⊢ ∃ x, Φ x.
Arguments IntoExist {_ _ _} _%I _%I : simpl never.
Arguments into_exist {_ _ _} _%I _%I {_}.
Hint Mode IntoExist - + - ! - : typeclass_instances.

Class IntoForall {SI} {PROP : bi SI} {A} (P : PROP) (Φ : A → PROP) :=
  into_forall : P ⊢ ∀ x, Φ x.
Arguments IntoForall {_ _ _} _%I _%I : simpl never.
Arguments into_forall {_ _ _} _%I _%I {_}.
Hint Mode IntoForall - + - ! - : typeclass_instances.

Class FromForall {SI} {PROP : bi SI} {A} (P : PROP) (Φ : A → PROP) :=
  from_forall : (∀ x, Φ x) ⊢ P.
Arguments FromForall {_ _ _} _%I _%I : simpl never.
Arguments from_forall {_ _ _} _%I _%I {_}.
Hint Mode FromForall - + - ! - : typeclass_instances.

Class IsExcept0 {SI} {PROP : sbi SI} (Q : PROP) := is_except_0 : ◇ Q ⊢ Q.
Arguments IsExcept0 {_ _} _%I : simpl never.
Arguments is_except_0 {_ _} _%I {_}.
Hint Mode IsExcept0 - + ! : typeclass_instances.

(** The [ElimModal φ p p' P P' Q Q'] class is used by the [iMod] tactic.

The inputs are [p], [P] and [Q], and the outputs are [φ], [p'], [P'] and [Q'].

The class is used to transform a hypothesis [P] into a hypothesis [P'], given
a goal [Q], which is simultaniously transformed into [Q']. The Booleans [p]
and [p'] indicate whether the original, respectively, updated hypothesis reside
in the persistent context (iff [true]). The proposition [φ] can be used to
express a side-condition that [iMod] will generate (if not [True]).

An example instance is:

  ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).

This instance expresses that to eliminate [|={E1,E2}=> P] the goal is
transformed from [|={E1,E3}=> Q] into [|={E2,E3}=> Q], and the resulting
hypothesis is moved into the spatial context (regardless of where it was
originally). A corresponding [ElimModal] instance for the Iris 1/2-style update
modality, would have a side-condition [φ] on the masks. *)
Class ElimModal {SI} {PROP : bi SI} (φ : Prop) (p p' : bool) (P P' : PROP) (Q Q' : PROP) :=
  elim_modal : φ → □?p P ∗ (□?p' P' -∗ Q') ⊢ Q.
Arguments ElimModal {_ _} _ _ _ _%I _%I _%I _%I : simpl never.
Arguments elim_modal {_ _} _ _ _ _%I _%I _%I _%I {_}.
Hint Mode ElimModal - + - ! - ! - ! - : typeclass_instances.

(* Used by the specialization pattern [ > ] in [iSpecialize] and [iAssert] to
add a modality to the goal corresponding to a premise/asserted proposition. *)
Class AddModal {SI} {PROP : bi SI} (P P' : PROP) (Q : PROP) :=
  add_modal : P ∗ (P' -∗ Q) ⊢ Q.
Arguments AddModal {_ _} _%I _%I _%I : simpl never.
Arguments add_modal {_ _} _%I _%I _%I {_}.
Hint Mode AddModal - + - ! ! : typeclass_instances.

Lemma add_modal_id {SI} {PROP : bi SI} (P Q : PROP) : AddModal P P Q.
Proof. by rewrite /AddModal wand_elim_r. Qed.

(** We use the classes [IsCons] and [IsApp] to make sure that instances such as
[frame_big_sepL_cons] and [frame_big_sepL_app] cannot be applied repeatedly
often when having [ [∗ list] k ↦ x ∈ ?e, Φ k x] with [?e] an evar. *)
Class IsCons {A} (l : list A) (x : A) (k : list A) := is_cons : l = x :: k.
Class IsApp {A} (l k1 k2 : list A) := is_app : l = k1 ++ k2.
Global Hint Mode IsCons + ! - - : typeclass_instances.
Global Hint Mode IsApp + ! - - : typeclass_instances.

Instance is_cons_cons {A} (x : A) (l : list A) : IsCons (x :: l) x l.
Proof. done. Qed.
Instance is_app_app {A} (l1 l2 : list A) : IsApp (l1 ++ l2) l1 l2.
Proof. done. Qed.

Class Frame {SI} {PROP : bi SI} (p : bool) (R P Q : PROP) := frame : □?p R ∗ Q ⊢ P.
Arguments Frame {_ _} _ _%I _%I _%I.
Arguments frame {_ _} _ _%I _%I _%I {_}.
Hint Mode Frame - + + ! ! - : typeclass_instances.

(* The boolean [progress] indicates whether actual framing has been performed.
If it is [false], then the default instance [maybe_frame_default] below has been
used. *)
Class MaybeFrame {SI} {PROP : bi SI} (p : bool) (R P Q : PROP) (progress : bool) :=
  maybe_frame : □?p R ∗ Q ⊢ P.
Arguments MaybeFrame {_ _} _ _%I _%I _%I _.
Arguments maybe_frame {_ _} _ _%I _%I _%I _ {_}.
Hint Mode MaybeFrame - + + ! - - - : typeclass_instances.

Instance maybe_frame_frame {SI} {PROP : bi SI} p (R P Q : PROP) :
  Frame p R P Q → MaybeFrame p R P Q true.
Proof. done. Qed.

Instance maybe_frame_default_persistent {SI} {PROP : bi SI} (R P : PROP) :
  MaybeFrame true R P P false | 100.
Proof. intros. rewrite /MaybeFrame /=. by rewrite sep_elim_r. Qed.
Instance maybe_frame_default {SI} {PROP : bi SI} (R P : PROP) :
  TCOr (Affine R) (Absorbing P) → MaybeFrame false R P P false | 100.
Proof. intros. rewrite /MaybeFrame /=. apply: sep_elim_r. Qed.

(* For each of the [MakeXxxx] class, there is a [KnownMakeXxxx]
   variant, that only succeeds if the parameter(s) is not an evar. In
   the case the parameter(s) is an evar, then [MakeXxxx] will not
   instantiate it arbitrarily.

   The reason for this is that if given an evar, these typeclasses
   would typically try to instantiate this evar with some arbitrary
   logical constructs such as emp or True. Therefore, we use an Hint
   Mode to disable all the instances that would have this behavior. *)

Class MakeEmbed {SI} {PROP PROP' : bi SI} `{BiEmbed SI PROP PROP'} (P : PROP) (Q : PROP') :=
  make_embed : ⎡P⎤ ⊣⊢ Q.
Arguments MakeEmbed {_ _ _ _} _%I _%I.
Hint Mode MakeEmbed - + + + - - : typeclass_instances.
Class KnownMakeEmbed {SI} {PROP PROP' : bi SI} `{BiEmbed SI PROP PROP'} (P : PROP) (Q : PROP') :=
  known_make_embed :> MakeEmbed P Q.
Arguments KnownMakeEmbed {_ _ _ _} _%I _%I.
Hint Mode KnownMakeEmbed - + + + ! - : typeclass_instances.

Class MakeSep {SI} {PROP : bi SI} (P Q PQ : PROP) := make_sep : P ∗ Q ⊣⊢ PQ .
Arguments MakeSep {_ _} _%I _%I _%I.
Hint Mode MakeSep - + - - - : typeclass_instances.
Class KnownLMakeSep {SI} {PROP : bi SI} (P Q PQ : PROP) :=
  knownl_make_sep :> MakeSep P Q PQ.
Arguments KnownLMakeSep {_ _} _%I _%I _%I.
Hint Mode KnownLMakeSep - + ! - - : typeclass_instances.
Class KnownRMakeSep {SI} {PROP : bi SI} (P Q PQ : PROP) :=
  knownr_make_sep :> MakeSep P Q PQ.
Arguments KnownRMakeSep {_ _} _%I _%I _%I.
Hint Mode KnownRMakeSep - + - ! - : typeclass_instances.

Class MakeAnd {SI} {PROP : bi SI} (P Q PQ : PROP) :=  make_and_l : P ∧ Q ⊣⊢ PQ.
Arguments MakeAnd {_ _} _%I _%I _%I.
Hint Mode MakeAnd - + - - - : typeclass_instances.
Class KnownLMakeAnd {SI} {PROP : bi SI} (P Q PQ : PROP) :=
  knownl_make_and :> MakeAnd P Q PQ.
Arguments KnownLMakeAnd {_ _} _%I _%I _%I.
Hint Mode KnownLMakeAnd - + ! - - : typeclass_instances.
Class KnownRMakeAnd {SI} {PROP : bi SI} (P Q PQ : PROP) :=
  knownr_make_and :> MakeAnd P Q PQ.
Arguments KnownRMakeAnd {_ _} _%I _%I _%I.
Hint Mode KnownRMakeAnd - + - ! - : typeclass_instances.

Class MakeOr {SI} {PROP : bi SI} (P Q PQ : PROP) := make_or_l : P ∨ Q ⊣⊢ PQ.
Arguments MakeOr {_ _} _%I _%I _%I.
Hint Mode MakeOr - + - - - : typeclass_instances.
Class KnownLMakeOr {SI} {PROP : bi SI} (P Q PQ : PROP) :=
  knownl_make_or :> MakeOr P Q PQ.
Arguments KnownLMakeOr {_ _} _%I _%I _%I.
Hint Mode KnownLMakeOr - + ! - - : typeclass_instances.
Class KnownRMakeOr {SI} {PROP : bi SI} (P Q PQ : PROP) := knownr_make_or :> MakeOr P Q PQ.
Arguments KnownRMakeOr {_ _} _%I _%I _%I.
Hint Mode KnownRMakeOr - + - ! - : typeclass_instances.

Class MakeAffinely {SI} {PROP : bi SI} (P Q : PROP) :=
  make_affinely : <affine> P ⊣⊢ Q.
Arguments MakeAffinely {_ _} _%I _%I.
Hint Mode MakeAffinely - + - - : typeclass_instances.
Class KnownMakeAffinely {SI} {PROP : bi SI} (P Q : PROP) :=
  known_make_affinely :> MakeAffinely P Q.
Arguments KnownMakeAffinely {_ _} _%I _%I.
Hint Mode KnownMakeAffinely - + ! - : typeclass_instances.

Class MakeIntuitionistically {SI} {PROP : bi SI} (P Q : PROP) :=
  make_intuitionistically : □ P ⊣⊢ Q.
Arguments MakeIntuitionistically {_ _} _%I _%I.
Hint Mode MakeIntuitionistically - + - - : typeclass_instances.
Class KnownMakeIntuitionistically {SI} {PROP : bi SI} (P Q : PROP) :=
  known_make_intuitionistically :> MakeIntuitionistically P Q.
Arguments KnownMakeIntuitionistically {_ _} _%I _%I.
Hint Mode KnownMakeIntuitionistically - + ! - : typeclass_instances.

Class MakeAbsorbingly {SI} {PROP : bi SI} (P Q : PROP) :=
  make_absorbingly : <absorb> P ⊣⊢ Q.
Arguments MakeAbsorbingly {_ _} _%I _%I.
Hint Mode MakeAbsorbingly - + - - : typeclass_instances.
Class KnownMakeAbsorbingly {SI} {PROP : bi SI} (P Q : PROP) :=
  known_make_absorbingly :> MakeAbsorbingly P Q.
Arguments KnownMakeAbsorbingly {_ _} _%I _%I.
Hint Mode KnownMakeAbsorbingly - + ! - : typeclass_instances.

Class MakePersistently {SI} {PROP : bi SI} (P Q : PROP) :=
  make_persistently : <pers> P ⊣⊢ Q.
Arguments MakePersistently {_ _} _%I _%I.
Hint Mode MakePersistently - + - - : typeclass_instances.
Class KnownMakePersistently {SI} {PROP : bi SI} (P Q : PROP) :=
  known_make_persistently :> MakePersistently P Q.
Arguments KnownMakePersistently {_ _} _%I _%I.
Hint Mode KnownMakePersistently - + ! - : typeclass_instances.

Class MakeLaterN {SI} {PROP : sbi SI} (n : nat) (P lP : PROP) :=
  make_laterN : ▷^n P ⊣⊢ lP.
Arguments MakeLaterN {_ _} _%nat _%I _%I.
Hint Mode MakeLaterN - + + - - : typeclass_instances.
Class KnownMakeLaterN {SI} {PROP : sbi SI} (n : nat) (P lP : PROP) :=
  known_make_laterN :> MakeLaterN n P lP.
Arguments KnownMakeLaterN {_ _} _%nat _%I _%I.
Hint Mode KnownMakeLaterN - + + ! - : typeclass_instances.

Class MakeExcept0 {SI} {PROP : sbi SI} (P Q : PROP) :=
  make_except_0 : sbi_except_0 P ⊣⊢ Q.
Arguments MakeExcept0 {_ _} _%I _%I.
Hint Mode MakeExcept0 - + - - : typeclass_instances.
Class KnownMakeExcept0 {SI} {PROP : sbi SI} (P Q : PROP) :=
  known_make_except_0 :> MakeExcept0 P Q.
Arguments KnownMakeExcept0 {_ _} _%I _%I.
Hint Mode KnownMakeExcept0 - + ! - : typeclass_instances.

Class IntoExcept0 {SI} {PROP : sbi SI} (P Q : PROP) := into_except_0 : P ⊢ ◇ Q.
Arguments IntoExcept0 {_ _} _%I _%I : simpl never.
Arguments into_except_0 {_ _} _%I _%I {_}.
Hint Mode IntoExcept0 - + ! - : typeclass_instances.
Hint Mode IntoExcept0 - + - ! : typeclass_instances.

(* The class [MaybeIntoLaterN] has only two instances:

- The default instance [MaybeIntoLaterN n P P], i.e. [▷^n P -∗ P]
- The instance [IntoLaterN n P Q → MaybeIntoLaterN n P Q], where [IntoLaterN]
  is identical to [MaybeIntoLaterN], but is supposed to make progress, i.e. it
  should actually strip a later.

The point of using the auxilary class [IntoLaterN] is to ensure that the
default instance is not applied deeply inside a term, which may result in too
many definitions being unfolded (see issue #55).

For binary connectives we have the following instances:

<<
IntoLaterN n P P'       MaybeIntoLaterN n Q Q'
------------------------------------------
     IntoLaterN n (P /\ Q) (P' /\ Q')


      IntoLaterN n Q Q'
-------------------------------
IntoLaterN n (P /\ Q) (P /\ Q')
>>

The Boolean [only_head] indicates whether laters should only be stripped in
head position or also below other logical connectives. For [iNext] it should
strip laters below other logical connectives, but this should not happen while
framing, e.g. the following should succeed:

<<
Lemma test_iFrame_later_1 P Q : P ∗ ▷ Q -∗ ▷ (P ∗ ▷ Q).
Proof. iIntros "H". iFrame "H". Qed.
>>
*)
Class MaybeIntoLaterN {SI} {PROP : sbi SI} (only_head : bool) (n : nat) (P Q : PROP) :=
  maybe_into_laterN : P ⊢ ▷^n Q.
Arguments MaybeIntoLaterN {_ _} _ _%nat_scope _%I _%I.
Arguments maybe_into_laterN {_ _} _ _%nat_scope _%I _%I {_}.
Hint Mode MaybeIntoLaterN - + + + - - : typeclass_instances.

Class IntoLaterN {SI} {PROP : sbi SI} (only_head : bool) (n : nat) (P Q : PROP) :=
  into_laterN :> MaybeIntoLaterN only_head n P Q.
Arguments IntoLaterN {_ _} _ _%nat_scope _%I _%I.
Hint Mode IntoLaterN - + + + ! - : typeclass_instances.

Instance maybe_into_laterN_default {SI} {PROP : sbi SI} only_head n (P : PROP) :
  MaybeIntoLaterN only_head n P P | 1000.
Proof. apply laterN_intro. Qed.
(* In the case both parameters are evars and n=0, we have to stop the
   search and unify both evars immediately instead of looping using
   other instances. *)
Instance maybe_into_laterN_default_0 {SI} {PROP : sbi SI} only_head (P : PROP) :
  MaybeIntoLaterN only_head 0 P P | 0.
Proof. apply _. Qed.

(** The class [IntoEmbed P Q] is used to transform hypotheses while introducing
embeddings using [iModIntro].

Input: the proposition [P], output: the proposition [Q] so that [P ⊢ ⎡Q⎤]. *)

Class IntoEmbed {SI} {PROP PROP' : bi SI} `{BiEmbed SI PROP PROP'} (P : PROP') (Q : PROP) :=
  into_embed : P ⊢ ⎡Q⎤.
Arguments IntoEmbed {_ _ _ _} _%I _%I.
Arguments into_embed {_ _ _ _} _%I _%I {_}.
Hint Mode IntoEmbed - + + + ! -  : typeclass_instances.

(* We use two type classes for [AsEmpValid], in order to avoid loops in
   typeclass search. Indeed, the [as_emp_valid_embed] instance would try
   to add an arbitrary number of embeddings. To avoid this, the
   [AsEmpValid0] type class cannot handle embeddings, and therefore
   [as_emp_valid_embed] only tries to add one embedding, and we never try
   to insert nested embeddings. This has the additional advantage of
   always trying [as_emp_valid_embed] as a second option, so that this
   instance is never used when the BI is unknown.

   No Hint Modes are declared here. The appropriate one would be
   [Hint Mode - ! -], but the fact that Coq ignores primitive
   projections for hints modes would make this fail.*)
Class AsEmpValid {SI} {PROP : bi SI} (φ : Prop) (P : PROP) :=
  as_emp_valid : φ ↔ bi_emp_valid P.
Arguments AsEmpValid {_ _} _%type _%I.
Class AsEmpValid0 {SI} {PROP : bi SI} (φ : Prop) (P : PROP) :=
  as_emp_valid_here : AsEmpValid φ P.
Arguments AsEmpValid0 {_ _} _%type _%I.
Existing Instance as_emp_valid_here | 0.

Lemma as_emp_valid_1 (φ : Prop) {SI} {PROP : bi SI} (P : PROP) `{!AsEmpValid φ P} :
  φ → bi_emp_valid P.
Proof. by apply as_emp_valid. Qed.
Lemma as_emp_valid_2 (φ : Prop) {SI} {PROP : bi SI} (P : PROP) `{!AsEmpValid φ P} :
  bi_emp_valid P → φ.
Proof. by apply as_emp_valid. Qed.

(* Input: [P]; Outputs: [N],
   Extracts the namespace associated with an invariant assertion. Used for [iInv]. *)
Class IntoInv {SI} {PROP : bi SI} (P: PROP) (N: namespace).
Arguments IntoInv {_ _} _%I _.
Hint Mode IntoInv - + ! - : typeclass_instances.

(** Accessors.
    This definition only exists for the purpose of the proof mode; a truly
    usable and general form would use telescopes and also allow binders for the
    closing view shift.  [γ] is an [option] to make it easy for ElimAcc
    instances to recognize the [emp] case and make it look nicer. *)
Definition accessor {SI} {PROP : bi SI} {X : Type} (M1 M2 : PROP → PROP)
           (α β : X → PROP) (mγ : X → option PROP) : PROP :=
  M1 (∃ x, α x ∗ (β x -∗ M2 (default emp (mγ x))))%I.

(* Typeclass for assertions around which accessors can be elliminated.
   Inputs: [Q], [E1], [E2], [α], [β], [γ]
   Outputs: [Q']

   Elliminates an accessor [accessor E1 E2 α β γ] in goal [Q'], turning the goal
   into [Q'] with a new assumption [α x]. *)
Class ElimAcc {SI} {PROP : bi SI} {X : Type} (M1 M2 : PROP → PROP)
      (α β : X → PROP) (mγ : X → option PROP)
      (Q : PROP) (Q' : X → PROP) :=
  elim_acc : ((∀ x, α x -∗ Q' x) -∗ accessor M1 M2 α β mγ -∗ Q).
Arguments ElimAcc {_ _} {_} _%I _%I _%I _%I _%I _%I : simpl never.
Arguments elim_acc {_ _} {_} _%I _%I _%I _%I _%I _%I {_}.
Hint Mode ElimAcc - + ! ! ! ! ! ! ! - : typeclass_instances.

(* Turn [P] into an accessor.
   Inputs:
   - [Pacc]: the assertion to be turned into an accessor (e.g. an invariant)
   Outputs:
   - [Pin]: additional logic assertion needed for starting the accessor.
   - [φ]: additional Coq assertion needed for starting the accessor.
   - [X] [α], [β], [γ]: the accessor parameters.
   - [M1], [M2]: the two accessor modalities (they will typically still have
     some evars though, e.g. for the masks)
*)
Class IntoAcc {SI} {PROP : bi SI} {X : Type} (Pacc : PROP) (φ : Prop) (Pin : PROP)
      (M1 M2 : PROP → PROP) (α β : X → PROP) (mγ : X → option PROP) :=
  into_acc : φ → Pacc -∗ Pin -∗ accessor M1 M2 α β mγ.
Arguments IntoAcc {_ _} {_} _%I _ _%I _%I _%I _%I _%I _%I : simpl never.
Arguments into_acc {_ _} {_} _%I _ _%I _%I _%I _%I _%I _%I {_} : simpl never.
Hint Mode IntoAcc - + - ! - - - - - - - : typeclass_instances.

(* The typeclass used for the [iInv] tactic.
   Input: [Pinv]
   Arguments:
   - [Pinv] is an invariant assertion
   - [Pin] is an additional logic assertion needed for opening an invariant
   - [φ] is an additional Coq assertion needed for opening an invariant
   - [Pout] is the assertion obtained by opening the invariant
   - [Pclose] is the closing view shift.  It must be (Some _) or None
     when doing typeclass search as instances are allowed to make a
     case distinction on whether the user wants a closing view-shift or not.
   - [Q] is a goal on which iInv may be invoked
   - [Q'] is the transformed goal that must be proved after opening the invariant.

   Most users will never want to instantiate this; there is a general instance
   based on [ElimAcc] and [IntoAcc].  However, logics like Iris 2 that support
   invariants but not mask-changing fancy updates can use this class directly to
   still benefit from [iInv].

   TODO: Add support for a binder (like accessors have it).
*)
Class ElimInv {SI} {PROP : bi SI} {X : Type} (φ : Prop)
      (Pinv Pin : PROP) (Pout : X → PROP) (mPclose : option (X → PROP))
      (Q : PROP) (Q' : X → PROP) :=
  elim_inv : φ → Pinv ∗ Pin ∗ (∀ x, Pout x ∗ (default (λ _, emp) mPclose) x -∗ Q' x) ⊢ Q.
Arguments ElimInv {_ _} {_} _ _%I _%I _%I _%I _%I _%I : simpl never.
Arguments elim_inv {_ _} {_} _ _%I _%I _%I _%I _%I _%I {_}.
Hint Mode ElimInv - + - - ! - - ! ! - : typeclass_instances.

(** We make sure that tactics that perform actions on *specific* hypotheses or
parts of the goal look through the [tc_opaque] connective, which is used to make
definitions opaque for type class search. For example, when using [iDestruct],
an explicit hypothesis is affected, and as such, we should look through opaque
definitions. However, when using [iFrame] or [iNext], arbitrary hypotheses or
parts of the goal are affected, and as such, type class opacity should be
respected.

This means that there are [tc_opaque] instances for all proofmode type classes
with the exception of:

- [FromAssumption] used by [iAssumption]
- [Frame] and [MaybeFrame] used by [iFrame]
- [MaybeIntoLaterN] and [FromLaterN] used by [iNext]
- [IntoPersistent] used by [iIntuitionistic]
*)
Instance into_pure_tc_opaque {SI} {PROP : bi SI} (P : PROP) φ :
  IntoPure P φ → IntoPure (tc_opaque P) φ := id.
Instance from_pure_tc_opaque {SI} {PROP : bi SI} (a : bool) (P : PROP) φ :
  FromPure a P φ → FromPure a (tc_opaque P) φ := id.
Instance from_wand_tc_opaque {SI} {PROP : bi SI} (P Q1 Q2 : PROP) :
  FromWand P Q1 Q2 → FromWand (tc_opaque P) Q1 Q2 := id.
Instance into_wand_tc_opaque {SI} {PROP : bi SI} p q (R P Q : PROP) :
  IntoWand p q R P Q → IntoWand p q (tc_opaque R) P Q := id.
(* Higher precedence than [from_and_sep] so that [iCombine] does not loop. *)
Instance from_and_tc_opaque {SI} {PROP : bi SI} (P Q1 Q2 : PROP) :
  FromAnd P Q1 Q2 → FromAnd (tc_opaque P) Q1 Q2 | 102 := id.
Instance into_and_tc_opaque {SI} {PROP : bi SI} p (P Q1 Q2 : PROP) :
  IntoAnd p P Q1 Q2 → IntoAnd p (tc_opaque P) Q1 Q2 := id.
Instance into_sep_tc_opaque {SI} {PROP : bi SI} (P Q1 Q2 : PROP) :
  IntoSep P Q1 Q2 → IntoSep (tc_opaque P) Q1 Q2 := id.
Instance from_or_tc_opaque {SI} {PROP : bi SI} (P Q1 Q2 : PROP) :
  FromOr P Q1 Q2 → FromOr (tc_opaque P) Q1 Q2 := id.
Instance into_or_tc_opaque {SI} {PROP : bi SI} (P Q1 Q2 : PROP) :
  IntoOr P Q1 Q2 → IntoOr (tc_opaque P) Q1 Q2 := id.
Instance from_exist_tc_opaque {SI} {PROP : bi SI} {A} (P : PROP) (Φ : A → PROP) :
  FromExist P Φ → FromExist (tc_opaque P) Φ := id.
Instance into_exist_tc_opaque {SI} {PROP : bi SI} {A} (P : PROP) (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (tc_opaque P) Φ := id.
Instance into_forall_tc_opaque {SI} {PROP : bi SI} {A} (P : PROP) (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (tc_opaque P) Φ := id.
Instance from_modal_tc_opaque {SI} {PROP1 PROP2 : bi SI} {A}
    M (sel : A) (P : PROP2) (Q : PROP1) :
  FromModal M sel P Q → FromModal M sel (tc_opaque P) Q := id.
Instance elim_modal_tc_opaque {SI} {PROP : bi SI} φ p p' (P P' Q Q' : PROP) :
  ElimModal φ p p' P P' Q Q' → ElimModal φ p p' (tc_opaque P) P' Q Q' := id.
Instance into_inv_tc_opaque {SI} {PROP : bi SI} (P : PROP) N :
  IntoInv P N → IntoInv (tc_opaque P) N := id.
Instance elim_inv_tc_opaque {SI} {PROP : sbi SI} {X} φ Pinv Pin Pout Pclose Q Q' :
  ElimInv (PROP:=PROP) (X:=X) φ Pinv Pin Pout Pclose Q Q' →
  ElimInv φ (tc_opaque Pinv) Pin Pout Pclose Q Q' := id.
