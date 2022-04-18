From iris.base_logic Require Export base_logic.
From iris.algebra Require Import gmap.
From iris.algebra Require cofe_solver.
Set Default Proof Using "Type".

(** In this file we construct the type [iProp] of propositions of the Iris
logic. This is done by solving the following recursive domain equation:

  iProp ≈ uPred (∀ i : gid, gname -fin-> (Σ i) iProp)

where:

  Σ : gFunctors  := lists of locally constractive functors
  i : gid        := indexes addressing individual functors in [Σ]
  γ : gname      := ghost variable names

The Iris logic is parametrized by a list of locally contractive functors [Σ]
from the category of COFEs to the category of CMRAs. These functors are
instantiated with [iProp], the type of Iris propositions, which allows one to
construct impredicate CMRAs, such as invariants and stored propositions using
the agreement CMRA. *)


(** * Locally contractive functors *)
(** The type [gFunctor] bundles a functor from the category of COFEs to the
category of CMRAs with a proof that it is locally contractive. *)
Structure gFunctor (SI: indexT) := GFunctor {
  gFunctor_F :> rFunctor SI;
  gFunctor_contractive : rFunctorContractive gFunctor_F;
}.
Arguments GFunctor {_} _ {_}.
Existing Instance gFunctor_contractive.
Add Printing Constructor gFunctor.

(** The type [gFunctors] describes the parameters [Σ] of the Iris logic: lists
of [gFunctor]s.

Note that [gFunctors] is isomorphic to [list gFunctor], but defined in an
alternative way to avoid universe inconsistencies with respect to the universe
monomorphic [list] type. *)
Definition gFunctors SI := { n : nat & fin n → gFunctor SI }.

Definition gid {SI} (Σ : gFunctors SI) := fin (projT1 Σ).
Definition gFunctors_lookup {SI} (Σ : gFunctors SI) : gid Σ → gFunctor SI := projT2 Σ.
Coercion gFunctors_lookup : gFunctors >-> Funclass.

Definition gname := positive.
Canonical Structure gnameO SI := leibnizO SI gname.

(** The resources functor [iResF Σ A := ∀ i : gid, gname -fin-> (Σ i) A]. *)
Definition iResF {SI} (Σ : gFunctors SI) : urFunctor SI :=
  discrete_funURF (λ i, gmapURF gname (Σ i)).


(** We define functions for the empty list of functors, the singleton list of
functors, and the append operator on lists of functors. These are used to
compose [gFunctors] out of smaller pieces. *)
Module gFunctors.
  Definition nil {SI} : gFunctors SI := existT 0 (fin_0_inv _).

  Definition singleton {SI} (F : gFunctor SI) : gFunctors SI :=
    existT 1 (fin_S_inv (λ _, gFunctor SI) F (fin_0_inv _)).

  Definition app {SI} (Σ1 Σ2 : gFunctors SI) : gFunctors SI :=
    existT (projT1 Σ1 + projT1 Σ2) (fin_plus_inv _ (projT2 Σ1) (projT2 Σ2)).
End gFunctors.

Coercion gFunctors.singleton : gFunctor >-> gFunctors.
Notation "#[ ]" := gFunctors.nil (format "#[ ]").
Notation "#[ Σ1 ; .. ; Σn ]" :=
  (gFunctors.app Σ1 .. (gFunctors.app Σn gFunctors.nil) ..).


(** * Subfunctors *)
(** In order to make proofs in the Iris logic modular, they are not done with
respect to some concrete list of functors [Σ], but are instead parametrized by
an arbitrary list of functors [Σ] that contains at least certain functors. For
example, the lock library is parameterized by a functor [Σ] that should have
the functors corresponding to the heap and the exclusive monoid to manage to
lock invariant.

The contraints to can be expressed using the type class [subG Σ1 Σ2], which
expresses that the functors [Σ1] are contained in [Σ2]. *)
Class subG {SI} (Σ1 Σ2 : gFunctors SI) := in_subG i : { j | Σ1 i = Σ2 j }.

(** Avoid trigger happy type class search: this line ensures that type class
search is only triggered if the arguments of [subG] do not contain evars. Since
instance search for [subG] is restrained, instances should persistently have [subG] as
their first parameter to avoid loops. For example, the instances [subG_authΣ]
and [auth_discrete] otherwise create a cycle that pops up arbitrarily. *)
Hint Mode subG - ! + : typeclass_instances.

Lemma subG_inv {SI} (Σ1 Σ2 Σ: gFunctors SI) :
  subG (gFunctors.app Σ1 Σ2) Σ → subG Σ1 Σ * subG Σ2 Σ.
Proof.
  move=> H; split.
  - move=> i; move: H=> /(_ (Fin.L _ i)) [j] /=. rewrite fin_plus_inv_L; eauto.
  - move=> i; move: H=> /(_ (Fin.R _ i)) [j] /=. rewrite fin_plus_inv_R; eauto.
Qed.

Instance subG_refl {SI} (Σ: gFunctors SI) : subG Σ Σ.
Proof. move=> i; by exists i. Qed.
Instance subG_app_l {SI} (Σ Σ1 Σ2: gFunctors SI) : subG Σ Σ1 → subG Σ (gFunctors.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.L _ j). by rewrite /= fin_plus_inv_L.
Qed.
Instance subG_app_r {SI} (Σ Σ1 Σ2 : gFunctors SI): subG Σ Σ2 → subG Σ (gFunctors.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.R _ j). by rewrite /= fin_plus_inv_R.
Qed.


(** * Solution of the recursive domain equation *)
(** We first declare a module type and then an instance of it so as to seal all of
the construction, this way we are sure we do not use any properties of the
construction, and also avoid Coq from blindly unfolding it. *)
Module Type iProp_solution_sig.
  Parameter iPreProp : ∀ {SI: indexT}, gFunctors SI → ofeT SI.
  Global Declare Instance iPreProp_cofe {SI}{Σ: gFunctors SI} : Cofe (iPreProp Σ).

  Definition iResUR {SI} (Σ : gFunctors SI) : ucmraT SI :=
    discrete_funUR (λ i, gmapUR gname (Σ i (iPreProp Σ) _)).
  Notation iProp Σ := (uPredO (iResUR Σ)).
  Notation iPropI Σ := (uPredI (iResUR Σ)).
  Notation iPropSI Σ := (uPredSI (iResUR Σ)).

  Parameter iProp_unfold: ∀ {SI} {Σ: gFunctors SI}, iProp Σ -n> iPreProp Σ.
  Parameter iProp_fold: ∀ {SI} {Σ: gFunctors SI}, iPreProp Σ -n> iProp Σ.
  Parameter iProp_fold_unfold: ∀ {SI} {Σ: gFunctors SI} (P : iProp Σ),
    iProp_fold (iProp_unfold P) ≡ P.
  Parameter iProp_unfold_fold: ∀ {SI} {Σ: gFunctors SI} (P : iPreProp Σ),
    iProp_unfold (iProp_fold P) ≡ P.
End iProp_solution_sig.

Module Export iProp_solution : iProp_solution_sig.
  Import cofe_solver.
  Definition iProp_result {SI} (Σ : gFunctors SI) :
    solution (uPredOF (iResF Σ)) := solver.solution_F _ (uPredOF (iResF Σ)) (uPred_pure True).
  Definition iPreProp {SI} (Σ : gFunctors SI) : ofeT SI := iProp_result Σ.
  Global Instance iPreProp_cofe {SI} {Σ: gFunctors SI} : Cofe (iPreProp Σ) := _.

  Definition iResUR {SI} (Σ : gFunctors SI) : ucmraT SI :=
    discrete_funUR (λ i, gmapUR gname (Σ i (iPreProp Σ) _)).
  Notation iProp Σ := (uPredO (iResUR Σ)).

  Definition iProp_unfold {SI} {Σ: gFunctors SI} : iProp Σ -n> iPreProp Σ :=
    solution_fold _ (iProp_result Σ).
  Definition iProp_fold {SI} {Σ: gFunctors SI} : iPreProp Σ -n> iProp Σ := solution_unfold _ _.
  Lemma iProp_fold_unfold {SI} {Σ: gFunctors SI} (P : iProp Σ) : iProp_fold (iProp_unfold P) ≡ P.
  Proof. apply @solution_unfold_fold. Qed.
  Lemma iProp_unfold_fold {SI} {Σ: gFunctors SI} (P : iPreProp Σ) : iProp_unfold (iProp_fold P) ≡ P.
  Proof. apply @solution_fold_unfold. Qed.
End iProp_solution.

(** * Properties of the solution to the recursive domain equation *)
Lemma iProp_unfold_equivI {SI} {Σ: gFunctors SI} (P Q : iProp Σ) :
  iProp_unfold P ≡ iProp_unfold Q ⊢@{iPropI Σ} P ≡ Q.
Proof.
  rewrite -{2}(iProp_fold_unfold P) -{2}(iProp_fold_unfold Q). apply: bi.f_equiv.
Qed.
