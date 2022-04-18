From iris.algebra Require Export ofe wf_IR.
Set Default Proof Using "Type".
Require Coq.Logic.PropExtensionality.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Logic.ProofIrrelevance.

Section cofe.
  Context (SI : indexT).
  (* Shorthand notation to avoid making a distinction between Cofes and ofes *)
  Definition COFE := { C : ofeT SI & Cofe C }.
  Global Coercion projCOFE (C: COFE) : ofeT SI := (projT1 C).
  Global Instance COFE_cofe (C: COFE) : Cofe C := projT2 C.
  Definition cofe (A: ofeT SI) `{C: Cofe SI A} := existT A C.
End cofe.

Definition proj_id {SI} {A B : COFE SI} (Heq : A = B) : projCOFE _ A = projCOFE _ B.
Proof. by rewrite Heq. Qed.

(* non-expansive maps commute with bounded limits only in a restricted way *)
Lemma bounded_ne_bcompl {SI : indexT} {A B : ofeT SI} {Hc : Cofe A} {Hb : Cofe B} (f : A -n> B):
  ∀ β (c : bchain _ β) Hβ γ (Hγ : γ ≺ β), f (bcompl Hβ c) ≡{γ}≡ bcompl Hβ (bchain_map f c).
Proof.
  intros β c Hβ γ Hγ.
  etransitivity.
  - rewrite ofe_mor_ne. 2: apply conv_bcompl. reflexivity.
  - rewrite conv_bcompl. unfold bchain_map. cbn. reflexivity.
  Unshelve. apply Hγ.
Qed.

Record solution {SI} (F : oFunctor SI) := Solution {
  solution_car :> ofeT SI;
  solution_cofe : Cofe solution_car;
  solution_unfold : solution_car -n> F solution_car;
  solution_fold : F solution_car -n> solution_car;
  solution_fold_unfold X : solution_fold (solution_unfold X) ≡ X;
  solution_unfold_fold X : solution_unfold (solution_fold X) ≡ X
}.

Arguments solution_unfold {_} _.
Arguments solution_fold {_} _.
Existing Instance solution_cofe.

Module solver. Section solver.
Context (SI : indexT) (F : oFunctor SI) `{Fcontr : oFunctorContractive SI F}.
Context `{Fcofe : ∀ (T1 T2 : ofeT SI), Cofe (oFunctor_car F T1 T2)}.
Context `{Ftrunc : ∀ (T1 T2 : ofeT SI), Truncatable (oFunctor_car F T1 T2)}.
Context `{Funique : ∀ (T1 T2 : ofeT SI), BcomplUniqueLim (oFunctor_car F T1 T2)}.
Notation map := (oFunctor_map F).
Context (inh_Funit : F (unitO SI)).

(* a version of the functor which directly integrates the Cofe instance *)
Definition G (A: ofeT SI): COFE SI := cofe SI (F A).

(** We are using proof irrelevance very much.
  Currently, that doesn't matter much, however, as we need PE for a different reason anyways.
  If we ever manage to kill the extensionality requirement, then it might also make sense to remove this instance
  and see if we can prove constructively that the things which we need to be proof irrelevant are in fact irrelevant.
*)
Import ProofIrrelevance.
Local Instance all_ProofIrrel (A : Prop) : ProofIrrel A.
Proof. intros a b. apply proof_irrelevance. Qed.

Lemma map_compose {A1 A2 A3 B1 B2 B3 : ofeT SI}
  (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) :
  map (g, g') ◎ map (f, f') ≡ map (f ◎ g, g' ◎ f').
Proof. intros x. cbn. by setoid_rewrite <- oFunctor_compose. Qed.

(* specialized version so that for dist (in principle, the previous lemma can be used, but this one is cheaper for rewriting due to TC inference *)
Lemma map_compose_dist {A1 A2 A3 B1 B2 B3 : ofeT SI}
  (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) α:
  map (g, g') ◎ map (f, f') ≡{α}≡ map (f ◎ g, g' ◎ f').
Proof. apply equiv_dist, map_compose. Qed.

(* sometimes, setoid_rewrite with the above lemmas will fail for unknown reasons.
  in these cases, we use rewrite.
  disadvantage: we just rewrite at the first matching occurrence and rewrite is not able to
    unify modulo β, so we have to fully instantiate & cbn first.
*)
Ltac map_compose_tac :=
  match goal with
  |- context[ofe_mor_car _ _ (map (?g0, ?g1)) (ofe_mor_car _ _ (map (?f0, ?f1)) ?x)] =>
      let H := fresh "H" in
        specialize (map_compose f0 g0 f1 g1 x) as H; cbn in H; rewrite H; clear H
  end.

(* somewhat costly instance which is however needed for map *)
Local Existing Instance ne_proper_2.

Ltac is_prop p :=
  match type of p with
    | ?Ht => match type of Ht with
             | ?Htt => constr_eq Htt Prop
            end
  end.
Ltac pi_clear := match goal with
                 | [H : (?p), H' : (?p) |- _] => is_prop H; is_prop H';
                     let Hr := fresh "H" in
                    specialize (proof_irrel H H') as Hr; subst H; try clear H' Hr
                 | [ |- context [(proof_irrel ?p ?p)]] => rewrite (proof_irrel (proof_irrel p p) eq_refl)
                 end.

Ltac unify_pi H1 H2 := first
  [ unify H1 H2
  (* do not rewrite H1 to H2 if H1 is a subterm of H2 -- otherwise, we will fail to make H1 and H2 equal *)
   | match H2 with context[H1] => rewrite (proof_irrel H2 H1) end
   | rewrite (proof_irrel H1 H2) ].

(* sometimes, the rewrite with trunc_map_compose doesn't work without explicitly instantiating the function arguments...
  so we use this ugly hack to make it work in these cases *)
Local Notation "f 'oapp' x 'opp' y" := (ofe_mor_car _ _ (ofe_mor_car _ _ f x) y) (at level 10, only parsing).
Ltac merge_truncs :=
  repeat match goal with
    | |- context[(trunc_map ?a ?b) oapp ?f opp ((trunc_map ?c ?a) oapp ?g opp ?x)] =>
        setoid_rewrite <- (dist_mono' _ _ _ _ (trunc_map_compose g f c b a _))
  end.

(** a typeclass for registering equalities between OFEs, used for the transport infrastructure *)
(* most of the times, we give instances explicitly (as transitivity and symmetry would make life hard for TC inference), but having it as a typeclass is still sensible for a few uses *)
Class ofe_eq (X Y : ofeT SI)  := ofe_equal : X = Y.
Hint Mode ofe_eq + + : typeclass_instances.
Arguments ofe_eq : simpl never.

(* We do not register these as instances as that would make typeclass search go south.
  Instead, the ofe_eq hint database is used to automatically solve the obligations.
  It is still worthwhile to have ofe_eq as a TC (not as a definition) as simple instances need not be given explicitly this way.
*)
Create HintDb ofe_eq.
Lemma ofe_eq_symm {X Y} (H : ofe_eq X Y) : ofe_eq Y X.
Proof. intros. by rewrite H. Qed.
Lemma ofe_eq_trans {X Y Z} (H1 : ofe_eq X Y) (H2 : ofe_eq Y Z) : ofe_eq X Z.
Proof. intros. by rewrite H1 H2. Qed.
Lemma ofe_eq_funct {X Y : ofeT SI} {α α'} (Heq : α = α') (H : ofe_eq X Y) :
  ofe_eq ([G X]_{α}) ([G Y]_{α'}).
Proof. by rewrite H Heq. Qed.

Hint Resolve ofe_eq_symm ofe_eq_trans ofe_eq_funct : ofe_eq.

Program Definition transport_id (X Y : ofeT SI) {H : ofe_eq X Y} : X -n> Y := λne x, _ .
Next Obligation. intros X Y Heq x. rewrite <- Heq. exact x. Defined.
Next Obligation. intros. intros x y H1. destruct H. apply H1. Defined.
Arguments transport_id : simpl never.

(** a huge advantage of using ofe_eq with transport_id over employing full-fledged isomorphisms is that
  the category of OFEs with transport_id arrows is thin if assuming proof irrelevance. Thus checking if
  any two transports are equal reduces to type-checking.
*)
Lemma transport_id_compose (X Y Z : ofeT SI) {H1 : ofe_eq X Y} {H2 : ofe_eq Y Z} :
  transport_id Y Z  ◎ transport_id X Y ≡ @transport_id X Z (ofe_eq_trans H1 H2).
Proof.
  intros x; cbn. destruct H1. destruct H2.
  by rewrite (proof_irrel (ofe_eq_trans eq_refl eq_refl) eq_refl ).
Qed.

Lemma transport_id_identity (X : ofeT SI) {H : ofe_eq X X} : @transport_id X X H ≡ cid.
Proof. intros x; cbn. by rewrite (proof_irrel H eq_refl). Qed.

Lemma transport_id_pi (X Y : ofeT SI) {H1 : ofe_eq X Y} {H2 : ofe_eq X Y}: @transport_id X Y H1 ≡ @transport_id X Y H2.
Proof. by rewrite (proof_irrel H1 H2). Qed.

(* commutation of transports with truncation/expansion *)
Lemma transport_id_truncate (Y Z : ofeT SI) γ γ' (Heq : γ = γ') I:
  @transport_id ([G Z]_{γ}) ([G Y]_{γ'}) (ofe_eq_funct Heq I) ◎ ofe_trunc_truncate γ
  ≡ ofe_trunc_truncate γ' ◎ map (@transport_id Y Z (ofe_eq_symm I), transport_id Z Y).
Proof using Fcontr.
  destruct I. subst. rewrite !transport_id_identity.
  intros x; cbn. by setoid_rewrite oFunctor_id.
Qed.

Lemma transport_id_truncate_symm (Y Z : ofeT SI) γ γ' (Heq : γ = γ') (I : ofe_eq Y Z):
  @transport_id ([G Z]_{γ}) ([G Y]_{γ'}) (ofe_eq_funct Heq (ofe_eq_symm I)) ◎ ofe_trunc_truncate γ
  ≡ ofe_trunc_truncate γ' ◎ map (@transport_id Y Z I, @transport_id Z Y (ofe_eq_symm I)).
Proof using Fcontr.
  destruct I. subst. rewrite !transport_id_identity.
  intros x; cbn. by setoid_rewrite oFunctor_id.
Qed.

Lemma transport_id_truncate' (Y Z : ofeT SI) γ γ' (Heq : γ = γ') I0 I1 I2:
  @transport_id ([G Z]_{γ}) ([G Y]_{γ'}) I0 ◎ ofe_trunc_truncate γ
  ≡ ofe_trunc_truncate γ' ◎ map (@transport_id Y Z I1, @transport_id Z Y I2).
Proof using Fcontr.
  specialize (proof_irrel I0 (ofe_eq_funct Heq I2)) as H1.
  specialize (proof_irrel I1 (ofe_eq_symm I2)) as H2.
  subst. apply transport_id_truncate.
Qed.

Lemma transport_id_expand (Y Z : ofeT SI) γ γ' (Heq : γ' = γ) I:
  map(@transport_id Y Z (ofe_eq_symm I), transport_id Z Y) ◎ ofe_trunc_expand γ'
  ≡ ofe_trunc_expand γ ◎ @transport_id ([G Z]_{γ'}) ([G Y]_{γ}) (ofe_eq_funct Heq I).
Proof using Fcontr.
  destruct I. subst. rewrite !transport_id_identity.
  intros x; cbn. by setoid_rewrite oFunctor_id.
Qed.

Lemma transport_id_expand_symm (Y Z : ofeT SI) γ γ' (Heq : γ' = γ) (I : ofe_eq Y Z):
  map(@transport_id Y Z I, @transport_id Z Y (ofe_eq_symm I)) ◎ ofe_trunc_expand γ'
  ≡ ofe_trunc_expand γ ◎ @transport_id ([G Z]_{γ'}) ([G Y]_{γ}) (ofe_eq_funct Heq (ofe_eq_symm I)).
Proof using Fcontr.
  destruct I. subst. rewrite !transport_id_identity.
  intros x; cbn. by setoid_rewrite oFunctor_id.
Qed.

Lemma transport_id_expand' (Y Z : ofeT SI) γ γ' (Heq : γ' = γ) I0 I1 I2:
  map(@transport_id Y Z I1, @transport_id Z Y I2) ◎ ofe_trunc_expand γ'
  ≡ ofe_trunc_expand γ ◎ @transport_id ([G Z]_{γ'}) ([G Y]_{γ}) I0.
Proof using Fcontr.
  specialize (proof_irrel I0 (ofe_eq_funct Heq I2)) as H1.
  specialize (proof_irrel I1 (ofe_eq_symm I2)) as H2.
  subst. apply transport_id_expand.
Qed.

(** automation to apply transport_id_expand', transport_id_truncate' to find the right instances
  (often setoid_rewrite isn't able to find the right way to unify) *)

(* shelve a goal *)
Ltac shelve :=
  match goal with
  | |- ?H => let p := fresh "p" in evar (p : H); exact p
  end.

Ltac clear_def H :=
  generalize H; clear H; intros H.
Ltac specialize_shelve H :=
  let H' := fresh H in
  refine (let H' := H ltac:(shelve) in _);
  clear_def H'; clear H; rename H' into H.

(* right to left rewrite with transport_id_truncate' *)
Ltac transport_id_truncate_rl :=
  match goal with
  |- context[ofe_mor_car _ _ (ofe_trunc_truncate ?a) (ofe_mor_car _ _
      (map (@transport_id ?A ?C ?I0, @transport_id ?B ?D ?I1)) ?x )] =>
      unify A D; unify C B;
      let H := fresh "H" in
      specialize (transport_id_truncate' A C a _ eq_refl) as H; specialize_shelve H;
      specialize (H I0 I1); setoid_rewrite <- (H x); clear H
  end.
(* left to right rewrite with transport_id_truncate' *)
Ltac transport_id_truncate_lr :=
  unshelve
  match goal with
  |- context[ofe_mor_car _ _ (@transport_id (@ofe_trunc_car _ _ (Ftrunc ?A ?A) ?g0) (@ofe_trunc_car _ _ (Ftrunc ?C ?C) ?g1) ?I0) (ofe_mor_car _ _ (ofe_trunc_truncate _) ?x)] =>
        let H := fresh "H" in
          specialize (transport_id_truncate' C A g0 g1) as H;
          specialize_shelve H;  (* shelve equality proof *)
          specialize (H I0);
          do 2 specialize_shelve H; (* shelve the ofe instances -- sometimes ltac:(...) will cause weird evar bugs *)
          setoid_rewrite (H x); clear H
  end; [eauto with ofe_eq | eauto with ofe_eq | eauto with ofe_eq | ].

(* right to left rewrite with transport_id_expand' *)
Ltac transport_id_expand_rl :=
  unshelve
  match goal with
  |- context[ofe_mor_car _ _ (ofe_trunc_expand _) (ofe_mor_car _ _ (@transport_id (@ofe_trunc_car _ _ (Ftrunc ?A ?A) ?g0) (@ofe_trunc_car _ _ (Ftrunc ?B ?B) ?g1) ?I0) ?x)] =>
      let H := fresh "H" in
        specialize (transport_id_expand' B A g1 g0) as H;
        specialize_shelve H; (* shelve equality *)
        specialize (H I0);
        do 2 specialize_shelve H;
        setoid_rewrite <- (H x); clear H
  end; [eauto with ofe_eq | eauto with ofe_eq | eauto with ofe_eq | ].

(* left to right rewrite with transport_id_expand' *)
Ltac transport_id_expand_lr :=
  match goal with
  |- context[ofe_mor_car _ _ (map (@transport_id ?A ?C ?I0, @transport_id ?B ?D ?I1)) (ofe_mor_car _ _ (ofe_trunc_expand ?a) ?x)] =>
      unify A D; unify C B;
      let H := fresh "H" in
      specialize (transport_id_expand' A C _ a eq_refl) as H; specialize_shelve H;
      specialize (H I0 I1); setoid_rewrite <- (H x); clear H
  end.

(** automation for positions at which proof irrelevance rewrites can be used to make two terms equal *)
Ltac pi_at_compat compat :=
  match goal with
  | |- ?a ≡ ?b => compat a b
  | |- ?a ≡{_}≡ ?b => compat a b
  | |- ?a = ?b => compat a b
  end.

Ltac pi_pat_db cont H1 H2 :=
  match H1 with
  (* basic compatibility positions for morphisms *)
  (* function application *)
  | ofe_mor_car _ _ ?f ?x =>
      match H2 with
      | ofe_mor_car _ _ ?g ?y =>
          cont f g; cont x y
      end
  (* application of the functor F *)
  | map (?a, ?b) =>
      match H2 with
      | map (?c, ?d) => cont a c; cont b d
      end
  (* composition *)
  | ?a ◎ ?b => match H2 with
                 | ?c ◎ ?d => cont a c; cont b d
                end
  (* basic compatibility for transports *)
  | @transport_id ?A0 ?B0 ?I0 =>
      match H2 with
      | @transport_id ?A1 ?B1 ?I1 =>
          unify A0 A1; unify B0 B1; unify_pi I0 I1
      | @transport_id ?A1 ?B1 ?I1 =>
          cont A0 A1; cont B0 B1
      end
  (* equality of truncated types *)
  | @ofe_trunc_car _ _ (Ftrunc ?X ?X) _ =>
      match H2 with
      | @ofe_trunc_car _ _ (Ftrunc ?Y ?Y) _ => cont X Y
      end
  | ofe_mor_car _ _ ofe_trunc_truncate ?x =>
      match H2 with
      | ofe_mor_car _ _ ofe_trunc_truncate ?y => cont x y
      end
  | ofe_mor_car _ _ ofe_trunc_expand ?x =>
      match H2 with
      | ofe_mor_car _ _ ofe_trunc_expand ?y => cont x y
      end
  (* remove projections *)
  | projCOFE _ ?X =>
      match H2 with
      | projCOFE _ ?Y => cont X Y
      end
  (* rewrite with proof irrelevance at proof arguments *)
  | ?X ?Xapp =>
      match H2 with
      | ?Y ?Yapp =>
          is_prop Xapp; unify_pi Xapp Yapp; cont X Y
      end
  | _ => idtac
  end.

Ltac contpat H1 H2 := pi_pat_db contpat H1 H2.
(* for a goal which is some form of equality, try to make the heads of both sides equal using proof irrelevance *)
Ltac equalise_pi_head := repeat pi_at_compat contpat.
(* for a goal which is some form of equality, try to solve it using PI *)
Ltac equalise_pi := equalise_pi_head; reflexivity.

(* merge all successive transports into a single one *)
Ltac compose_transports :=
  repeat (cbn -[trunc_map]; match goal with
  | |- context[ofe_mor_car _ _ (@transport_id ?W ?Z ?I) (ofe_mor_car _ _ (@transport_id ?X ?Y ?I0) ?x)]
      => unify Y W; setoid_rewrite (@transport_id_compose X Y Z I0 I x)
  | |- context[@transport_id ?Y ?Z ?I ◎ @transport_id ?X ?Y ?I0] => setoid_rewrite (transport_id_compose X Y Z I0 I)
  end).
(* clear transports which have the same domain and codomain (up to registered PI instances) *)
Ltac clear_id_transports :=
  repeat (cbn -[trunc_map]; match goal with
         | |- context[ofe_mor_car _ _ (@transport_id ?X ?Y ?I) ?x] => progress contpat constr:(X) constr:(Y)
         | |- context[ofe_mor_car _ _ (@transport_id ?X ?Y ?I) ?x] => unify X Y; setoid_rewrite (@transport_id_identity X I x)
         | |- context[@transport_id ?X ?X ?I] => setoid_rewrite (@transport_id_identity X I)
        end).
Ltac clear_transports := compose_transports; clear_id_transports; cbn -[trunc_map].


(* shortcut definition for the often-used fold/unfold pattern *)
Definition unfold_transport {Y Z: ofeT SI} (Heq : ofe_eq Y Z) := transport_id Y Z.
Definition fold_transport {Y Z : ofeT SI} (Heq : ofe_eq Y Z) := @transport_id Z Y (ofe_eq_symm Heq).

(** casts between OFEs commute with bcompl *)
(*the COFEs really need to be equal so that the limits are also equal *)
Lemma transport_id_bcompl {A B : COFE SI} (Heq : A = B) (Heq' : projCOFE _ A = projCOFE _ B) α (Hα : zero ≺ α) (ch : bchain A α)
  : @transport_id A B Heq' (bcompl Hα ch) ≡{α}≡ bcompl Hα (bchain_map (@transport_id A B Heq') ch).
Proof.
  unfold ofe_eq in *. subst. setoid_rewrite (transport_id_identity _ _).
  cbn. apply bcompl_ne. intros. cbn. by clear_transports.
Qed.

(** * Preliminary definitions for the induction *)

(** A record for the inductive hypothesis.
  Parameterised by a predicate P (instead of an ordinal β and specialising to the predicate ⪯ β) as we have different instantiations (with ≺ β and True) for the two limit cases.
*)
Record is_bounded_approx {P : SI -> Prop} {X : ∀ α, P α → COFE SI}
  {e : ∀ α₁ α₂ (Hα₁ : P α₁) (Hα₂ : P α₂), α₁ ≺ α₂ → X α₁ Hα₁ -n> X α₂ Hα₂}
  {p : ∀ α₁ α₂ (Hα₁ : P α₁) (Hα₂ : P α₂), α₁ ≺ α₂ → X α₂ Hα₂ -n> X α₁ Hα₁}
  {ϕ : ∀ α (Hα : P α), X α Hα -n> [G (X α Hα)]_{succ α}}
  {ψ : ∀ α (Hα : P α), [G (X α Hα)]_{succ α} -n> X α Hα}
  := mk_is_bounded_approx
  {
    approx_p_e_id α₁ α₂ Hα₁ Hα₂ Hlt : (p α₁ α₂ Hα₁ Hα₂ Hlt) ◎ (e α₁ α₂ Hα₁ Hα₂ Hlt) ≡ cid;
    approx_e_p_id α₁ α₂ Hα₁ Hα₂ Hlt : (e α₁ α₂ Hα₁ Hα₂ Hlt) ◎ (p α₁ α₂ Hα₁ Hα₂ Hlt) ≡{α₁}≡ cid;
    approx_e_funct α₁ α₂ α₃ Hα₁ Hα₂ Hα₃ Hlt1 Hlt2 Hlt3 :
      (e α₂ α₃ Hα₂ Hα₃ Hlt2) ◎ (e α₁ α₂ Hα₁ Hα₂ Hlt1) ≡ (e α₁ α₃ Hα₁ Hα₃ Hlt3);
    approx_p_funct α₁ α₂ α₃ Hα₁ Hα₂ Hα₃ Hlt1 Hlt2 Hlt3 :
      (p α₁ α₂ Hα₁ Hα₂ Hlt1) ◎ (p α₂ α₃ Hα₂ Hα₃ Hlt2) ≡ (p α₁ α₃ Hα₁ Hα₃ Hlt3);
    approx_ψ_ϕ_id α Hα: (ψ α Hα) ◎ (ϕ α Hα) ≡ cid;
    approx_ϕ_ψ_id α Hα : (ϕ α Hα) ◎ (ψ α Hα) ≡{α}≡ cid;

    approx_eq {α} Hα Hsα: projCOFE _ (X (succ α) Hsα) = [G (X α Hα)]_{succ α};
    approx_X_truncated α Hα : OfeTruncated (X α Hα) α;


    (* only interesting for the successor case *)
    approx_Fep_p γ0 γ1 (Hγ0 : P γ0) (Hγ1 : P γ1) (Hsγ0 : P (succ γ0)) (Hsγ1 : P (succ γ1))
      (Hlt : γ0 ≺ γ1) (Hlts : succ γ0 ≺ succ γ1):
      fold_transport (approx_eq Hγ0 Hsγ0)
      ◎ (trunc_map _ _ (map (e γ0 γ1 Hγ0 Hγ1 Hlt, p γ0 γ1 Hγ0 Hγ1 Hlt)))
      ◎ unfold_transport (approx_eq Hγ1 Hsγ1)
      ≡ p (succ γ0) (succ γ1) Hsγ0 Hsγ1 Hlts;
    approx_p_ψ_unfold γ Hγ Hsγ (Hlt : γ ≺ succ γ): p γ (succ γ) Hγ Hsγ Hlt ≡ ψ γ Hγ ◎ unfold_transport (approx_eq Hγ Hsγ);
    approx_e_fold_ϕ γ Hγ Hsγ (Hlt : γ ≺ succ γ): e γ (succ γ) Hγ Hsγ Hlt ≡ fold_transport (approx_eq Hγ Hsγ) ◎ ϕ γ Hγ;
    approx_ϕ_succ_id γ Hle Hsle :
      ϕ (succ γ) Hsle
      ≡ trunc_map (succ γ) (succ (succ γ)) (map (ψ γ Hle ◎ unfold_transport (approx_eq Hle Hsle),
          fold_transport (approx_eq Hle Hsle) ◎ ϕ γ Hle))
        ◎ unfold_transport (approx_eq Hle Hsle);
    approx_ψ_succ_id γ Hle Hsle :
      ψ (succ γ) Hsle
      ≡ fold_transport (approx_eq Hle Hsle)
        ◎ trunc_map (succ (succ γ)) (succ γ) (map (fold_transport (approx_eq Hle Hsle) ◎ ϕ γ Hle, ψ γ Hle ◎ unfold_transport (approx_eq Hle Hsle) ));

    (* only interesting for the limit case *)
    approx_Fep_p_limit γ0 γ1 (Hlim: index_is_limit γ1) Hγ0 Hsγ0 Hγ1 Hlt Hslt:
      fold_transport (approx_eq Hγ0 Hsγ0)
      ◎ (trunc_map (succ γ1) (succ γ0) (map (e γ0 γ1 Hγ0 Hγ1 Hlt, p γ0 γ1 Hγ0 Hγ1 Hlt)))
      ≡ p (succ γ0) γ1 Hsγ0 Hγ1 Hslt ◎ ψ γ1 Hγ1;
  }.
Arguments is_bounded_approx {_} _ _ _ _ _.

Record bounded_approx {P : SI → Prop} := mk_bounded_approx
  {
    bounded_approx_X : ∀ α, P α → COFE SI;
    bounded_approx_e : ∀ α₁ α₂ (Hα₁ : P α₁) (Hα₂ : P α₂), α₁ ≺ α₂ → bounded_approx_X α₁ Hα₁ -n> bounded_approx_X α₂ Hα₂;
    bounded_approx_p : ∀ α₁ α₂ (Hα₁ : P α₁) (Hα₂ : P α₂), α₁ ≺ α₂ → bounded_approx_X α₂ Hα₂ -n> bounded_approx_X α₁ Hα₁;
    bounded_approx_ϕ : ∀ α (Hα : P α), bounded_approx_X α Hα -n> [G (bounded_approx_X α Hα)]_{succ α};
    bounded_approx_ψ : ∀ α (Hα : P α), [G (bounded_approx_X α Hα)]_{succ α} -n> bounded_approx_X α Hα;
    bounded_approx_props : is_bounded_approx bounded_approx_X bounded_approx_e bounded_approx_p bounded_approx_ϕ bounded_approx_ψ
  }.
Arguments bounded_approx _ : clear implicits.


(** * Definition of agreement of approximations *)

(** Consider the following for this definition of agreement:
  For the following merger (see Section below), we will need to redefine all maps, e.g. e, p.
  Just having isomorphisms between the different approximations will not suffice; for properties like functoriality,
  we also need that the isomorphisms compose, e.g.: iso_γ^{γ₀, γ₂} ≡ iso_γ^{γ₁, γ₂} ◎ iso_γ^{γ₀, γ₁}.
    (here, iso_γ^{γ₀, γ₁} denotes the iso of the γ-th components of the γ₀-th and γ₁-st approximations)
  Similarly, we need that (iso_γ^{γ₀, γ₁})^{-1} ≡ iso_γ^{γ₁, γ₀}.

  Let's call this property coherence. The trouble is that coherence talks about different isomorphisms and connects them.
  In the transfinite induction piecing the whole stuff together, we will need to come up with a proof of coherence in the limit case.
  But the isomorphisms were defined in a previous transfinite induction (for the uniqueness of the IR predicate), after truncating the approximation, etc.
  Looking into the definitions of those and proving properties about that would be EXTREMELY ugly and troublesome.

  Instead, we use transports, which are isomorphisms which are "essentially identity" (up to typecasts).
  They just encapsulte a typecast in a more usable way.

  We implement this by requiring actual Leibniz equality between the OFEs and wrapping this equality in fold_transport, unfold_transport for easier handling.
  That way, we can use the type cast like isomorphisms (without nasty eq_rect stuff), but can still prove properties using the information that the transports are just typecasts.
*)
Inductive approx_agree {P0 P1 : SI → Prop} {A0 : bounded_approx P0} {A1 : bounded_approx P1} : Type :=
  {
    agree_eq : ∀ γ (H0 : P0 γ) (H1 : P1 γ), projCOFE _ (bounded_approx_X A0 γ H0) = projCOFE _ (bounded_approx_X A1 γ H1);

    agree_bcompl_nat : ∀ γ H0 H1,
      ∀ α (Hα : zero ≺ α) (ch : bchain (bounded_approx_X A0 γ H0) α),
        bcompl Hα ch ≡{α}≡ fold_transport (agree_eq γ H0 H1) (bcompl Hα (bchain_map (unfold_transport (agree_eq γ H0 H1)) ch));

    agree_e_nat : ∀ γ0 γ1 (Hlt : γ0 ≺ γ1) (Hγ0 : P0 γ0) (Hγ0' : P1 γ0) (Hγ1 : P0 γ1) (Hγ1' : P1 γ1),
      bounded_approx_e A0 γ0 γ1 Hγ0 Hγ1 Hlt ≡
      fold_transport (agree_eq γ1 Hγ1 Hγ1')
      ◎ bounded_approx_e A1 γ0 γ1 Hγ0' Hγ1' Hlt
      ◎ unfold_transport (agree_eq γ0 Hγ0 Hγ0');

    agree_p_nat : ∀ γ0 γ1 (Hlt : γ0 ≺ γ1) (Hγ0 : P0 γ0) (Hγ0' : P1 γ0) (Hγ1 : P0 γ1) (Hγ1' : P1 γ1),
      bounded_approx_p A0 γ0 γ1 Hγ0 Hγ1 Hlt ≡
      fold_transport (agree_eq γ0 Hγ0 Hγ0')
      ◎ bounded_approx_p A1 γ0 γ1 Hγ0' Hγ1' Hlt
      ◎ unfold_transport (agree_eq γ1 Hγ1 Hγ1');

    agree_ϕ_nat : ∀ γ (Hγ : P0 γ) (Hγ' : P1 γ), bounded_approx_ϕ A0 γ Hγ ≡
      fold_transport (ofe_eq_funct eq_refl (agree_eq γ Hγ Hγ'))
      ◎ bounded_approx_ϕ A1 γ Hγ'
      ◎ unfold_transport (agree_eq γ Hγ Hγ');

    agree_ψ_nat : ∀ γ (Hγ : P0 γ) (Hγ' : P1 γ), bounded_approx_ψ A0 γ Hγ ≡
      fold_transport (agree_eq γ Hγ Hγ')
      ◎ bounded_approx_ψ A1 γ Hγ'
      ◎ unfold_transport (ofe_eq_funct eq_refl (agree_eq γ Hγ Hγ'));
  }.
Arguments approx_agree {_ _} _ _.

Lemma approx_agree_symmetric P0 P1 A0 A1 : @approx_agree P0 P1 A0 A1 → @approx_agree P1 P0 A1 A0.
Proof with (cbn; unfold fold_transport, unfold_transport; by clear_transports).
  intros H.
  assert (X_eq : ∀ γ (H1 : P1 γ) (H0 : P0 γ), projCOFE _ (bounded_approx_X A1 γ H1) = projCOFE _ (bounded_approx_X A0 γ H0)).
  { intros. symmetry. apply H. }
  exists X_eq.
  - intros. setoid_rewrite (agree_bcompl_nat H _ _ _ _ _ _).
    unfold fold_transport; clear_transports. apply bcompl_ne. intros...
  - intros. cbn. setoid_rewrite (agree_e_nat H _ _ _ _ _ _ _); intros x...
  - intros. cbn. setoid_rewrite (agree_p_nat H _ _ _ _ _ _ _); intros x...
  - intros. cbn. setoid_rewrite (agree_ϕ_nat H _ _ _); intros x...
  - intros. cbn. setoid_rewrite (agree_ψ_nat H _ _ _); intros x...
Qed.

Lemma approx_agree_reflexive P A : @approx_agree P P A A.
Proof.
  assert (X_eq : ∀ γ (H0 : P γ) (H1 : P γ), projCOFE _ (bounded_approx_X A γ H0) = projCOFE _ (bounded_approx_X A γ H1)).
  { intros. pi_clear. reflexivity. }
  exists X_eq.
  2-5: intros; unfold fold_transport, unfold_transport; intros x; cbn; repeat pi_clear; by clear_transports.
  intros. unfold fold_transport, unfold_transport. pi_clear. clear_transports.
  apply bcompl_ne. intros. cbn. by clear_transports.
Qed.

(* A0 and A1 agree on P0 ∧ P1;
   A1 and A2 agree on P1 ∧ P2;
   thus A0 and A2 can only agree on P0 ∧ P1 ∧ P2.
  This is captured by the requirement P0 → P2 → P1
*)
Lemma approx_agree_transitive (P0 P1 P2 : SI → Prop) A0 A1 A2: (∀ γ, P0 γ → P2 γ → P1 γ)
  → @approx_agree P0 P1 A0 A1 → @approx_agree P1 P2 A1 A2 → @approx_agree P0 P2 A0 A2.
Proof with (intros x; cbn; unfold fold_transport, unfold_transport; clear_transports; equalise_pi).
  intros H Hag0 Hag1.
  assert (X_eq : ∀ γ (H0 : P0 γ) (H1 : P2 γ), projCOFE _ (bounded_approx_X A0 γ H0) = projCOFE _ (bounded_approx_X A2 γ H1)).
  { intros. rewrite (agree_eq Hag0). by apply H. intros. apply Hag1. }
  exists X_eq.
  - intros. setoid_rewrite (agree_bcompl_nat Hag0  _ _ _ _ _ _). setoid_rewrite (agree_bcompl_nat Hag1 _ _ _ _ _ _).
    unfold fold_transport, unfold_transport. clear_transports. equalise_pi_head. apply ofe_mor_ne.
    apply bcompl_ne. intros. cbn. clear_transports. equalise_pi.
  - intros. setoid_rewrite (agree_e_nat Hag0 _ _ _ _ _ _ _).
    setoid_rewrite (agree_e_nat Hag1 _ _ _ _ _ _ _)...
  - intros. setoid_rewrite (agree_p_nat Hag0 _ _ _ _ _ _ _).
    setoid_rewrite (agree_p_nat Hag1 _ _ _ _ _ _ _)...
  - intros.  setoid_rewrite (agree_ϕ_nat Hag0 _ _ _). setoid_rewrite (agree_ϕ_nat Hag1 _ _ _)...
  - intros.  setoid_rewrite (agree_ψ_nat Hag0 _ _ _). setoid_rewrite (agree_ψ_nat Hag1 _ _ _)...
    Unshelve. all: eauto.
Qed.

Lemma bounded_approx_eq {P : SI → Prop} (A : bounded_approx P) α Hα Hsα :
  projCOFE _ (bounded_approx_X A (succ α) Hsα) = [G (bounded_approx_X A α Hα)]_{succ α}.
Proof. eapply approx_eq, A. Defined.

Fact agree_transport_functorial P0 P1 P2 (A0 : bounded_approx P0) (A1 : bounded_approx P1) (A2 : bounded_approx P2) (H0 : approx_agree A0 A1) (H1 : approx_agree A1 A2) (H2 : approx_agree A0 A2) γ
   (Hγ0 : P0 γ) (Hγ1 : P1 γ) (Hγ2 : P2 γ) :
  @transport_id _ _ (agree_eq H1 γ Hγ1 Hγ2) ◎ @transport_id _ _ (agree_eq H0 γ Hγ0 Hγ1) ≡ @transport_id _ _ (agree_eq H2 γ Hγ0 Hγ2).
Proof. rewrite transport_id_compose. apply transport_id_pi. Qed.

(** * One-step Extensions *)
Record extension {γ : SI} {A : bounded_approx (λ γ', γ' ≺ γ)} :=
  {
    ext_Xγ : COFE SI;
    ext_eγ : ∀ γ0 (Hγ0 : γ0 ≺ γ), bounded_approx_X A γ0 Hγ0 -n> ext_Xγ;
    ext_pγ : ∀ γ0 (Hγ0 : γ0 ≺ γ), ext_Xγ -n> bounded_approx_X A γ0 Hγ0;
    ext_ϕγ : ext_Xγ -n> [G ext_Xγ]_{succ γ};
    ext_ψγ : [G ext_Xγ]_{succ γ} -n> ext_Xγ;

    ext_pγ_eγ_id γ0 Hγ0 : ext_pγ γ0 Hγ0 ◎ ext_eγ γ0 Hγ0 ≡ cid;
    ext_eγ_pγ_id γ0 Hγ0 : ext_eγ γ0 Hγ0 ◎ ext_pγ γ0 Hγ0 ≡{γ0}≡ cid;
    ext_eγ_funct γ0 γ1 Hγ0 Hγ1 Hlt : ext_eγ γ1 Hγ1 ◎ bounded_approx_e A γ0 γ1 Hγ0 Hγ1 Hlt ≡ ext_eγ γ0 Hγ0;
    ext_pγ_funct γ0 γ1 Hγ0 Hγ1 Hlt : bounded_approx_p A γ0 γ1 Hγ0 Hγ1 Hlt ◎ ext_pγ γ1 Hγ1 ≡ ext_pγ γ0 Hγ0;

    ext_ψγ_ϕγ_id : ext_ψγ ◎ ext_ϕγ ≡ cid;
    ext_ϕγ_ψγ_id : ext_ϕγ ◎ ext_ψγ ≡{γ}≡ cid;

    ext_Xγ_truncated : OfeTruncated ext_Xγ γ;

    (* if γ is a successor ordinal....: *)
    ext_eq γ' (Hlt : γ' ≺ γ) : γ = succ γ' → projCOFE _ ext_Xγ = [G (bounded_approx_X A γ' Hlt)]_{succ γ'};
    ext_Fep_p γ0 γ1 (Hγ0 : γ0 ≺ γ) (Hγ1 : γ1 ≺ γ) (Hsγ0 : succ γ0 ≺ γ) (Hsγ1 : γ = succ γ1) (Hlt: γ0 ≺ γ1):
      fold_transport (bounded_approx_eq A γ0 Hγ0 Hsγ0)
      ◎ trunc_map (succ γ1) (succ γ0) (map (bounded_approx_e A γ0 γ1 Hγ0 Hγ1 Hlt, bounded_approx_p A γ0 γ1 Hγ0 Hγ1 Hlt))
      ◎ unfold_transport (ext_eq γ1 Hγ1 Hsγ1)
      ≡ ext_pγ (succ γ0) Hsγ0;
    ext_p_ψ_unfold γ' (Hlt : γ' ≺ γ) (Heq : γ = succ γ') :
      ext_pγ γ' Hlt ≡ bounded_approx_ψ A γ' Hlt ◎ unfold_transport (ext_eq γ' Hlt Heq);
    ext_e_fold_ϕ γ' Hlt Heq :
      ext_eγ γ' Hlt ≡ fold_transport (ext_eq γ' Hlt Heq) ◎ bounded_approx_ϕ A γ' Hlt;
    ext_ϕ_succ_id γ' (Hlt : γ' ≺ γ) (Heq : γ = succ γ') :
      ext_ϕγ
      ≡ trunc_map (succ γ') (succ γ) (map (bounded_approx_ψ A γ' Hlt ◎ unfold_transport (ext_eq γ' Hlt Heq),
                                           fold_transport (ext_eq γ' Hlt Heq) ◎ bounded_approx_ϕ A γ' Hlt))
        ◎ unfold_transport (ext_eq γ' Hlt Heq);
    ext_ψ_succ_id γ' Hlt Heq :
      ext_ψγ
      ≡ fold_transport (ext_eq γ' Hlt Heq)
        ◎ trunc_map (succ γ) (succ γ') (map (fold_transport (ext_eq γ' Hlt Heq) ◎ bounded_approx_ϕ A γ' Hlt,
                                             bounded_approx_ψ A γ' Hlt ◎ unfold_transport (ext_eq γ' Hlt Heq)));

    (* if γ is a limit ordinal *)
    ext_Fep_p_limit γ0 Hγ0 Hsγ0 : index_is_limit γ →
      fold_transport (bounded_approx_eq A γ0 Hγ0 Hsγ0)
        ◎ trunc_map (succ γ) (succ γ0) (map (ext_eγ γ0 Hγ0, ext_pγ γ0 Hγ0))
      ≡ ext_pγ (succ γ0) Hsγ0 ◎ ext_ψγ;
  }.
Arguments extension {_} _.

Record extension_agree {γ} {A0 A1 : bounded_approx (λ γ', γ' ≺ γ)} {E0 : extension A0} {E1 : extension A1} {H : approx_agree A0 A1} : Prop :=
  {
    eagree_eq : projCOFE _ (ext_Xγ E0) = projCOFE _ (ext_Xγ E1);
    eagree_bcompl_nat : ∀ α (Hα : zero ≺ α) (ch : bchain (ext_Xγ E0) α),
                         bcompl Hα ch ≡{α}≡
                         fold_transport eagree_eq (bcompl Hα (bchain_map (unfold_transport eagree_eq) ch));
    eagree_e_nat γ' Hγ' : ext_eγ E0 γ' Hγ'
      ≡ fold_transport eagree_eq ◎ ext_eγ E1 γ' Hγ' ◎ unfold_transport (agree_eq H γ' Hγ' Hγ');
    eagree_p_nat γ' Hγ' : ext_pγ E0 γ' Hγ'
      ≡ fold_transport (agree_eq H γ' Hγ' Hγ') ◎ ext_pγ E1 γ' Hγ' ◎ unfold_transport eagree_eq;
    eagree_ϕ_nat : ext_ϕγ E0 ≡ fold_transport (ofe_eq_funct (α := succ γ) (α' := succ γ) eq_refl eagree_eq)
      ◎ ext_ϕγ E1 ◎ unfold_transport eagree_eq;
    eagree_ψ_nat : ext_ψγ E0 ≡ fold_transport eagree_eq ◎ ext_ψγ E1 ◎ unfold_transport (ofe_eq_funct (α := succ γ) (α' := succ γ) eq_refl eagree_eq)
  }.
Arguments extension_agree {_ _ _} _ _ _.

Lemma extension_agree_reflexive γ A E H: @extension_agree γ A A E E H.
Proof.
  unshelve eexists.
  reflexivity.
  2-5: intros; unfold fold_transport, unfold_transport; intros x; cbn; by clear_transports.
  intros. unfold fold_transport, unfold_transport. clear_transports.
  apply bcompl_ne. intros. cbn. by clear_transports.
Qed.

Lemma extension_agree_symmetric γ A0 A1 E0 E1 H: @extension_agree γ A0 A1 E0 E1 H → @extension_agree γ A1 A0 E1 E0 (approx_agree_symmetric _ _ A0 A1 H).
Proof with (cbn; unfold fold_transport, unfold_transport; by clear_transports).
  intros H0. assert (Heq: projCOFE _ (ext_Xγ E1) = projCOFE _ (ext_Xγ E0)).
  { symmetry. apply H0. }
  exists Heq.
  - intros. setoid_rewrite (eagree_bcompl_nat H0 _ _ _).
    unfold fold_transport, unfold_transport. clear_transports.
    apply bcompl_ne. intros; cbn...
  - intros. setoid_rewrite (eagree_e_nat H0 _ _); intros x...
  - intros. setoid_rewrite (eagree_p_nat H0 _ _); intros x...
  - intros. setoid_rewrite (eagree_ϕ_nat H0); intros x...
  - intros. setoid_rewrite (eagree_ψ_nat H0); intros x...
Qed.

Lemma extension_agree_transitive γ A0 A1 A2 E0 E1 E2 H0 H1 He :
  @extension_agree γ A0 A1 E0 E1 H0
  → @extension_agree γ A1 A2 E1 E2 H1
  → @extension_agree γ A0 A2 E0 E2 (approx_agree_transitive _ _ _ A0 A1 A2 He H0 H1).
Proof with (unfold fold_transport, unfold_transport; intros x; cbn; clear_transports; equalise_pi).
  intros Hag0 Hag1. assert (X_eq : projCOFE _ (ext_Xγ E0) = projCOFE _ (ext_Xγ E2)).
  { rewrite (eagree_eq Hag0). apply (eagree_eq Hag1). }
  exists X_eq.
  - intros. setoid_rewrite (eagree_bcompl_nat Hag0 _ _ _). setoid_rewrite (eagree_bcompl_nat Hag1 _ _ _).
    unfold fold_transport, unfold_transport. clear_transports. equalise_pi_head. apply ofe_mor_ne.
    apply bcompl_ne. intros. cbn. clear_transports. equalise_pi.
  - intros. setoid_rewrite (eagree_e_nat Hag0 _ _). setoid_rewrite (eagree_e_nat Hag1 _ _)...
  - intros. setoid_rewrite (eagree_p_nat Hag0 _ _). setoid_rewrite (eagree_p_nat Hag1 _ _)...
  - intros. setoid_rewrite (eagree_ϕ_nat Hag0). setoid_rewrite (eagree_ϕ_nat Hag1)...
  - intros. setoid_rewrite (eagree_ψ_nat Hag0). setoid_rewrite (eagree_ψ_nat Hag1)...
Qed.

(** * Base case *)
Lemma zero_e_p (α₁ α₂ : SI) : α₁ ⪯ zero → α₂ ⪯ zero → α₁ ≺ α₂ → False.
Proof.
  intros Hα₁ Hα₂ Hlt.
  destruct Hα₁ as [ -> | H%index_lt_zero_is_normal]; [ | easy].
  destruct Hα₂ as [ -> | H%index_lt_zero_is_normal]; [ | easy].
  by eapply index_lt_irrefl.
Qed.

(*FIXME: the format stuff does not work *)
(*Notation "'[' f ']^{' a '}_{' b '}'" := (trunc_map a b f) (format "'[' f ']^{' a '}_{' b '}'").*)
Notation "'[' f ']^{' a '}_{' b '}'" := (trunc_map a b f).
Section base_case.
  Let X0' : COFE SI := cofe _ (unitO SI).
  Let X0 : COFE SI := cofe _ ([ G X0']_{zero}).

  Let ϕ0' : X0' -n> X0 := λne _, ⌊inh_Funit⌋_{zero}.
  Let ψ0' : X0 -n> X0' := λne _, ().

  Let ϕ0 : X0 -n> [G X0]_{succ zero} := [map (ψ0' , ϕ0')]^{zero}_{succ zero}.
  Let ψ0 : [G X0]_{succ zero} -n> X0 := [map (ϕ0', ψ0')]^{succ zero}_{zero}.


  Lemma bounded_inverse_ϕ0_ψ0 : boundedInverse ϕ0 ψ0 zero.
  Proof using Fcontr.
    unfold ϕ0, ψ0. apply trunc_map_inv. eauto with index.
    split; rewrite map_compose_dist.
    - rewrite Fcontr. 2: { instantiate (1 := (cid, cid)). intros ? ?; index_contra_solve. }
      intros x; by rewrite (oFunctor_id _ _).
    - rewrite Fcontr. 2: { instantiate (1 := (cid, cid)). intros ? ?; index_contra_solve. }
      intros x; by rewrite (oFunctor_id _ _).
  Qed.

  Program Definition approx_base : @bounded_approx (λ x, x ⪯ zero) := mk_bounded_approx _
    (λ _ _, X0)
    (λ α1 α2 Hα1 Hα2 Hlt, _)
    (λ α1 α2 Hα1 Hα2 Hlt, _)
    (λ α Hα, ϕ0)
    (λ α Hα, ψ0)
    _ .
  Next Obligation.
    intros; cbn in Hα1, Hα2. subst. exfalso; eapply zero_e_p; [ apply Hα1 | apply Hα2 | apply Hlt].
  Defined.
  Next Obligation.
    intros; cbn in Hα1, Hα2; subst. exfalso; eapply zero_e_p; [apply Hα1 | apply Hα2 | apply Hlt].
  Defined.
  Next Obligation.
    intros; cbn in Hα. destruct Hα as [-> | []%index_lt_zero_is_normal]. subst. reflexivity.
  Defined.
  Next Obligation.
    intros α [-> | []%index_lt_zero_is_normal]. reflexivity.
  Defined.
  Next Obligation.
    unshelve econstructor.
    all: try (intros; subst; index_contra_solve).
    3: { intros; destruct Hα as [-> | []%index_lt_zero_is_normal]. apply _. }
    all: intros; destruct Hα as [-> | Hα]; [ | exfalso; by apply index_lt_zero_is_normal in Hα]; cbn -[trunc_map].
    rewrite ofe_truncated_equiv.
    all: apply bounded_inverse_ϕ0_ψ0.
  Qed.
End base_case.

(* program mode does insert quite nasty matches, we'd rather not have them as we have to reason about the functions defined in program mode *)
Unset Program Cases.
(* needed for some of the program definitions where two symmetric functions are defined (e.g. e, p).
  Using transparent obligations makes some of that work without too much PI.
*)
Set Transparent Obligations.

Ltac autorew :=
  try (intros x; cbn);
  repeat (
  try rewrite oFunctor_id;
  try setoid_rewrite (ofe_trunc_truncate_expand_id _);
  try setoid_rewrite (ofe_trunc_expand_truncate_id _);
  try setoid_rewrite (transport_id_identity _ _);
  try reflexivity).

(** * Successor case *)

Section succ_case_X.
  Context (β : SI).
  Context (IH : @bounded_approx (λ γ, γ ≺ succ β)).

  Let X := bounded_approx_X IH.
  Let ϕ := bounded_approx_ϕ IH.
  Let ψ := bounded_approx_ψ IH.
  Let e := bounded_approx_e IH.
  Let p := bounded_approx_p IH.

  Instance Xsucc_eq α Hα Hsα : ofe_eq (X (succ α) Hsα) ([G (X α Hα)]_{succ α}).
  Proof. eapply approx_eq, IH. Defined. (* defined transparently so the IH lemmas depending on approx_eq can be used *)
  Arguments Xsucc_eq: simpl never.

  Let unfold α Hα Hsα := unfold_transport (Xsucc_eq α Hα Hsα).
  Let fold α Hα Hsα := fold_transport (Xsucc_eq α Hα Hsα).

  Let ϕ_ψ_id : ∀ α (Hα : α ≺ succ β), ϕ α Hα ◎ ψ α Hα ≡{α}≡ cid. eapply approx_ϕ_ψ_id, IH. Qed.
  Let ψ_ϕ_id : ∀ α (Hα : α ≺ succ β), ψ α Hα ◎ ϕ α Hα ≡ cid. eapply approx_ψ_ϕ_id, IH. Qed.
  Let p_e_id : ∀ α1 α2 (Hα1 : α1 ≺ succ β) (Hα2 : α2 ≺ succ β) (Hlt : α1 ≺ α2), p α1 α2 Hα1 Hα2 Hlt ◎ e α1 α2 Hα1 Hα2 Hlt≡ cid. eapply approx_p_e_id, IH. Qed.
  Let e_p_id : ∀ α1 α2 (Hα1 : α1 ≺ succ β) (Hα2 : α2 ≺ succ β) (Hlt : α1 ≺ α2), e α1 α2 Hα1 Hα2 Hlt ◎ p α1 α2 Hα1 Hα2 Hlt ≡{α1}≡ cid. eapply approx_e_p_id, IH. Qed.
  Let e_funct : ∀ α1 α2 α3 (Hα1 : α1 ≺ succ β) (Hα2 : α2 ≺ succ β) (Hα3 : α3 ≺ succ β) (Hlt1 : α1 ≺ α2) (Hlt2 : α2 ≺ α3) (Hlt3 : α1 ≺ α3), e α2 α3 Hα2 Hα3 Hlt2 ◎ e α1 α2 Hα1 Hα2 Hlt1 ≡ e α1 α3 Hα1 Hα3 Hlt3. eapply approx_e_funct, IH. Qed.
  Let p_funct : ∀ α1 α2 α3 (Hα1 : α1 ≺ succ β) (Hα2 : α2 ≺ succ β) (Hα3 : α3 ≺ succ β) (Hlt1 : α1 ≺ α2) (Hlt2 : α2 ≺ α3) (Hlt3 : α1 ≺ α3), p α1 α2 Hα1 Hα2 Hlt1 ◎ p α2 α3 Hα2 Hα3 Hlt2  ≡ p α1 α3 Hα1 Hα3 Hlt3. eapply approx_p_funct, IH. Qed.
  Let X_truncated : ∀ α Hα, OfeTruncated (X α Hα) α. eapply approx_X_truncated, IH. Qed.
  Existing Instance X_truncated.
  Let ϕ_succ_id : ∀ γ Hle Hsle, ϕ (succ γ) Hsle ≡ trunc_map (succ γ) (succ (succ γ)) (map (ψ γ Hle ◎ unfold γ Hle Hsle, fold γ Hle Hsle ◎ ϕ γ Hle)) ◎ unfold γ Hle Hsle. eapply (approx_ϕ_succ_id (P:= λ γ, γ ≺ succ β)). Qed.
  Let ψ_succ_id : ∀ γ Hle Hsle, ψ (succ γ) Hsle ≡ fold γ Hle Hsle ◎ trunc_map (succ (succ γ)) (succ γ) (map (fold γ Hle Hsle ◎ ϕ γ Hle, ψ γ Hle ◎ unfold γ Hle Hsle)). eapply (approx_ψ_succ_id (P:= λ γ, γ ≺ succ β)). Qed.
  Let Fep_p : ∀ γ0 γ1 Hγ0 Hγ1 Hsγ0 Hsγ1 Hlt Hlts,
    fold γ0 Hγ0 Hsγ0 ◎ trunc_map (succ γ1) (succ γ0) (map (e γ0 γ1 Hγ0 Hγ1 Hlt, p γ0 γ1 Hγ0 Hγ1 Hlt)) ◎ unfold γ1 Hγ1 Hsγ1
    ≡ p (succ γ0) (succ γ1) Hsγ0 Hsγ1 Hlts.
    eapply (approx_Fep_p (P := λ γ, γ ≺ succ β)).
  Qed.
  Let Fep_p_limit : ∀ γ0 γ1 (Hlim: index_is_limit γ1) Hγ0 Hsγ0 Hγ1 Hlt Hslt,
    fold γ0 Hγ0 Hsγ0 ◎ trunc_map (succ γ1) (succ γ0) (map (e γ0 γ1 Hγ0 Hγ1 Hlt, p γ0 γ1 Hγ0 Hγ1 Hlt))
    ≡ p (succ γ0) γ1 Hsγ0 Hγ1 Hslt ◎ ψ γ1 Hγ1.
    eapply (approx_Fep_p_limit (P := λ γ, γ ≺ succ β)).
  Qed.
  Let e_fold_ϕ : ∀ γ Hγ Hsγ Hlt, e γ (succ γ) Hγ Hsγ Hlt ≡ fold γ Hγ Hsγ ◎ ϕ γ Hγ.
    eapply (approx_e_fold_ϕ (P := λ γ, γ ≺ succ β)). Qed.
  Let p_ψ_unfold : ∀ γ Hγ Hsγ Hlt, p γ (succ γ) Hγ Hsγ Hlt ≡ ψ γ Hγ ◎ unfold γ Hγ Hsγ.
    eapply (approx_p_ψ_unfold (P := λ γ, γ ≺ succ β)). Qed.

  Fact succ_le_gt_eq γ : γ ⪯ succ β → β ≺ γ → γ = succ β.
  Proof.
    intros [-> | Hlt] H1; [reflexivity | ]. index_contra_solve.
  Qed.

  Definition β_refl : β ≺ succ β. eauto with index. Qed.
  Definition sX' : COFE SI := cofe _ ([G (X β β_refl)]_{succ β}).
  Lemma sX'_id Hβ : projCOFE _ sX' = [G (X β Hβ)]_{succ β}.
  Proof. unfold sX'. set (β_refl). pi_clear. reflexivity. Qed.

  Let unfold' Hβ : sX' -n> [G (X β Hβ)]_{succ β} := unfold_transport (sX'_id Hβ).
  Let fold' Hβ : [G (X β Hβ)]_{succ β} -n> sX' := fold_transport (sX'_id Hβ).
  Lemma unfold'_fold'_id Hβ : unfold' Hβ ◎ fold' Hβ ≡ cid.
  Proof. unfold unfold', fold', unfold_transport, fold_transport. intros x; cbn. by clear_transports. Qed.
  Lemma fold'_unfold'_id Hβ : fold' Hβ ◎ unfold' Hβ ≡ cid.
  Proof. unfold unfold', fold', unfold_transport, fold_transport. intros x; cbn. by clear_transports. Qed.

  Lemma fold'_id : fold' β_refl ≡ cid.
  Proof. unfold fold', fold_transport. apply transport_id_identity. Qed.
  Lemma unfold'_id : unfold' β_refl ≡ cid.
  Proof. unfold unfold', unfold_transport. apply transport_id_identity. Qed.

  Ltac open_folds :=
    unfold unfold, fold, unfold', fold', unfold_transport, fold_transport.

  Definition sϕ' : sX' -n> [G sX']_{succ (succ β)} :=
    trunc_map (succ β) (succ (succ β)) (map (ψ β β_refl, ϕ β β_refl)).
  Definition sψ' : [G sX']_{succ (succ β)} -n> sX' :=
    trunc_map (succ (succ β)) (succ β) (map (ϕ β β_refl, ψ β β_refl)).

  Lemma dist_later_succ (A : ofeT SI) (x y : A) γ : dist_later (succ γ) x y ↔ x ≡{γ}≡ y.
  Proof.
    split; intros H.
    - eauto with index.
    - intros γ' Hγ'. eapply dist_mono'. exact H. by apply index_succ_iff.
  Qed.

  Lemma sϕ'_sψ'_id : sϕ' ◎ sψ' ≡{succ β}≡ cid.
  Proof using ϕ_ψ_id Fcontr.
    unfold sϕ', sψ'. intros x; cbn -[trunc_map]. merge_truncs. 2: reflexivity. cbn.
    setoid_rewrite (map_compose_dist _ _ _ _ _ _). setoid_rewrite Fcontr.
    2: { apply dist_later_succ. apply pair_ne; by setoid_rewrite (ϕ_ψ_id _ _). }
    rewrite oFunctor_id. by setoid_rewrite (ofe_trunc_truncate_expand_id _).
  Qed.


  Lemma sψ'_sϕ'_id : sψ' ◎ sϕ' ≡ cid.
  Proof using ψ_ϕ_id Fcontr.
    unfold sϕ', sψ'. intros x; cbn -[trunc_map]. rewrite ofe_truncated_equiv.
    merge_truncs. 2: eauto with index.
    cbn. setoid_rewrite (map_compose_dist _ _ _ _ _ _). setoid_rewrite Fcontr.
    2: { apply dist_later_succ. apply pair_ne; by setoid_rewrite (ψ_ϕ_id _ _). }
    autorew.
  Qed.

  Lemma sϕ'_succ_id Hle : sϕ'
    ≡ trunc_map (succ β) (succ (succ β)) (map (ψ β Hle ◎ unfold' Hle, fold' Hle ◎ ϕ β Hle)) ◎ unfold' Hle.
  Proof.
    unfold sϕ'. cbn. setoid_rewrite <- (map_compose _ _ _ _).  intros x; cbn.
    rewrite ofe_truncated_equiv. apply ofe_mor_ne. rewrite (proof_irrel Hle β_refl).
    rewrite (unfold'_id _). setoid_rewrite oFunctor_ne at 2 .
    2:{ rewrite unfold'_id fold'_id. reflexivity. }
    autorew.
  Qed.

  Lemma sψ'_succ_id Hle : sψ'
    ≡ fold' Hle ◎ trunc_map (succ (succ β)) (succ β) (map (fold' Hle ◎ ϕ β Hle, ψ β Hle ◎ unfold' Hle)).
  Proof.
    unfold sψ'. cbn. setoid_rewrite <- (map_compose _ _ _ _). intros x; cbn.
    rewrite (proof_irrel Hle β_refl).
    rewrite ofe_truncated_equiv. setoid_rewrite (fold'_id _).
    do 2 apply ofe_mor_ne. setoid_rewrite oFunctor_ne.
    2: { rewrite unfold'_id fold'_id. reflexivity. }
    autorew.
  Qed.

  Lemma se'_ca γ (Hγ : γ ≺ succ β) : { γ ≺ β } + { γ = β}.
  Proof.
    destruct (index_le_lt_dec β γ) as [H1 | H1].
    - right. apply index_succ_iff in Hγ. by apply index_le_ge_eq.
    - by left.
  Qed.

  Lemma sX_pi_id γ γ' Hγ Hγ' (Heq : γ = γ') : ofe_eq (X γ Hγ) (X γ' Hγ').
  Proof. subst. pi_clear. reflexivity. Qed.

  Definition se' γ Hγ : X γ Hγ -n> sX' :=
    match se'_ca γ Hγ with
    | left Hlt => ϕ β β_refl ◎ e γ β Hγ β_refl Hlt
    | right Heq => ϕ β β_refl ◎ @transport_id _ _ (sX_pi_id γ β Hγ β_refl Heq)
    end.
  Definition sp' γ Hγ : sX' -n> X γ Hγ :=
    match se'_ca γ Hγ with
    | left Hlt => p γ β Hγ β_refl Hlt ◎ ψ β β_refl
    | right Heq => @transport_id _ _ (sX_pi_id β γ β_refl Hγ (symmetry Heq)) ◎ ψ β β_refl
    end.

  Lemma se'_sp'_id γ Hγ : se' γ Hγ ◎ sp' γ Hγ ≡{γ}≡ cid.
  Proof.
    unfold se', sp'. destruct se'_ca as [H1 | H1].
    - intros x; cbn. setoid_rewrite (e_p_id _ _ _ _ _ _). cbn. eapply dist_mono.
      by setoid_rewrite (ϕ_ψ_id _ _ _). assumption.
    - intros x; cbn. clear_transports. subst. by setoid_rewrite (ϕ_ψ_id _ _ _).
  Qed.
  Lemma sp'_se'_id γ Hγ : sp' γ Hγ ◎ se' γ Hγ ≡ cid.
  Proof.
    unfold se', sp'. destruct se'_ca as [H1 | H1].
    - intros x; cbn. setoid_rewrite (ψ_ϕ_id _ _ _). by setoid_rewrite (p_e_id _ _ _ _ _ _).
    - intros x; cbn. setoid_rewrite (ψ_ϕ_id _ _ _). by clear_transports.
  Qed.

  Lemma sp'_ψ_unfold Hβ : sp' β Hβ ≡ ψ β Hβ ◎ unfold' Hβ.
  Proof.
    unfold sp'. destruct se'_ca as [H1 | H1]. index_contra_solve.
    rewrite (proof_irrel Hβ β_refl). rewrite unfold'_id. autorew.
  Qed.

  Lemma se'_fold_ϕ Hβ : se' β Hβ ≡ fold' Hβ ◎ ϕ β Hβ.
  Proof.
    unfold se'. destruct se'_ca as [H1 | H1]. index_contra_solve.
    rewrite (proof_irrel Hβ β_refl). rewrite fold'_id. autorew.
  Qed.

  Lemma se'_funct γ0 γ1 Hγ0 Hγ1 Hlt : se' γ1 Hγ1 ◎ e γ0 γ1 Hγ0 Hγ1 Hlt ≡ se' γ0 Hγ0.
  Proof.
    unfold se'. destruct (se'_ca γ1) as [H1 | H1], (se'_ca γ0) as [H2 | H2].
    all: try by (exfalso; subst; index_contra_solve).
    - intros x; cbn. f_equiv. by setoid_rewrite (e_funct _ _ _ _ _ _ _ _ _ _).
    - intros x; cbn. f_equiv. subst. set β_refl. repeat pi_clear. by clear_transports.
  Qed.

  Lemma sp'_funct γ0 γ1 Hγ0 Hγ1 Hlt : p γ0 γ1 Hγ0 Hγ1 Hlt ◎ sp' γ1 Hγ1 ≡ sp' γ0 Hγ0.
  Proof.
    unfold sp'. destruct (se'_ca γ1) as [H1 | H1], (se'_ca γ0) as [H2 | H2].
    all: try by (exfalso; subst; index_contra_solve).
    - intros x; cbn. by setoid_rewrite (p_funct _ _ _ _ _ _ _ _ _ _).
    - intros x; cbn. subst. set β_refl. repeat pi_clear. by clear_transports.
  Qed.

  Lemma Fep_sp' γ Hγ Hβ Hsγ Hlt :
    fold_transport (Xsucc_eq γ Hγ Hsγ)
    ◎ trunc_map (succ β) (succ γ) (map (e γ β Hγ Hβ Hlt, p γ β Hγ Hβ Hlt))
    ◎ unfold' Hβ
    ≡ sp' (succ γ) Hsγ.
  Proof using Fcontr.
    unfold sp', unfold'. destruct (se'_ca) as [H1 | H1].
    - destruct (index_dec_limit β) as [[β' Hβ'] | Hlim].
      + unfold Xsucc_eq in *.
        generalize (sX'_id Hβ) as e0.
        revert Hγ Hβ Hsγ Hlt H1.
        unfold sX' in *.
        generalize (β_refl) as H0.
        subst unfold' fold' unfold fold.
        generalize (Xsucc_eq) as H1.
        subst β. intros. repeat pi_clear.
        setoid_rewrite <- (Fep_p _ _ _ _ _ _ _ _ ).
        intros x; cbn. rewrite ofe_truncated_equiv.
        do 2 apply ofe_mor_ne.
        setoid_rewrite oFunctor_ne at 1.
        2: { apply pair_ne.
          { rewrite <- (e_funct γ β' (succ β')). rewrite (e_fold_ϕ). rewrite ccompose_assoc. reflexivity.  }
          { setoid_rewrite <- (p_funct γ β' (succ β')) at 1. rewrite (p_ψ_unfold).
            Unshelve. 2-3,5-10: abstract (eauto 3 with index).
            apply equiv_dist. symmetry. apply ccompose_assoc.
          }
        }
        setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
        setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
        cbn. equalise_pi_head.
        apply ofe_mor_ne.
        setoid_rewrite (ψ_succ_id _ _ _ _). cbn.
        unfold fold_transport, unfold_transport. clear_transports.
        setoid_rewrite (dist_mono' _ _ _ _ (ofe_trunc_expand_truncate_id _)). 2: eauto with index.
        setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). equalise_pi.
      + assert (Hterm : zero ≺ β).
        { destruct (index_le_lt_dec β zero) as [H2 | H2]. 2: assumption.
          exfalso. index_contra_solve.
        }
        specialize (Fep_p_limit γ β Hlim Hγ Hsγ β_refl Hlt H1) as H3.
        cbn in H3. setoid_rewrite <- H3. intros x; cbn.
        set β_refl. repeat pi_clear.
        open_folds. clear_transports. equalise_pi.
    - unfold Xsucc_eq in *.
      match goal with
      |- context[sX_pi_id ?a ?b ?c ?d ?e] => generalize (sX_pi_id a b c d e) as e0 end.
      match goal with
      |- context[sX'_id ?a] => generalize (sX'_id a) as e1 end.
      unfold sX' in*.
      revert Hγ Hβ Hsγ Hlt.
      generalize (β_refl) as H0.
      subst unfold' fold' unfold fold.
      generalize (Xsucc_eq) as H2.
      subst β. intros. repeat pi_clear.
      rewrite (ψ_succ_id _ _ _). cbn.
      intros x; cbn.
      rewrite ofe_truncated_equiv.
      unfold fold_transport. clear_transports.
      equalise_pi_head. do 2 apply ofe_mor_ne.
      unfold unfold_transport.
      setoid_rewrite <- (transport_id_expand' _ _  _ _ _ _ _ _ _). 2: reflexivity.
      cbn. map_compose_tac.
      setoid_rewrite oFunctor_ne at 1.
      2: { apply pair_ne.
        { rewrite e_fold_ϕ. rewrite <- ccompose_assoc. unfold fold_transport. rewrite transport_id_compose. reflexivity. }
        { rewrite p_ψ_unfold. rewrite ccompose_assoc. unfold unfold_transport. rewrite transport_id_compose. reflexivity. }
      }
      equalise_pi.
  Qed.


  Ltac solve_tac := intros x; cbn; repeat f_equiv; open_folds; equalise_pi.
  Program Definition succ_extension : extension IH :=
    {|
      ext_Xγ := sX';
      ext_eγ := se';
      ext_pγ := sp';
      ext_ϕγ := sϕ';
      ext_ψγ := sψ';
    |}.
  Next Obligation. apply sp'_se'_id. Qed.
  Next Obligation. apply se'_sp'_id. Qed.
  Next Obligation. apply se'_funct. Qed.
  Next Obligation. apply sp'_funct. Qed.
  Next Obligation. apply sψ'_sϕ'_id. Qed.
  Next Obligation. apply sϕ'_sψ'_id. Qed.
  Next Obligation.
    intros γ' Hlt <-%index_succ_inj. apply sX'_id.
  Defined.
  Next Obligation.
    intros. specialize (index_succ_inj _ _ Hsγ1) as H1. subst γ1.
    setoid_rewrite <- (Fep_sp' _ _ _ _ _). solve_tac.
  Qed.
  Next Obligation.
    intros. specialize (index_succ_inj _ _ Heq) as <-. rewrite sp'_ψ_unfold. solve_tac.
  Qed.
  Next Obligation.
    intros. specialize (index_succ_inj _ _ Heq) as <-. rewrite se'_fold_ϕ. solve_tac.
  Qed.
  Next Obligation.
    intros. specialize (index_succ_inj _ _ Heq) as <-. rewrite sϕ'_succ_id. solve_tac.
  Qed.
  Next Obligation.
    intros. specialize (index_succ_inj _ _ Heq) as <-. rewrite sψ'_succ_id. solve_tac.
  Qed.
  Next Obligation.
    intros ? ? ? Hlim.
    (* well, succ β certainly isn't a limit *)
    exfalso. eapply index_lt_irrefl, (Hlim β). apply index_succ_greater.
  Qed.

End succ_case_X.

Lemma succ_extension_coherent β (A0 A1 : bounded_approx (λ γ, γ ≺ succ β)) :
  ∀ H : approx_agree A0 A1, @extension_agree (succ β) A0 A1 (succ_extension β A0) (succ_extension β A1) H.
Proof with (unfold fold_transport, unfold_transport; intros x; cbn; clear_transports; equalise_pi).
  intros H. destruct H as [F1 Flim F2 F3 F4 F5].
  assert (Heq : ext_Xγ (succ_extension β A0) = ext_Xγ (succ_extension β A1)).
  { cbn. unfold sX'. rewrite F1. by rewrite (proof_irrel (β_refl β) (index_succ_greater β)). }
  exists (proj_id Heq). all: intros; cbn.
  { unfold fold_transport. cbn in Heq. unfold sX' in Heq. setoid_rewrite (transport_id_bcompl (symmetry Heq) _ _ _ _).
    apply bcompl_ne. intros. cbn. unfold unfold_transport. by clear_transports. }
  { unfold se'. destruct (se'_ca β) as [H1 | H1].
    + rewrite F4. rewrite F2...
    + subst. rewrite F4... }
  { unfold sp'. destruct (se'_ca β) as [H1 | H1].
    + rewrite F5. rewrite F3...
    + subst. rewrite F5... }
  all: intros x; cbn; rewrite ofe_truncated_equiv.
  all: setoid_rewrite oFunctor_ne at 1; [ | rewrite F4 F5; setoid_rewrite ccompose_assoc at 1; reflexivity].
  all: setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
  all: setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
  all: cbn; unfold unfold_transport, fold_transport.
  all: setoid_rewrite <- (transport_id_truncate_symm  _ _ _ _ _ _ _).
  all: setoid_rewrite (transport_id_expand _ _ _ _ _ _ _).
  all: cbn; equalise_pi.
  Unshelve. all: eauto.
Qed.


(** * Inverse Limits *)
(* this is needed for the limit case construction *)
Section inverse_limit.
  (* for every index γ satisfying P, we have an OFE X_γ *)
  Context {P : SI → Prop}.
  Context (X : ∀ β, P β → ofeT SI).

  Definition btowerO : ofeT SI := discrete_funO (λ β: SI, discrete_funO (λ (H : P β), X β H)).

  Program Definition proj_tower (β :SI) (Hβ : P β) := λne (t : btowerO), t β Hβ.
  Next Obligation.
    intros β Hβ α' x y Heq. unfold btowerO in *. apply Heq.
  Qed.

  Context (p : ∀ γ0 γ1 (Hγ0 : P γ0) (Hγ1 : P γ1), γ0 ≺ γ1 → X γ1 Hγ1 -n> X γ0 Hγ0).

  Definition inv_lim := sigO (λ f, ∀ γ0 γ1 (Hγ0γ1 : γ0 ≺ γ1) (Hγ0 : P γ0) (Hγ1 : P γ1),
    p _ _ Hγ0 Hγ1 Hγ0γ1  (proj_tower _ Hγ1 f) ≡ proj_tower _ Hγ0 f).

  Program Definition proj_lim γ Hγ := λne (x : inv_lim), proj_tower γ Hγ (proj1_sig x) .
  Next Obligation.
    intros γ Hγ β x y Heq. destruct x as [x x'], y as [y y']. cbn.
    unfold dist, inv_lim, sigO, ofe_dist, sig_dist in Heq.
    cbn in Heq. unfold btowerO in *. apply Heq.
  Qed.

  Lemma inv_lim_eq_iff (x y : inv_lim) : x ≡ y ↔ ∀ γ Hγ, proj_lim γ Hγ x ≡ proj_lim γ Hγ y.
  Proof.
    split.
    - intros Heq γ Hγ. unfold proj_lim. cbn.
      destruct x, y. cbn. unfold equiv, inv_lim, sigO, ofe_equiv, sig_equiv in Heq.
      cbn in Heq. unfold btowerO in *. apply Heq.
    - intros H. destruct x, y. cbn in H.
      unfold equiv, inv_lim, sigO, ofe_equiv, sig_equiv. cbn. intros a Ha. by apply H.
  Qed.

  Lemma inv_lim_dist_iff (x y : inv_lim) β : x ≡{β}≡ y ↔ ∀ γ Hγ, proj_lim γ Hγ x ≡{β}≡ proj_lim γ Hγ y.
    split.
    - intros Heq γ Hγ. unfold proj_lim. cbn.
      destruct x, y. unfold proj_tower. cbn. unfold dist, inv_lim, sigO, ofe_dist, sig_dist in Heq.
      cbn in Heq. unfold btowerO in *. apply Heq.
    - intros H. destruct x, y. cbn in H.
      unfold dist, inv_lim, sigO, ofe_dist, sig_dist. cbn.
      intros a Ha. by apply H.
  Qed.

  Lemma inv_lim_equalises γ0 γ1 (Hγ0γ1 : γ0 ≺ γ1) (Hγ0 : P γ0 ) (Hγ1 : P γ1 ) x:
    p _ _ Hγ0 Hγ1 Hγ0γ1 (proj_lim _ Hγ1 x) ≡ proj_lim _ Hγ0 x.
  Proof. apply (proj2_sig x). Qed.
End inverse_limit.

Section inv_lim_extensional.
  (* This whole section is a quite a mess because of dependent typing.
    We need to unfold all the nasty equalities below to get the required commuting property
    and somehow be able to rewrite with the dependent equalities.
    At least we can use abstract for the irrelevant parts of the proofs, I guess... *)

  Import Coq.Logic.PropExtensionality.
  Import Coq.Logic.FunctionalExtensionality.
  Lemma sigO_extensional (A : ofeT SI) (P1 P2 : A → Prop) : (∀ x, P1 x ↔ P2 x) → sigO P1 = sigO P2.
  Proof.
    intros H. unfold sigO.
    assert (P1 = P2).
    { abstract (apply functional_extensionality; intros; apply propositional_extensionality, H). }
    by subst.
  Defined.

  Context
    {P : SI → Prop} (X1 X2 : ∀ β, P β → ofeT SI)
    (p1 : ∀ γ γ' Hγ Hγ' (Hlt : γ ≺ γ'), X1 γ' Hγ' -n> X1 γ Hγ)
    (p2 : ∀ γ γ' Hγ Hγ' (Hlt : γ ≺ γ'), X2 γ' Hγ' -n> X2 γ Hγ)
    (Heq : ∀ γ Hγ, X1 γ Hγ = X2 γ Hγ).
  (* Hmorph states that p1 and p2 essentially are the same, modulo the type equality Heq *)
  Context
    (Hmorph : ∀ γ0 γ1 Hγ0 Hγ1 Hγ0γ1, p1 γ0 γ1 Hγ0 Hγ1 Hγ0γ1
      ≡ @transport_id (X2 γ0 Hγ0) (X1 γ0 Hγ0) (ofe_eq_symm (Heq γ0 Hγ0))
        ◎ p2 γ0 γ1 Hγ0 Hγ1 Hγ0γ1
        ◎ @transport_id (X1 γ1 Hγ1) (X2 γ1 Hγ1) (Heq γ1 Hγ1)).

  Lemma Hfulleq : X1 = X2.
  Proof using Heq.
    eapply functional_extensionality_dep. intros. eapply functional_extensionality_dep. intros. apply Heq.
  Defined.

  Lemma inv_lim_eq : inv_lim X1 p1 = inv_lim X2 p2.
  Proof using Hmorph Heq.
    unfold inv_lim.
    specialize (Hfulleq) as ->.
    apply sigO_extensional.
    abstract (
      setoid_rewrite (transport_id_identity) in Hmorph;
      setoid_rewrite (ccompose_cid_l) in Hmorph;
      setoid_rewrite (ccompose_cid_r) in Hmorph;

      intros; split; intros; [
      by setoid_rewrite <- (Hmorph _ _ _ _ _ _) |
      by setoid_rewrite (Hmorph _ _ _ _ _ _)]).
  Defined.

  (** we show that proj_lim commutes with transports *)
  Lemma unfold_transport_proj_lim :
    ∀ γ Hγ, unfold_transport (Heq γ Hγ) ◎ proj_lim X1 p1 γ Hγ
      ≡ proj_lim X2 p2 γ Hγ ◎ unfold_transport inv_lim_eq.
  Proof.
    intros.
    unfold inv_lim_eq, Hfulleq. specialize Hfulleq as ->.
    assert (Hp1p2 : ∀ γ0 γ1 Hγ0 Hγ1 Hγ0γ1, p1 γ0 γ1 Hγ0 Hγ1 Hγ0γ1 ≡ p2 γ0 γ1 Hγ0 Hγ1 Hγ0γ1).
    { intros. setoid_rewrite Hmorph. intros z; cbn. by clear_transports. }

    unfold sigO_extensional.

    set (y := eq_ind_r _ _ _). cbn in y.
    set (e := y p1 Heq Hmorph). generalize e. clear e y.
    (* we need to prove that the two predicates we instantiate sigO with are the same *)
    assert ((λ f : btowerO X2,
           ∀ (γ0 γ1 : SI) (Hγ0γ1 : γ0 ≺ γ1) (Hγ0 : P γ0) (Hγ1 : P γ1),
             p1 γ0 γ1 Hγ0 Hγ1 Hγ0γ1 (f γ1 Hγ1) ≡ f γ0 Hγ0)
            = (λ f : btowerO X2,
           ∀ (γ0 γ1 : SI) (Hγ0γ1 : γ0 ≺ γ1) (Hγ0 : P γ0) (Hγ1 : P γ1),
             p2 γ0 γ1 Hγ0 Hγ1 Hγ0γ1 (f γ1 Hγ1) ≡ f γ0 Hγ0)).
    {
      apply functional_extensionality_dep; intros.
      apply propositional_extensionality.
      split; intros.
      - setoid_rewrite <- (Hp1p2 _ _ _ _ _ _). apply H.
      - setoid_rewrite (Hp1p2 _ _ _ _ _ _). apply H.
    }
    intros e. intros x.
    cbn. unfold unfold_transport. clear_transports. revert e x.
    unfold unfold_transport, inv_lim in *.
    rewrite H.
    intros e. rewrite (proof_irrel e eq_refl).
    intros. unfold transport_id. cbn. reflexivity.
  Qed.

  Lemma fold_transport_proj_lim :
    ∀ γ Hγ, fold_transport (Heq γ Hγ) ◎ proj_lim X2 p2 γ Hγ ≡ proj_lim X1 p1 γ Hγ ◎ fold_transport inv_lim_eq.
  Proof.
    intros.
    enough (proj_lim X1 p1 γ Hγ ≡ fold_transport (Heq γ Hγ) ◎ proj_lim X2 p2 γ Hγ ◎ unfold_transport inv_lim_eq) as ->.
    { rewrite !ccompose_assoc. unfold fold_transport, unfold_transport. setoid_rewrite transport_id_compose.
      setoid_rewrite transport_id_identity. rewrite ccompose_cid_r. reflexivity. }
    rewrite ccompose_assoc. rewrite <- unfold_transport_proj_lim.
    rewrite <- ccompose_assoc. rewrite transport_id_compose transport_id_identity. by rewrite ccompose_cid_l.
  Qed.
End inv_lim_extensional.


Section limit_case.
  (* We assume an already merged approximation.
    Later on, when we combine the cases, we use the above merged_agree lemma + transitivity of approx_agree to show that the new approximation we define in the limit case agrees with the original, unmerged approximations*)
  Context (β : limit_idx SI) (IH : @bounded_approx (λ γ, γ ≺ β)).

  Let X α (H: α ≺ β) := bounded_approx_X IH α H.
  Let e := bounded_approx_e IH.
  Let p := bounded_approx_p IH.

  (* we apply the functor F to every Xα and then truncate at α -- thus FX α is equal to X (α + 1) *)
  Definition FX : ∀ α, α ≺ β → ofeT SI := λ α Hα, [G (X α Hα)]_{succ α}.
  Instance FX_cofe α Hα : Cofe (FX α Hα) := _.

  Instance lX_truncated (α: SI) Hlt : OfeTruncated (X α Hlt) α.
  Proof. eapply approx_X_truncated, IH. Qed.
  Instance Xeq α Hlt Hslt : ofe_eq (X (succ α) Hslt) (FX α Hlt).
  Proof. eapply approx_eq, IH. Defined.

  Definition unfold α Hlt Hslt : X (succ α) Hslt -n> [G (X α Hlt)]_{succ α} := unfold_transport (Xeq α Hlt Hslt).
  Definition fold α Hlt Hslt : [G (X α Hlt)]_{succ α} -n> X (succ α) Hslt := fold_transport (Xeq α Hlt Hslt).
  Ltac clear_fold := unfold fold, unfold, unfold_transport, fold_transport.
  Lemma unfold_fold_id α Hlt Hslt : unfold α Hlt Hslt ◎ fold α Hlt Hslt ≡ cid.
  Proof. clear_fold. intros x. by clear_transports. Qed.
  Lemma fold_unfold_id α Hlt Hslt : fold α Hlt Hslt ◎ unfold α Hlt Hslt ≡ cid.
  Proof. clear_fold. intros x. by clear_transports. Qed.

  (* restating the fold/unfolds from the IH *)
  Let p_functorial α₁ α₂ α₃ Hα₁ Hα₂ Hα₃ Hlt1 Hlt2 Hlt3 : (p α₁ α₂ Hα₁ Hα₂ Hlt1) ◎ (p α₂ α₃ Hα₂ Hα₃ Hlt2) ≡ (p α₁ α₃ Hα₁ Hα₃ Hlt3).
  Proof. eapply approx_p_funct. apply IH. Qed.
  Let e_functorial α₁ α₂ α₃ Hα₁ Hα₂ Hα₃ Hlt1 Hlt2 Hlt3 : (e α₂ α₃ Hα₂ Hα₃ Hlt2) ◎ (e α₁ α₂ Hα₁ Hα₂ Hlt1) ≡ (e α₁ α₃ Hα₁ Hα₃ Hlt3).
  Proof. eapply approx_e_funct. apply IH. Qed.

  Let e_p_id α₁ α₂ Hα₁ Hα₂ Hlt : (e α₁ α₂ Hα₁ Hα₂ Hlt) ◎ (p α₁ α₂ Hα₁ Hα₂ Hlt) ≡{α₁}≡ cid.
  Proof. eapply approx_e_p_id, IH. Qed.
  Let p_e_id α₁ α₂ Hα₁ Hα₂ Hlt : (p α₁ α₂ Hα₁ Hα₂ Hlt) ◎ (e α₁ α₂ Hα₁ Hα₂ Hlt) ≡ cid.
  Proof. eapply approx_p_e_id, IH. Qed.

  Let ϕ : ∀ α (Hα : α ≺ β), X α Hα -n> FX α Hα. eapply bounded_approx_ϕ. Defined.
  Let ψ : ∀ α (Hα : α ≺ β), FX α Hα -n> X α Hα. eapply bounded_approx_ψ. Defined.

  Let ψ_ϕ_id α Hα: (ψ α Hα) ◎ (ϕ α Hα) ≡ cid. eapply approx_ψ_ϕ_id; apply IH. Qed.
  Let ϕ_ψ_id α Hα : (ϕ α Hα) ◎ (ψ α Hα) ≡{α}≡ cid. eapply approx_ϕ_ψ_id, IH. Qed.

  Let p_ψ_unfold γ Hγ Hsγ (Hlt : γ ≺ succ γ): p γ (succ γ) Hγ Hsγ Hlt ≡ ψ γ Hγ ◎ unfold γ Hγ Hsγ.
  Proof. by eapply approx_p_ψ_unfold. Qed.
  Let e_fold_ϕ γ Hγ Hsγ (Hlt : γ ≺ succ γ): e γ (succ γ) Hγ Hsγ Hlt ≡ fold γ Hγ Hsγ ◎ ϕ γ Hγ.
  Proof. by eapply approx_e_fold_ϕ. Qed.

  Let ψ_p_fold γ Hγ Hsγ (Hlt : γ ≺ succ γ): ψ γ Hγ ≡ p γ (succ γ) Hγ Hsγ Hlt ◎ fold γ Hγ Hsγ.
  Proof. intros x. setoid_rewrite (p_ψ_unfold _ _ _ _ _). cbn. by setoid_rewrite (unfold_fold_id _ _ _ _). Qed.
  Let ϕ_unfold_e γ Hγ Hsγ (Hlt : γ ≺ succ γ): ϕ γ Hγ ≡ unfold γ Hγ Hsγ ◎ e γ (succ γ) Hγ Hsγ Hlt.
  Proof. intros x. cbn. setoid_rewrite (e_fold_ϕ _ _ _ _ x). by setoid_rewrite (unfold_fold_id _ _ _ _). Qed.

  Let ψ_succ_id γ Hle Hsle : ψ (succ γ) Hsle ≡ fold γ Hle Hsle ◎ trunc_map (succ (succ γ)) (succ γ) (map (fold γ Hle Hsle ◎ ϕ γ Hle, ψ γ Hle ◎ unfold γ Hle Hsle)).
  Proof. by eapply approx_ψ_succ_id. Qed.

  Let X_pi_id γ γ' Hγ Hγ' : γ = γ' → ofe_eq (X γ Hγ) (X γ' Hγ').
  Proof. intros ->. pi_clear. reflexivity. Qed.

  (** the maps F(e_{α₁, α₂}, p_{α₁, α₂}) lifted to the truncation -- essentially, this is equal to p_{1+α₁, 1 + α₂} *)
  Program Definition Fep : ∀ α₁ α₂ Hα₁ Hα₂, α₁ ≺ α₂ → FX α₂ Hα₂ -n> FX α₁ Hα₁
    := λ α₁ α₂ Hα₁ Hα₂ Hlt, trunc_map _ _ (map (e α₁ α₂ Hα₁ Hα₂ Hlt, p α₁ α₂ Hα₁ Hα₂ Hlt)).

  (* we have the equality fold_G ◎ Fep ◎ unfold_G ≡ p (for suitable indices) *)
  Let Fep_lifts_p γ0 γ1 (Hγ0 : γ0 ≺ β) (Hγ1 : γ1 ≺ β) (Hsγ0 : (succ γ0) ≺ β) (Hsγ1 : (succ γ1) ≺ β) (Hlt : γ0 ≺ γ1) (Hlts : succ γ0 ≺ succ γ1) :
    (fold γ0 Hγ0 Hsγ0) ◎ (Fep γ0 γ1 Hγ0 Hγ1 Hlt) ◎ (unfold γ1 Hγ1 Hsγ1) ≡ p (succ γ0) (succ γ1) Hsγ0 Hsγ1 Hlts.
  Proof. eapply approx_Fep_p. Qed.

  Lemma Fep_unfold γ0 γ1 (Hγ0 : γ0 ≺ β) (Hγ1 : γ1 ≺ β) (Hsγ0 : (succ γ0) ≺ β) (Hsγ1 : (succ γ1) ≺ β) (Hlt : γ0 ≺ γ1) (Hlts : succ γ0 ≺ succ γ1) :
    (Fep γ0 γ1 Hγ0 Hγ1 Hlt) ◎ (unfold γ1 Hγ1 Hsγ1) ≡ (unfold γ0 Hγ0 Hsγ0) ◎  p (succ γ0) (succ γ1) Hsγ0 Hsγ1 Hlts.
  Proof.
    intros x. cbn. setoid_rewrite <- (Fep_lifts_p _ _ _ _ _ _ _ _ x).
    cbn -[Fep].
    Unshelve. 2-4: eauto.
    setoid_rewrite (unfold_fold_id _ _ _ _). cbn. reflexivity.
  Qed.

  Lemma fold_Fep γ0 γ1 (Hγ0 : γ0 ≺ β) (Hγ1 : γ1 ≺ β) (Hsγ0 : (succ γ0) ≺ β) (Hsγ1 : (succ γ1) ≺ β) (Hlt : γ0 ≺ γ1) (Hlts : succ γ0 ≺ succ γ1) :
    (fold γ0 Hγ0 Hsγ0) ◎ (Fep γ0 γ1 Hγ0 Hγ1 Hlt) ≡ p (succ γ0) (succ γ1) Hsγ0 Hsγ1 Hlts ◎ (fold γ1 Hγ1 Hsγ1).
  Proof.
    intros x. cbn -[Fep].
    setoid_rewrite <- (Fep_lifts_p _ _ _ _ _ _ _ _ _).
    cbn -[Fep]. by setoid_rewrite (unfold_fold_id _ _ _ _).
  Qed.

  Arguments Fep : simpl never.

  (** The inverse limit. This definition is not a COFE and does not yet satisfy the properties we need, but it is close.
    We will essentially apply the successor case construction once to fix this up (see below).
  *)
  Definition Xβ := inv_lim FX Fep.
  Definition proj_Xβ := proj_lim FX Fep.
  Lemma Xβ_equalises γ0 γ1 Hγ0 Hγ1 Hlt: Fep γ0 γ1 Hγ0 Hγ1 Hlt ◎ proj_Xβ γ1 Hγ1 ≡ proj_Xβ γ0 Hγ0.
  Proof. intros x. apply (inv_lim_equalises FX Fep). Qed.

  (** Definition of eβ *)
  Program Definition eβ : ∀ γ (Hγ : γ ≺ β), (X γ Hγ) -n> Xβ
    := λ γ Hγ, λne (x : X γ Hγ), exist _ (λ γ' Hγ',
    match index_lt_eq_lt_dec (succ γ') γ with
      | inl (inl Hlt) =>
          unfold γ' _ _ (p (succ γ') γ _ Hγ Hlt x) : [G (X γ' Hγ')]_{succ γ'}
      | inl (inr Heq) =>
          unfold _ _ _ (@transport_id (X γ Hγ) (X (succ γ') _) (X_pi_id _ _ _ _ (symmetry Heq)) x)
      | inr Hgt => unfold γ' _ _ (e γ (succ γ') Hγ _ Hgt x) : [G (X γ' Hγ')]_{succ γ'}
      end : FX γ' Hγ' ) _.
  Next Obligation. intros. by eapply limit_index_is_limit. Defined.
  Next Obligation. intros. rewrite Heq. apply Hγ. Defined.
  Next Obligation. intros. by eapply limit_index_is_limit. Defined.
  Next Obligation.
    (* equaliser property *)
    intros. intros γ0 γ1 Hγ0γ1 Hγ0 Hγ1. cbn -[Fep].
    destruct (index_lt_eq_lt_dec (succ γ1) γ) as [[Hlt1 | Heq1] | Hgt1],
        (index_lt_eq_lt_dec (succ γ0) γ) as [[Hlt0 | Heq0] | Hgt0].
    all: try by (subst; index_contra_solve).
    - setoid_rewrite (Fep_unfold _ _ _ _  _ _ _ _ _).
      cbn. by setoid_rewrite (p_functorial _ _ _ _ _ _ _ _ _ x).
      Unshelve. eauto 3 with index.
    - subst. cbn. setoid_rewrite (Fep_unfold _ _ _ _  _ _ _ _ _). cbn.
      clear_transports. reflexivity.
    - setoid_rewrite (Fep_unfold _ _ _ _  _ _ _ _ _).
      cbn. apply ofe_mor_f_equal.
      setoid_rewrite <- (p_functorial (succ γ0) γ (succ γ1) _ _ _ _ _ _ _).
      cbn. apply ofe_mor_f_equal. by setoid_rewrite (p_e_id _ _ _ _ _ _).
      Unshelve. by eapply index_lt_succ_mono.
    - destruct Heq0. cbn -[Fep].
      setoid_rewrite (Fep_unfold _ _ _ _  _ _ _ _ _). cbn. apply ofe_mor_f_equal.
      equalise_pi_head. clear_transports. by setoid_rewrite (p_e_id _ _ _ _ _ _ ).
    - setoid_rewrite (Fep_unfold _ _ _ _  _ _ _ _ _). cbn. apply ofe_mor_f_equal.
      setoid_rewrite <- (e_functorial γ (succ γ0) (succ γ1) _ _ _ _ _ _ _).
      setoid_rewrite (p_e_id _ _ _ _ _ _). cbn. reflexivity.
      Unshelve. by apply index_lt_succ_mono.
  Qed.
  Next Obligation.
    (* non-expansiveness *)
    intros γ Hγ α. cbn. intros x y Heq i Hi. cbn.
    destruct (index_lt_eq_lt_dec (succ i) γ) as [[Hlti | Heqi] | Hgti]; subst; by rewrite Heq.
  Qed.

  (** Definition of pβ *)
  Definition pβ : ∀ γ (Hγ : γ ≺ β), Xβ -n> X γ Hγ :=
    λ γ Hγ, ψ γ Hγ ◎ (proj_Xβ γ Hγ).

  (** Showing that these definitions satisfy the inverse/functoriality/etc stuff *)

  Hint Extern 2 => apply limit_index_is_limit : index.
  Lemma eβ_pβ_id γ Hγ: eβ γ Hγ ◎ pβ γ Hγ ≡{γ}≡ cid.
  Proof.
    intros x. apply inv_lim_dist_iff. intros δ Hδ.
    destruct x as [x Hx]. cbn.
    destruct (index_lt_eq_lt_dec (succ δ) γ) as [[Hlt | Heq] | Hgt].
    - setoid_rewrite (ψ_p_fold _ _ _ _ _).
      cbn. setoid_rewrite (p_functorial _ _ _ _ _ _ _ _ _ _).
      setoid_rewrite <- (Fep_unfold _ _ _ _ _ _ _ _ _).
      cbn. setoid_rewrite (unfold_fold_id _ _ _ _).
      cbn. setoid_rewrite (Hx _ _ _ _ _).
      reflexivity.
      Unshelve. all: eauto 4 with index.
    - destruct Heq. cbn. setoid_rewrite (ψ_p_fold _ _ _ _ _).
      setoid_rewrite <- (Fep_lifts_p  _ _ _ _ _ _ _ _ _).
      cbn. clear_transports. setoid_rewrite (unfold_fold_id _ _ _ _).
      cbn. setoid_rewrite (unfold_fold_id _ _ _ _).
      cbn. by setoid_rewrite (Hx _ _ _ _ _).
      Unshelve. all: eauto 4 with index.
    - setoid_rewrite (ψ_p_fold _ _ _ _ _).
      destruct (index_lt_eq_lt_dec γ δ) as [[Hγlt | Hγeq] | Hγgt].
      + setoid_rewrite <- (e_functorial γ (succ γ) (succ δ) _ _ _ _ _ _ _ ).
        cbn. setoid_rewrite (e_p_id γ (succ γ) _ _ _ _). 2: auto.
        cbn. setoid_rewrite <- (Hx _ _ _ _ _) at 1.
        setoid_rewrite (fold_Fep _ _ _ _ _ _ _ _ _). cbn.
        setoid_rewrite (dist_mono _ _ _ _ (e_p_id (succ γ) (succ δ) _ _ _ _)). 2: { apply index_succ_greater. }
        setoid_rewrite (unfold_fold_id _ _ _ _). reflexivity.
        Unshelve. all: eauto 4 with index.
      + subst.
        rewrite (proof_irrel Hgt (index_succ_greater δ)).
        rewrite (proof_irrel (eβ_obligation_3 δ Hδ) (limit_index_is_limit β δ Hγ)).
        setoid_rewrite (e_p_id _ _ _ _ _ _).
        cbn. rewrite (proof_irrel Hδ Hγ). by setoid_rewrite (unfold_fold_id _ _ _ _).
      + index_contra_solve.
  Qed.

  Lemma pβ_eβ_id γ Hγ: pβ γ Hγ ◎ eβ γ Hγ ≡ cid.
  Proof.
    intros x.
    cbn. destruct (index_lt_eq_lt_dec (succ γ) γ) as [[H1 | H1] | H1].
    1-2: index_contra_solve.
    setoid_rewrite <- (p_ψ_unfold _ _ _ _ _). apply p_e_id.
  Qed.

  Lemma eβ_functorial γ0 γ1 Hγ0 Hγ1 Hlt: eβ γ0 Hγ0 ≡ eβ γ1 Hγ1 ◎ e γ0 γ1 Hγ0 Hγ1 Hlt .
  Proof.
    intros x. apply inv_lim_eq_iff. intros γ Hγ. cbn.
    destruct (index_lt_eq_lt_dec (succ γ) γ0) as [[H1 | H1] | H1],
        (index_lt_eq_lt_dec (succ γ) γ1) as [[H2 | H2] | H2].
    all: try index_contra_solve.
    - setoid_rewrite <- (p_functorial (succ γ) γ0 γ1 _ _ _ _ _ _ _).
      cbn. setoid_rewrite (p_e_id _ _ _ _ _ _). reflexivity.
    - subst. cbn.
      rewrite (proof_irrel (eβ_obligation_1 _ _) Hγ0).
      rewrite (proof_irrel H2 Hlt).
      setoid_rewrite (p_e_id _ _ _ _ _ _).
      clear_transports. reflexivity.
    - setoid_rewrite <- (e_functorial γ0 (succ γ) γ1 _ _ _ _ _ _ _).
      cbn. setoid_rewrite (p_e_id _ _ _ _ _ _). cbn. reflexivity.
    - subst. cbn. equalise_pi_head. rewrite (proof_irrel H1 Hlt). clear_transports. reflexivity.
    - setoid_rewrite (e_functorial _ _ _ _ _ _ _ _ _ _). reflexivity.
  Qed.

  Lemma pβ_functorial γ0 γ1 Hγ0 Hγ1 Hlt: pβ γ0 Hγ0 ≡ p γ0 γ1 Hγ0 Hγ1 Hlt ◎ pβ γ1 Hγ1.
  Proof.
    intros x. cbn.
    setoid_rewrite (ψ_p_fold _ _ _ _ _). cbn. setoid_rewrite (p_functorial γ0 γ1 (succ γ1) _ _ _ _ _ _ _).
    setoid_rewrite <- (inv_lim_equalises _ _ _ _ _ _ _ x) at 1.
    setoid_rewrite (fold_Fep _ _ _ _ _ _ _ _ _). cbn. setoid_rewrite (p_functorial _ _ _ _ _ _ _ _ _ _).
    reflexivity.
    Unshelve. all: eauto 3 with index.
  Qed.

  (** We now define ϕ, ψ. These are not the final definitions yet, see below. *)

  (** definition of ψ *)
  Program Definition ψβ : [G Xβ]_{β} -n> Xβ :=
    λne x, exist _ (λ γ' Hγ',
    trunc_map _ _ (map (eβ γ' Hγ', pβ γ' Hγ')) x) _.
  Next Obligation.
    intros x γ0 γ1 Hγ0γ1 Hγ0 Hγ1.
    unfold Fep. cbn.
    eapply ofe_truncated_equiv. apply _.
    setoid_rewrite (dist_mono _ _ _ _ (ofe_trunc_expand_truncate_id _)).
    2: eauto with index.
    cbn. rewrite ofe_mor_f_equal. reflexivity.
    apply equiv_dist => α.
    map_compose_tac.
    setoid_rewrite oFunctor_ne.
    2: { apply pair_ne.
      by rewrite <- (eβ_functorial).
      symmetry; apply equiv_dist. apply pβ_functorial. (* weird stuff again, rewrite does not find matching occurrence *)
    }
    all: reflexivity.
  Qed.
  Next Obligation.
    intros α x y Heq. apply inv_lim_dist_iff. intros γ Hγ. cbn. by rewrite Heq.
  Qed.

  (** definition of ϕ*)
  Program Definition ϕβ : Xβ -n> [G Xβ]_{β} :=
    λne x, bcompl _ (mkbchain _ ([G Xβ]_{β}) β (λ γ Hγ,
      trunc_map (succ γ) β  (map (pβ γ Hγ, eβ γ Hγ)) (proj_lim _ _ γ _ x))_).
  Next Obligation.
    intros _. apply limit_index_not_zero.
  Defined.
  Next Obligation.
    intros x γ' γ Hle Hγ' Hγ. cbn.
    destruct Hle as [-> | Hlt].
    { assert (Hγ' = Hγ) as ->. 2: reflexivity. apply proof_irrel. }
    destruct x as [x Hx].
    symmetry.
    rewrite ofe_mor_ne.
    2: by setoid_rewrite <- Hx.
    Unshelve. 2: exact γ. 2, 3: eauto.
    unfold Fep. cbn.
    setoid_rewrite (dist_mono _ _ _ _ (ofe_trunc_expand_truncate_id _)).
    2: eauto with index.
    cbn.

    apply ofe_mor_ne. map_compose_tac.

    (* now we need to use composition of functors *)
    setoid_rewrite oFunctor_ne.
    2: { rewrite pair_ne.
      2: { rewrite ccompose_ne. 3: setoid_rewrite (pβ_functorial _ _ _ _ _); reflexivity.
          2: reflexivity.
          rewrite <- ccompose_assoc.
          setoid_rewrite (dist_mono' _ _ _ _ (e_p_id _ _ _ _ _) ).
          by rewrite ccompose_cid_l. by left.
      }
      2: { rewrite ccompose_ne. 2: setoid_rewrite (eβ_functorial _ _ _ _ _); reflexivity.
           2: reflexivity.
           rewrite ccompose_assoc.
           setoid_rewrite (dist_mono' _ _ _ _ _) at 1.
           reflexivity.
           rewrite ccompose_ne; [ | reflexivity | eapply e_p_id]. by rewrite ccompose_cid_r.
           by left.
      }
      reflexivity.
    }
    all: reflexivity.
  Qed.
  Next Obligation.
    intros α x y Heq.
    destruct (index_lt_eq_lt_dec α β) as [[Hα | -> ]| Hβ].
    - rewrite !conv_bcompl. cbn -[proj_lim].
      apply ofe_mor_ne.
      by rewrite Heq.
      Unshelve. auto.
    - apply cofe_unique_lim. apply limit_index_is_limit.
      intros γ Hγ. cbn -[proj_lim].
      do 3 apply ofe_mor_ne.
      eapply dist_mono' in Heq. 2: right; apply Hγ.
      apply (proj1 (inv_lim_dist_iff _ _ _ _ _) Heq).
    - eapply ofe_truncated_dist. apply _. rewrite index_min_r. 2: by right.
      apply cofe_unique_lim; [apply limit_index_is_limit |]. intros γ Hγ. cbn.
      do 3 apply ofe_mor_ne.
      apply (dist_mono _ _ _ _ (proj1 (inv_lim_dist_iff _ _ _ _ _) Heq γ Hγ)). by etransitivity.
  Qed.

  (** Verifying property (9) *)
  (* first a few lemmas that will help us with one particular step of the chain of rewrites *)
  Lemma pβ_eβ_up γ γ' Hγ Hγ' Hlt : pβ γ' Hγ' ◎ eβ γ Hγ ≡ e γ γ' Hγ Hγ' Hlt.
  Proof.
    setoid_rewrite (eβ_functorial γ γ' Hγ Hγ' Hlt).
    rewrite -ccompose_assoc. setoid_rewrite (pβ_eβ_id γ' Hγ').
    by rewrite ccompose_cid_l.
  Qed.

  Lemma pβ_eβ_down γ γ' Hγ Hγ' Hgt : pβ γ' Hγ' ◎ eβ γ Hγ ≡ p γ' γ Hγ' Hγ Hgt.
  Proof.
    rewrite pβ_functorial.
    rewrite ccompose_assoc.
    Unshelve. 4: apply Hgt. 2: apply Hγ.
    rewrite (pβ_eβ_id γ Hγ).
    by rewrite ccompose_cid_r.
  Qed.

  Lemma pβ_eβ_id' γ γ' Hγ Hγ' (x : Xβ): trunc_map _ _ (map (pβ γ' Hγ' ◎ eβ γ Hγ, pβ γ Hγ ◎ eβ γ' Hγ')) (proj_Xβ _ Hγ' x) ≡{γ'}≡ proj_Xβ _ Hγ x.
  Proof using Fcontr.
    destruct (index_lt_eq_lt_dec γ γ') as [[Hlt | Heq] | Hgt].
    - cbn. setoid_rewrite oFunctor_ne.
      2: { apply pair_ne.
        - by rewrite pβ_eβ_up.
        - by rewrite pβ_eβ_down.
      }
      specialize (inv_lim_equalises _ _ γ γ' Hlt Hγ Hγ' x) as Heq.
      unfold Fep in Heq. cbn in Heq. cbn. rewrite <- Heq. reflexivity.
    - cbn. subst. rewrite (proof_irrel Hγ Hγ'). setoid_rewrite oFunctor_ne.
      2: apply pair_ne; by rewrite pβ_eβ_id.
      rewrite oFunctor_id. cbn. by setoid_rewrite (ofe_trunc_truncate_expand_id _).
    - specialize (inv_lim_equalises _ _ γ' γ Hgt Hγ' Hγ x) as Heq.
      cbn. rewrite ofe_mor_ne.
      2: setoid_rewrite <- Heq; reflexivity.
      cbn.
      setoid_rewrite (dist_mono _ _ _ _ (ofe_trunc_expand_truncate_id _)).
      2: apply index_succ_greater. cbn.

      rewrite ofe_mor_ne.
      2: {
        setoid_rewrite oFunctor_ne.
        2: { apply pair_ne.
          - by unshelve setoid_rewrite pβ_eβ_down.
          - by unshelve setoid_rewrite pβ_eβ_up.
       }
       Fail setoid_rewrite (map_compose_dist _ _ _ _ _ _).
       map_compose_tac.
       setoid_rewrite Fcontr.
       2: intros γ'' Hγ''; apply pair_ne; (eapply dist_mono; [apply e_p_id | assumption]).
       rewrite oFunctor_id. reflexivity.
    }
    by setoid_rewrite (ofe_trunc_truncate_expand_id _).
  Qed.

  Instance lXβ_truncated : OfeTruncated Xβ β.
  Proof.
    intros x y α Hβ. split.
    - setoid_rewrite inv_lim_dist_iff. intros Heq γ Hγ.
      destruct x as [x Hx], y as [y Hy].
      cbn. specialize (Heq γ Hγ).
      cbn in Heq. rewrite ofe_truncated_dist. rewrite index_min_r.
      2: eauto with index.
      eapply dist_mono; [apply Heq | by apply limit_index_is_limit, Hγ].
    - intros Heq γ Hγ. eapply dist_mono'. apply (Heq γ). auto.
  Qed.

  Lemma ψβ_ϕβ_id : ψβ ◎ ϕβ ≡ cid.
  Proof using Fcontr.
    intros x. apply inv_lim_eq_iff. intros γ Hγ.
    unfold Fep, ϕβ.
    eapply ofe_truncated_equiv. apply _.
    cbn -[trunc_map].
    (* we move the truncated map inside the limit *)
    rewrite bounded_ne_bcompl. 2: eauto 3 with index.
    (* now we rewrite a bit inside the limit *)
    unshelve erewrite (cofe_bcompl_weakly_unique _ _ _ _ _ _ _ _ _).
    1: { (* we pick the constant chain with the γ-th component of the limit x *)
      apply bchain_const. apply (proj_lim _ _ γ Hγ x).
    }
    1: {
      intros γ' Hγ'. cbn.
      etransitivity.
      setoid_rewrite (dist_mono _ _ _ _ (ofe_trunc_expand_truncate_id _)). 2: auto.
      setoid_rewrite (map_compose _ _ _ _ _).
      apply pβ_eβ_id'. reflexivity.
    }
    2: rewrite bcompl_bchain_const. all: eauto 3 with index.
  Qed.

  (** Verifying property (10) *)
  Lemma ϕβ_ψβ_id : dist_later β (ϕβ ◎ ψβ) cid.
  Proof using Fcontr.
    intros γ Hγ x.
    setoid_rewrite (cofe_bcompl_weakly_unique _ _ _ _ _ _ _ γ Hγ).

    instantiate (1 := bchain_const _ β).
    2: {
      intros γ' Hγ'. cbn.
      setoid_rewrite (dist_mono _ _ _ _ (ofe_trunc_expand_truncate_id _)).
      2: apply index_succ_greater.
      cbn.

      rewrite ofe_mor_ne. 2: {
        setoid_rewrite (map_compose_dist _ _ _ _ _ _).
        setoid_rewrite oFunctor_ne.
        2: { apply pair_ne. all: apply eβ_pβ_id. }
        rewrite oFunctor_id.
        reflexivity.
      }
      setoid_rewrite (ofe_trunc_truncate_expand_id _) at 1. cbn.
      change x with ((λ (γ : SI) (Hγ : γ ≺ β), x) γ' Hγ') at 1.
      reflexivity.
    }
    rewrite bcompl_bchain_const; auto.
  Qed.

  Lemma Fep_p_limit γ0 Hlt Hslt: (fold γ0 Hlt Hslt) ◎ (trunc_map β (succ γ0) (map (eβ γ0 Hlt, pβ γ0 Hlt))) ≡ pβ (succ γ0) Hslt ◎ ψβ.
  Proof using ψ_succ_id Fcontr Funique.
    (* multiply with ϕ from the right *)
    enough (fold γ0 Hlt Hslt ◎ trunc_map β (succ γ0) (map (eβ γ0 Hlt, pβ γ0 Hlt)) ◎ ϕβ ≡ pβ (succ γ0) Hslt) as H.
    {
      rewrite <- H. setoid_rewrite ccompose_assoc at 2.
      rewrite ofe_truncated_equiv.
      setoid_rewrite (ϕβ_ψβ_id (succ γ0) Hslt). rewrite ccompose_cid_r. reflexivity.
    }
    setoid_rewrite ccompose_assoc.
    rewrite ofe_truncated_equiv.
    assert ((trunc_map β (succ γ0) (map (eβ γ0 Hlt, pβ γ0 Hlt)) ◎ ϕβ) ≡{succ γ0}≡ proj_Xβ γ0 Hlt) as ->.
    { setoid_rewrite <- ccompose_cid_r at 7. rewrite <- ψβ_ϕβ_id.
      intros x. reflexivity.
    }
    unfold pβ.
    rewrite ψ_succ_id.
    rewrite <- Xβ_equalises.
    unfold Fep. Unshelve. 4: apply Hslt. 2-3: eauto 4 with index.
    cbn. rewrite oFunctor_ne. 2: { rewrite e_fold_ϕ. rewrite p_ψ_unfold. reflexivity. }
    intros x; reflexivity.
  Qed.

  (** Without smoothness of equality at limit ordinals, we can only get the dist_later in the statement (10) above.
    Our fix: just apply the successor case once; as the functor is contractive, this will give us strong enough inverses. *)
  Definition Xβ' : COFE SI := cofe _ [G Xβ]_{β}.

  Definition ϕβ' : Xβ' -n> [G Xβ']_{succ β} := trunc_map β (succ β) (map (ψβ, ϕβ)).
  Definition ψβ' : [G Xβ']_{succ β} -n> Xβ' := trunc_map (succ β) β (map (ϕβ, ψβ)).

  Lemma ϕβ'_ψβ'_id: ϕβ' ◎ ψβ' ≡{β}≡ cid.
  Proof using Fcontr.
    intros x. unfold ϕβ', ψβ'. cbn.
    rewrite ofe_mor_ne. 2: { rewrite ofe_mor_ne.
      2: { setoid_rewrite (ofe_trunc_expand_truncate_id _). cbn. reflexivity. }
      setoid_rewrite (map_compose_dist _ _ _ _ _ _). setoid_rewrite Fcontr.
      2: { instantiate (1 := (cid, cid)).
        intros α Hα. split; intros y; cbn -[ϕβ ψβ]; apply ϕβ_ψβ_id; assumption.
      }
      rewrite oFunctor_id. reflexivity.
    }
    by setoid_rewrite (ofe_trunc_truncate_expand_id _).
  Qed.

  Lemma ψβ'_ϕβ'_id: ψβ' ◎ ϕβ' ≡ cid.
  Proof using Fcontr.
    intros x. unfold ψβ', ϕβ'. cbn. apply equiv_dist; intros α.
    rewrite ofe_truncated_dist ofe_mor_ne.
    2: {
      eapply dist_mono.
      setoid_rewrite (ofe_trunc_expand_truncate_id _).
      setoid_rewrite (map_compose_dist _ _ _ _ _ _). setoid_rewrite Fcontr.
      2: { instantiate (1 := (cid, cid)).
        intros α' Hα'. eapply dist_mono'. 2: right; apply Hα'.
        split; intros y; cbn -[ψβ ϕβ]; by setoid_rewrite (ψβ_ϕβ_id _).
      }
      rewrite oFunctor_id. reflexivity.
      unfold index_min.
      destruct (index_le_total α β); eauto 4 with index.
    }
    by setoid_rewrite (ofe_trunc_truncate_expand_id _).
  Qed.

  Definition eβ' : ∀ γ (Hγ : γ ≺ β), X γ Hγ -n> Xβ'
    := λ γ Hγ, ϕβ ◎ eβ γ Hγ.
  Definition pβ' : ∀ γ (Hγ : γ ≺ β), Xβ' -n> X γ Hγ
    := λ γ Hγ, pβ γ Hγ ◎ ψβ.

  Lemma eβ'_pβ'_id γ Hγ : eβ' γ Hγ ◎ pβ' γ Hγ ≡{γ}≡ cid.
  Proof using Fcontr.
    intros x. unfold eβ', pβ'. cbn -[ϕβ ψβ eβ pβ].
    setoid_rewrite (eβ_pβ_id _ _ _). setoid_rewrite (ϕβ_ψβ_id γ Hγ _). reflexivity.
  Qed.

  Lemma pβ'_eβ'_id γ Hγ : pβ' γ Hγ ◎ eβ' γ Hγ ≡ cid.
  Proof using Fcontr.
    intros x. cbn -[ϕβ ψβ eβ pβ].
    setoid_rewrite (ψβ_ϕβ_id _). setoid_rewrite (pβ_eβ_id γ Hγ _). reflexivity.
  Qed.

  Lemma eβ'_functorial γ0 γ1 Hγ0 Hγ1 Hlt: eβ' γ1 Hγ1 ◎ e γ0 γ1 Hγ0 Hγ1 Hlt ≡ eβ' γ0 Hγ0.
  Proof.
    symmetry. unfold eβ'. rewrite eβ_functorial. rewrite ccompose_assoc. reflexivity.
  Qed.

  Lemma pβ'_functorial γ0 γ1 Hγ0 Hγ1 Hlt: p γ0 γ1 Hγ0 Hγ1 Hlt ◎ pβ' γ1 Hγ1 ≡ pβ' γ0 Hγ0.
  Proof.
    symmetry. unfold pβ'. rewrite pβ_functorial. rewrite ccompose_assoc. reflexivity.
  Qed.

  Lemma Fep_p_limit0 γ0 Hlt Hslt: (fold γ0 Hlt Hslt) ◎ (trunc_map (succ β) (succ γ0) (map (eβ' γ0 Hlt, pβ' γ0 Hlt))) ≡ pβ' (succ γ0) Hslt ◎ ψβ'.
  Proof using ψ_succ_id Fcontr Funique.
    unfold eβ', pβ', ψβ'.
    rewrite <- Fep_p_limit.
    setoid_rewrite ccompose_assoc at 3.
    rewrite ofe_truncated_equiv.
    setoid_rewrite <- (dist_mono _ _ _ _ (trunc_map_compose _ _ _ _ _)).
    2: assumption.
    by rewrite map_compose.
  Qed.

  (** ** Defining the limit extension *)
  Program Definition limit_extension : extension IH :=
    {|
      ext_Xγ := Xβ';
      ext_eγ := eβ';
      ext_pγ := pβ';
      ext_ϕγ := ϕβ';
      ext_ψγ := ψβ';
    |}.
  Solve Obligations with
    (intros;
    try  match goal with
    | H : limit_index β = succ _ |- _ =>
        exfalso; eapply index_limit_not_succ; [ | apply H]; refine (limit_index_is_limit _)
    end).
  Next Obligation. apply pβ'_eβ'_id. Qed.
  Next Obligation. apply eβ'_pβ'_id. Qed.
  Next Obligation. apply eβ'_functorial. Qed.
  Next Obligation. apply pβ'_functorial. Qed.
  Next Obligation. apply ψβ'_ϕβ'_id. Qed.
  Next Obligation. apply ϕβ'_ψβ'_id. Qed.
  Next Obligation. intros. apply Fep_p_limit0. Qed.
End limit_case.

Section limit_coherent.
  Context (β : limit_idx SI) (A0 A1 : bounded_approx (λ γ, γ ≺ β)) (H : approx_agree A0 A1).

  Lemma FX_eq γ Hγ: FX β A0 γ Hγ = FX β A1 γ Hγ.
  Proof using H. unfold FX. by rewrite (agree_eq H _ _ _). Qed.

  Lemma Xβ_eq : Xβ β A0 = Xβ β A1.
  Proof using H Fcontr.
    unfold Xβ.
    unshelve eapply inv_lim_eq. apply FX_eq.
    intros. unfold Fep. cbn.
    setoid_rewrite (agree_e_nat H _ _ _ _ _ _ _).
    setoid_rewrite (agree_p_nat H _ _ _ _ _ _ _).
    intros x; cbn. rewrite ofe_truncated_equiv.
    setoid_rewrite oFunctor_ne at 1.
    2: { apply pair_ne. { setoid_rewrite ccompose_assoc. reflexivity. } reflexivity. }
    setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
    setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
    unfold unfold_transport, fold_transport.
    setoid_rewrite <- (transport_id_truncate_symm _ _ _ _ _ _ _). cbn.
    unfold FX. equalise_pi_head. do 3 apply ofe_mor_ne.
    setoid_rewrite (transport_id_expand _ _ _ _ _ _ _). cbn.
    clear_transports. equalise_pi.
    Unshelve. all: reflexivity.
  Defined.

  (* if we plug in the same OFE into the functor, we also get the same Cofe instance out *)
  Lemma FXβ_eq : cofe _ [G (Xβ β A0)]_{β} = cofe _ [G (Xβ β A1)]_{β}.
  Proof using H Fcontr. by rewrite (Xβ_eq). Qed.


  Lemma proj_Xβ_eq_fold γ' Hγ' :
    proj_lim (FX β A0) (Fep β A0) γ' Hγ' ◎ fold_transport Xβ_eq ≡
    fold_transport (FX_eq γ' Hγ') ◎ proj_lim (FX β A1) (Fep β A1) γ' Hγ'.
  Proof.
    symmetry. rewrite fold_transport_proj_lim. intros x. equalise_pi.
  Qed.

  Lemma proj_Xβ_eq_unfold γ' Hγ' :
    proj_lim (FX β A1) (Fep β A1) γ' Hγ' ◎ unfold_transport Xβ_eq ≡
    unfold_transport (FX_eq γ' Hγ') ◎ proj_lim (FX β A0) (Fep β A0) γ' Hγ'.
  Proof.
    symmetry. rewrite unfold_transport_proj_lim. intros x; equalise_pi.
  Qed.

  Lemma eβ_coherent γ Hγ : eβ β A0 γ Hγ ≡{β}≡ fold_transport (Xβ_eq) ◎ eβ β A1 γ Hγ ◎ unfold_transport (agree_eq H γ Hγ Hγ).
  Proof with (cbn; unfold unfold, unfold_transport, fold_transport; clear_transports; equalise_pi).
    intros x. rewrite inv_lim_dist_iff. intros γ' Hγ'.
    setoid_rewrite (proj_Xβ_eq_fold _ _ _). cbn.
    destruct (index_lt_eq_lt_dec (succ γ')) as [[H1 | H1] | H1].
    - setoid_rewrite (agree_p_nat H _ _ _ _ _ _ _ _)...
    - subst...
    - setoid_rewrite (agree_e_nat H _ _ _ _ _ _ _ _)...
  Qed.

  Lemma pβ_coherent γ Hγ : pβ β A0 γ Hγ ≡{β}≡ fold_transport (agree_eq H γ Hγ Hγ) ◎ pβ β A1 γ Hγ ◎ unfold_transport (Xβ_eq).
  Proof with (cbn; unfold unfold, unfold_transport, fold_transport; clear_transports; equalise_pi).
    intros x. unfold pβ. cbn. setoid_rewrite (proj_Xβ_eq_unfold _ _ _). cbn.
    setoid_rewrite (agree_ψ_nat H _ _ _ _)...
  Qed.

  (* this pattern is needed for the following two lemmas *)
  Ltac eq_pβ_eβ :=
    setoid_rewrite oFunctor_ne at 1; [ |
      rewrite eβ_coherent pβ_coherent; rewrite ccompose_assoc; reflexivity ];
    setoid_rewrite <- (map_compose_dist _ _ _ _ _ _);
    setoid_rewrite <- (map_compose_dist _ _ _ _ _ _);
    cbn; unfold unfold_transport, fold_transport;
    setoid_rewrite <- (transport_id_truncate_symm _ _ _ _ _ _ _);
    cbn; equalise_pi_head; do 3 apply ofe_mor_ne;
    setoid_rewrite (transport_id_expand _ _ _ _ _ _ _); cbn;
    apply ofe_mor_ne.

  Lemma ϕβ_coherent : ϕβ β A0 ≡{β}≡ fold_transport (ofe_eq_funct eq_refl Xβ_eq)  ◎ ϕβ β A1 ◎ unfold_transport Xβ_eq.
  Proof.
    intros x; cbn.
    setoid_rewrite (transport_id_bcompl (symmetry FXβ_eq) _ _ _ _).
    apply bcompl_ne. intros; cbn. unfold unfold_transport.
    eq_pβ_eβ.
    setoid_rewrite (proj_Xβ_eq_unfold _ _ _).
    cbn. unfold unfold_transport. equalise_pi.
    Unshelve. all: reflexivity.
  Qed.

  Lemma ψβ_coherent : ψβ β A0 ≡{β}≡ fold_transport Xβ_eq ◎ ψβ β A1 ◎ unfold_transport (ofe_eq_funct eq_refl Xβ_eq).
  Proof.
    intros x. rewrite inv_lim_dist_iff. intros γ Hγ.
    setoid_rewrite (proj_Xβ_eq_fold _ _ _). cbn.
    eq_pβ_eβ. reflexivity.
    Unshelve. reflexivity.
  Qed.

  Instance bounded_approx_A0_truncated γ Hγ : OfeTruncated (bounded_approx_X A0 γ Hγ) γ.
  Proof. eapply approx_X_truncated, A0. Qed.
  Instance bounded_approx_A1_truncated γ Hγ : OfeTruncated (bounded_approx_X A1 γ Hγ) γ.
  Proof. eapply approx_X_truncated, A1. Qed.

  Arguments eβ : simpl never.
  Arguments ϕβ : simpl never.
  Arguments pβ : simpl never.
  Arguments ψβ : simpl never.
  Lemma limit_extension_coherent :
    @extension_agree β A0 A1 (limit_extension β A0) (limit_extension β A1) H.
  Proof with (intros x; cbn; unfold fold_transport, unfold_transport; clear_transports; equalise_pi).
    exists (proj_id FXβ_eq).
    - intros. cbn in *.
      setoid_rewrite (transport_id_bcompl (symmetry FXβ_eq) _ _ _ _).
      apply bcompl_ne. intros; cbn. unfold unfold_transport. by clear_transports.
    - intros. cbn. rewrite ofe_truncated_equiv. unfold eβ'.
      setoid_rewrite eβ_coherent. setoid_rewrite ϕβ_coherent...
    - intros. cbn. rewrite ofe_truncated_equiv. unfold pβ'.
      eapply dist_mono. 2: apply Hγ'.
      setoid_rewrite pβ_coherent. setoid_rewrite ψβ_coherent...
    - intros. cbn. rewrite ofe_truncated_equiv. intros x; cbn.
      setoid_rewrite Fcontr at 1.
      2: { intros γ Hγ. eapply dist_mono'. 2: { apply index_succ_iff, Hγ. }
        setoid_rewrite ϕβ_coherent. rewrite ψβ_coherent. rewrite ccompose_assoc. reflexivity.
      }
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
      cbn. unfold unfold_transport, fold_transport.
      setoid_rewrite <- (transport_id_truncate_symm _ _ _ _ _ _ _).
      cbn. equalise_pi_head. do 3 apply ofe_mor_ne.
      setoid_rewrite (transport_id_expand _ _ _ _ _ _ _). cbn.
      apply ofe_mor_ne. equalise_pi.
      Unshelve. all: reflexivity.
    - intros. cbn. rewrite ofe_truncated_equiv. intros x; cbn.
      setoid_rewrite oFunctor_ne at 1.
      2: { setoid_rewrite ϕβ_coherent. rewrite ψβ_coherent. rewrite ccompose_assoc. reflexivity.
      }
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
      cbn. unfold unfold_transport, fold_transport.
      setoid_rewrite <- (transport_id_truncate_symm _ _ _ _ _ _ _).
      cbn. equalise_pi_head. do 3 apply ofe_mor_ne.
      setoid_rewrite (transport_id_expand _ _ _ _ _ _ _). cbn.
      apply ofe_mor_ne. equalise_pi.
      Unshelve. all: reflexivity.
  Qed.
End limit_coherent.


(** * Final limit *)

Section final_limit.
  (* Now that we've got approximations for every ordinal, we can take a final inverse limit to end up with the solution to the domain equation. *)

  Context (IH : @bounded_approx (λ _, True)).

  Let X β:= bounded_approx_X IH β I.
  Let ϕ β := bounded_approx_ϕ IH β I.
  Let ψ β := bounded_approx_ψ IH β I.

  Let ϕ_ψ_id : ∀ β, ϕ β ◎ ψ β ≡{β}≡ cid. intros β. eapply approx_ϕ_ψ_id, IH. Qed.
  Let ψ_ϕ_id : ∀ β, ψ β ◎ ϕ β ≡ cid. intros β. eapply approx_ψ_ϕ_id, IH. Qed.
  Let X_eq γ : ofe_eq (X (succ γ)) ([G (X γ)]_{succ γ}).
  Proof. apply IH. Defined.

  Let fold β := fold_transport (X_eq β).
  Let unfold β := unfold_transport (X_eq β).
  Let fold_unfold_id : ∀ β, fold β ◎ unfold β ≡ cid.
  Proof. intros β x; cbn. unfold fold, unfold, unfold_transport, fold_transport. by clear_transports. Qed.
  Let unfold_fold_id : ∀ β, unfold β ◎ fold β ≡ cid.
  Proof. intros β x; cbn. unfold fold, unfold, unfold_transport, fold_transport. by clear_transports. Qed.

  Let e γ0 γ1 (Hlt : γ0 ≺ γ1) := bounded_approx_e IH γ0 γ1 I I Hlt.
  Let p γ0 γ1 (Hlt : γ0 ≺ γ1) := bounded_approx_p IH γ0 γ1 I I Hlt.
  Let e_p_id : ∀ γ0 γ1 Hlt, e γ0 γ1 Hlt ◎ p γ0 γ1 Hlt ≡{γ0}≡ cid. intros; eapply approx_e_p_id, IH. Qed.
  Let p_e_id : ∀ γ0 γ1 Hlt, p γ0 γ1 Hlt ◎ e γ0 γ1 Hlt ≡ cid. intros; eapply approx_p_e_id, IH. Qed.
  Let e_funct : ∀ γ0 γ1 γ2 H1 H2 H3, e γ1 γ2 H2 ◎ e γ0 γ1 H1 ≡ e γ0 γ2 H3. intros; eapply approx_e_funct, IH. Qed.
  Let p_funct : ∀ γ0 γ1 γ2 H1 H2 H3, p γ0 γ1 H1 ◎ p γ1 γ2 H2 ≡ p γ0 γ2 H3. intros; eapply approx_p_funct, IH. Qed.

  Let p_ψ_unfold γ Hlt : p γ (succ γ) Hlt ≡ ψ γ ◎ unfold γ. eapply approx_p_ψ_unfold. Qed.
  Let e_fold_ϕ γ Hlt : e γ (succ γ) Hlt ≡ fold γ ◎ ϕ γ. eapply approx_e_fold_ϕ. Qed.

  Let ψ_p_fold γ (Hlt : γ ≺ succ γ): ψ γ ≡ p γ (succ γ) Hlt ◎ fold γ.
  Proof.
    intros x.
    setoid_rewrite (p_ψ_unfold _ _ _). cbn. by setoid_rewrite (unfold_fold_id _ x).
  Qed.
  Let ϕ_unfold_e γ (Hlt : γ ≺ succ γ): ϕ γ ≡ unfold γ ◎ e γ (succ γ) Hlt.
  Proof.
    intros x.
    cbn. setoid_rewrite (e_fold_ϕ _ _ x). by setoid_rewrite (unfold_fold_id _ _).
  Qed.

  (* definition of the final limit *)
  Definition FX_lim : ∀ γ, COFE SI := λ γ, cofe _ ([G (X γ)]_{succ γ}).
  Definition Fep_lim : ∀ γ0 γ1, γ0 ≺ γ1 → FX_lim γ1 -n> FX_lim γ0
    := λ γ0 γ1 Hlt, trunc_map _ _ (map (e γ0 γ1 Hlt, p γ0 γ1 Hlt)).

  Definition Xlim := inv_lim (P := λ _, True) (λ β _, FX_lim β) (λ γ0 γ1 _ _ Hlt, Fep_lim γ0 γ1 Hlt).
  Definition proj_Xlim γ : Xlim -n> FX_lim γ := proj_lim (P := λ _, True) (λ β _, FX_lim β) (λ γ0 γ1 _ _ Hlt, Fep_lim γ0 γ1 Hlt) γ I.

  Lemma Xlim_equalises γ0 γ1 Hlt: Fep_lim γ0 γ1 Hlt ◎ proj_Xlim γ1 ≡ proj_Xlim γ0.
  Proof.
    intros x. cbn -[Fep_lim].
    refine (inv_lim_equalises _ _ _ _ _ _ _ _).
  Qed.

  Lemma Xlim_dist_iff β (x y : Xlim) : x ≡{β}≡ y ↔ (∀ γ, proj_Xlim γ x ≡{β}≡ proj_Xlim γ y).
  Proof.
    rewrite (inv_lim_dist_iff _ _ x y β). cbn.
    split; intros; [ | destruct Hγ ]; auto.
  Qed.

  Lemma Xlim_equiv_iff (x y : Xlim) : x ≡ y ↔ (∀ γ, proj_Xlim γ x ≡ proj_Xlim γ y).
  Proof.
    rewrite (inv_lim_eq_iff _ _ x y). cbn.
    split; intros; [ | destruct Hγ]; auto.
  Qed.

  Let Fep_lim_lifts_p : ∀ γ0 γ1 (Hlt : γ0 ≺ γ1) (Hlts : succ γ0 ≺ succ γ1), fold γ0 ◎ Fep_lim γ0 γ1 Hlt ◎ unfold γ1 ≡ p (succ γ0) (succ γ1) Hlts.
    intros; eapply approx_Fep_p.
  Qed.

  Lemma Fep_lim_unfold γ0 γ1 (Hlt : γ0 ≺ γ1) (Hlts : succ γ0 ≺ succ γ1) :
    (Fep_lim γ0 γ1 Hlt) ◎ (unfold γ1) ≡ (unfold γ0) ◎  p (succ γ0) (succ γ1) Hlts.
  Proof using Fep_lim_lifts_p unfold_fold_id.
    intros x. cbn.
    setoid_rewrite <- (Fep_lim_lifts_p _ _ _ _ x).
    cbn -[Fep_lim].
    Unshelve. 2-4: eauto.
    setoid_rewrite (unfold_fold_id _ _).
    cbn. reflexivity.
  Qed.

  Lemma fold_Fep_lim γ0 γ1 (Hlt : γ0 ≺ γ1) (Hlts : succ γ0 ≺ succ γ1) :
    (fold γ0) ◎ (Fep_lim γ0 γ1 Hlt) ≡ p (succ γ0) (succ γ1) Hlts ◎ (fold γ1).
  Proof.
    intros x. cbn -[Fep_lim].
    setoid_rewrite <- (Fep_lim_lifts_p  _ _ _ _ _).
    cbn -[Fep_lim]. by setoid_rewrite (unfold_fold_id _ _).
  Qed.

  Program Definition e_lim : ∀ γ, X γ -n> Xlim
    := λ γ, λne (x : X γ), exist _ (λ γ' _,
    match index_lt_eq_lt_dec (succ γ') γ with
      | inl (inl Hlt) => unfold γ' (p (succ γ') γ Hlt x)
      | inl (inr Heq) => _
      | inr Hgt => unfold γ' (e γ (succ γ') Hgt x)
      end : FX_lim γ') _.
  Next Obligation.
    intros γ x γ' _ _ <-. unfold FX_lim. refine (unfold _ x).
  Defined.
  Next Obligation.
    (* equaliser property *)
    intros. intros γ0 γ1 Hγ0γ1 [] [].
    unfold proj_tower. cbn -[Fep].
    destruct (index_lt_eq_lt_dec (succ γ1) γ) as [[Hlt1 | Heq1] | Hgt1],
        (index_lt_eq_lt_dec (succ γ0) γ) as [[Hlt0 | Heq0] | Hgt0].
    all: try index_contra_solve.
    - setoid_rewrite (Fep_lim_unfold _ _ _ _ _).
      cbn. by setoid_rewrite (p_funct _ _ _ _ _ _ _).
      Unshelve. by apply index_lt_succ_mono.
    - destruct Heq1. cbn -[Fep].
      setoid_rewrite (Fep_lim_unfold _ _ _ _ _). cbn. reflexivity.
    - setoid_rewrite (Fep_lim_unfold _ _ _ _ _).
      cbn. apply ofe_mor_f_equal.
      setoid_rewrite <- (p_funct (succ γ0) γ (succ γ1) _ _ _ _).
      cbn. apply ofe_mor_f_equal. by setoid_rewrite (p_e_id _ _ _ _ ).
      Unshelve. by eapply index_lt_succ_mono.
    - destruct Heq0. cbn -[Fep].
      setoid_rewrite (Fep_lim_unfold _ _ _ _  _ ). cbn. apply ofe_mor_f_equal.
      by setoid_rewrite (p_e_id _ _ _ _ ).
    - setoid_rewrite (Fep_lim_unfold _ _ _ _ _).
      cbn. apply ofe_mor_f_equal.
      setoid_rewrite <- (e_funct γ (succ γ0) (succ γ1) _ _ _ _).
      setoid_rewrite (p_e_id _ _ _ _). cbn. reflexivity.
      Unshelve. by apply index_lt_succ_mono.
  Qed.
  Next Obligation.
    (* non-expansiveness *)
    intros γ α. cbn. intros x y Heq i Hi. cbn.
    destruct (index_lt_eq_lt_dec (succ i) γ) as [[Hlti | Heqi] | Hgti].
    - by rewrite Heq.
    - destruct Heqi. cbn. by rewrite Heq.
    - by rewrite Heq.
  Qed.

  (** Definition of p_lim *)
  Definition p_lim : ∀ γ, Xlim -n> X γ := λ γ, ψ γ ◎ (proj_Xlim γ).

  Lemma e_lim_p_lim_id γ : e_lim γ ◎ p_lim γ ≡{γ}≡ cid.
  Proof.
    intros x. apply inv_lim_dist_iff. intros δ Hδ.
    destruct x as [x Hx]. cbn.
    destruct (index_lt_eq_lt_dec (succ δ) γ) as [[Hlt | Heq] | Hgt].
    - setoid_rewrite (ψ_p_fold _ _ _).
      cbn. setoid_rewrite (p_funct _ _ _ _ _ _ _).
      setoid_rewrite <- (Fep_lim_unfold _ _ _ _ _).
      cbn -[Fep_lim]. setoid_rewrite (unfold_fold_id _ _).
      cbn -[Fep_lim]. setoid_rewrite (Hx _ _ _ _ _).
      cbn. reflexivity.
      Unshelve. all: eauto 3 with index.
    - destruct Heq. cbn. setoid_rewrite (ψ_p_fold _ _ _).
      setoid_rewrite <- (Fep_lim_lifts_p  _ _ _ _ _).
      setoid_rewrite (unfold_fold_id  _ _).
      cbn -[Fep_lim]. setoid_rewrite (unfold_fold_id _ _).
      cbn -[Fep_lim]. setoid_rewrite (Hx _ _ _ _ _). cbn. reflexivity.
      Unshelve. all: eauto with index.
    - setoid_rewrite (ψ_p_fold _ _ _).
      destruct (index_lt_eq_lt_dec γ δ) as [[Hγlt | Hγeq] | Hγgt].
      + setoid_rewrite <- (e_funct γ (succ γ) (succ δ) _ _ _ _ ).
        cbn. setoid_rewrite (e_p_id γ (succ γ) _ _). 2: auto.
        cbn. setoid_rewrite <- (Hx _ _ _ _ _) at 1.
        setoid_rewrite (fold_Fep_lim _ _ _ _ _). cbn.
        setoid_rewrite (dist_mono _ _ _ _ (e_p_id (succ γ) (succ δ) _ _)). 2: auto.
        setoid_rewrite (unfold_fold_id _ _). cbn. reflexivity.
        Unshelve. all: eauto with index.
      + subst. rewrite (proof_irrel Hgt (index_succ_greater δ)).
        setoid_rewrite (e_p_id _ _ _ _).
        cbn. destruct Hδ. by setoid_rewrite (unfold_fold_id _ _).
      + index_contra_solve.
  Qed.

  Lemma p_lim_e_lim_id γ: p_lim γ ◎ e_lim γ ≡ cid.
  Proof.
    intros x.
    cbn. destruct (index_lt_eq_lt_dec (succ γ) γ) as [[H1 | H1] | H1].
    1-2: index_contra_solve.
    setoid_rewrite <- (p_ψ_unfold _ _ _). apply p_e_id.
  Qed.

  Lemma e_lim_funct γ0 γ1 Hlt: e_lim γ0 ≡ e_lim γ1 ◎ e γ0 γ1 Hlt .
  Proof.
    intros x. apply inv_lim_eq_iff. intros γ Hγ. cbn.
    destruct (index_lt_eq_lt_dec (succ γ) γ0) as [[H1 | H1] | H1],
        (index_lt_eq_lt_dec (succ γ) γ1) as [[H2 | H2] | H2].
    all: try index_contra_solve.
    - setoid_rewrite <- (p_funct (succ γ) γ0 γ1 _ _ _ _).
      cbn. setoid_rewrite (p_e_id _ _ _ _). cbn. reflexivity.
    - subst. cbn. rewrite (proof_irrel H2 Hlt). by setoid_rewrite (p_e_id _ _ _ _).
    - setoid_rewrite <- (e_funct γ0 (succ γ) γ1 _ _ _ _).
      setoid_rewrite (p_e_id _ _ _ _). cbn. reflexivity.
    - subst. cbn. rewrite (proof_irrel H1 Hlt). reflexivity.
    - setoid_rewrite (e_funct _ _ _ _ _ _ _). reflexivity.
  Qed.

  Lemma p_lim_funct γ0 γ1 Hlt: p_lim γ0 ≡ p γ0 γ1 Hlt ◎ p_lim γ1.
  Proof.
    intros x. cbn.
    setoid_rewrite (ψ_p_fold _ _ _). cbn. setoid_rewrite (p_funct γ0 γ1 (succ γ1) _ _ _ _).
    setoid_rewrite <- (inv_lim_equalises _ _ _ _ _ _ _ x) at 1.
    setoid_rewrite (fold_Fep_lim _ _ _ _ _). cbn. setoid_rewrite (p_funct _ _ _ _ _ _ _).
    Unshelve. all: eauto 3 with index.
  Qed.

  (** definition of ψ *)
  Program Definition ψ_lim : G Xlim -n> Xlim :=
    λne x, exist _ (λ γ' _, ofe_trunc_truncate (succ γ') (map (e_lim γ', p_lim γ') x)) _.
  Next Obligation.
    intros x γ0 γ1 Hγ0γ1 [] [].
    unfold Fep_lim. cbn.
    eapply ofe_truncated_equiv. apply _.
    setoid_rewrite (dist_mono _ _ _ _ (ofe_trunc_expand_truncate_id _)); [ | eauto using index_lt_succ_mono].
    cbn. rewrite ofe_mor_f_equal. reflexivity.
    map_compose_tac.
    apply equiv_dist => α.
    setoid_rewrite oFunctor_ne.
    2: { apply pair_ne.
      by rewrite <- (e_lim_funct).
      symmetry; apply equiv_dist. apply p_lim_funct.
    }
    all:reflexivity.
  Qed.
  Next Obligation.
    intros α x y Heq. apply inv_lim_dist_iff. intros γ Hγ. cbn.
    by rewrite Heq.
  Qed.

  (** definition of ϕ*)
  Program Definition ϕ_lim : Xlim -n> G Xlim :=
    λne x, compl (mkchain _ (G Xlim) (λ γ, map (p_lim γ, e_lim γ) (ofe_trunc_expand _ (proj_lim _ _ γ I x))) _).
  Next Obligation.
    intros x γ' γ Hle. cbn.
    destruct Hle as [-> | Hlt]. { reflexivity. }
    destruct x as [x Hx]. symmetry.
    rewrite ofe_mor_ne.
    2: by setoid_rewrite <- Hx.
    Unshelve. 2: exact γ. 2, 3: eauto.
    unfold Fep. cbn.
    setoid_rewrite (dist_mono _ _ _ _ (ofe_trunc_expand_truncate_id _)).
    2: apply index_succ_greater.
    cbn.

    map_compose_tac.
    (* now we need to use composition of functors *)
    setoid_rewrite oFunctor_ne.
    2: { rewrite pair_ne.
      2: { rewrite ccompose_ne. 3: setoid_rewrite (p_lim_funct _ _ _); reflexivity.
          2: reflexivity.
          rewrite <- ccompose_assoc.
          setoid_rewrite (dist_mono' _ _ _ _ (e_p_id _ _ _) ).
          by rewrite ccompose_cid_l. by left.
      }
      2: { rewrite ccompose_ne. 2: setoid_rewrite (e_lim_funct _ _ _); reflexivity.
           2: reflexivity.
           rewrite ccompose_assoc.
           setoid_rewrite (dist_mono' _ _ _ _ _) at 1.
           reflexivity.
           rewrite ccompose_ne; [ | reflexivity | eapply e_p_id]. by rewrite ccompose_cid_r.
           by left.
      }
      reflexivity.
    }
    all: reflexivity.
  Qed.
  Next Obligation.
    intros α x y Heq.
    rewrite !conv_compl. cbn.
    do 2 apply ofe_mor_ne. apply Xlim_dist_iff, Heq.
  Qed.

  Lemma ϕ_lim_ψ_lim_id : ϕ_lim ◎ ψ_lim ≡ cid.
  Proof.
    intros x. cbn. apply equiv_dist => α. rewrite conv_compl; cbn.
    setoid_rewrite (dist_mono _ _ _ _ (ofe_trunc_expand_truncate_id _)). 2: auto.
    cbn. setoid_rewrite (map_compose_dist _ _ _ _ _ _).
    setoid_rewrite oFunctor_ne.
    2: { apply pair_ne; apply e_lim_p_lim_id. }
    rewrite oFunctor_id. reflexivity.
  Qed.

  Lemma ψ_lim_ϕ_lim_id : ψ_lim ◎ ϕ_lim ≡ cid.
  Proof.
    intros x. cbn. apply Xlim_equiv_iff.
    intros γ; cbn. rewrite ofe_truncated_equiv.
    rewrite conv_compl. cbn. rewrite ofe_mor_ne.
    2: {
      setoid_rewrite (map_compose_dist _ _ _ _ _ _). setoid_rewrite oFunctor_ne.
      2: { apply pair_ne.
        - unshelve setoid_rewrite (proj1 (equiv_dist _ _) (e_lim_funct γ (succ γ) _)). auto.
          rewrite -ccompose_assoc (p_lim_e_lim_id _) ccompose_cid_l. reflexivity.
        - unshelve setoid_rewrite (proj1 (equiv_dist _ _) (p_lim_funct γ (succ γ) _)). auto.
          rewrite ccompose_assoc (p_lim_e_lim_id _) ccompose_cid_r. reflexivity.
      }
      reflexivity.
    }
    apply equiv_dist. apply Xlim_equalises.
  Qed.

  Program Definition pre_solution_F : solution F := Solution _ F Xlim _ ϕ_lim ψ_lim _ _.
  Next Obligation.
    eapply iso_cofe_subtype with (P := λ _, True) (g := λ x, ϕ_lim x) (f := λ x _, ψ_lim x).
    3, 4: tauto.
    - intros n y1 y2. split => H.
      + apply ofe_mor_ne, H.
      + setoid_rewrite <- (ψ_lim_ϕ_lim_id y1). setoid_rewrite <- (ψ_lim_ϕ_lim_id y2).
        cbn -[ϕ_lim ψ_lim]. by rewrite H.
    - intros x _. apply ϕ_lim_ψ_lim_id.
  Qed.
  Next Obligation. apply ψ_lim_ϕ_lim_id. Qed.
  Next Obligation. apply ϕ_lim_ψ_lim_id. Qed.
End final_limit.

(** * Mergin an extension to an approximation *)
Section merge_extension.
  Context (β: SI).
  Context (A : bounded_approx (λ γ, γ ≺ β)).
  Context (E : extension A).

  Context (succ_or_limit : {β' | β = succ β'} + {index_is_limit β}).

  (** we want to define A' : bounded_approx (λ γ, γ ⪯ β) s.t. A' satisfies all sorts of agreement properties. *)

  Let X : ∀ γ, γ ≺ β → COFE SI := bounded_approx_X A.
  Let e : ∀ γ0 γ1 Hγ0 Hγ1 Hlt, X γ0 Hγ0 -n> X γ1 Hγ1 := bounded_approx_e A.
  Let p : ∀ γ0 γ1 Hγ0 Hγ1 Hlt, X γ1 Hγ1 -n> X γ0 Hγ0 := bounded_approx_p A.
  Let ϕ : ∀ γ Hγ, X γ Hγ -n> [G (X γ Hγ)]_{succ γ} := bounded_approx_ϕ A.
  Let ψ : ∀ γ Hγ, [G (X γ Hγ)]_{succ γ} -n> X γ Hγ := bounded_approx_ψ A.

  Let X_eq γ Hγ Hsγ: projCOFE _ (X (succ γ) Hsγ) = [G (X γ Hγ)]_{succ γ}. apply A. Defined.
  Instance X_truncated γ Hγ : OfeTruncated (X γ Hγ) γ. apply A. Qed.

  Let p_e_id γ0 γ1 Hγ0 Hγ1 Hlt : p γ0 γ1 Hγ0 Hγ1 Hlt ◎ e γ0 γ1 Hγ0 Hγ1 Hlt ≡ cid. apply A. Qed.
  Let e_p_id γ0 γ1 Hγ0 Hγ1 Hlt : e γ0 γ1 Hγ0 Hγ1 Hlt ◎ p γ0 γ1 Hγ0 Hγ1 Hlt ≡{γ0}≡ cid. apply A. Qed.
  Let ϕ_ψ_id γ Hγ : ϕ γ Hγ ◎ ψ γ Hγ ≡{γ}≡ cid. apply A. Qed.
  Let ψ_ϕ_id γ Hγ : ψ γ Hγ ◎ ϕ γ Hγ ≡ cid. apply A. Qed.

  Let e_funct γ0 γ1 γ2 Hγ0 Hγ1 Hγ2 Hlt0 Hlt1 Hlt2 : e γ1 γ2 Hγ1 Hγ2 Hlt1 ◎ e γ0 γ1 Hγ0 Hγ1 Hlt0 ≡ e γ0 γ2 Hγ0 Hγ2 Hlt2. apply A. Qed.
  Let p_funct γ0 γ1 γ2 Hγ0 Hγ1 Hγ2 Hlt0 Hlt1 Hlt2 : p γ0 γ1 Hγ0 Hγ1 Hlt0 ◎ p γ1 γ2 Hγ1 Hγ2 Hlt1 ≡ p γ0 γ2 Hγ0 Hγ2 Hlt2. apply A. Qed.

  Let fold γ Hγ Hsγ := fold_transport (X_eq γ Hγ Hsγ).
  Let unfold γ Hγ Hsγ := unfold_transport (X_eq γ Hγ Hsγ).

  Let Fep_p γ0 γ1 Hγ0 Hγ1 Hsγ0 Hsγ1 Hlt Hlts :
    fold γ0 Hγ0 Hsγ0 ◎ trunc_map (succ γ1) (succ γ0) (map (e γ0 γ1 Hγ0 Hγ1 Hlt, p γ0 γ1 Hγ0 Hγ1 Hlt)) ◎ unfold γ1 Hγ1 Hsγ1
    ≡ p (succ γ0) (succ γ1) Hsγ0 Hsγ1 Hlts.
    apply approx_Fep_p. Qed.
  Let Fep_p_limit γ0 γ1 (Hlim : index_is_limit γ1) Hγ0 Hsγ0 Hγ1 Hlt Hslt :
    fold γ0 Hγ0 Hsγ0 ◎ trunc_map (succ γ1) (succ γ0) (map (e γ0 γ1 Hγ0 Hγ1 Hlt, p γ0 γ1 Hγ0 Hγ1 Hlt))
    ≡ p (succ γ0) γ1 Hsγ0 Hγ1 Hslt ◎ ψ γ1 Hγ1.
    by apply approx_Fep_p_limit. Qed.

  Let p_ψ_unfold γ Hγ Hsγ Hlt : p γ (succ γ) Hγ Hsγ Hlt ≡ ψ γ Hγ ◎ unfold γ Hγ Hsγ. apply approx_p_ψ_unfold. Qed.
  Let e_fold_ϕ γ Hγ Hsγ Hlt : e γ (succ γ) Hγ Hsγ Hlt ≡ fold γ Hγ Hsγ ◎ ϕ γ Hγ. apply approx_e_fold_ϕ. Qed.

  Let ϕ_succ_id γ Hle Hsle: ϕ (succ γ) Hsle
    ≡ trunc_map (succ γ) (succ (succ γ)) (map (ψ γ Hle ◎ unfold γ Hle Hsle, fold γ Hle Hsle ◎ ϕ γ Hle))
      ◎ unfold γ Hle Hsle.
    eapply approx_ϕ_succ_id. Qed.
  Let ψ_succ_id γ Hle Hsle: ψ (succ γ) Hsle
    ≡ fold γ Hle Hsle ◎ trunc_map (succ (succ γ)) (succ γ) (map (fold γ Hle Hsle ◎ ϕ γ Hle, ψ γ Hle ◎ unfold γ Hle Hsle)).
    eapply approx_ψ_succ_id. Qed.


  Let Xβ : COFE SI := ext_Xγ E.
  Let eβ : ∀ γ0 Hγ0, X γ0 Hγ0 -n> Xβ := ext_eγ E.
  Let pβ : ∀ γ0 Hγ0, Xβ -n> X γ0 Hγ0 := ext_pγ E.
  Let ϕβ : Xβ -n> [G Xβ]_{succ β} := ext_ϕγ E.
  Let ψβ : [G Xβ]_{succ β} -n> Xβ := ext_ψγ E.

  Let pβ_eβ_id γ0 Hγ0 : pβ γ0 Hγ0 ◎ eβ γ0 Hγ0 ≡ cid. apply E. Qed.
  Let eβ_pβ_id γ0 Hγ0 : eβ γ0 Hγ0 ◎ pβ γ0 Hγ0 ≡{γ0}≡ cid. apply E. Qed.
  Let eβ_funct γ0 γ1 Hγ0 Hγ1 Hlt : eβ γ1 Hγ1 ◎ e γ0 γ1 Hγ0 Hγ1 Hlt ≡ eβ γ0 Hγ0. apply E. Qed.
  Let pβ_funct γ0 γ1 Hγ0 Hγ1 Hlt : p γ0 γ1 Hγ0 Hγ1 Hlt ◎ pβ γ1 Hγ1 ≡ pβ γ0 Hγ0. apply E. Qed.

  Let ψβ_ϕβ_id : ψβ ◎ ϕβ ≡ cid. apply E. Qed.
  Let ϕβ_ψβ_id : ϕβ ◎ ψβ ≡{β}≡ cid. apply E. Qed.

  Instance Xβ_truncated : OfeTruncated Xβ β. apply E. Qed.

  (* if β is a successor ordinal....: *)
  Let Xβ_eq γ' (Hlt : γ' ≺ β) (Heq : β = succ γ'): projCOFE _ Xβ = [G (X γ' Hlt)]_{succ γ'}. by apply E. Defined.

  Let foldβ γ' Hlt Heq := fold_transport (Xβ_eq γ' Hlt Heq).
  Let unfoldβ γ' Hlt Heq := unfold_transport (Xβ_eq γ' Hlt Heq).

  Let Fep_pβ γ0 γ1 Hγ0 Hγ1 Hsγ0 Hsγ1 Hlt:
      fold γ0 Hγ0 Hsγ0
      ◎ trunc_map (succ γ1) (succ γ0) (map (e γ0 γ1 Hγ0 Hγ1 Hlt, p γ0 γ1 Hγ0 Hγ1 Hlt))
      ◎ unfoldβ γ1 Hγ1 Hsγ1
      ≡ pβ (succ γ0) Hsγ0.
    apply ext_Fep_p. Qed.
  Let p_ψ_unfoldβ γ' Hlt Heq :
      pβ γ' Hlt ≡ ψ γ' Hlt ◎ unfoldβ γ' Hlt Heq.  apply ext_p_ψ_unfold. Qed.
  Let e_fold_ϕβ γ' Hlt Heq : eβ γ' Hlt ≡ foldβ γ' Hlt Heq ◎ ϕ γ' Hlt.  apply ext_e_fold_ϕ. Qed.
  Let ϕβ_succ_id γ' Hlt Heq: ϕβ ≡ trunc_map (succ γ') (succ β) (map (ψ γ' Hlt ◎ unfoldβ γ' Hlt Heq,
                                           foldβ γ' Hlt Heq ◎ ϕ γ' Hlt)) ◎ unfoldβ γ' Hlt Heq.
    apply ext_ϕ_succ_id. Qed.
  Let ψβ_succ_id γ' Hlt Heq : ψβ
      ≡ foldβ γ' Hlt Heq
        ◎ trunc_map (succ β) (succ γ') (map (foldβ γ' Hlt Heq ◎ ϕ γ' Hlt,
                                             ψ γ' Hlt ◎ unfoldβ γ' Hlt Heq)).
    apply ext_ψ_succ_id. Qed.

  (* if β is a limit ordinal *)
  Let Fep_pβ_limit γ0 Hγ0 Hsγ0 (Hlim : index_is_limit β) :
      fold γ0 Hγ0 Hsγ0
        ◎ trunc_map (succ β) (succ γ0) (map (eβ γ0 Hγ0, pβ γ0 Hγ0))
      ≡ pβ (succ γ0) Hsγ0 ◎ ψβ.
    by apply ext_Fep_p_limit. Qed.

  (** now we can define the new stuff *)
  Lemma le_lt_eq_dec γ (Hγ : γ ⪯ β) : {γ ≺ β} + {γ= β}.
  Proof.
    destruct (index_le_lt_dec β γ) as [H1 | H1].
    - right. by apply index_le_ge_eq.
    - by left.
  Qed.

  Definition X' γ (Hγ : γ ⪯ β) : COFE SI := match le_lt_eq_dec γ Hγ with
                                            | left Hlt => X γ Hlt
                                            | right Heq => Xβ
                                            end.

  Lemma X'_id_lt γ Hγ (Hlt : γ ≺ β): ofe_eq (X' γ Hγ) (X γ Hlt).
  Proof.
    unfold X'. destruct le_lt_eq_dec as [H1 | H1]. by pi_clear. index_contra_solve.
  Qed.
  Hint Resolve X'_id_lt : ofe_eq.

  Lemma X'_id_β Hβ : ofe_eq (X' β Hβ) Xβ.
  Proof.
    unfold X'. destruct le_lt_eq_dec as [H1 | H1]. 2: reflexivity. index_contra_solve.
  Qed.
  Hint Resolve X'_id_β : ofe_eq.

  Lemma X'_pi_id γ γ' Hγ Hγ' (H: γ = γ') : ofe_eq (X' γ Hγ) (X' γ' Hγ').
  Proof.
    intros; subst. pi_clear. reflexivity.
  Qed.
  Hint Resolve X'_pi_id : ofe_eq.

  Instance X'_truncated γ Hγ : OfeTruncated (X' γ Hγ) γ.
  Proof. unfold X'. destruct le_lt_eq_dec; subst; apply _. Qed.


  Let FX γ Hγ : COFE SI := cofe _ [G (X γ Hγ)]_{succ γ}.

  Unset Program Cases.
  (** definitions of ϕ, ψ *)
  Program Definition ϕ' γ (Hγ : γ ⪯ β) : X' γ Hγ -n> [G (X' γ Hγ)]_{succ γ} :=
    match le_lt_eq_dec γ Hγ with
    | left Hlt =>
        @transport_id (FX γ Hlt) ([G (X' γ Hγ)]_{succ γ}) (ofe_eq_symm (ofe_eq_funct _ (X'_id_lt γ _ _)))
        ◎ ϕ γ Hlt
        ◎ @transport_id (X' γ Hγ) (X γ Hlt) (X'_id_lt γ _ _)
    | right Heq =>
        @transport_id ([G (X' β _)]_{succ β}) ([G (X' γ _)]_{succ γ}) (ofe_eq_funct _ (X'_pi_id _ _ _ _ _))
        ◎ @transport_id ([G Xβ]_{succ β}) ([G (X' β _)]_{succ β}) (ofe_eq_symm (ofe_eq_funct _ (X'_id_β _)))
        ◎ ϕβ
        ◎ @transport_id (X' β _) Xβ (X'_id_β _)
        ◎ @transport_id (X' γ Hγ) (X' β _) (X'_pi_id _ _ _ _ _)
    end.
  Solve Obligations with eauto.
  Next Obligation.
    intros; by subst.
  Defined.

  Program Definition ψ' γ (Hγ : γ ⪯ β) : [G (X' γ Hγ)]_{succ γ} -n> X' γ Hγ :=
    match le_lt_eq_dec γ Hγ with
    | left Hlt =>
        @transport_id (X γ Hlt) (X' γ Hγ) (ofe_eq_symm (X'_id_lt γ _ _))
        ◎ ψ γ Hlt
        ◎ @transport_id ([G (X' γ Hγ)]_{succ γ}) (FX γ Hlt) (ofe_eq_funct _ (X'_id_lt γ _ _))
    | right Heq =>
        @transport_id (X' β _) (X' γ Hγ) (ofe_eq_symm (X'_pi_id _ _ _ _ _))
        ◎ @transport_id Xβ (X' β _) (ofe_eq_symm (X'_id_β _))
        ◎ ψβ
        ◎ @transport_id ([G (X' β _)]_{succ β}) ([G Xβ]_{succ β}) (ofe_eq_funct _ (X'_id_β _))
        ◎ @transport_id ([G (X' γ Hγ)]_{succ γ}) ([G (X' β _)]_{succ β}) (ofe_eq_symm (ofe_eq_funct _ (X'_pi_id _ _ _ _ _)))
    end.
  Solve Obligations with eauto.
  Next Obligation.
    intros; by subst.
  Defined.

  Lemma ϕ_ψ_id' γ Hγ : ϕ' γ Hγ ◎ ψ' γ Hγ ≡{γ}≡ cid.
  Proof using Fcontr.
    unfold ϕ', ψ'. destruct le_lt_eq_dec as [H1 | H1].
    - intros x; cbn. clear_transports. setoid_rewrite (ϕ_ψ_id _ _ _). by clear_transports.
    - intros x. cbn -[trunc_map]. clear_transports. subst. setoid_rewrite (ϕβ_ψβ_id _). by clear_transports.
  Qed.

  Lemma ψ_ϕ_id' γ Hγ : ψ' γ Hγ ◎ ϕ' γ Hγ ≡ cid.
  Proof using Fcontr.
    unfold ψ', ϕ'. destruct le_lt_eq_dec as [H1 | H1].
    - intros x; cbn. clear_transports. setoid_rewrite (ψ_ϕ_id _ _ _). by clear_transports.
    - intros x; cbn -[trunc_map]. clear_transports.
      subst. setoid_rewrite (ψβ_ϕβ_id _). by clear_transports.
  Qed.

  Lemma X'_succ_id γ Hγ Hsγ : ofe_eq (X' (succ γ) Hsγ) ([G (X' γ Hγ)]_{succ γ}).
  Proof using succ_or_limit Fcofe.
    destruct succ_or_limit as [[β' H] | H].
    - unfold X'. destruct (le_lt_eq_dec) as [H1 | H1]; destruct (le_lt_eq_dec) as [H2 | H2].
      all: try by (exfalso; subst; index_contra_solve).
      by apply X_eq.
      by apply Xβ_eq.
    - rewrite !X'_id_lt. { apply H. apply index_succ_le_lt, Hsγ. } { apply index_succ_le_lt, Hsγ. }
      intros. apply X_eq.
  Qed.
  Hint Resolve X'_succ_id : ofe_eq.

  Let fold' γ Hγ Hsγ := fold_transport (X'_succ_id γ Hγ Hsγ).
  Let unfold' γ Hγ Hsγ := unfold_transport (X'_succ_id γ Hγ Hsγ).
  Fact fold_unfold_id' γ Hγ Hsγ : fold' γ Hγ Hsγ ◎ unfold' γ Hγ Hsγ ≡ cid.
  Proof. unfold fold', unfold', fold_transport, unfold_transport. intros x; cbn. by clear_transports. Qed.
  Lemma unfold_fold_id' γ Hγ Hsγ : unfold' γ Hγ Hsγ ◎ fold' γ Hγ Hsγ ≡ cid.
  Proof. unfold fold', unfold', fold_transport, unfold_transport. intros x; cbn. by clear_transports. Qed.

  Ltac open_folds := unfold unfold, fold, fold', unfold', foldβ, unfoldβ, fold_transport, unfold_transport.

  Lemma e'_ca γ0 γ1 (Hγ0 : γ0 ⪯ β) (Hγ1 : γ1 ⪯ β) (Hlt : γ0 ≺ γ1) : {γ0 ≺ β ∧ γ1 ≺ β} + {γ0 ≺ β ∧ γ1 = β}.
  Proof.
    destruct (index_le_lt_dec β γ1) as [H1 | H1].
    - right. assert (γ1 = β) as ->. { apply index_le_ge_eq; assumption. }
      split; auto.
    - left. split; last assumption. etransitivity; eassumption.
  Qed.

  Program Definition e' γ0 γ1 Hγ0 Hγ1 (Hlt : γ0 ≺ γ1) : X' γ0 Hγ0 -n> X' γ1 Hγ1 :=
    match e'_ca γ0 γ1 Hγ0 Hγ1 Hlt with
    | left (conj H0 H1) =>
        @transport_id (X γ1 H1) (X' γ1 Hγ1) (ofe_eq_symm (X'_id_lt _ _ _))
        ◎ e γ0 γ1 H0 H1 Hlt
        ◎ @transport_id (X' γ0 Hγ0) (X γ0 H0) (X'_id_lt _ _ _)
    | right (conj H0 H1) =>
        @transport_id (X' β _) (X' γ1 _) (X'_pi_id _ _ _ _ _)
        ◎ @transport_id Xβ (X' β _) (ofe_eq_symm (X'_id_β _))
        ◎ eβ γ0 H0
        ◎ @transport_id (X' γ0 Hγ0) (X γ0 H0) (X'_id_lt _ _ _)
    end.
  Solve Obligations with eauto.

  Program Definition p' γ0 γ1 Hγ0 Hγ1 (Hlt : γ0 ≺ γ1) : X' γ1 Hγ1 -n> X' γ0 Hγ0  :=
    match e'_ca γ0 γ1 Hγ0 Hγ1 Hlt with
    | left (conj H0 H1) =>
        @transport_id (X γ0 H0) (X' γ0 Hγ0) (ofe_eq_symm (X'_id_lt _ _ _))
        ◎ p γ0 γ1 H0 H1 Hlt
        ◎ @transport_id (X' γ1 Hγ1) (X γ1 H1)  (X'_id_lt _ _ _)
    | right (conj H0 H1) =>
        @transport_id (X γ0 H0) (X' γ0 Hγ0) (ofe_eq_symm (X'_id_lt _ _ _))
        ◎ pβ γ0 H0
        ◎ @transport_id (X' β _) Xβ (X'_id_β _)
        ◎ @transport_id (X' γ1 _) (X' β _) (ofe_eq_symm (X'_pi_id _ _ _ _ _))
    end.
  Solve Obligations with eauto.

  Lemma p_e_id' γ0 γ1 Hγ0 Hγ1 Hlt : p' γ0 γ1 Hγ0 Hγ1 Hlt ◎ e' γ0 γ1 Hγ0 Hγ1 Hlt ≡ cid.
  Proof using Fcontr.
    unfold p', e'. destruct e'_ca as [[H0 H1] | [H0 H1]].
    - intros x; cbn. clear_transports. setoid_rewrite (p_e_id _ _ _ _ _ _). by clear_transports.
    - intros x; cbn. clear_transports. setoid_rewrite (pβ_eβ_id _ _ _). by clear_transports.
  Qed.

  Lemma e_p_id' γ0 γ1 Hγ0 Hγ1 Hlt : e' γ0 γ1 Hγ0 Hγ1 Hlt ◎ p' γ0 γ1 Hγ0 Hγ1 Hlt ≡{γ0}≡ cid.
  Proof using Fcontr.
    unfold p', e'. destruct e'_ca as [[H0 H1] | [H0 H1]].
    - intros x; cbn. clear_transports. setoid_rewrite (e_p_id _ _ _ _ _ _). by clear_transports.
    - intros x; cbn. clear_transports. setoid_rewrite (eβ_pβ_id _ _ _). by clear_transports.
  Qed.

  Lemma p'_funct γ0 γ1 γ2 Hγ0 Hγ1 Hγ2 Hlt0 Hlt1 Hlt2 :
    p' γ0 γ1 Hγ0 Hγ1 Hlt0 ◎ p' γ1 γ2 Hγ1 Hγ2 Hlt1 ≡ p' γ0 γ2 Hγ0 Hγ2 Hlt2.
  Proof.
    unfold p'. destruct (e'_ca γ0 γ1) as [[H0 H1] | [H0 H1]];
        destruct (e'_ca γ1 γ2) as [[H3 H4] | [H3 H4]];
        destruct (e'_ca γ0 γ2) as [[H5 H6] | [H5 H6]].
    all: try index_contra_solve.
    - intros x; cbn. repeat pi_clear. clear_transports.
      setoid_rewrite (p_funct _ _ _ _ _ _ _ _ _ _). reflexivity.
    - intros x; cbn. repeat pi_clear. clear_transports.
      setoid_rewrite (pβ_funct _ _ _ _ _ _). reflexivity.
  Qed.

  Lemma e'_funct γ0 γ1 γ2 Hγ0 Hγ1 Hγ2 Hlt0 Hlt1 Hlt2 :
    e' γ1 γ2 Hγ1 Hγ2 Hlt1 ◎ e' γ0 γ1 Hγ0 Hγ1 Hlt0 ≡ e' γ0 γ2 Hγ0 Hγ2 Hlt2.
  Proof.
    unfold e'. destruct (e'_ca γ0 γ1) as [[H0 H1] | [H0 H1]];
        destruct (e'_ca γ1 γ2) as [[H3 H4] | [H3 H4]];
        destruct (e'_ca γ0 γ2) as [[H5 H6] | [H5 H6]].
    all: try index_contra_solve.
    - intros x; cbn. repeat pi_clear. clear_transports.
      setoid_rewrite (e_funct _ _ _ _ _ _ _ _ _ _). reflexivity.
    - intros x; cbn. repeat pi_clear. clear_transports.
      setoid_rewrite (eβ_funct _ _ _ _ _ _). reflexivity.
  Qed.

  Lemma fold'_eq γ (Hγ : γ ≺ β) (Hγ' : γ ⪯ β) (Hsγ : succ γ ≺ β) (Hsγ' : succ γ⪯ β): fold' γ Hγ' Hsγ'
    ≡ @transport_id (X (succ γ) Hsγ) (X' (succ γ) Hsγ') (ofe_eq_symm (X'_id_lt (succ γ) Hsγ' Hsγ))
      ◎ fold γ Hγ Hsγ
      ◎ @transport_id ([G (X' γ Hγ')]_{succ γ}) ([G (X γ Hγ)]_{succ γ}) (ofe_eq_funct eq_refl (X'_id_lt γ Hγ' Hγ)).
  Proof.
    rewrite ofe_truncated_equiv. unfold fold', fold, fold_transport. intros x; cbn.
    clear_transports. equalise_pi.
  Qed.

  Lemma unfold'_eq γ Hγ Hγ' Hsγ Hsγ' : unfold' γ Hγ' Hsγ'
    ≡ @transport_id  ([G (X γ Hγ)]_{succ γ}) ([G (X' γ Hγ')]_{succ γ}) (ofe_eq_symm (ofe_eq_funct eq_refl (X'_id_lt γ Hγ' Hγ)))
      ◎ unfold γ Hγ Hsγ
      ◎ @transport_id (X' (succ γ) Hsγ') (X (succ γ) Hsγ) (X'_id_lt (succ γ) Hsγ' Hsγ).
  Proof.
    rewrite ofe_truncated_equiv. unfold unfold', unfold, unfold_transport. intros x; cbn.
    clear_transports. equalise_pi.
  Qed.

  (* I don't know what this says intuitively, but it can be reused for the two following lemmas... *)
  Lemma pull_transports γ0 γ1 Hγ0 Hsγ0 H1 Hγ1 H0 Hlt I I1 I2 I3 I4 I5 I6:
    @transport_id ([G (X' γ0 Hγ0)]_{succ γ0}) (X' (succ γ0) Hsγ0) I
    ◎ trunc_map (succ γ1) (succ γ0)
     (map
        (@transport_id (X γ1 H1) (X' γ1 Hγ1) I1 ◎ e γ0 γ1 H0 H1 Hlt ◎ @transport_id (X' γ0 Hγ0) (X γ0 H0) I2,
         @transport_id (X γ0 H0) (X' γ0 Hγ0) I3 ◎ p γ0 γ1 H0 H1 Hlt ◎ @transport_id (X' γ1 Hγ1) (X γ1 H1) I4))
  ≡ @transport_id ([G (X γ0 H0)]_{succ γ0}) (X' (succ γ0) Hsγ0) I5
      ◎ trunc_map (succ γ1) (succ γ0)
         (map (e γ0 γ1 H0 H1 Hlt, p γ0 γ1 H0 H1 Hlt))
      ◎ @transport_id ([G (X' γ1 Hγ1)]_{succ γ1}) ([G (X γ1 H1)]_{succ γ1}) I6.
  Proof using succ_or_limit Fcontr Fcofe.
    intros x; cbn. clear_transports.
    rewrite ofe_truncated_equiv.
    setoid_rewrite oFunctor_ne at 1; [ | setoid_rewrite (ccompose_assoc) at 2; reflexivity ].
    setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
    unshelve transport_id_truncate_rl. eauto with ofe_eq.
    cbn. clear_transports. equalise_pi_head. do 2 f_equiv.
    setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
    equalise_pi_head. apply ofe_mor_ne.
    transport_id_expand_lr.
    cbn. equalise_pi.
  Qed.

  Lemma Fep_p' γ0 γ1 (Hγ0 : γ0 ⪯ β) (Hγ1 : γ1 ⪯ β) (Hsγ0 : succ γ0 ⪯ β) (Hsγ1 : succ γ1 ⪯ β) (Hlt : γ0 ≺ γ1) (Hlts : succ γ0 ≺ succ γ1):
    fold' γ0 Hγ0 Hsγ0
    ◎ trunc_map (succ γ1) (succ γ0)
        (map (e' γ0 γ1 Hγ0 Hγ1 Hlt, p' γ0 γ1 Hγ0 Hγ1 Hlt))
    ◎ unfold' γ1 Hγ1 Hsγ1 ≡ p' (succ γ0) (succ γ1) Hsγ0 Hsγ1 Hlts.
  Proof using Fcontr.
    destruct succ_or_limit as [[β' H] | Hlim].
    { (* successor case *)
      open_folds. unfold p', e'.
      destruct (e'_ca γ0 γ1) as [[H1 H2] | [H1 H2]], (e'_ca (succ γ0) (succ γ1)) as [[H3 H4] | [H3 H4]].
      1: rewrite <- Fep_p.
      2: rewrite <- Fep_pβ.
      3-4: index_contra_solve.
      all: erewrite pull_transports.
      all: open_folds.
      all: intros x; cbn; clear_transports.
      all: do 3 f_equiv; equalise_pi.
      Unshelve. by auto. all: eauto with ofe_eq.
    }
    {
      (* limit case *)
      assert (γ0 ≺ β) as T1. { apply index_succ_le_lt, Hsγ0. }
      assert (succ γ0 ≺ β) as T2. { apply Hlim. apply index_succ_le_lt, Hsγ0. }
      unshelve setoid_rewrite (fold'_eq _ _ _ _ _). 1-2:assumption.
      unfold fold', unfold', e', p', fold_transport, unfold_transport.
      destruct e'_ca as [[H0 H1] | [H0 H1]]; destruct (e'_ca) as [[H3 H4] | [H3 H4]].
      3-4: index_contra_solve.
      - intros x; cbn -[trunc_map].
        clear_transports.
        equalise_pi_head. f_equiv.
        setoid_rewrite <- (Fep_p _ _ _ _ _ _ _ _ _ ). cbn -[trunc_map].
        f_equiv. unfold unfold, unfold_transport. clear_transports.
        setoid_rewrite (transport_id_truncate _ _ _ _ _ _ _) at 1. cbn. f_equiv.
        rewrite equiv_dist => α.
        setoid_rewrite oFunctor_ne at 2. 2: { setoid_rewrite (ccompose_assoc _ _ _) at 1. reflexivity. }
        setoid_rewrite <- (map_compose _ _ _ _ _).
        setoid_rewrite (map_compose _ _ _ _ _).
        rewrite (proof_irrel H0 T1).
        setoid_rewrite oFunctor_ne at 1. 2: { apply pair_ne; intros y; cbn; clear_transports; reflexivity. }
        apply ofe_mor_ne. open_folds.
        setoid_rewrite (transport_id_expand _ _ _ _ _ _ _). cbn.
        clear_transports. Unshelve. 3: reflexivity. equalise_pi.
      - exfalso. specialize (Hlim γ1 H1) as H. rewrite H4 in H. index_contra_solve.
    }
  Qed.

  Lemma Fep_p_limit' γ0 γ1 (Hlim : index_is_limit γ1) (Hγ0 : γ0 ⪯ β) (Hsγ0 : succ γ0 ⪯ β) (Hγ1 : γ1 ⪯ β) (Hlt : γ0 ≺ γ1) (Hslt : succ γ0 ≺ γ1):
    fold' γ0 Hγ0 Hsγ0
    ◎ trunc_map (succ γ1) (succ γ0)
        (map (e' γ0 γ1 Hγ0 Hγ1 Hlt, p' γ0 γ1 Hγ0 Hγ1 Hlt))
    ≡ p' (succ γ0) γ1 Hsγ0 Hγ1 Hslt ◎ ψ' γ1 Hγ1.
  Proof using Fcontr.
    unfold fold', e', p', ψ', fold_transport.
    destruct (e'_ca γ0 γ1) as [[H0 H1] | [H0 H1]],
      (e'_ca (succ γ0) γ1) as [[H3 H4] | [H3 H4]],
      (le_lt_eq_dec γ1 Hγ1) as [H5 | H5].
    all: try index_contra_solve.
    - erewrite pull_transports. intros x; cbn -[trunc_map]. clear_transports.
      unshelve setoid_rewrite <- (Fep_p_limit _ _ _ _ _ _ _ _ _). 1-2,4: assumption.
      open_folds. cbn -[trunc_map]. clear_transports.
      repeat pi_clear. equalise_pi.
    - intros x; cbn-[trunc_map]. clear_transports.
      setoid_rewrite <- (Fep_pβ_limit _ _ _ _ _). 2: { rewrite <- H5. assumption. }
      open_folds. cbn-[trunc_map]. clear_transports.
      rewrite ofe_truncated_equiv. cbn.
      setoid_rewrite oFunctor_ne at 1.
      2: { split; cbn.
          - setoid_rewrite (transport_id_compose _ _ _ ). instantiate (1 := (_, _)). cbn. reflexivity.
          - cbn. setoid_rewrite (ccompose_assoc _ _ _). setoid_rewrite (transport_id_compose _ _ _).
           setoid_rewrite (ccompose_assoc _ _ _). reflexivity.
      }
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
      setoid_rewrite <- (transport_id_truncate_symm _ _ _ _ _  _ _ ) at 1.
      cbn. clear_transports. equalise_pi_head. do 2 apply ofe_mor_ne.
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
      equalise_pi_head. apply ofe_mor_ne.
      apply equiv_dist. eapply transport_id_expand'.
      by rewrite H4.
      Unshelve. reflexivity.
  Qed.

  Ltac equal_maps := open_folds; intros x; cbn; clear_transports; equalise_pi.
  Lemma p_succ_id' γ (Hγ : γ ⪯ β) (Hsγ : succ γ ⪯ β) (Hlt : γ ≺ succ γ):
    p' γ (succ γ) Hγ Hsγ Hlt ≡ ψ' γ Hγ ◎ unfold' γ Hγ Hsγ.
  Proof.
    unfold p', ψ', unfold'. destruct (e'_ca) as [[H1 H2] | [H1 H2]], (le_lt_eq_dec) as [H3 | H3].
    all: try index_contra_solve.
    - rewrite (p_ψ_unfold). equal_maps.
    - rewrite p_ψ_unfoldβ. equal_maps.
      Unshelve. auto.
  Qed.

  Lemma e_succ_id' γ (Hγ : γ ⪯ β) (Hsγ : succ γ ⪯ β) (Hlt : γ ≺ succ γ):
    e' γ (succ γ) Hγ Hsγ Hlt ≡ fold' γ Hγ Hsγ ◎ ϕ' γ Hγ.
  Proof.
    unfold e', ϕ', fold'. destruct (e'_ca) as [[H1 H2] | [H1 H2]], (le_lt_eq_dec) as [H3 | H3].
    all: try index_contra_solve.
    - rewrite e_fold_ϕ. equal_maps.
    - rewrite e_fold_ϕβ. equal_maps.
      Unshelve. auto.
  Qed.

  Lemma ϕ_succ_id' γ (Hle : γ ⪯ β) (Hsle : succ γ ⪯ β):
    ϕ' (succ γ) Hsle
    ≡ trunc_map (succ γ) (succ (succ γ))
        (map (ψ' γ Hle ◎ unfold' γ Hle Hsle, fold' γ Hle Hsle ◎ ϕ' γ Hle))
      ◎ unfold' γ Hle Hsle.
  Proof using Fcontr.
    unfold ϕ', ψ'. open_folds.
    destruct (le_lt_eq_dec (succ γ)) as [H1 | H1], (le_lt_eq_dec γ) as [H2 | H2].
    all: try index_contra_solve.
    - unshelve rewrite ϕ_succ_id. assumption.
      intros x; cbn. open_folds. clear_transports.
      transport_id_truncate_lr.
      cbn. rewrite ofe_truncated_equiv. apply ofe_mor_ne.
      setoid_rewrite (map_compose_dist _ _ _ _ _ _).
      cbn.
      setoid_rewrite oFunctor_ne at 2. 2: {
        apply pair_ne.
        { rewrite ccompose_assoc. rewrite (transport_id_compose _ _ _). rewrite ccompose_assoc. reflexivity. }
        { rewrite <- !ccompose_assoc. rewrite transport_id_compose. reflexivity. }
      }
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _) at 2. cbn.
      setoid_rewrite (transport_id_expand _ _ _ _ _ _ _).
      cbn. clear_transports.
      setoid_rewrite oFunctor_ne at 1.
      2: { apply pair_ne.
        { rewrite ccompose_assoc. rewrite transport_id_compose. reflexivity. }
        { rewrite <- ccompose_assoc. rewrite transport_id_compose. reflexivity. }
      }
      equalise_pi.
    - unshelve rewrite ϕβ_succ_id. 3: symmetry; apply H1. assumption.
      intros x; cbn. open_folds. clear_transports.
      rewrite ofe_truncated_equiv.
      transport_id_truncate_lr. by rewrite H1.
      cbn. apply ofe_mor_ne.
      setoid_rewrite oFunctor_ne at 3.
      2: { apply pair_ne.
        { rewrite ccompose_assoc. rewrite transport_id_compose. rewrite ccompose_assoc. reflexivity. }
        { rewrite <- !ccompose_assoc. rewrite transport_id_compose. reflexivity. }
      }
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _) at 2. cbn.
      setoid_rewrite (map_compose_dist _ _ _ _ _ _) at 1. cbn.
      setoid_rewrite oFunctor_ne at 1.
      2: { apply pair_ne.
        { rewrite ccompose_assoc. rewrite transport_id_compose. reflexivity. }
        { rewrite <- ccompose_assoc. rewrite transport_id_compose. reflexivity. }
      }
      equalise_pi_head. apply ofe_mor_ne.
      setoid_rewrite (transport_id_expand _ _ _ _ _ _ _). cbn. clear_transports. equalise_pi.
      Unshelve. all: reflexivity.
  Qed.

  Lemma ψ_succ_id' γ (Hle : γ ⪯ β) (Hsle : succ γ ⪯ β):
    ψ' (succ γ) Hsle
    ≡ fold' γ Hle Hsle
      ◎ trunc_map (succ (succ γ)) (succ γ) (map (fold' γ Hle Hsle ◎ ϕ' γ Hle, ψ' γ Hle ◎ unfold' γ Hle Hsle)).
  Proof using Fcontr.
    unfold ϕ', ψ'. open_folds.
    destruct (le_lt_eq_dec (succ γ)) as [H1 | H1], (le_lt_eq_dec γ) as [H2 | H2].
    all: try solve [index_contra_solve].
    - unshelve rewrite ψ_succ_id. assumption.
      intros x; cbn. open_folds. clear_transports.
      rewrite ofe_truncated_equiv.
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _) at 1. cbn.
      setoid_rewrite oFunctor_ne at 3. 2: {
        apply pair_ne.
        { rewrite <- !ccompose_assoc. rewrite (transport_id_compose _ _ _). rewrite ccompose_assoc. reflexivity. }
        { rewrite !ccompose_assoc. rewrite (transport_id_compose _ _ _). rewrite <- ccompose_assoc. reflexivity. }
      }
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.

      setoid_rewrite <- (transport_id_truncate_symm _ _ _ _ _ _ _). cbn.
      clear_transports. equalise_pi_head. do 3 apply ofe_mor_ne.
      setoid_rewrite <- (transport_id_expand _ _ _ _ _ _ _). cbn.
      setoid_rewrite (map_compose_dist _ _ _ _ _ _).
      setoid_rewrite oFunctor_ne at 1.
      2: { apply pair_ne. all: rewrite (transport_id_compose _ _ _); reflexivity. }
      equalise_pi.
    - unshelve rewrite ψβ_succ_id. 3: symmetry; apply H1. assumption.
      intros x; cbn. open_folds. clear_transports.
      rewrite ofe_truncated_equiv.

      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _) at 1. cbn.
      setoid_rewrite oFunctor_ne at 3. 2: {
        apply pair_ne.
        { rewrite <- !ccompose_assoc. rewrite (transport_id_compose _ _ _). rewrite ccompose_assoc. reflexivity. }
        { rewrite !ccompose_assoc. rewrite (transport_id_compose _ _ _). rewrite <- ccompose_assoc. reflexivity. }
      }
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
      setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.

      setoid_rewrite <- (transport_id_truncate_symm _ _ _ _ _ _ _). cbn.
      clear_transports. equalise_pi_head. do 3 apply ofe_mor_ne.

      transport_id_expand_rl. by rewrite H1. cbn.

      setoid_rewrite (map_compose_dist _ _ _ _ _ _).
      setoid_rewrite oFunctor_ne at 1. 2: { apply pair_ne. all: rewrite (transport_id_compose _ _ _); reflexivity. }
      equalise_pi.
      Unshelve. all: reflexivity.
  Qed.

  Program Definition extended_approx : @bounded_approx (λ γ, γ ⪯ β) :=
    {|
      bounded_approx_X := X';
      bounded_approx_e := e';
      bounded_approx_p := p';
      bounded_approx_ϕ := ϕ';
      bounded_approx_ψ := ψ';
    |}.
  Next Obligation.
    eexists X'_succ_id.
    - apply p_e_id'.
    - apply e_p_id'.
    - apply e'_funct.
    - apply p'_funct.
    - apply ψ_ϕ_id'.
    - apply ϕ_ψ_id'.
    - intros. unfold X'. destruct le_lt_eq_dec; subst; apply _.
    - apply Fep_p'.
    - apply p_succ_id'.
    - apply e_succ_id'.
    - apply ϕ_succ_id'.
    - apply ψ_succ_id'.
    - apply Fep_p_limit'.
  Qed.

  Lemma extended_approx_agree : approx_agree A extended_approx.
  Proof.
    assert (Heq : ∀ (γ : SI) (H0 : γ ≺ β) (H1 : γ ⪯ β), bounded_approx_X A γ H0 = bounded_approx_X extended_approx γ H1).
    { intros. cbn. unfold X'. destruct le_lt_eq_dec as [H2 | H2]. by pi_clear.
      subst; index_contra_solve.
    }
    exists (λ γ H0 H1, proj_id (Heq γ H0 H1)).
    { intros. unfold fold_transport. setoid_rewrite (transport_id_bcompl _ _ _ _). 2: symmetry; apply Heq.
      apply bcompl_ne. intros. cbn. unfold unfold_transport. clear_transports. equalise_pi.
    }
    1-2: intros; cbn; unfold e', p'; (destruct e'_ca as [[H1 H2] | [H1 H2]]; [ | subst; index_contra_solve ]).
    3-4: intros; cbn; unfold ϕ', ψ'; (destruct le_lt_eq_dec as [H1 | H1]; [ |  subst; index_contra_solve ]).
    all: unfold fold_transport, unfold_transport; intros x; cbn; repeat pi_clear; by clear_transports.
  Qed.

End merge_extension.

Lemma cofe_eq_bcompl_nat (A B : COFE SI) (Heq : A = B) (Heq' : projCOFE _ A = projCOFE _ B):
 ∀ α (Hα : zero ≺ α) (ch : bchain A α), bcompl Hα ch ≡{α}≡ fold_transport Heq' (bcompl Hα (bchain_map (unfold_transport Heq') ch)).
Proof.
  intros. subst. unfold fold_transport, unfold_transport. clear_transports.
  apply bcompl_ne. intros. cbn. by clear_transports.
Qed.

(** we need to show that merging extensions preserves agreement *)
Lemma extension_coherent β (A0 A1 : bounded_approx (λ γ, γ ≺ β))
  (E0 : extension A0) (E1 : extension A1) succ_or_limit :
  ∀ H : approx_agree A0 A1,
  @extension_agree β A0 A1 E0 E1 H
  → approx_agree (extended_approx β A0 E0 succ_or_limit) (extended_approx β A1 E1 succ_or_limit).
Proof with (unfold fold_transport, unfold_transport; intros x; cbn; clear_transports; equalise_pi).
  intros H Hag.
  unshelve refine ( let X_eq : ∀ (γ : SI) (H0 H1 : γ ⪯ β), projCOFE _ (X' β A0 E0 γ H0) = projCOFE _ (X' β A1 E1 γ H1) := _  in _).
  { intros. unfold X'. pi_clear. destruct le_lt_eq_dec as [H2 | H2]. apply H. apply Hag. }
  exists X_eq.
  - intros.
    (* this is a bit fiddly due to dependent typing. we need the X_eq equality to be transparent for this,
      in order to make a case analysis on the def of X *)
    repeat pi_clear. cbn in ch. unfold X' in ch.
    unfold fold_transport, unfold_transport. cbn. unfold X' in *.
    subst X_eq.
    cbn. set (e := proof_irrel _ _).
    rewrite !(proof_irrel e eq_refl). subst. cbn.
    destruct (le_lt_eq_dec β γ H1) as [H2 | H2].
    + apply agree_bcompl_nat.
    + subst. apply eagree_bcompl_nat.
  - intros. repeat pi_clear. cbn.
    unfold e'. destruct (e'_ca) as [[F0 F1] | [F0 F1]].
    + setoid_rewrite (agree_e_nat H _ _ _ _ _ _ _)...
    + setoid_rewrite (eagree_e_nat Hag _ _)...
  - intros. repeat pi_clear. cbn.
    unfold p'. destruct (e'_ca) as [[F0 F1] | [F0 F1]].
    + setoid_rewrite (agree_p_nat H _ _ _ _ _ _ _)...
    + setoid_rewrite (eagree_p_nat Hag _ _)...
  - intros. repeat pi_clear. cbn.
    unfold ϕ'. destruct (le_lt_eq_dec) as [F0 | F0].
    + setoid_rewrite (agree_ϕ_nat H _ _ _)...
    + setoid_rewrite (eagree_ϕ_nat Hag)...
  - intros. repeat pi_clear. cbn.
    unfold ψ'. destruct (le_lt_eq_dec) as [F0 | F0].
    + setoid_rewrite (agree_ψ_nat H _ _ _)...
    + setoid_rewrite (eagree_ψ_nat Hag)...
Qed.

(** * Proving that we can merge approximations in limit cases *)

Section merge.
  Context (P : SI → Prop).
  Context (IH : ∀ α, P α → bounded_approx (λ γ, γ ⪯ α)).
  Context (IH_agree : ∀ α0 α1 Hα0 Hα1, approx_agree (IH α0 Hα0) (IH α1 Hα1)).

  (* we want to get merged_IH : bounded_approx P such that
    ∀ α (Hα : P α), approx_agree (IH α Hα) merged_IH
  *)

  Program Definition mX γ (Hγ : P γ) := bounded_approx_X (IH γ Hγ) γ _.
  Solve Obligations with cbn; eauto.
  Instance mX_truncated γ Hγ: OfeTruncated (mX γ Hγ) γ.
  Proof.
    unfold mX. eapply approx_X_truncated. apply IH.
  Qed.

  Program Definition me γ0 γ1 (Hγ0 : P γ0) (Hγ1 : P γ1) (Hlt : γ0 ≺ γ1) : mX γ0 Hγ0 -n> mX γ1 Hγ1 :=
    bounded_approx_e (IH γ1 Hγ1) γ0 γ1 _ _ Hlt
    ◎ unfold_transport (agree_eq (IH_agree _ _ _ _) γ0  _ _).
  Next Obligation.
    intros; cbn. by right.
  Defined.

  Program Definition mp γ0 γ1 (Hγ0 : P γ0) (Hγ1 : P γ1) (Hlt : γ0 ≺ γ1) : mX γ1 Hγ1 -n> mX γ0 Hγ0 :=
    fold_transport (agree_eq (IH_agree _ _ _ _) γ0  _ _)
    ◎ bounded_approx_p (IH γ1 Hγ1) γ0 γ1 _ _ Hlt.
  Next Obligation.
    intros; cbn. by right.
  Defined.

  Lemma me_mp_id γ0 γ1 Hγ0 Hγ1 Hlt : me γ0 γ1 Hγ0 Hγ1 Hlt ◎ mp γ0 γ1 Hγ0 Hγ1 Hlt ≡{γ0}≡ cid.
  Proof.
    unfold me, mp. setoid_rewrite ccompose_assoc. setoid_rewrite <- ccompose_assoc at 2.
    unfold unfold_transport, fold_transport. intros x; cbn. clear_transports. apply IH.
  Qed.

  Lemma mp_me_id γ0 γ1 Hγ0 Hγ1 Hlt : mp γ0 γ1 Hγ0 Hγ1 Hlt ◎ me γ0 γ1 Hγ0 Hγ1 Hlt ≡ cid.
  Proof.
    unfold me, mp. setoid_rewrite ccompose_assoc. setoid_rewrite <- ccompose_assoc at 2.
    setoid_rewrite (approx_p_e_id (bounded_approx_props (IH _ _)) _ _ _ _ _).
    setoid_rewrite ccompose_cid_l. intros x; cbn. unfold fold_transport, unfold_transport. by clear_transports.
  Qed.

  Lemma me_funct γ0 γ1 γ2 Hγ0 Hγ1 Hγ2 Hlt1 Hlt2 Hlt3 : me γ1 γ2 Hγ1 Hγ2 Hlt2 ◎ me γ0 γ1 Hγ0 Hγ1 Hlt1 ≡ me γ0 γ2 Hγ0 Hγ2 Hlt3.
  Proof.
    unfold me. symmetry. intros x. cbn.
    setoid_rewrite <- (approx_e_funct (bounded_approx_props (IH _ _)) γ0 γ1 γ2 _ _ _ _ _ _ _) at 1.
    cbn. f_equiv.
    setoid_rewrite (agree_e_nat _ _ _ _ _ _ _ _ _) at 1. cbn.
    unfold fold_transport, unfold_transport. compose_transports. equalise_pi.
    Unshelve. all: apply IH_agree.
  Qed.

  Lemma mp_funct γ0 γ1 γ2 Hγ0 Hγ1 Hγ2 Hlt1 Hlt2 Hlt3 : mp γ0 γ1 Hγ0 Hγ1 Hlt1 ◎ mp γ1 γ2 Hγ1 Hγ2 Hlt2  ≡ mp γ0 γ2 Hγ0 Hγ2 Hlt3.
  Proof.
    unfold mp. symmetry. intros x. cbn.
    unfold fold_transport, unfold_transport.
    setoid_rewrite <- (approx_p_funct (bounded_approx_props (IH _ _)) γ0 γ1 γ2 _ _ _ _ _ _ _) at 1. cbn.
    setoid_rewrite (agree_p_nat _ _ _ _ _ _ _ _ _) at 1. cbn.
    unfold fold_transport.
    compose_transports. equalise_pi.
    Unshelve. apply IH_agree.
  Qed.

  Program Definition mϕ γ (Hγ : P γ) : mX γ Hγ -n> [G (mX γ Hγ)]_{succ γ} :=
    bounded_approx_ϕ (IH γ Hγ) γ _.
  Program Definition mψ γ (Hγ : P γ) : [G (mX γ Hγ)]_{succ γ} -n> mX γ Hγ :=
    bounded_approx_ψ (IH γ Hγ) γ _.

  Lemma mϕ_mψ_id γ Hγ : mϕ γ Hγ ◎ mψ γ Hγ ≡{γ}≡ cid.
  Proof. apply IH. Qed.
  Lemma mψ_mϕ_id γ Hγ : mψ γ Hγ ◎ mϕ γ Hγ ≡ cid.
  Proof. apply IH. Qed.

  Instance msucc_eq α Hα Hsα : ofe_eq (mX (succ α) Hsα) ([G (mX α Hα)]_{succ α}).
  Proof using IH_agree.
    unfold mX. symmetry. erewrite agree_eq. symmetry; eapply approx_eq. apply IH. apply IH_agree.
    Unshelve. cbn; eauto.
  Qed.


  Lemma Fmemp_mp γ0 γ1 (Hγ0 : P γ0) (Hγ1 : P γ1) (Hsγ0 : P (succ γ0)) (Hsγ1 : P (succ γ1)) (Hlt : γ0 ≺ γ1) (Hlts : succ γ0 ≺ succ γ1):
    fold_transport (msucc_eq γ0 Hγ0 Hsγ0)
    ◎ trunc_map (succ γ1) (succ γ0)
        (map (me γ0 γ1 Hγ0 Hγ1 Hlt, mp γ0 γ1 Hγ0 Hγ1 Hlt))
    ◎ unfold_transport (msucc_eq γ1 Hγ1 Hsγ1) ≡ mp (succ γ0) (succ γ1) Hsγ0 Hsγ1 Hlts.
  Proof using Fcontr Fcofe.
    unfold me, mp. intros x; cbn. rewrite ofe_truncated_equiv.
    setoid_rewrite oFunctor_ne at 1.
    2: { apply pair_ne.
      { rewrite (agree_e_nat (IH_agree γ1 (succ γ1) Hγ1 Hsγ1)).
        rewrite !ccompose_assoc. rewrite (transport_id_compose _ _ _). reflexivity. }
      { rewrite (agree_p_nat (IH_agree γ1 (succ γ1) Hγ1 Hsγ1)).
        rewrite <- !ccompose_assoc. rewrite (transport_id_compose _ _ _). reflexivity. }
    }
    setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
    setoid_rewrite <- (map_compose_dist _ _ _ _ _ _).
    cbn.
    transport_id_truncate_rl.

    setoid_rewrite <- (approx_Fep_p (bounded_approx_props (IH (succ γ1) Hsγ1)) _ _ _ _ _ _ _ _ _).
    cbn. unfold fold_transport, unfold_transport. clear_transports. equalise_pi_head.
    do 3 apply ofe_mor_ne.
    cbn.
    setoid_rewrite (transport_id_expand _ _ _ _ _ _ _).
    cbn. clear_transports. equalise_pi.
    Unshelve. all: eauto with index.
    apply ofe_eq_funct. reflexivity. apply IH_agree.
  Qed.

  Lemma Fmemp_mp_lim γ0 γ1 (Hlim : index_is_limit γ1) (Hγ0 : P γ0) (Hsγ0 : P (succ γ0)) (Hγ1 : P γ1) (Hlt : γ0 ≺ γ1) (Hslt : succ γ0 ≺ γ1):
    fold_transport (msucc_eq γ0 Hγ0 Hsγ0)
    ◎ trunc_map (succ γ1) (succ γ0)
        (map (me γ0 γ1 Hγ0 Hγ1 Hlt, mp γ0 γ1 Hγ0 Hγ1 Hlt))
    ≡ mp (succ γ0) γ1 Hsγ0 Hγ1 Hslt ◎ mψ γ1 Hγ1.
  Proof using Fcontr.
    unfold me, mp, mϕ. intros x; cbn. rewrite ofe_truncated_equiv.
    setoid_rewrite <- (approx_Fep_p_limit (bounded_approx_props (IH γ1 Hγ1)) _ _ _ _ _ _ _ _ _); last assumption.
    cbn.
    rewrite <- (map_compose_dist _ _ _ _ _ _).
    cbn. unfold unfold_transport, fold_transport.
    setoid_rewrite <- (transport_id_truncate_symm _ _  _ _ _ _ _).
    cbn. clear_transports. equalise_pi.
    Unshelve. reflexivity.
  Qed.

  Lemma mp_succ_id γ (Hγ : P γ) (Hsγ : P (succ γ)) (Hlt : γ ≺ succ γ):
    mp γ (succ γ) Hγ Hsγ Hlt ≡ mψ γ Hγ ◎ unfold_transport (msucc_eq γ Hγ Hsγ).
  Proof.
    unfold mp, mψ.
    rewrite (agree_ψ_nat (IH_agree γ (succ γ) Hγ Hsγ) _ _ _).
    rewrite (approx_p_ψ_unfold (bounded_approx_props (IH (succ γ) Hsγ)) _ _ _ _).
    intros x; cbn. unfold fold_transport, unfold_transport. clear_transports. equalise_pi.
  Qed.

  Lemma me_succ_id γ (Hγ : P γ) (Hsγ : P (succ γ)) (Hlt : γ ≺ succ γ):
    me γ (succ γ) Hγ Hsγ Hlt ≡ fold_transport (msucc_eq γ Hγ Hsγ) ◎ mϕ γ Hγ.
  Proof.
    unfold me, mϕ.
    rewrite (agree_ϕ_nat (IH_agree γ (succ γ) Hγ Hsγ) _ _ _).
    rewrite (approx_e_fold_ϕ (bounded_approx_props (IH (succ γ) Hsγ)) _ _ _ _).
    intros x; cbn. unfold fold_transport, unfold_transport. clear_transports. equalise_pi.
  Qed.

  Lemma mϕ_succ_id γ (Hle : P γ) (Hsle : P (succ γ)):
    mϕ (succ γ) Hsle
    ≡ trunc_map (succ γ) (succ (succ γ))
        (map (mψ γ Hle ◎ unfold_transport (msucc_eq γ Hle Hsle), fold_transport (msucc_eq γ Hle Hsle) ◎ mϕ γ Hle))
      ◎ unfold_transport (msucc_eq γ Hle Hsle).
  Proof using Fcontr.
    unfold mϕ, mψ. rewrite ofe_truncated_equiv. intros x; cbn.
    setoid_rewrite (approx_ϕ_succ_id (bounded_approx_props (IH (succ γ) Hsle)) _ _ _ _).
    cbn. apply ofe_mor_ne.
    setoid_rewrite oFunctor_ne at 2.
    2: { apply pair_ne.
      { rewrite (agree_ψ_nat (IH_agree γ (succ γ) Hle Hsle) _ _ _ ). unfold fold_transport, unfold_transport.
        rewrite !ccompose_assoc. rewrite transport_id_compose. reflexivity. }
      { rewrite (agree_ϕ_nat (IH_agree γ (succ γ) Hle Hsle) _ _ _ ). unfold fold_transport, unfold_transport.
        rewrite <- !ccompose_assoc. rewrite transport_id_compose. reflexivity. }
    }
    cbn.
    do 2 setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
    unfold unfold_transport, fold_transport. equalise_pi_head. do 2 apply ofe_mor_ne.
    setoid_rewrite (transport_id_expand _ _ _ _ _ _ _). cbn. clear_transports. equalise_pi.
    Unshelve. all: eauto with index.
  Qed.

  Lemma mψ_succ_id γ (Hle : P γ) (Hsle : P (succ γ)):
    mψ (succ γ) Hsle
    ≡ fold_transport (msucc_eq γ Hle Hsle)
      ◎ trunc_map (succ (succ γ)) (succ γ)
          (map (fold_transport (msucc_eq γ Hle Hsle) ◎ mϕ γ Hle, mψ γ Hle ◎ unfold_transport (msucc_eq γ Hle Hsle))).
  Proof using Fcontr.
    unfold mψ, mϕ. rewrite ofe_truncated_equiv. intros x; cbn.
    setoid_rewrite (approx_ψ_succ_id (bounded_approx_props (IH (succ γ) Hsle)) _ _ _ _).
    cbn. setoid_rewrite oFunctor_ne at 2.
    2: { apply pair_ne.
      { rewrite (agree_ϕ_nat (IH_agree γ (succ γ) Hle Hsle) _ _ _ ). unfold fold_transport, unfold_transport.
        rewrite <- !ccompose_assoc. rewrite transport_id_compose. rewrite ccompose_assoc. reflexivity. }
      { rewrite (agree_ψ_nat (IH_agree γ (succ γ) Hle Hsle) _ _ _ ). unfold fold_transport, unfold_transport.
        rewrite !ccompose_assoc. rewrite transport_id_compose. rewrite <- ccompose_assoc. reflexivity. }
    }
    cbn. do 2 setoid_rewrite <- (map_compose_dist _ _ _ _ _ _). cbn.
    setoid_rewrite <- (transport_id_truncate_symm _ _ _ _ _ _ _).
    unfold unfold_transport, fold_transport. clear_transports. equalise_pi.
    Unshelve. all: eauto with index.
  Qed.

  Program Definition merged_approx : bounded_approx (P) :=
    {|
      bounded_approx_X := mX;
      bounded_approx_e := me;
      bounded_approx_p := mp;
      bounded_approx_ϕ := mϕ;
      bounded_approx_ψ := mψ;
    |}.
  Next Obligation.
    eexists msucc_eq.
    - apply mp_me_id.
    - apply me_mp_id.
    - apply me_funct.
    - apply mp_funct.
    - apply mψ_mϕ_id.
    - apply mϕ_mψ_id.
    - intros. unfold mX. apply IH.
    - apply Fmemp_mp.
    - apply mp_succ_id.
    - apply me_succ_id.
    - apply mϕ_succ_id.
    - apply mψ_succ_id.
    - apply Fmemp_mp_lim.
  Qed.

  Lemma merged_agree γ Hγ: approx_agree (IH γ Hγ) merged_approx.
  Proof with (unfold fold_transport, unfold_transport; intros x; cbn; clear_transports; equalise_pi).
    assert (X_eq : ∀ (γ0 : SI) (H0 : γ0 ⪯ γ) (H1 : P γ0), projCOFE _ (bounded_approx_X (IH γ Hγ) γ0 H0) = projCOFE _ (mX γ0 H1)).
    { intros. unfold mX. apply agree_eq, IH_agree.  }
    exists X_eq; intros; cbn.
    - rewrite (agree_bcompl_nat (IH_agree γ γ0 Hγ H1) _ _ _ _ _ _).
      unfold fold_transport, unfold_transport. clear_transports. equalise_pi_head. apply ofe_mor_ne. apply bcompl_ne.
      intros. cbn. equalise_pi.
    - unfold me. rewrite (agree_e_nat (IH_agree γ γ1 Hγ Hγ1') _ _ _ _ _ _ _)...
    - unfold mp. rewrite (agree_p_nat (IH_agree γ γ1 Hγ Hγ1') _ _ _ _ _ _ _)...
    - unfold mϕ. rewrite (agree_ϕ_nat (IH_agree γ γ0 Hγ Hγ') _ _ _)...
    - unfold mψ. rewrite (agree_ψ_nat (IH_agree γ γ0 Hγ Hγ') _ _ _)...
  Qed.
End merge.

(* we have to show that merging two coherent & agreeing chains of approximations results in two agreeing approximations *)
Lemma merge_coherent_agree (P : SI → Prop) (IH1 IH2 : ∀ α, P α → bounded_approx (λ γ, γ ⪯ α))
  (H1 : ∀ α0 α1 Hα0 Hα1, approx_agree (IH1 α0 Hα0) (IH1 α1 Hα1))
  (H2 : ∀ α0 α1 Hα0 Hα1, approx_agree (IH2 α0 Hα0) (IH2 α1 Hα1)):
  (∀ α Hα, approx_agree (IH1 α Hα) (IH2 α Hα))
  → approx_agree (merged_approx P IH1 H1) (merged_approx P IH2 H2).
Proof with (unfold fold_transport, unfold_transport; intros x; cbn; clear_transports; equalise_pi).
  intros IH_agree.
  assert (X_eq : ∀ (γ : SI) (H0 H3 : P γ), projCOFE _ (mX P IH1 γ H0) = projCOFE _ (mX P IH2 γ H3)).
  { intros. unfold mX. pi_clear. apply IH_agree. }
  exists X_eq; intros; cbn.
  - repeat pi_clear. rewrite (agree_bcompl_nat (IH_agree γ H3) _ _ _ _ _ _ ).
    unfold fold_transport, unfold_transport. clear_transports. equalise_pi_head. apply ofe_mor_ne. apply bcompl_ne.
    intros; cbn. equalise_pi.
  - unfold me. repeat pi_clear. rewrite (agree_e_nat (IH_agree γ1 Hγ1') _ _ _ _ _ _)...
  - unfold mp. repeat pi_clear. rewrite (agree_p_nat (IH_agree γ1 Hγ1') _ _ _ _ _ _)...
  - unfold mϕ. repeat pi_clear. rewrite (agree_ϕ_nat (IH_agree γ Hγ') _ _ _)...
  - unfold mψ. repeat pi_clear. rewrite (agree_ψ_nat (IH_agree γ Hγ') _ _ _)...
Qed.

(** * Showing uniqueness of the approximations to close the induction *)
Definition full_approximation : bounded_approx (λ _, True).
Proof using inh_Funit Funique Fcontr.
  unshelve eapply (full_A_transfinite SI (@bounded_approx) (@approx_agree) _ _ _ _ (@extension) (@extension_agree) (@extended_approx) _ _ (@merged_approx)).
  - intros. unshelve eexists. all: intros; exfalso; by eapply H.
  - eapply approx_agree_transitive.
  - apply approx_agree_symmetric.
  - apply approx_agree_reflexive.
  - apply extended_approx_agree.
  - apply extension_coherent.
  - apply succ_extension.
  - apply limit_extension.
  - intros. apply merged_agree.
  - apply merge_coherent_agree.
  - apply approx_base.
  - apply succ_extension_coherent.
  - apply limit_extension_coherent.
Qed.

Definition solution_F := pre_solution_F full_approximation.
End solver. End solver.
(*Print Assumptions solver.solution_F. *)
