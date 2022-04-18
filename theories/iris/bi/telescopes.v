From stdpp Require Export telescopes.
From iris.bi Require Export bi.
Set Default Proof Using "Type*".
Import bi.

(* This cannot import the proofmode because it is imported by the proofmode! *)

(** Telescopic quantifiers *)
Definition bi_texist {SI} {PROP : bi SI} {TT : tele} (Ψ : TT → PROP) : PROP :=
  tele_fold (@bi_exist SI PROP) (λ x, x) (tele_bind Ψ).
Arguments bi_texist {_ _ !_} _ /.
Definition bi_tforall {SI} {PROP : bi SI} {TT : tele} (Ψ : TT → PROP) : PROP :=
  tele_fold (@bi_forall SI PROP) (λ x, x) (tele_bind Ψ).
Arguments bi_tforall {_ _ !_} _ /.

Notation "'∃..' x .. y , P" := (bi_texist (λ x, .. (bi_texist (λ y, P)) .. )%I)
  (at level 200, x binder, y binder, right associativity,
  format "∃..  x  ..  y ,  P") : bi_scope.
Notation "'∀..' x .. y , P" := (bi_tforall (λ x, .. (bi_tforall (λ y, P)) .. )%I)
  (at level 200, x binder, y binder, right associativity,
  format "∀..  x  ..  y ,  P") : bi_scope.

Section telescope_quantifiers.
  Context {SI} {PROP : bi SI} {TT : tele}.

  Lemma bi_tforall_forall (Ψ : TT → PROP) :
    bi_tforall Ψ ⊣⊢ bi_forall Ψ.
  Proof.
    symmetry. unfold bi_tforall. induction TT as [|X ft IH].
    - simpl. apply (anti_symm _).
      + by rewrite (forall_elim TargO).
      + rewrite -forall_intro; first done.
        intros p. rewrite (tele_arg_O_inv p) /= //.
    - simpl. apply (anti_symm _); apply forall_intro; intros a.
      + rewrite /= -IH. apply forall_intro; intros p.
        by rewrite (forall_elim (TargS a p)).
      + move/tele_arg_inv : (a) => [x [pf ->]] {a} /=.
        setoid_rewrite <- IH.
        rewrite 2!forall_elim. done.
  Qed.

  Lemma bi_texist_exist (Ψ : TT → PROP) :
    bi_texist Ψ ⊣⊢ bi_exist Ψ.
  Proof.
    symmetry. unfold bi_texist. induction TT as [|X ft IH].
    - simpl. apply (anti_symm _).
      + apply exist_elim; intros p.
        rewrite (tele_arg_O_inv p) //.
      + by rewrite -(exist_intro TargO).
    - simpl. apply (anti_symm _); apply exist_elim.
      + intros p. move/tele_arg_inv: (p) => [x [pf ->]] {p} /=.
        by rewrite -exist_intro -IH -exist_intro.
      + intros x.
        rewrite /= -IH. apply exist_elim; intros p.
        by rewrite -(exist_intro (TargS x p)).
  Qed.

  Global Instance bi_tforall_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_tforall SI PROP TT).
  Proof.
    intros ?? EQ. rewrite !bi_tforall_forall. rewrite EQ //.
  Qed.

  Global Instance bi_tforall_proper :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_tforall SI PROP TT).
  Proof.
    intros ?? EQ. rewrite !bi_tforall_forall. rewrite EQ //.
  Qed.

  Global Instance bi_texist_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_texist SI PROP TT).
  Proof.
    intros ?? EQ. rewrite !bi_texist_exist. rewrite EQ //.
  Qed.

  Global Instance bi_texist_proper :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_texist SI PROP TT).
  Proof.
    intros ?? EQ. rewrite !bi_texist_exist. rewrite EQ //.
  Qed.

End telescope_quantifiers.
