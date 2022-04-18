From iris.algebra Require Import monoid.
From iris.bi Require Import interface derived_laws_sbi big_op plainly updates.

Class Embed (A B : Type) := embed : A → B.
Arguments embed {_ _ _} _%I : simpl never.
Notation "⎡ P ⎤" := (embed P) : bi_scope.
Instance: Params (@embed) 3 := {}.
Typeclasses Opaque embed.

Hint Mode Embed ! - : typeclass_instances.
Hint Mode Embed - ! : typeclass_instances.

(* Mixins allow us to create instances easily without having to use Program *)
Record BiEmbedMixin {SI} (PROP1 PROP2 : bi SI) `(Embed PROP1 PROP2) := {
  bi_embed_mixin_ne : NonExpansive (embed (A:=PROP1) (B:=PROP2));
  bi_embed_mixin_mono : Proper ((⊢) ==> (⊢)) (embed (A:=PROP1) (B:=PROP2));
  bi_embed_mixin_emp_valid_inj (P : PROP1) :
    bi_emp_valid (PROP:=PROP2) ⎡P⎤ → bi_emp_valid P;
  bi_embed_mixin_emp_2 : emp ⊢@{PROP2} ⎡emp⎤;
  bi_embed_mixin_impl_2 (P Q : PROP1) :
    (⎡P⎤ → ⎡Q⎤) ⊢@{PROP2} ⎡P → Q⎤;
  bi_embed_mixin_forall_2 A (Φ : A → PROP1) :
    (∀ x, ⎡Φ x⎤) ⊢@{PROP2} ⎡∀ x, Φ x⎤;
  bi_embed_mixin_exist_1 A (Φ : A → PROP1) :
    ⎡∃ x, Φ x⎤ ⊢@{PROP2} ∃ x, ⎡Φ x⎤;
  bi_embed_mixin_sep (P Q : PROP1) :
    ⎡P ∗ Q⎤ ⊣⊢@{PROP2} ⎡P⎤ ∗ ⎡Q⎤;
  bi_embed_mixin_wand_2 (P Q : PROP1) :
    (⎡P⎤ -∗ ⎡Q⎤) ⊢@{PROP2} ⎡P -∗ Q⎤;
  bi_embed_mixin_persistently (P : PROP1) :
    ⎡<pers> P⎤ ⊣⊢@{PROP2} <pers> ⎡P⎤
}.

Class BiEmbed {SI} (PROP1 PROP2 : bi SI) := {
  bi_embed_embed :> Embed PROP1 PROP2;
  bi_embed_mixin : BiEmbedMixin PROP1 PROP2 bi_embed_embed;
}.
Hint Mode BiEmbed - ! - : typeclass_instances.
Hint Mode BiEmbed - - ! : typeclass_instances.
Arguments bi_embed_embed : simpl never.

Class BiEmbedEmp {SI} (PROP1 PROP2 : bi SI) `{BiEmbed SI PROP1 PROP2} := {
  embed_emp_1 : ⎡ emp : PROP1 ⎤ ⊢ emp;
}.
Hint Mode BiEmbedEmp - ! - - : typeclass_instances.
Hint Mode BiEmbedEmp - - ! - : typeclass_instances.

Class SbiEmbed {SI} (PROP1 PROP2 : sbi SI) `{BiEmbed SI PROP1 PROP2} := {
  embed_internal_eq_1 (A : ofeT SI) (x y : A) : ⎡x ≡ y⎤ ⊢ x ≡ y;
  embed_later P : ⎡▷ P⎤ ⊣⊢ ▷ ⎡P⎤;
  embed_interal_inj (PROP' : sbi SI) (P Q : PROP1) : ⎡P⎤ ≡ ⎡Q⎤ ⊢@{PROP'} (P ≡ Q);
}.
Hint Mode SbiEmbed - ! - - : typeclass_instances.
Hint Mode SbiEmbed - - ! - : typeclass_instances.

Class BiEmbedBUpd {SI} (PROP1 PROP2 : bi SI)
      `{BiEmbed SI PROP1 PROP2, BiBUpd SI PROP1, BiBUpd SI PROP2} := {
  embed_bupd  P : ⎡|==> P⎤ ⊣⊢@{PROP2} |==> ⎡P⎤
}.
Hint Mode BiEmbedBUpd - - ! - - - : typeclass_instances.
Hint Mode BiEmbedBUpd - ! - - - - : typeclass_instances.

Class BiEmbedFUpd {SI} (PROP1 PROP2 : sbi SI)
      `{BiEmbed SI PROP1 PROP2, BiFUpd SI PROP1, BiFUpd SI PROP2} := {
  embed_fupd E1 E2 P : ⎡|={E1,E2}=> P⎤ ⊣⊢@{PROP2} |={E1,E2}=> ⎡P⎤
}.
Hint Mode BiEmbedFUpd - - ! - - - : typeclass_instances.
Hint Mode BiEmbedFUpd - ! - - - - : typeclass_instances.

Class BiEmbedPlainly {SI} (PROP1 PROP2 : sbi SI)
      `{BiEmbed SI PROP1 PROP2, BiPlainly SI PROP1, BiPlainly SI PROP2} := {
  embed_plainly_2 (P : PROP1) : ■ ⎡P⎤ ⊢ (⎡■ P⎤ : PROP2)
}.
Hint Mode BiEmbedPlainly - - ! - - - : typeclass_instances.
Hint Mode BiEmbedPlainly - ! - - - - : typeclass_instances.

Section embed_laws.
  Context {SI} `{BiEmbed SI PROP1 PROP2}.
  Local Notation embed := (embed (A:=PROP1) (B:=PROP2)).
  Local Notation "⎡ P ⎤" := (embed P) : bi_scope.
  Implicit Types P : PROP1.

  Global Instance embed_ne : NonExpansive embed.
  Proof. eapply bi_embed_mixin_ne, bi_embed_mixin. Qed.
  Global Instance embed_mono : Proper ((⊢) ==> (⊢)) embed.
  Proof. eapply bi_embed_mixin_mono, bi_embed_mixin. Qed.
  Lemma embed_emp_valid_inj P : (bi_emp_valid ⎡P⎤)%I → bi_emp_valid P.
  Proof. eapply bi_embed_mixin_emp_valid_inj, bi_embed_mixin. Qed.
  Lemma embed_emp_2 : emp ⊢ ⎡emp⎤.
  Proof. eapply bi_embed_mixin_emp_2, bi_embed_mixin. Qed.
  Lemma embed_impl_2 P Q : (⎡P⎤ → ⎡Q⎤) ⊢ ⎡P → Q⎤.
  Proof. eapply bi_embed_mixin_impl_2, bi_embed_mixin. Qed.
  Lemma embed_forall_2 A (Φ : A → PROP1) : (∀ x, ⎡Φ x⎤) ⊢ ⎡∀ x, Φ x⎤.
  Proof. eapply bi_embed_mixin_forall_2, bi_embed_mixin. Qed.
  Lemma embed_exist_1 A (Φ : A → PROP1) : ⎡∃ x, Φ x⎤ ⊢ ∃ x, ⎡Φ x⎤.
  Proof. eapply bi_embed_mixin_exist_1, bi_embed_mixin. Qed.
  Lemma embed_sep P Q : ⎡P ∗ Q⎤ ⊣⊢ ⎡P⎤ ∗ ⎡Q⎤.
  Proof. eapply bi_embed_mixin_sep, bi_embed_mixin. Qed.
  Lemma embed_wand_2 P Q : (⎡P⎤ -∗ ⎡Q⎤) ⊢ ⎡P -∗ Q⎤.
  Proof. eapply bi_embed_mixin_wand_2, bi_embed_mixin. Qed.
  Lemma embed_persistently P : ⎡<pers> P⎤ ⊣⊢ <pers> ⎡P⎤.
  Proof. eapply bi_embed_mixin_persistently, bi_embed_mixin. Qed.
End embed_laws.

Section embed.
  Context `{BiEmbed SI PROP1 PROP2}.
  Local Notation embed := (embed (A:=PROP1) (B:=PROP2)).
  Local Notation "⎡ P ⎤" := (embed P) : bi_scope.
  Implicit Types P Q R : PROP1.

  Global Instance embed_proper : Proper ((≡) ==> (≡)) embed.
  Proof. apply (ne_proper _). Qed.
  Global Instance embed_flip_mono : Proper (flip (⊢) ==> flip (⊢)) embed.
  Proof. solve_proper. Qed.
  Global Instance embed_entails_inj : Inj (⊢) (⊢) embed.
  Proof.
    move=> P Q /bi.entails_wand. rewrite embed_wand_2.
    by move=> /embed_emp_valid_inj /bi.wand_entails.
  Qed.

  Global Instance embed_inj : Inj (≡) (≡) embed.
  Proof.
    intros P Q EQ. apply bi.equiv_spec, conj; apply (inj embed); rewrite EQ //.
  Qed.

  Lemma embed_emp_valid (P : PROP1) : (bi_emp_valid ⎡P⎤%I) ↔ (bi_emp_valid P).
  Proof.
    rewrite /bi_emp_valid. split=> HP.
    - by apply embed_emp_valid_inj.
    - by rewrite embed_emp_2 HP.
  Qed.

  Lemma embed_emp `{!BiEmbedEmp PROP1 PROP2} : ⎡ emp ⎤ ⊣⊢ emp.
  Proof. apply (anti_symm _); eauto using embed_emp_1, embed_emp_2. Qed.

  Lemma embed_forall A (Φ : A → PROP1) : ⎡∀ x, Φ x⎤ ⊣⊢ ∀ x, ⎡Φ x⎤.
  Proof.
    apply bi.equiv_spec; split; [|apply embed_forall_2].
    apply bi.forall_intro=>?. by rewrite bi.forall_elim.
  Qed.
  Lemma embed_exist A (Φ : A → PROP1) : ⎡∃ x, Φ x⎤ ⊣⊢ ∃ x, ⎡Φ x⎤.
  Proof.
    apply bi.equiv_spec; split; [apply embed_exist_1|].
    apply bi.exist_elim=>?. by rewrite -bi.exist_intro.
  Qed.
  Lemma embed_and P Q : ⎡P ∧ Q⎤ ⊣⊢ ⎡P⎤ ∧ ⎡Q⎤.
  Proof. rewrite !bi.and_alt embed_forall. by f_equiv=>-[]. Qed.
  Lemma embed_or P Q : ⎡P ∨ Q⎤ ⊣⊢ ⎡P⎤ ∨ ⎡Q⎤.
  Proof. rewrite !bi.or_alt embed_exist. by f_equiv=>-[]. Qed.
  Lemma embed_impl P Q : ⎡P → Q⎤ ⊣⊢ (⎡P⎤ → ⎡Q⎤).
  Proof.
    apply bi.equiv_spec; split; [|apply embed_impl_2].
    apply bi.impl_intro_l. by rewrite -embed_and bi.impl_elim_r.
  Qed.
  Lemma embed_wand P Q : ⎡P -∗ Q⎤ ⊣⊢ (⎡P⎤ -∗ ⎡Q⎤).
  Proof.
    apply bi.equiv_spec; split; [|apply embed_wand_2].
    apply bi.wand_intro_l. by rewrite -embed_sep bi.wand_elim_r.
  Qed.
  Lemma embed_pure φ : ⎡⌜φ⌝⎤ ⊣⊢ ⌜φ⌝.
  Proof.
    rewrite (@bi.pure_alt SI PROP1) (@bi.pure_alt SI PROP2) embed_exist.
    do 2 f_equiv. apply bi.equiv_spec. split; [apply bi.True_intro|].
    rewrite -(_ : (emp → emp : PROP1) ⊢ True) ?embed_impl;
      last apply bi.True_intro.
    apply bi.impl_intro_l. by rewrite right_id.
  Qed.

  Lemma embed_iff P Q : ⎡P ↔ Q⎤ ⊣⊢ (⎡P⎤ ↔ ⎡Q⎤).
  Proof. by rewrite embed_and !embed_impl. Qed.
  Lemma embed_wand_iff P Q : ⎡P ∗-∗ Q⎤ ⊣⊢ (⎡P⎤ ∗-∗ ⎡Q⎤).
  Proof. by rewrite embed_and !embed_wand. Qed.
  Lemma embed_affinely_2 P : <affine> ⎡P⎤ ⊢ ⎡<affine> P⎤.
  Proof. by rewrite embed_and -embed_emp_2. Qed.
  Lemma embed_affinely `{!BiEmbedEmp PROP1 PROP2} P : ⎡<affine> P⎤ ⊣⊢ <affine> ⎡P⎤.
  Proof. by rewrite /bi_intuitionistically embed_and embed_emp. Qed.
  Lemma embed_absorbingly P : ⎡<absorb> P⎤ ⊣⊢ <absorb> ⎡P⎤.
  Proof. by rewrite embed_sep embed_pure. Qed.
  Lemma embed_intuitionistically_2 P : □ ⎡P⎤ ⊢ ⎡□ P⎤.
  Proof. by rewrite /bi_intuitionistically -embed_affinely_2 embed_persistently. Qed.
  Lemma embed_intuitionistically `{!BiEmbedEmp PROP1 PROP2} P : ⎡□ P⎤ ⊣⊢ □ ⎡P⎤.
  Proof. by rewrite /bi_intuitionistically embed_affinely embed_persistently. Qed.

  Lemma embed_persistently_if P b : ⎡<pers>?b P⎤ ⊣⊢ <pers>?b ⎡P⎤.
  Proof. destruct b; simpl; auto using embed_persistently. Qed.
  Lemma embed_affinely_if_2 P b : <affine>?b ⎡P⎤ ⊢ ⎡<affine>?b P⎤.
  Proof. destruct b; simpl; auto using embed_affinely_2. Qed.
  Lemma embed_affinely_if `{!BiEmbedEmp PROP1 PROP2} P b :
    ⎡<affine>?b P⎤ ⊣⊢ <affine>?b ⎡P⎤.
  Proof. destruct b; simpl; auto using embed_affinely. Qed.
  Lemma embed_absorbingly_if b P : ⎡<absorb>?b P⎤ ⊣⊢ <absorb>?b ⎡P⎤.
  Proof. destruct b; simpl; auto using embed_absorbingly. Qed.
  Lemma embed_intuitionistically_if_2 P b : □?b ⎡P⎤ ⊢ ⎡□?b P⎤.
  Proof. destruct b; simpl; auto using embed_intuitionistically_2. Qed.
  Lemma embed_intuitionistically_if `{!BiEmbedEmp PROP1 PROP2} P b :
    ⎡□?b P⎤ ⊣⊢ □?b ⎡P⎤.
  Proof. destruct b; simpl; auto using embed_intuitionistically. Qed.

  Global Instance embed_persistent P : Persistent P → Persistent ⎡P⎤.
  Proof. intros ?. by rewrite /Persistent -embed_persistently -persistent. Qed.
  Global Instance embed_affine `{!BiEmbedEmp PROP1 PROP2} P : Affine P → Affine ⎡P⎤.
  Proof. intros ?. by rewrite /Affine (affine P) embed_emp. Qed.
  Global Instance embed_absorbing P : Absorbing P → Absorbing ⎡P⎤.
  Proof. intros ?. by rewrite /Absorbing -embed_absorbingly absorbing. Qed.

  Global Instance embed_and_homomorphism :
    MonoidHomomorphism bi_and bi_and (≡) embed.
  Proof.
    by split; [split|]; try apply _;
      [setoid_rewrite embed_and|rewrite embed_pure].
  Qed.
  Global Instance embed_or_homomorphism :
    MonoidHomomorphism bi_or bi_or (≡) embed.
  Proof.
    by split; [split|]; try apply _;
      [setoid_rewrite embed_or|rewrite embed_pure].
  Qed.

  Global Instance embed_sep_entails_homomorphism :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) embed.
  Proof.
    split; [split|]; simpl; try apply _;
      [by setoid_rewrite embed_sep|by rewrite embed_emp_2].
  Qed.

  Lemma embed_big_sepL_2 {A} (Φ : nat → A → PROP1) l :
    ([∗ list] k↦x ∈ l, ⎡Φ k x⎤) ⊢ ⎡[∗ list] k↦x ∈ l, Φ k x⎤.
  Proof. apply (big_opL_commute (R:=flip (⊢)) _). Qed.
  Lemma embed_big_sepM_2 `{Countable K} {A} (Φ : K → A → PROP1) (m : gmap K A) :
    ([∗ map] k↦x ∈ m, ⎡Φ k x⎤) ⊢ ⎡[∗ map] k↦x ∈ m, Φ k x⎤.
  Proof. apply (big_opM_commute (R:=flip (⊢)) _). Qed.
  Lemma embed_big_sepS_2 `{Countable A} (Φ : A → PROP1) (X : gset A) :
    ([∗ set] y ∈ X, ⎡Φ y⎤) ⊢ ⎡[∗ set] y ∈ X, Φ y⎤.
  Proof. apply (big_opS_commute (R:=flip (⊢)) _). Qed.
  Lemma embed_big_sepMS_2 `{Countable A} (Φ : A → PROP1) (X : gmultiset A) :
    ([∗ mset] y ∈ X, ⎡Φ y⎤) ⊢ ⎡[∗ mset] y ∈ X, Φ y⎤.
  Proof. apply (big_opMS_commute (R:=flip (⊢)) _). Qed.

  Section big_ops_emp.
    Context `{!BiEmbedEmp PROP1 PROP2}.

    Global Instance embed_sep_homomorphism :
      MonoidHomomorphism bi_sep bi_sep (≡) embed.
    Proof.
      by split; [split|]; try apply _;
        [setoid_rewrite embed_sep|rewrite embed_emp].
    Qed.

    Lemma embed_big_sepL {A} (Φ : nat → A → PROP1) l :
      ⎡[∗ list] k↦x ∈ l, Φ k x⎤ ⊣⊢ [∗ list] k↦x ∈ l, ⎡Φ k x⎤.
    Proof. apply (big_opL_commute _). Qed.
    Lemma embed_big_sepM `{Countable K} {A} (Φ : K → A → PROP1) (m : gmap K A) :
      ⎡[∗ map] k↦x ∈ m, Φ k x⎤ ⊣⊢ [∗ map] k↦x ∈ m, ⎡Φ k x⎤.
    Proof. apply (big_opM_commute _). Qed.
    Lemma embed_big_sepS `{Countable A} (Φ : A → PROP1) (X : gset A) :
      ⎡[∗ set] y ∈ X, Φ y⎤ ⊣⊢ [∗ set] y ∈ X, ⎡Φ y⎤.
    Proof. apply (big_opS_commute _). Qed.
    Lemma embed_big_sepMS `{Countable A} (Φ : A → PROP1) (X : gmultiset A) :
      ⎡[∗ mset] y ∈ X, Φ y⎤ ⊣⊢ [∗ mset] y ∈ X, ⎡Φ y⎤.
    Proof. apply (big_opMS_commute _). Qed.
  End big_ops_emp.
End embed.

Section sbi_embed.
  Context `{SbiEmbed SI PROP1 PROP2}.
  Implicit Types P Q R : PROP1.

  Lemma embed_internal_eq (A : ofeT SI) (x y : A) : ⎡x ≡ y⎤ ⊣⊢ x ≡ y.
  Proof.
    apply bi.equiv_spec; split; [apply embed_internal_eq_1|].
    etrans; [apply (bi.internal_eq_rewrite x y (λ y, ⎡x ≡ y⎤%I)); solve_proper|].
    rewrite -(bi.internal_eq_refl True%I) embed_pure.
    eapply bi.impl_elim; [done|]. apply bi.True_intro.
  Qed.
  Lemma embed_laterN n P : ⎡▷^n P⎤ ⊣⊢ ▷^n ⎡P⎤.
  Proof. induction n=>//=. rewrite embed_later. by f_equiv. Qed.
  Lemma embed_except_0 P : ⎡◇ P⎤ ⊣⊢ ◇ ⎡P⎤.
  Proof. by rewrite embed_or embed_later embed_pure. Qed.

  (* Not an instance, since it may cause overlap *)
  Lemma bi_embed_plainly_emp `{!BiPlainly PROP1, !BiPlainly PROP2} :
    BiEmbedEmp PROP1 PROP2 → BiEmbedPlainly PROP1 PROP2.
  Proof.
    intros. constructor=> P. rewrite !plainly_alt embed_internal_eq.
    by rewrite -embed_affinely -embed_emp embed_interal_inj.
  Qed.

  Lemma embed_plainly_1 `{!BiPlainly PROP1, !BiPlainly PROP2} P : ⎡■ P⎤ ⊢ ■ ⎡P⎤.
  Proof.
    assert (∀ P, <affine> ⎡ P ⎤ ⊣⊢ (<affine> ⎡ <affine> P ⎤ : PROP2)) as Hhelp.
    { intros P'. apply (anti_symm _).
      - by rewrite -bi.affinely_idemp (embed_affinely_2 P').
      - by rewrite (bi.affinely_elim P'). }
    assert (<affine> ⎡ emp ⎤ ⊣⊢ (emp : PROP2)) as Hemp.
    { apply (anti_symm _).
      - apply bi.affinely_elim_emp.
      - apply bi.and_intro; auto using embed_emp_2. }
    rewrite !plainly_alt embed_internal_eq. by rewrite Hhelp -Hemp -!bi.f_equiv.
  Qed.
  Lemma embed_plainly `{!BiPlainly PROP1, !BiPlainly PROP2,
    !BiEmbedPlainly PROP1 PROP2} P : ⎡■ P⎤ ⊣⊢ ■ ⎡P⎤.
  Proof.
    apply (anti_symm _). by apply embed_plainly_1. by apply embed_plainly_2.
  Qed.

  Lemma embed_plainly_if `{!BiPlainly PROP1, !BiPlainly PROP2,
    !BiEmbedPlainly PROP1 PROP2} p P : ⎡■?p P⎤ ⊣⊢ ■?p ⎡P⎤.
  Proof. destruct p; simpl; auto using embed_plainly. Qed.
  Lemma embed_plainly_if_1 `{!BiPlainly PROP1, !BiPlainly PROP2} p P :
    ⎡■?p P⎤ ⊢ ■?p ⎡P⎤.
  Proof. destruct p; simpl; auto using embed_plainly_1. Qed.

  Lemma embed_plain `{!BiPlainly PROP1, !BiPlainly PROP2} (P : PROP1) :
    Plain P → Plain (PROP:=PROP2) ⎡P⎤.
  Proof. intros ?. by rewrite /Plain {1}(plain P) embed_plainly_1. Qed.

  Global Instance embed_timeless P : Timeless P → Timeless ⎡P⎤.
  Proof.
    intros ?. by rewrite /Timeless -embed_except_0 -embed_later timeless.
  Qed.
End sbi_embed.

(* Not defined using an ordinary [Instance] because the default
[class_apply @bi_embed_plainly] shelves the [BiPlainly] premise, making proof
search for the other premises fail. See the proof of [monPred_objectively_plain]
for an example where it would fail with a regular [Instance].*)
Hint Extern 4 (Plain ⎡_⎤) => eapply @embed_plain : typeclass_instances.
