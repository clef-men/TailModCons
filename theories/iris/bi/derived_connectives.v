From iris.bi Require Export interface.
From iris.algebra Require Import monoid.

Definition bi_iff `{PROP : bi SI} (P Q : PROP) : PROP := ((P → Q) ∧ (Q → P))%I.
Arguments bi_iff {_ _} _%I _%I : simpl never.
Instance: Params (@bi_iff) 2 := {}.
Infix "↔" := bi_iff : bi_scope.

Definition bi_wand_iff `{PROP : bi SI} (P Q : PROP) : PROP :=
  ((P -∗ Q) ∧ (Q -∗ P))%I.
Arguments bi_wand_iff {_ _} _%I _%I : simpl never.
Instance: Params (@bi_wand_iff) 2 := {}.
Infix "∗-∗" := bi_wand_iff : bi_scope.

Class Persistent `{PROP : bi SI} (P : PROP) := persistent : P ⊢ <pers> P.
Arguments Persistent {_ _} _%I : simpl never.
Arguments persistent {_ _} _%I {_}.
Hint Mode Persistent - + ! : typeclass_instances.
Instance: Params (@Persistent) 2 := {}.

Definition bi_affinely `{PROP : bi SI} (P : PROP) : PROP := (emp ∧ P)%I.
Arguments bi_affinely {_ _} _%I : simpl never.
Instance: Params (@bi_affinely) 2 := {}.
Typeclasses Opaque bi_affinely.
Notation "'<affine>' P" := (bi_affinely P) : bi_scope.

Class Affine `{PROP : bi SI} (Q : PROP) := affine : Q ⊢ emp.
Arguments Affine {_ _} _%I : simpl never.
Arguments affine {_ _} _%I {_}.
Hint Mode Affine - + ! : typeclass_instances.

Class BiAffine `(PROP : bi SI) := absorbing_bi (Q : PROP) : Affine Q.
Hint Mode BiAffine - ! : typeclass_instances.
Existing Instance absorbing_bi | 0.

Class BiPositive `(PROP : bi SI) :=
  bi_positive (P Q : PROP) : <affine> (P ∗ Q) ⊢ <affine> P ∗ Q.
Hint Mode BiPositive - ! : typeclass_instances.

Definition bi_absorbingly `{PROP : bi SI} (P : PROP) : PROP := (True ∗ P)%I.
Arguments bi_absorbingly {_ _} _%I : simpl never.
Instance: Params (@bi_absorbingly) 2 := {}.
Typeclasses Opaque bi_absorbingly.
Notation "'<absorb>' P" := (bi_absorbingly P) : bi_scope.

Class Absorbing `{PROP : bi SI} (P : PROP) := absorbing : <absorb> P ⊢ P.
Arguments Absorbing {_ _} _%I : simpl never.
Arguments absorbing {_ _} _%I.
Hint Mode Absorbing - + ! : typeclass_instances.

Definition bi_persistently_if `{PROP : bi SI} (p : bool) (P : PROP) : PROP :=
  (if p then <pers> P else P)%I.
Arguments bi_persistently_if {_ _} !_ _%I /.
Instance: Params (@bi_persistently_if) 3 := {}.
Typeclasses Opaque bi_persistently_if.
Notation "'<pers>?' p P" := (bi_persistently_if p P) : bi_scope.

Definition bi_affinely_if `{PROP : bi SI} (p : bool) (P : PROP) : PROP :=
  (if p then <affine> P else P)%I.
Arguments bi_affinely_if {_ _} !_ _%I /.
Instance: Params (@bi_affinely_if) 3 := {}.
Typeclasses Opaque bi_affinely_if.
Notation "'<affine>?' p P" := (bi_affinely_if p P) : bi_scope.

Definition bi_absorbingly_if `{PROP : bi SI} (p : bool) (P : PROP) : PROP :=
  (if p then <absorb> P else P)%I.
Arguments bi_absorbingly_if {_ _} !_ _%I /.
Instance: Params (@bi_absorbingly_if) 3 := {}.
Typeclasses Opaque bi_absorbingly_if.
Notation "'<absorb>?' p P" := (bi_absorbingly_if p P) : bi_scope.

Definition bi_intuitionistically `{PROP : bi SI} (P : PROP) : PROP :=
  (<affine> <pers> P)%I.
Arguments bi_intuitionistically {_ _} _%I : simpl never.
Instance: Params (@bi_intuitionistically) 2 := {}.
Typeclasses Opaque bi_intuitionistically.
Notation "□ P" := (bi_intuitionistically P) : bi_scope.

Definition bi_intuitionistically_if `{PROP : bi SI} (p : bool) (P : PROP) : PROP :=
  (if p then □ P else P)%I.
Arguments bi_intuitionistically_if {_ _} !_ _%I /.
Instance: Params (@bi_intuitionistically_if) 3 := {}.
Typeclasses Opaque bi_intuitionistically_if.
Notation "'□?' p P" := (bi_intuitionistically_if p P) : bi_scope.

Definition sbi_except_0 `{PROP : sbi SI} (P : PROP) : PROP := (▷ False ∨ P)%I.
Arguments sbi_except_0 {_ _} _%I : simpl never.
Notation "◇ P" := (sbi_except_0 P) : bi_scope.
Instance: Params (@sbi_except_0) 2 := {}.
Typeclasses Opaque sbi_except_0.

Class Timeless `{PROP : sbi SI} (P : PROP) := timeless : ▷ P ⊢ ◇ P.
Arguments Timeless {_ _} _%I : simpl never.
Arguments timeless {_ _} _%I {_}.
Hint Mode Timeless - + ! : typeclass_instances.
Instance: Params (@Timeless) 2 := {}.

(** An optional precondition [mP] to [Q].
    TODO: We may actually consider generalizing this to a list of preconditions,
    and e.g. also using it for texan triples. *)
Definition bi_wandM `{PROP : bi SI} (mP : option PROP) (Q : PROP) : PROP :=
  match mP with
  | None => Q
  | Some P => (P -∗ Q)%I
  end.
Arguments bi_wandM {_ _} !_%I _%I /.
Notation "mP -∗? Q" := (bi_wandM mP Q)
  (at level 99, Q at level 200, right associativity) : bi_scope.
