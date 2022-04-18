From stdpp Require Export coPset.
From iris.program_logic Require Import language.
From iris.bi Require Import interface derived_connectives.

Inductive stuckness := NotStuck | MaybeStuck.

Definition stuckness_leb (s1 s2 : stuckness) : bool :=
  match s1, s2 with
  | MaybeStuck, NotStuck => false
  | _, _ => true
  end.
Instance stuckness_le : SqSubsetEq stuckness := stuckness_leb.
Instance stuckness_le_po : PreOrder stuckness_le.
Proof. split; by repeat intros []. Qed.

Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  if s is MaybeStuck then StronglyAtomic else WeaklyAtomic.

(** Weakest preconditions [WP e @ s ; E {{ Φ }}] have an additional argument [s]
of arbitrary type [A], that can be chosen by the one instantiating the [Wp] type
class. This argument can be used for e.g. the stuckness bit (as in Iris) or
thread IDs (as in iGPS).

For the case of stuckness bits, there are two specific notations
[WP e @ E {{ Φ }}] and [WP e @ E ?{{ Φ }}], which forces [A] to be [stuckness],
and [s] to be [NotStuck] or [MaybeStuck].  This will fail to typecheck if [A] is
not [stuckness].  If we ever want to use the notation [WP e @ E {{ Φ }}] with a
different [A], the plan is to generalize the notation to use [Inhabited] instead
to pick a default value depending on [A]. *)
Class Wp (Λ : language) (PROP A : Type) :=
  wp : A → coPset → expr Λ → (val Λ → PROP) → PROP.
Arguments wp {_ _ _ _} _ _ _%E _%I.
Instance: Params (@wp) 7 := {}.

Class Swp (Λ : language) (PROP A : Type) :=
  swp : nat → A → coPset → expr Λ → (val Λ → PROP) → PROP.
Arguments swp  {_ _ _ _} _ _ _%E _%I.
Instance: Params (@swp) 8 := {}.

Class Twp (Λ : language) (PROP A : Type) :=
  twp : A → coPset → expr Λ → (val Λ → PROP) → PROP.
Arguments twp {_ _ _ _} _ _ _%E _%I.
Instance: Params (@twp) 7 := {}.

Class Rwp (Λ : language) (PROP A : Type) :=
  rwp : A → coPset → expr Λ → (val Λ → PROP) → PROP.
Arguments rwp {_ _ _ _} _ _ _%E _%I.
Instance: Params (@rwp) 7 := {}.

Class Rswp (Λ : language) (PROP A : Type) :=
  rswp : nat → A → coPset → expr Λ → (val Λ → PROP) → PROP.
Arguments rswp {_ _ _ _} _ _ _ _%E _%I.
Instance: Params (@rswp) 8 := {}.

(** Notations for partial weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WP' e @ s ; E {{ Φ } }" := (wp s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E {{ Φ } }" := (wp NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E ? {{ Φ } }" := (wp MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e {{ Φ } }" := (wp NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e ? {{ Φ } }" := (wp MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'WP' e @ s ; E {{ v , Q } }" := (wp s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[          ' @  s ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e @ E {{ v , Q } }" := (wp NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[       ' @  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e @ E ? {{ v , Q } }" := (wp MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[        ' @  E  ? {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e {{ v , Q } }" := (wp NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[   ' {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e ? {{ v , Q } }" := (wp MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[    ' ? {{  v ,  Q  } } ']' ']'") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  s ;  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  x  ..  y ,   RET  pat ;  Q  } } } ']'") : bi_scope.

Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  s ;  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }}) : stdpp_scope.

(** Notations for total weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WP' e @ s ; E [{ Φ } ]" := (twp s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E [{ Φ } ]" := (twp NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E ? [{ Φ } ]" := (twp MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e [{ Φ } ]" := (twp NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e ? [{ Φ } ]" := (twp MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'WP' e @ s ; E [{ v , Q } ]" := (twp s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[          ' @  s ;  E  [{  v ,  Q  } ] ']' ']'") : bi_scope.
Notation "'WP' e @ E [{ v , Q } ]" := (twp NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[       ' @  E  [{  v ,  Q  } ] ']' ']'") : bi_scope.
Notation "'WP' e @ E ? [{ v , Q } ]" := (twp MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[        ' @  E  ? [{  v ,  Q  } ] ']' ']'") : bi_scope.
Notation "'WP' e [{ v , Q } ]" := (twp NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[   ' [{  v ,  Q  } ] ']' ']'") : bi_scope.
Notation "'WP' e ? [{ v , Q } ]" := (twp MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[    ' ? [{  v ,  Q  } ] ']' ']'") : bi_scope.

(* Texan triples *)
Notation "'[[{' P } ] ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  s ;  E  [[{  x  ..  y ,  RET  pat ;  Q  } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  E  [[{  x  ..  y ,  RET  pat ;  Q  } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?[{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  E  ? [[{  x  ..  y ,  RET  pat ;  Q  } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' [[{  x  ..  y ,  RET  pat ;  Q  } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?[{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' ? [[{  x  ..  y ,   RET  pat ;  Q  } ] ] ']'") : bi_scope.

Notation "'[[{' P } ] ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ s; E [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  s ;  E  [[{  RET  pat ;  Q  } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ E [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  E  [[{  RET  pat ;  Q  } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ E ?[{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' @  E  ? [[{  RET  pat ;  Q  } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' [[{  RET  pat ;  Q  } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e ?[{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  P  } ] ]  '/  ' e  '/' ? [[{  RET  pat ;  Q  } ] ] ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'[[{' P } ] ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?[{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?[{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ s; E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ E ?[{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e ?[{ Φ }]) : stdpp_scope.


(** Notations for stronger weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'SWP' e 'at' k @ s ; E {{ Φ } }" := (swp k s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'SWP' e 'at' k @ E {{ Φ } }" := (swp k NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'SWP' e 'at' k @ E ? {{ Φ } }" := (swp k MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'SWP' e 'at' k {{ Φ } }" := (swp k NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'SWP' e 'at' k ? {{ Φ } }" := (swp k MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'SWP' e 'at' k @ s ; E {{ v , Q } }" := (swp k s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'SWP'  e  'at'  k  '/' '[          ' @  s ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'SWP' e 'at' k @ E {{ v , Q } }" := (swp k NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'SWP'  e  'at'  k  '/' '[       ' @  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'SWP' e 'at' k @ E ? {{ v , Q } }" := (swp k MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'SWP'  e  'at'  k  '/' '[        ' @  E  ? {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'SWP' e 'at' k {{ v , Q } }" := (swp k NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'SWP'  e  'at'  k  '/' '[   ' {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'SWP' e 'at' k ? {{ v , Q } }" := (swp k MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'SWP'  e  'at'  k  '/' '[    ' ? {{  v ,  Q  } } ']' ']'") : bi_scope.


(* Texan triples *)
Notation "'{{{' P } } } e 'at' k @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k @ s; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  'at'  k  '/' @  s ;  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' k @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  'at'  k  '/' @  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' k @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k @ E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  'at'  k  '/' @  E  ? {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' k {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e   'at'  k  '/' {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' k ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  'at'  k  '/' ? {{{  x  ..  y ,   RET  pat ;  Q  } } } ']'") : bi_scope.

Notation "'{{{' P } } } e 'at' k @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k @ s; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  'at'  k  '/' @  s ;  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' k @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k @ E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  'at'  k  '/' @  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' k @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k @ E ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  '  e  'at'  k  '/' @  E  ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' k {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  'at'  k  '/' {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' k ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  'at'  k  '/' ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e 'at' k @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' k @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' k @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k @ E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' k {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' k ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ SWP e at k ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' k @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' k @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' k @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k @ E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' k {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' k ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ SWP e at k ?{{ Φ }}) : stdpp_scope.


(** Notations for stronger weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'RSWP' e 'at' k @ s ; E ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RSWP' e 'at' k @ E ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RSWP' e 'at' k @ E ? ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RSWP' e 'at' k ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RSWP' e 'at' k ? ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'RSWP' e 'at' k @ s ; E ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[          ' @  s ;  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RSWP' e 'at' k @ E ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[       ' @  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RSWP' e 'at' k @ E ? ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[        ' @  E  ? ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RSWP' e 'at' k ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[   ' ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RSWP' e 'at' k ? ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[    ' ? ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.


(* Texan triples *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  s ;  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ? ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ E ?⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  E  ? ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e   'at'  k  '/' ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ? ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k ?⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' ? ⟨⟨⟨  x  ..  y ,   RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  s ;  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ? ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ E ?⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  '  e  'at'  k  '/' @  E  ? ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k(Q -∗ Φ pat%V) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ? ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k ?⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' ? ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ? ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ E ?⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ? ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k ?⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ? ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ E ?⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ? ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k ?⟨⟨ Φ ⟩⟩) : stdpp_scope.


(** Notations for refinement weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'RWP' e @ s ; E ⟨⟨ Φ ⟩ ⟩" := (rwp s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RWP' e @ E ⟨⟨ Φ ⟩ ⟩" := (rwp NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RWP' e @ E ? ⟨⟨ Φ ⟩ ⟩" := (rwp MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RWP' e ⟨⟨ Φ ⟩ ⟩" := (rwp NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RWP' e ? ⟨⟨ Φ ⟩ ⟩" := (rwp MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'RWP' e @ s ; E ⟨⟨ v , Q ⟩ ⟩" := (rwp s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RWP'  e  '/' '[          ' @  s ;  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RWP' e @ E ⟨⟨ v , Q ⟩ ⟩" := (rwp NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RWP'  e  '/' '[       ' @  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RWP' e @ E ? ⟨⟨ v , Q ⟩ ⟩" := (rwp MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RWP'  e  '/' '[        ' @  E  ? ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RWP' e ⟨⟨ v , Q ⟩ ⟩" := (rwp NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RWP'  e  '/' '[   ' ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RWP' e ? ⟨⟨ v , Q ⟩ ⟩" := (rwp MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RWP'  e  '/' '[    ' ? ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.


(* Texan triples *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  s ;  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ? ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ E ?⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  E  ? ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ? ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e ?⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' ? ⟨⟨⟨  x  ..  y ,   RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  s ;  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ? ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ E ?⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  E  ? ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ? ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e ?⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' ? ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ? ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ E ?⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ? ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e ?⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ? ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ E ?⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ? ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e ?⟨⟨ Φ ⟩⟩) : stdpp_scope.
