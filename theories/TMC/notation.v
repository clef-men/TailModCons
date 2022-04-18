From TMC Require Export lang.

(* ---- index ---- *)

Declare Scope index_scope.
Delimit Scope index_scope with index.
Bind Scope index_scope with index.

Notation "𝟙" := one : index_scope.
Notation "𝟚" := two : index_scope.

Coercion Idx : index >-> val.

(* ---- val ---- *)

Notation "()" :=
  Unit
: val_scope.

Coercion Val : val >-> expr.

(* ---- expr ---- *)

Notation Seq e1 e2 := (Let e1 $ rename (+1) e2) (only parsing).
Notation SeqCtx e2 := (LetCtx $ rename (+1) e2) (only parsing).

Notation "# v" :=
  (Val v%V%index) (
  at level 8,
  format "# v"
).

Notation "$ x" :=
  (Var x%nat) (
  at level 8,
  format "$ x"
) : expr_scope.

Notation "'fail'" :=
  Fail
: expr_scope.

Notation "'let:' e1 'in' e2" :=
  (Let e1%E e2%E) (
  at level 200,
  e1, e2 at level 200,
  format "'[' 'let:'  '[' e1 ']'  'in'  '/' e2 ']'"
) : expr_scope.

Notation "e1 ;; e2" :=
  (Seq e1%E e2%E) (
  at level 100,
  e2 at level 200,
  format "'[' '[hv' '[' e1 ']'  ;;  ']' '/' e2 ']'"
) : expr_scope.

Notation "( e1 , e2 , .. , en )" :=
  (Pair .. (Pair e1%E e2%E) .. en%E)
: expr_scope.

Notation "( e1 | i | e2 )" :=
  (PairIdx i%index e1%E e2%E)
: expr_scope.

Notation "'match:' e0 'with' () => e1 | '_' => e2 'end'" :=
  (Match e0%E e1%E e2%E) (
  e0, e1, e2 at level 200,
  format "'[hv' 'match:'  e0  'with'  '/  ' '[' ()  =>  '/    ' e1 ']'  '/' '[' |  '_'  =>  '/    ' e2 ']'  '/' 'end' ']'"
) : expr_scope.

Notation "e1 .# e2 <− e3" :=
  (Store e1%E e2%E e3%E) (
  at level 80
) : expr_scope.
