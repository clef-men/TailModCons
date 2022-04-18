From iris.proofmode Require Export classes.
From iris.algebra Require Export cmra.

(* There are various versions of [IsOp] with different modes:

- [IsOp a b1 b2]: this one has no mode, it can be used regardless of whether
  any of the arguments is an evar. This class has only one direct instance:
  [IsOp (a ⋅ b) a b].
- [IsOp' a b1 b2]: requires either [a] to start with a constructor, OR [b1] and
  [b2] to start with a constructor. All usual instances should be of this
  class to avoid loops.
- [IsOp'LR a b1 b2]: requires either [a] to start with a constructor. This one
  has just one instance: [IsOp'LR (a ⋅ b) a b] with a very low precendence.
  This is important so that when performing, for example, an [iDestruct] on
  [own γ (q1 + q2)] where [q1] and [q2] are fractions, we actually get
  [own γ q1] and [own γ q2] instead of [own γ ((q1 + q2)/2)] twice.
*)
Class IsOp {SI} {A : cmraT SI} (a b1 b2 : A) := is_op : a ≡ b1 ⋅ b2.
Arguments is_op {_ _} _ _ _ {_}.
Hint Mode IsOp - + - - - : typeclass_instances.

Instance is_op_op {SI} {A : cmraT SI} (a b : A) : IsOp (a ⋅ b) a b | 100.
Proof. by rewrite /IsOp. Qed.

Class IsOp' {SI} {A : cmraT SI} (a b1 b2 : A) := is_op' :> IsOp a b1 b2.
Hint Mode IsOp' - + ! - - : typeclass_instances.
Hint Mode IsOp' - + - ! ! : typeclass_instances.

Class IsOp'LR {SI} {A : cmraT SI} (a b1 b2 : A) := is_op_lr : IsOp a b1 b2.
Existing Instance is_op_lr | 0.
Hint Mode IsOp'LR - + ! - - : typeclass_instances.
Instance is_op_lr_op {SI} {A : cmraT SI} (a b : A) : IsOp'LR (a ⋅ b) a b | 0.
Proof. by rewrite /IsOp'LR /IsOp. Qed.

(* FromOp *)
(* TODO: Worst case there could be a lot of backtracking on these instances,
try to refactor. *)
Global Instance is_op_pair {SI} {A B : cmraT SI} (a b1 b2 : A) (a' b1' b2' : B) :
  IsOp a b1 b2 → IsOp a' b1' b2' → IsOp' (a,a') (b1,b1') (b2,b2').
Proof. by constructor. Qed.
Global Instance is_op_pair_core_id_l {SI} {A B : cmraT SI} (a : A) (a' b1' b2' : B) :
  CoreId a → IsOp a' b1' b2' → IsOp' (a,a') (a,b1') (a,b2').
Proof. constructor=> //=. by rewrite -core_id_dup. Qed.
Global Instance is_op_pair_core_id_r {SI} {A B : cmraT SI} (a b1 b2 : A) (a' : B) :
  CoreId a' → IsOp a b1 b2 → IsOp' (a,a') (b1,a') (b2,a').
Proof. constructor=> //=. by rewrite -core_id_dup. Qed.

Global Instance is_op_Some {SI} {A : cmraT SI} (a : A) b1 b2 :
  IsOp a b1 b2 → IsOp' (Some a) (Some b1) (Some b2).
Proof. by constructor. Qed.
(* This one has a higher precendence than [is_op_op] so we get a [+] instead of
an [⋅]. *)
Global Instance is_op_plus (I: indexT) (n1 n2 : nat) : @IsOp I _ (n1 + n2) n1 n2.
Proof. done. Qed.
