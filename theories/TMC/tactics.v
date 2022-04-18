From TMC Require Export lang.

Ltac reshape_expr e tac :=
  let rec go K e :=
    let go Ki e := go (Ki :: K) e in
    match e with
    | _ => tac K e
    | Let ?e1 ?e2 => go (LetCtx e2) e1
    | PairIdx one ?e1 ?e2 => go (PairOneLCtx e2) e1
    | PairIdx one (Val ?v1) ?e2 => go (PairOneRCtx v1) e2
    | PairIdx two ?e1 ?e2 => go (PairTwoRCtx e1) e2
    | PairIdx two ?e1 (Val ?v2) => go (PairTwoLCtx v2) e1
    | Match ?e0 ?e1 ?e2 => go (MatchCtx e1 e2) e0
    | Store ?e1 ?e2 ?e3 => go (Store1Ctx e2 e3) e1
    | Store (Val ?v1) ?e2 ?e3 => go (Store2Ctx v1 e3) e2
    | Store (Val ?v1) (Val ?v2) ?e3 => go (Store3Ctx v1 v2) e3
    end
  in
  go (@nil ectx_item) e
.
