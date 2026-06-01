import Figures

namespace Geometry.Construction.DSL

open Figures

inductive Stmt where
  | «exists»  (names : Array Name) (sort : Name) : Stmt
  | assert    (claim : ConstraintExpr) (description : String := "") : Stmt
  | construct (name : Name) (expr : ConstraintExpr) : Stmt
  deriving Repr, Inhabited

structure Construction where
  stmts : Array Stmt
  deriving Repr, Inhabited


private partial def exprToString : ConstraintExpr → String
  | .name n   => n
  | .num k    => toString k
  | .app f [] => f
  | .app f args =>
    let parts := args.map fun a => match a with
      | .app _ [] | .name _ | .num _ => exprToString a
      | _ => "(" ++ exprToString a ++ ")"
    f ++ " " ++ String.intercalate " " parts

def printStmt : Stmt → String
  | .«exists» names sort =>
    "exists " ++ String.intercalate " " names.toList ++ " : " ++ sort
  | .assert claim "" =>
    "assert " ++ exprToString claim
  | .assert claim desc =>
    "assert " ++ exprToString claim ++ "    -- " ++ desc
  | .construct name expr =>
    "construct " ++ name ++ " := " ++ exprToString expr

def printConstruction (c : Construction) : String :=
  String.intercalate "\n" (c.stmts.toList.map printStmt)


end Geometry.Construction.DSL
