/- Lemmas relating to the `distinct` condition -/

import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

namespace Geometry.Theory.Distinct

open Set

open Lean Meta Expr Elab.Tactic Qq


-- idea: when this is called, assume the main goal is of the form
-- A ≠ B ∧ ...
-- search for any `distinct` blocks floating around and attempt to refine the goal
-- as much as possible, so ideally a proof like:
--
-- h : distinct A B C D E := by magic
-- ⊢ A ≠ B ∧ B ≠ E ∧ X ≠ A
--
-- runDistinguish should satisfy the first two and leave the last one.
--

structure Distinct {α : Type*} (points : List α) : Prop where
  pairwise : List.Pairwise (· ≠ ·) points

-- Custom syntax category for the distinct binder
declare_syntax_cat distinct_binder
syntax ident+ " : " term : distinct_binder

syntax "distinct" ident+ : term
macro_rules
  | `(distinct $xs*) => `(Distinct [$xs,*])

/-- Extracts a list of expressions like `X ≠ Y ∧ ...` into [ X≠Y, ...] -/
partial def extractIneqs (e : Expr) : MetaM (List Expr) := do
  have qe : Q(Prop) := e
  match qe with
  | ~q(@And $lhs $rhs) => do
    let lhsIneqs ← extractIneqs lhs
    let rhsIneqs ← extractIneqs rhs
    return lhsIneqs ++ rhsIneqs
  | ~q(@Ne _ $a $b) =>
    return [e]
  | _ => return []

/-- Finds all `Distinct` hypotheses in the local context -/
def findDistinctHypos : TacticM (List Expr) := do
  withMainContext do
    let lctx ← getLCtx
    let mut distinctHypos : List Expr := []
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let declType ← instantiateMVars decl.type
      if declType.isAppOfArity ``Distinct 2 then
        distinctHypos := decl.toExpr :: distinctHypos
    return distinctHypos


def runDistinguish : TacticM Unit := do
  withMainContext do
    let tgt ← getMainTarget
    let ineqs ← extractIneqs tgt
    logInfo m!"{ineqs}"
    --
    let distinctHypos ← findDistinctHypos
    logInfo m!"found hypos {distinctHypos}"
 
    --
    throwError "test"

example : Distinct [A, B, C, D, E] -> A ≠ B ∧ B ≠ C ∧ X ≠ A ∧ (∀ P : Nat, P > 1) ∧ C ≠ D := by
  intro h
  run_tac runDistinguish -- should be A≠B, B≠C, X≠A, C≠D
  sorry

example : distinct A B C D E -> A ≠ B ∧ B ≠ C ∧ X ≠ A ∧ (∀ P : Nat, P > 1) ∧ C ≠ D := by
  intro h
  run_tac runDistinguish -- should be A≠B, B≠C, X≠A, C≠D
  sorry

-- TODO: Make the `h` optional by searching the proofstate
-- TODO: Maybe make the X and Y optional as well
-- TODO: an unelaborator to pretty-print the distinct condition as the distinct condition


-- @[simp] lemma forget :

-- gut check
example (A B C D : Point) (h : distinct A B C D) : A ≠ B ∧ B ≠ C ∧ A ≠ D := by
  have AneB := by distinguish h A B
  constructor
  · exact AneB
  constructor
  · distinguish h B C
  · distinguish h A D

end Geometry.Theory.Distinct
