/- Lemmas relating to the `distinct` condition -/

import Geometry.Tactics
import Mathlib.Data.List.Basic

namespace Geometry.Theory

open Lean Meta Expr Elab.Tactic Qq

-- Lots of imperative code here, newlines help make sense of things.
set_option linter.style.emptyLine false

-- Say you have a main goal is a conjunction of 'interesting' goals and also a bunch of inequality goals.
-- Further say you have a bunch of `distinct` conditions listing variables which are pairwise distinct.
--
-- h : distinct A B C D E := by magic
-- ⊢ A ≠ B ∧ B ≠ E ∧ X ≠ A
--
-- This provides a tactic, `distinguish`, which searches the local proof environment for `distinct` hypotheses
-- and then splits the conjunction to the smallest goals it can, and tries to prove as many inequality goals
-- as possible. The above would reduce to `X ≠ A` after running `distinguish`
--
-- `distinguish` will not try to re-write any hypotheses or use any ambient inequality hypotheses.
--
-- TODO: Reassemble the conjunction after splitting it.
-- TODO: When splitting, gather goals and place them into some inductive structure which
--    categorizes them; simple inequalities are covered now, but a disjunction containing a conjunction
--    would be possible as well if we can prove one side of it; it might be possible to 'look past' quantifiers, etc.
-- TODO: an unelaborator to pretty-print the distinct condition as the distinct condition


structure Distinct {α : Type*} (points : List α) : Prop where
  pairwise : List.Pairwise (· ≠ ·) points

namespace Distinct

/-- Get the list of points from a Distinct hypothesis (meta-level) -/
partial def getPointsExpr (distinctExpr : Expr) : MetaM (Option (List Expr)) := do
  let hypoType ← inferType distinctExpr
  if hypoType.isAppOfArity ``Distinct 2 then
    let listExpr := hypoType.getArg! 1

    let rec extract (e : Expr) : List Expr :=
      if e.isAppOfArity ``List.cons 3 then
        let head := e.appFn!.appArg!
        let tail := e.appArg!
        head :: extract tail
      else
        []

    return some (extract listExpr)
  else
    return none

/-- Extracts a list of expressions like `X ≠ Y ∧ ...` into [ X≠Y, ...], [ non-equality goals ] -/
partial def extractIneqs (e : Expr) : MetaM (List Expr × List Expr) := do
  have qe : Q(Prop) := e
  match qe with
  | ~q(@And $lhs $rhs) => do
    let (lhsIneqs, lhsOther) ← extractIneqs lhs
    let (rhsIneqs, rhsOther) ← extractIneqs rhs
    return (lhsIneqs ++ rhsIneqs, lhsOther ++ rhsOther)
  | ~q(@Ne _ $a $b) => return ([e], [])
  | _ => return ([], [e])

/-- Finds all `Distinct` hypotheses in the local context -/
def findDistinctHypos : TacticM (List LocalDecl) := do
  let lctx ← getLCtx
  let mut distinctHypos : List LocalDecl := []
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let declType ← instantiateMVars decl.type
    if declType.isAppOfArity ``Distinct 2 then
      distinctHypos := decl :: distinctHypos
  return distinctHypos

/-- Split a conjunction into separate goals, returning MVars for each -/
def splitConjunction (goals : List Expr) : TacticM (List MVarId) := do
  match goals with
  | [] => return []
  | [single] =>
    -- Single goal, just return current goal
    let mvar ← mkFreshExprSyntheticOpaqueMVar single
    return [mvar.mvarId!]
  | _ => do
    -- Build nested And.intro structure using Qq
    let rec buildAndIntros (gs : List Expr) : TacticM (Expr × List MVarId) := do
      match gs with
      | [] => throwError "empty list"
      | [last] =>
        have lastQ : Q(Prop) := last
        let mvar : Q($lastQ) ← mkFreshExprSyntheticOpaqueMVar last
        return (mvar, [mvar.mvarId!])
      | g :: gs' => do
        have gQ : Q(Prop) := g
        let leftMvar : Q($gQ) ← mkFreshExprSyntheticOpaqueMVar g
        let (rightExpr, rightMvars) ← buildAndIntros gs'
        let rightType ← inferType rightExpr
        have rightQ : Q(Prop) := rightType
        have rightTyped : Q($rightQ) := rightExpr
        let andProof : Q($gQ ∧ $rightQ) := q(And.intro $leftMvar $rightTyped)
        return (andProof, rightMvars ++ [leftMvar.mvarId!])

    let (proof, mvars) ← buildAndIntros goals
    let mainGoal ← getMainGoal
    mainGoal.assign proof
    return mvars

/-- Split out the conjunction goals into a list of MVars to populate -/
partial def splitConjunctionGoals : TacticM (List MVarId) := do
  let rec split : TacticM (List MVarId) := do
    let [goal] ← getGoals | throwError "Expected exactly one goal"
    let goalType ← goal.getType
    have goalTypeProp : Q(Prop) := goalType
    match goalTypeProp with
    | ~q($a ∧ $b) => do
      setGoals [goal]
      evalTactic (← `(tactic| constructor))
      let [leftGoal, rightGoal] ← getGoals | throwError "Expected two goals after constructor"
      setGoals [leftGoal]
      let leftGoals ← split
      setGoals [rightGoal]
      let rightGoals ← split
      return leftGoals ++ rightGoals
    | _ => return [goal]
  split

/-- Split goal and track which subgoals are inequalities. -/
partial def splitAndTagGoals : TacticM (List MVarId × List Nat) := do
  let goal ← getMainGoal
  let tgt ← goal.getType
  -- Extract inequalities and others, preserving order
  let rec extract (e : Expr) (idx : Nat) : MetaM (List (Expr × Nat × Bool)) := do
    have qe : Q(Prop) := e
    match qe with
    | ~q(@And $lhs $rhs) => do
      let lhsResults ← extract lhs idx
      let rhsIdx := idx + lhsResults.length
      let rhsResults ← extract rhs rhsIdx
      return lhsResults ++ rhsResults
    | ~q(@Ne _ $a $b) => return [(e, idx, true)]  -- (expr, index, isInequality)
    | _ => return [(e, idx, false)] -- Not an inequality
  let tagged ← extract tgt 0
  let subgoals ← splitConjunctionGoals
  let ineqIndices := tagged.filterMap (fun (_, idx, isIneq) => if isIneq then some idx else none)
  return (subgoals, ineqIndices)

def runDistinguish : TacticM Unit := do
  withMainContext do
    -- Split and tag goals as ineq goals or not.
    let (allGoals, ineqIndices) ← splitAndTagGoals
    -- Try to solve inequality goals using the distinct hypos in the current environment
    let distinctHypos ← findDistinctHypos
    let mut solvedIndices : List Nat := []
    for idx in ineqIndices do
      let goalMVar := allGoals[idx]!
      setGoals [goalMVar]

      for hypo in distinctHypos do
        -- 1. break into the fvars on either side
        let goalType ← goalMVar.getType
        have goalTypeProp : Q(Prop) := goalType
        if let ~q(@Ne $typ $lhs $rhs) := goalTypeProp then
          -- 2a. if the fvars are the same, then the two things are equal, reject
          if lhs.fvarId! != rhs.fvarId! then
            -- 3. now search the `points` of the `distinct` condition and we can conclude inequality based
            -- on the pairwise relationship
            if let some points ← Distinct.getPointsExpr hypo.toExpr then
              -- establish that both lhs and rhs are in the list of distinct variables
              let lhsIn := points.any (fun p => p.isFVar && p.fvarId! == lhs.fvarId!)
              let rhsIn := points.any (fun p => p.isFVar && p.fvarId! == rhs.fvarId!)
              if lhsIn && rhsIn then
                -- we can prove it, we have the technology
                let proofGoal ← mkFreshExprMVar goalType
                let proofMVar := proofGoal.mvarId!
                setGoals [proofMVar]
                let hypoName := mkIdent hypo.userName

                -- prove using aesop + simp, this is not ideal, it should be possible to construct a direct
                -- proof, but it's not low-effort, so FIXME some other time.
                evalTactic (← `(tactic| (
                  have h := ($hypoName).pairwise
                  simp only [List.Pairwise, List.mem_cons] at h
                  aesop
                )))

                -- Check if it was solved, then assign the goal if it is.
                if ← proofMVar.isAssigned then
                  let proof ← instantiateMVars proofGoal
                  goalMVar.assign proof
          else
            -- in this case, lhs is _literally the same variable reference_ as rhs, so we are trying to prove
            -- ¬(rfl A), which is just false, so the whole conjunction is false and we should replace the goal
            -- with false. I'm not doing that now, but it's doable, I think.
            throwError "lhs is identical to rhs, you're trying to prove A ≠ A, and that's no bueno"
        else
          logInfo m!"{goalType}"
          -- 2b. do nothing, this case is not possible because we're only inspecting inequalities.
          throwError "not possible"
      -- bookkeeping to make sure we set the goals correctly later.
      -- FIXME: I think this could probably be based on whether or not the mvar is assigned?
      if ← goalMVar.isAssigned then
        solvedIndices := idx :: solvedIndices

    -- Collect unsolved goals
    let mut unsolvedGoals : List MVarId := []
    for i in [:allGoals.length] do
      if !solvedIndices.contains i then
        unsolvedGoals := unsolvedGoals ++ [allGoals[i]!]

    setGoals unsolvedGoals

-- Custom syntax for distinct/distinguish
declare_syntax_cat distinct_binder
syntax ident+ " : " term : distinct_binder

syntax "distinct" ident+ : term
macro_rules
  | `(distinct $xs*) => `(Distinct [$xs,*])

syntax "distinguish" : tactic

macro_rules
  | `(tactic| distinguish) => `(tactic| run_tac runDistinguish)


example : distinct A B C D E -> A ≠ X -> A ≠ B ∧ B ≠ C ∧ X ≠ A ∧ (∀ P : Nat, P = 2 -> P > 1) ∧ C ≠ D := by
  intro h AneX
  distinguish
  -- this part doesn't matter, the assertions are just to make sure the distiguish step doesn't oversolve
  exact AneX.symm
  intro P Peq2
  rw [Peq2]; trivial

example : distinct A B C D E -> A ≠ X -> A ≠ B ∧ (B ≠ C ∧ X ≠ A) ∧ (∀ P : Nat, P = 3 -> P > 1) ∧ (C ≠ D ∨ V = W) := by
  intro h AneX
  distinguish -- should be A≠B, B≠C, X≠A, C≠D
  · exact AneX.symm
  · intro P Peq3; rw [Peq3]; trivial
  · have CneD : C ≠ D := by distinguish
    left; trivial

example (A B C D : Point) (h : distinct A B C D) : A ≠ B ∧ B ≠ C ∧ A ≠ D := by
  distinguish

end Distinct
end Geometry.Theory
