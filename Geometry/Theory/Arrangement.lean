import Mathlib.Data.List.Basic
import Geometry.Theory.Axioms
import Geometry.Tactics

import Geometry.Ch3.Prop.P3
import Geometry.Ch3.Ex.Ex1

import Atlas

namespace Geometry.Theory

open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas

structure Arrangement (pts : List Point) : Prop where
  three_plus : pts.length ≥ 3
  ordered_triple : ∀ (i j k : Fin pts.length),
    i.val < j.val → j.val < k.val →
    Between (pts.get i) (pts.get j) (pts.get k)

theorem Arrangement.tri {pts : List Point} (arr : Arrangement pts)
    (i j k : Nat) (hi : i < pts.length) (hj : j < pts.length) (hk : k < pts.length)
    (hij : i < j) (hjk : j < k) :
    Between (pts.get ⟨i, hi⟩) (pts.get ⟨j, hj⟩) (pts.get ⟨k, hk⟩) :=
  arr.ordered_triple ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk

atlas commentary := by
  ref lemma 1.0.39
  name "Arrangement.of_3"
  preface "A single A-B-C is a 3-arrangement."

atlas lemma 1.0.39 "Arrangement.of_3"
  {A B C : Point} (h : A - B - C) : Arrangement [A, B, C] := by
  refine ⟨by simp, ?_⟩
  intro i j k hij hjk
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  simp only [show ([A, B, C] : List Point).length = 3 from rfl] at hi hj hk
  have hij : i < j := hij
  have hjk : j < k := hjk
  obtain ⟨rfl, rfl, rfl⟩ : i = 0 ∧ j = 1 ∧ k = 2 := by omega
  exact h

macro_rules (kind := dashChain)
  | `($a:term - $b:term - $c:term - $d:term $[- $rest:term]*) =>
    `(Arrangement [$a, $b, $c, $d, $rest,*])

end Geometry.Theory

namespace Geometry.Theory.Arrangement

open Lean Elab Tactic Meta

private partial def listExprToArray : Expr → Option (Array Expr) :=
  fun e => go e #[]
where
  go (e : Expr) (acc : Array Expr) : Option (Array Expr) :=
    match e.getAppFnArgs with
    | (``List.cons, #[_, hd, tl]) => go tl (acc.push hd)
    | (``List.nil, _)             => some acc
    | _                           => none

private def findIndex (pts : Array Expr) (target : Expr) : MetaM (Option Nat) := do
  for h : i in [:pts.size] do
    if ← isDefEq pts[i] target then
      return some i
  return none

syntax (name := arrangementTac) "arrangement" term : tactic

@[tactic arrangementTac]
def elabArrangementTac : Tactic := fun stx => match stx with
  | `(tactic| arrangement $h:term) => do
    let goal ← getMainGoal
    goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      let some (x, y, z) := target.app3? ``Between
        | throwError "arrangement: goal is not of the form 'X - Y - Z'"
      let hExpr ← Term.elabTerm h none
      let hType ← instantiateMVars (← inferType hExpr)
      let some ptsExpr := hType.app1? ``Geometry.Theory.Arrangement
        | throwError "arrangement: hypothesis is not an `Arrangement`"
      let some pts := listExprToArray ptsExpr
        | throwError "arrangement: arrangement's point list is not a literal list"
      let some i ← findIndex pts x
        | throwError m!"arrangement: cannot find {x} in the arrangement"
      let some j ← findIndex pts y
        | throwError m!"arrangement: cannot find {y} in the arrangement"
      let some k ← findIndex pts z
        | throwError m!"arrangement: cannot find {z} in the arrangement"
      let iLit := Syntax.mkNumLit (toString i)
      let jLit := Syntax.mkNumLit (toString j)
      let kLit := Syntax.mkNumLit (toString k)
      if i < j && j < k then
        let tac ← `(tactic|
          exact ($h).ordered_triple
            ⟨$iLit, by simp⟩ ⟨$jLit, by simp⟩ ⟨$kLit, by simp⟩
            (by simp) (by simp))
        evalTactic tac
      else if k < j && j < i then
        let tac ← `(tactic|
          exact (($h).ordered_triple
            ⟨$kLit, by simp⟩ ⟨$jLit, by simp⟩ ⟨$iLit, by simp⟩
            (by simp) (by simp)).symm)
        evalTactic tac
      else
        throwError m!"arrangement: points are not in monotonic order \
          (indices {i}, {j}, {k}). Both X-Y-Z and Z-Y-X are supported; \
          any other interleaving needs to be derived manually."
  | _ => throwUnsupportedSyntax

end Geometry.Theory.Arrangement

namespace Geometry.Theory

open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas

private lemma cons_get_succ {α} {a : α} {l : List α} {k : Nat}
    (hk : k + 1 < (a :: l).length) :
    (a :: l).get ⟨k + 1, hk⟩ = l.get ⟨k, by simp only [List.length_cons] at hk; omega⟩ := by simp

atlas commentary := by
  ref lemma 3.0.5
  name "Arrangement.cons"
  preface "Given a prior arrangement B-C-... and an anchor A-B-C, the chain A-B-C-... is also an arrangement."

atlas lemma 3.0.5 "Arrangement.cons"
  {A B C : Point} {rest : List Point}
  (anchor : A - B - C) (arr : Arrangement (B :: C :: rest)) :
    Arrangement (A :: B :: C :: rest) := by
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons]; omega
  rintro ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk
  have hij : i < j := hij
  have hjk : j < k := hjk
  simp only [List.length_cons] at hi hj hk
  have hOldLen : (B :: C :: rest).length = rest.length + 2 := by simp
  have h_AB_at : ∀ m (_ : 2 ≤ m) (hm' : m < rest.length + 3),
      A - B - ((A :: B :: C :: rest).get
        ⟨m, by simp only [List.length_cons]; omega⟩) := by
    intro m hm hm'
    rcases m with _ | _ | _ | m
    · omega
    · omega
    · change A - B - C
      exact anchor
    · have key : B - C - (rest.get ⟨m, by omega⟩) := by
        have h := arr.tri 0 1 (m + 2)
          (by rw [hOldLen]; omega)
          (by rw [hOldLen]; omega)
          (by rw [hOldLen]; omega)
          (by omega) (by omega)
        simpa using h
      change A - B - (rest.get ⟨m, by omega⟩)
      exact via corollary 3.3.i ⟨anchor, key⟩
  rcases i with _ | i
  · change A -
      ((A :: B :: C :: rest).get ⟨j, by simp only [List.length_cons]; omega⟩) -
      ((A :: B :: C :: rest).get ⟨k, by simp only [List.length_cons]; omega⟩)
    rcases j with _ | _ | j
    · omega
    · change A - B - ((A :: B :: C :: rest).get _)
      exact h_AB_at k (by omega) hk
    · have hAB : A - B - ((A :: B :: C :: rest).get
          ⟨j + 2, by simp only [List.length_cons]; omega⟩) :=
        h_AB_at (j + 2) (by omega) hj
      have hBjk : B -
          ((A :: B :: C :: rest).get ⟨j + 2, by simp only [List.length_cons]; omega⟩) -
          ((A :: B :: C :: rest).get ⟨k, by simp only [List.length_cons]; omega⟩) := by
        rcases k with _ | k
        · omega
        have h := arr.tri 0 (j + 1) k
          (by rw [hOldLen]; omega)
          (by rw [hOldLen]; omega)
          (by rw [hOldLen]; omega)
          (by omega) (by omega)
        have e1 : (B :: C :: rest).get ⟨0, by rw [hOldLen]; omega⟩ = B := by simp
        have e2 : (B :: C :: rest).get ⟨j + 1, by rw [hOldLen]; omega⟩ =
                  (A :: B :: C :: rest).get ⟨j + 2, by simp only [List.length_cons]; omega⟩ := by
          rw [cons_get_succ (a := A) (l := B :: C :: rest) (k := j + 1)
                (hk := by simp only [List.length_cons]; omega)]
        have e3 : (B :: C :: rest).get ⟨k, by rw [hOldLen]; omega⟩ =
                  (A :: B :: C :: rest).get ⟨k + 1, by simp only [List.length_cons]; omega⟩ := by
          rw [cons_get_succ (a := A) (l := B :: C :: rest) (k := k)
                (hk := by simp only [List.length_cons]; omega)]
        rw [e1, e2, e3] at h
        exact h
      exact via corollary 3.3.ii ⟨hAB, hBjk⟩
  · rcases j with _ | j
    · omega
    rcases k with _ | k
    · omega
    have h := arr.tri i j k
      (by rw [hOldLen]; omega)
      (by rw [hOldLen]; omega)
      (by rw [hOldLen]; omega)
      (by omega) (by omega)
    have ei : (B :: C :: rest).get ⟨i, by rw [hOldLen]; omega⟩ =
              (A :: B :: C :: rest).get ⟨i + 1, by simp only [List.length_cons]; omega⟩ := by
      rw [cons_get_succ (a := A) (l := B :: C :: rest) (k := i)
            (hk := by simp only [List.length_cons]; omega)]
    have ej : (B :: C :: rest).get ⟨j, by rw [hOldLen]; omega⟩ =
              (A :: B :: C :: rest).get ⟨j + 1, by simp only [List.length_cons]; omega⟩ := by
      rw [cons_get_succ (a := A) (l := B :: C :: rest) (k := j)
            (hk := by simp only [List.length_cons]; omega)]
    have ek : (B :: C :: rest).get ⟨k, by rw [hOldLen]; omega⟩ =
              (A :: B :: C :: rest).get ⟨k + 1, by simp only [List.length_cons]; omega⟩ := by
      rw [cons_get_succ (a := A) (l := B :: C :: rest) (k := k)
            (hk := by simp only [List.length_cons]; omega)]
    rw [ei, ej, ek] at h
    exact h

atlas commentary := by
  ref alternate 3.3
  name "If A-B-C and A-C-D, then A-B-C-D"
  preface ""
  notes "Greenberg relies on figures to disambiguate arrangements, we cannot do that. To accomodate this infacility, we
  have `Arrangements`, which allow for deducing every included ordered triple in the list of points they arrange."

atlas alternate 3.3 "full chain arrangement from overlapping outer-pair triples"
  {A B C D : Point} (h₁ : A - B - C) (h₂ : A - C - D) : A - B - C - D := by
  have hBCD : B - C - D := via proposition 3.3.i ⟨h₁, h₂⟩
  exact via lemma 3.0.5 h₁ (ref lemma 1.0.39 hBCD)

end Geometry.Theory
