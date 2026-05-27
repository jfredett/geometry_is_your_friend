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

private lemma get_of_idx_eq {α} (l : List α) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (h : i = j) : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩ := by subst h; rfl

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
  -- The index shift: prefixing A bumps every old index by 1.
  have shift : ∀ (m : Nat) (hm : m < rest.length + 2),
      (B :: C :: rest).get ⟨m, by rw [hOldLen]; omega⟩ =
      (A :: B :: C :: rest).get ⟨m + 1, by simp only [List.length_cons]; omega⟩ := by
    intro m hm
    rw [cons_get_succ (a := A) (l := B :: C :: rest) (k := m)
          (hk := by simp only [List.length_cons]; omega)]
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
          (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
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
          (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
          (by omega) (by omega)
        have e1 : (B :: C :: rest).get ⟨0, by rw [hOldLen]; omega⟩ = B := by simp
        rw [e1, shift (j + 1) (by omega), shift k (by omega)] at h
        exact h
      exact via corollary 3.3.ii ⟨hAB, hBjk⟩
  · rcases j with _ | j
    · omega
    rcases k with _ | k
    · omega
    have h := arr.tri i j k
      (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
      (by omega) (by omega)
    rw [shift i (by omega), shift j (by omega), shift k (by omega)] at h
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

atlas commentary := by
  ref lemma 3.0.6
  name "Arrangement.head_swap"
  preface "Given Arr[B,C,…] and B-X-C, derive Arr[X,C,…]."

atlas lemma 3.0.6 "Arrangement.head_swap"
  {B C X : Point} {suf : List Point}
  (arr : Arrangement (B :: C :: suf)) (bxc : B - X - C) :
    Arrangement (X :: C :: suf) := by
  refine ⟨?_, ?_⟩
  · have := arr.three_plus
    simp only [List.length_cons] at this ⊢
    exact this
  rintro ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk
  have hij : i < j := hij
  have hjk : j < k := hjk
  simp only [List.length_cons] at hi hj hk
  have hOldLen : (B :: C :: suf).length = suf.length + 2 := by simp
  have arr_BC_suf : ∀ m (hm : m < suf.length),
      B - C - (suf.get ⟨m, hm⟩) := fun m hm => by
    have h := arr.tri 0 1 (m + 2)
      (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
      (by omega) (by omega)
    simpa using h
  have h_XC_at : ∀ m (hm : m < suf.length),
      X - C - (suf.get ⟨m, hm⟩) := fun m hm =>
    via proposition 3.3.i ⟨bxc, arr_BC_suf m hm⟩
  -- Index-conversion helpers: for any list l ∈ {(X::C::suf), (B::C::suf)} and idx m ≥ 2,
  -- l.get ⟨m, _⟩ = suf.get ⟨m - 2, _⟩.
  have suf_get_of_geq2 :
      ∀ {Y : Point} (m : Nat) (hm : m < suf.length + 2) (hm2 : 2 ≤ m) (hmr : m - 2 < suf.length),
        (Y :: C :: suf).get ⟨m, by simp only [List.length_cons]; omega⟩ = suf.get ⟨m - 2, hmr⟩ := by
    intro Y m hm hm2 hmr
    rw [get_of_idx_eq (Y :: C :: suf) _ (by simp only [List.length_cons]; omega)
        (show m = (m - 2) + 2 from by omega)]
    simp
  rcases Nat.lt_or_ge i 1 with _ | hi'
  · obtain rfl : i = 0 := by omega
    rcases Nat.lt_or_ge j 2 with _ | hj'
    · obtain rfl : j = 1 := by omega
      have hkr : k - 2 < suf.length := by omega
      have e0 : (X :: C :: suf).get ⟨0, by simp only [List.length_cons]; omega⟩ = X := rfl
      have e1 : (X :: C :: suf).get ⟨1, by simp only [List.length_cons]; omega⟩ = C := rfl
      have ek := suf_get_of_geq2 (Y := X) k hk (by omega) hkr
      rw [e0, e1, ek]
      exact h_XC_at (k - 2) hkr
    · have hjr : j - 2 < suf.length := by omega
      have hkr : k - 2 < suf.length := by omega
      have e0 : (X :: C :: suf).get ⟨0, by simp only [List.length_cons]; omega⟩ = X := rfl
      have ej := suf_get_of_geq2 (Y := X) j hj (by omega) hjr
      have ek := suf_get_of_geq2 (Y := X) k hk (by omega) hkr
      rw [e0, ej, ek]
      have hXCj : X - C - (suf.get ⟨j - 2, hjr⟩) := h_XC_at (j - 2) hjr
      have hC_jk : C - (suf.get ⟨j - 2, hjr⟩) - (suf.get ⟨k - 2, hkr⟩) := by
        have h := arr.tri 1 j k
          (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
          (by omega) (by omega)
        have e1' : (B :: C :: suf).get ⟨1, by rw [hOldLen]; omega⟩ = C := rfl
        have ej' := suf_get_of_geq2 (Y := B) j (by rw [hOldLen] at *; omega) (by omega) hjr
        have ek' := suf_get_of_geq2 (Y := B) k (by rw [hOldLen] at *; omega) (by omega) hkr
        rw [e1', ej', ek'] at h
        exact h
      exact via corollary 3.3.ii ⟨hXCj, hC_jk⟩
  · -- i ≥ 1: triple in old arr at same indices. For m ≥ 1, both lists agree.
    have new_eq_old : ∀ (m : Nat) (_hm_pos : 1 ≤ m) (hm : m < suf.length + 2),
        (B :: C :: suf).get ⟨m, by simp only [List.length_cons]; omega⟩ =
        (X :: C :: suf).get ⟨m, by simp only [List.length_cons]; omega⟩ := by
      intro m _ hm
      rw [get_of_idx_eq (X :: C :: suf) _ (by simp only [List.length_cons]; omega)
            (show m = (m - 1) + 1 from by omega),
          get_of_idx_eq (B :: C :: suf) _ (by simp only [List.length_cons]; omega)
            (show m = (m - 1) + 1 from by omega)]
      simp
    have h := arr.tri i j k
      (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
      hij hjk
    rw [new_eq_old i (by omega) (by rw [hOldLen] at *; omega),
        new_eq_old j (by omega) (by rw [hOldLen] at *; omega),
        new_eq_old k (by omega) (by rw [hOldLen] at *; omega)] at h
    exact h

atlas commentary := by
  ref lemma 3.0.7
  name "Arrangement.insert_head"
  preface "Given Arr[B,C,…] and B-X-C, derive Arr[B,X,C,…]. Composes head_swap with cons."

atlas lemma 3.0.7 "Arrangement.insert_head"
  {B C X : Point} {suf : List Point}
  (arr : Arrangement (B :: C :: suf)) (bxc : B - X - C) :
    Arrangement (B :: X :: C :: suf) :=
  via lemma 3.0.5 bxc (via lemma 3.0.6 arr bxc)

atlas commentary := by
  ref lemma 3.0.8
  name "If A-B-C and B-C-D, then A-B-C-D"
  preface ""

atlas lemma 3.0.8 "If A-B-C and B-C-D, then A-B-C-D"
  {A B C D : Point} (h₁ : A - B - C) (h₂ : B - C - D) : A - B - C - D := by
  have hACD : A - C - D := via corollary 3.3.ii ⟨h₁, h₂⟩
  exact via alternate 3.3 h₁ hACD

end Geometry.Theory
