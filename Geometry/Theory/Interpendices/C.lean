import Mathlib.Data.List.Basic
import Geometry.Theory.Axioms
import Geometry.Theory.Interpendices.A
import Geometry.Tactics

import Geometry.Ch3.Prop.P3
import Geometry.Ch3.Ex.Ex1

import Atlas

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
