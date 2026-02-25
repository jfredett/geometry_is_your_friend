/- Lemmas relating to lines that do not require any theory besides the basic axioms available in Ch1. -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Tactics

namespace Geometry.Theory.Line

open Set
open Geometry.Theory

/-- If two distinct points are found on two lines, those lines are equal. -/
lemma equiv : ∀ L M : Line, ∀ A B : Point, A ≠ B -> ((A on L) ∧ (A on M) ∧ (B on L) ∧ (B on M) -> L = M) := by
  intro L M A B AneB ⟨AonL, AonM, BonL, BonM⟩
  -- idea, assume L intersects M at X, then X on L and X on M; and X is unique, so X = A and X = B, but A ≠ B
  by_contra! hNeg
  by_cases LnoparM : L ∦ M
  have ⟨X, Xexists, Xuniq⟩ := P1 hNeg LnoparM
  -- Little clean up to make these more useful
  simp only [P5.L2, mem_inter_iff, mem_singleton_iff] at Xexists
  simp only [P5.L2, mem_inter_iff, mem_singleton_iff] at Xuniq
  have AeqX : A = X := (Xexists A).mp ⟨AonL, AonM⟩
  have BeqX : B = X := (Xexists B).mp ⟨BonL, BonM⟩
  rw [AeqX, BeqX] at AneB
  contradiction
  -- if L and M are parallel, then A cannot be on both L and M, because Parallel lines share no points in common.
  push_neg at LnoparM
  obtain ⟨_, LnoparM⟩ := LnoparM
  specialize LnoparM A
  push_neg at LnoparM
  specialize LnoparM AonL
  contradiction

end Geometry.Theory.Line
