
import Geometry.Tactics

import Geometry.Theory.Axioms

open Geometry.Theory

/-- p71, "For every line, there is at least one point not lying on it." -/
theorem Geometry.Ch2.Prop.P3 :
    ∀ L : Line, ∃ P : Point, (P off L) := by
      intro L
      by_contra! hNeg
      -- idea: There exist three non-colinear points, but if all points are on L (hNeg), then
      -- those points are colinear
      have ⟨A,B,C, hDistinct, hNC⟩ := I3
      have AonL := hNeg A
      have BonL := hNeg B
      have ConL := hNeg C
      specialize hNC L AonL BonL
      contradiction
