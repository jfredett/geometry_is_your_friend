module

public import Geometry.Tactics
public import Geometry.Ch2.Theory
public import Geometry.Ch2.Defs
public import Geometry.Ch2.Prop.P2

open Geometry.Ch2.Defs

@[expose] public section

open Geometry.Ch2.Theory
open Geometry.Ch2.Defs

variable (G : IncidenceGeometry)

-- p71, "For every line, there is at least one point not lying on it."
theorem Geometry.Ch2.Prop.P3 {G : IncidenceGeometry} :
    ∀ L : G.Line, ∃ P : G.Point, (P off L) := by
      intro L
      by_contra! hNeg
      -- idea: There exist three non-colinear points, but if all points are on L (hNeg), then
      -- those points are colinear
      have ⟨A,B,C, hDistinct, hNC⟩ := G.ia_3_three_noncolinear_points
      have AonL := hNeg A
      have BonL := hNeg B
      have ConL := hNeg C
      specialize hNC L AonL BonL
      contradiction
