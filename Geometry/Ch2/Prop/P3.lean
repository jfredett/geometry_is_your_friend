module

public import Geometry.Tactics
public import Geometry.Ch2.Theory
public import Geometry.Ch2.Defs
public import Geometry.Ch2.Prop.P2

open Geometry.Ch2.Defs

@[expose] public section

namespace Geometry.Ch2.Prop

open Geometry.Ch2.Theory
open Geometry.Ch2.Defs

variable (G : IncidenceGeometry)

-- p71, "For every line, there is at least one point not lying on it."
theorem P3 {G : IncidenceGeometry} :
    ∀ L : G.Line, ∃ P : G.Point, ¬(G.Incident P L) := by
      intro L
      by_contra! hNeg

      sorry

end Geometry.Ch2.Prop
