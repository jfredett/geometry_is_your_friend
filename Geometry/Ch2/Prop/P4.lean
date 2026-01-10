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

-- p71. "For every point, there is at least one line not passing through it."
theorem P4 {G : IncidenceGeometry} :
    ∀ P : G.Point, ∃ L : G.Line, ¬(G.Incident P L) := by
    sorry

end Geometry.Ch2.Prop
