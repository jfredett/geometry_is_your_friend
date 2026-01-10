module

public import Geometry.Ch2.Theory

open Geometry.Ch2.Theory

namespace Geometry.Ch2.Defs

-- p. 70, "Three or more points A, B, C are _collinear_ if there exists a line incident with all of them."
@[expose] public def Collinear {G : IncidenceGeometry} (A B C : G.Point) : Prop :=
    ∃ L : G.Line, G.Incident A L ∧ G.Incident B L ∧ G.Incident C L

end Geometry.Ch2.Defs
