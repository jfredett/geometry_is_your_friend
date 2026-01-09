module

public import Geometry.Ch2.Theory

open Geometry.Ch2.Theory

namespace Geometry.Ch2.Defs

-- p. 70, "Three or more lines `l, m, n` are _concurrent_ if there exists a point incident with all of them."
@[expose] public def Concurrent {G : IncidenceGeometry} (L M N : G.Line) : Prop :=
    ∃ P : G.Point, G.Incident P L ∧ G.Incident P M ∧ G.Incident P N

end Geometry.Ch2.Defs
