module

public import Geometry.Ch2.Theory

namespace Geometry.Ch2.Defs

open Geometry.Ch2.Theory

variable {G : FreeGeometry}

-- p. 70, "Three or more points A, B, C are _collinear_ if there exists a line incident with all of them."
@[expose] public def Collinear (A B C : G.Point) : Prop :=
    ∃ L : G.Line, (A on L) ∧ (B on L) ∧ (C on L)

end Geometry.Ch2.Defs
