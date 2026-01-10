module

public import Geometry.Ch2.Theory

namespace Geometry.Ch2.Defs

open Geometry.Ch2.Theory

variable {G : FreeGeometry}

-- p. 70, "Three or more lines `l, m, n` are _concurrent_ if there exists a point incident with all of them."
@[expose] public def Concurrent (L M N : FreeGeometry.Line) : Prop :=
    ∃ P : FreeGeometry.Point, (P on L) ∧ (P on M) ∧ (P on N)

end Geometry.Ch2.Defs
