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

-- p71. "For every point P, there are at least two distinct lines through P"
theorem P5 { G : IncidenceGeometry } :
    ∀ P : G.Point, ∃ L M : G.Line,
    L ≠ M ∧ G.Incident P L ∧ G.Incident P M := by
     sorry
