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
theorem P4 (P : G.Point) : ∃ L : G.Line, (P off L) := by
    -- Similar to 2.3, but using 2.2's configuration.
    obtain ⟨L, M, N, hDistinct, hNC⟩ := Geometry.Ch2.Prop.P2
    unfold Concurrent at hNC
    by_contra! hNeg
    push_neg at *
    specialize hNC P
    have PonN := hNeg N
    have PoffN := hNC (hNeg L) (hNeg M)
    contradiction

end Geometry.Ch2.Prop
