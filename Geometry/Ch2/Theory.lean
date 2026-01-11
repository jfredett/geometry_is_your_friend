module

public import Geometry.Tactics


@[expose] public section

namespace Geometry.Ch2.Theory


-- FIXME: this might actually belong in a hypothetical 'Ch1' theory. Where maybe some definitions could end up (Parallel, Colinear, Concurrent?)
public class FreeGeometry where
    /-- Definitions -/
    (Point : Type)  -- Points exist
    (Line : Type)   -- Two points determine a line
    /-- Primitive Constructions -/
    Incident : Point -> Line -> Prop

variable {G : FreeGeometry}

def On [FreeGeometry] (P : FreeGeometry.Point) (L : FreeGeometry.Line) : Prop := FreeGeometry.Incident P L

notation:20 P " on " L => On P L
notation:20 P " off " L => ¬(On P L)
notation:20 L " has " P => (On P L)
notation:20 L " avoids " P => ¬(On P L)

-- p. 69-70, IncidenceGeometry
public class IncidenceGeometry extends FreeGeometry where
    (ia_1_unique_line :
        ∀ P Q : Point, P ≠ Q ->
        ∃! L : Line, (P on L) ∧ (Q on L))
    (ia_2_lines_have_two_points :
        ∀ L : Line,
        ∃ A B : Point,
         A ≠ B ∧ (A on L) ∧ (B on L))
    (ia_3_three_noncolinear_points :
        ∃ A B C : Point,
        (A ≠ B ∧ A ≠ C ∧ B ≠ C) ∧
        (∀ (L : Line), (A on L) → (B on L) → (C off L)))

end Geometry.Ch2.Theory
