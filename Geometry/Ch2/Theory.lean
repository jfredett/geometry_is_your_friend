module

public import Geometry.Tactics


@[expose] public section

namespace Geometry.Ch2.Theory

-- p. 69-70, IncidenceGeometry
public structure IncidenceGeometry where
    /-- Definitions -/
    (Point : Type)    -- Points exist
    (Line : Type) -- Two points determine a line
    /-- Primitive Constructions -/
    Incident : Point -> Line -> Prop
    /-- Axioms -/
    -- Incidence Axioms
    (ia_1_unique_line :
        ∀ P Q : Point, P ≠ Q ->
        ∃! L : Line, Incident P L ∧ Incident Q L)
    (ia_2_lines_have_two_points :
        ∀ L : Line,
        ∃ A B : Point,
         A ≠ B ∧ Incident A L ∧ Incident B L)
    (ia_3_three_noncolinear_points :
        ∃ A B C : Point,
        (A ≠ B ∧ A ≠ C ∧ B ≠ C) ∧
        (∀ (L : Line), Incident A L → Incident B L → ¬Incident C L))

end Geometry.Ch2.Theory

-- p71, "For every line, there is at least one point not lying on it."
-- theorem prop_2_3 := by sorry
-- p71. "For every point, there is at least one line not passing through it."
-- theorem prop_2_4 := by sorry
-- p71. "For every point P, there are at least two distinct lines through P"
-- theorem prop_2_5 := by sorry


-- p92. "For each pair of axioms of incidence geometry, invent an interpretation in which those two axioms are satisfied,
-- but the third is not. (This will show that the three axioms are _independent_ in the sense that it is impossible to
-- prove any one of them from the other two)."
-- theorem ex_2_7_ia_independence := by sorry

-- p92. "Show that the interpretations in examples 3 and 4 of [chapter 2] are models of incidence geometry and that the
-- Euclidian and hyperbolic parallel properties, respectively, hold for them."
-- theorem ex_2_8_model := by sorry

-- p93. "
-- A. Show that when each of two models of incidence geometry has exactly three "points" in it, the models are
-- isomorphic
-- theorem ex_2_10a := by sorry
-- B. Must two models having exactly four "points" be isomorphic? [Prove or provide counterex]"
-- theorem ex_2_10b := by sorry
-- [ED: C. Omitted since we're not doing ex 9.]

-- p93. "Invent a model of incidence geometry that has neither the elliptic, hyperbolic, nor Euclidean parallel
-- properties... [ED: Definitions follow]"
-- example ex_2_11 := by sorry

-- exercise 2.12 := by sorry

-- FIXME: Ideally, propositions would be under their own ns, and exercises another. so the result'd be something like:
-- Geometry.ch2.props.p1 -> prop 2.1
-- Geometry.ch2.exers.e1 -> exercise 1 of ch2

-- TODO: Macro for prop vs theorem that does the above.

-- NOTE: Exercises are only going to be done where it makes sense to do them, e.g., if they have geometric value.
-- many of the exercises, especially in the early chapters, are just exercising basic logic rules, and while that's
-- valuable and you should do it, it's assumed that if you know what Lean4 is, have assessed this work as _somehow_
-- having value, and are reading this comment, that you know how to manipulate logical sentences relatively well.
