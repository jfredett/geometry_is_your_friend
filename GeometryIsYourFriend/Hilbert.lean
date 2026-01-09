-- p. 69,
structure HilbertPlane where
    /-- Definitions -/
    (Point : Type u)                  -- Points exist
    (Line : Type u) -- Two points determine a line
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
        (∀ L : Line,
        (Incident A L ∧ Incident B L -> ¬Incident C L) ∨
         (Incident B L ∧ Incident C L -> ¬Incident A L) ∨
         (Incident A L ∧ Incident C L -> ¬Incident B L)))
