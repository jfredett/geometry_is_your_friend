module

public import Geometry.Tactics
public import Geometry.Ch2.Theory
public import Geometry.Ch2.Defs
public import Geometry.Ch2.Prop.P2
public import Geometry.Ch2.Prop.P3

open Geometry.Ch2.Defs

@[expose] public section

namespace Geometry.Ch2.Prop

open Geometry.Ch2.Theory
open Geometry.Ch2.Defs

variable (G : IncidenceGeometry)

-- Ed. Lemma "For every Point, there is at least one point that isn't that point."
lemma P5.L1 {G : IncidenceGeometry} : ∀ P : G.Point, ∃ Q : G.Point, P ≠ Q := by
    intro P
    obtain ⟨A, B, C, hDistinct, _⟩ := G.ia_3_three_noncolinear_points
    -- Idea: There is a configuration of 3 non-colinear points. Either P is one of those points, or it's none of
    -- them. If it's one of them, there are two other points distinct from P; if it's not one of them, then
    -- there are three distinct points.
    by_cases hSupposePeqA : P = A -- ∨ P = B ∨ P = C
    rw [<- hSupposePeqA] at hDistinct
    use B
    exact hDistinct.left
    use A

-- Ed. Lemma "Two lines are coincident iff every point on one is on the other."
lemma P5.L2 {G : IncidenceGeometry} : ∀ L M : G.Line,
     L = M ↔ ∀ P : G.Point, (P on L) ↔ (P on M) := by
     intros L M
     constructor
     -- Forward Case
     intros LeqM P
     rw [LeqM]
     -- Backward Case
     intro hAllPonLonM
     obtain ⟨A,B,AneB,AonL,BonL⟩ := G.ia_2_lines_have_two_points L
     obtain ⟨C,D,CneD,ConM,DonM⟩ := G.ia_2_lines_have_two_points M
     have ABonM : (A on M) ∧ (B on M) := by
        have AonM := hAllPonLonM A
        have BonM := hAllPonLonM B
        tauto
     -- Idea: Above, we show that under this case, A,B are on M, so let's construct the unique line AB from AB
     -- This is obviously equal to both L and M, since it's uniquely defined by A and B
     obtain ⟨AB, ⟨AonAB, BonAB⟩, ABuniq⟩ := G.ia_1_unique_line A B AneB
     have ABeqL := ABuniq L ⟨AonL, BonL⟩
     have ABeqM := ABuniq M ABonM
     rw [ABeqL, ABeqM]

-- Ed. Corollary "Two lines are distinct iff they have at least one point not in common"
lemma P5.L2.C1 {G : IncidenceGeometry} : ∀ L M : G.Line,
    L ≠ M ↔ ∃ P, ((P on L) ∧ (P off M)) ∨ ((P off L) ∧ (P on M)) := by
    -- TODO: This is ugly, and it's essentially just !P5.L2, but I couldn't cajole it into place.
    intros L M
    contrapose!
    rw [P5.L2]
    constructor
    intros LMCoincident P
    have LeqM : L = M := by
        rw [P5.L2]; trivial
    rw [LeqM]
    constructor
    tauto
    tauto
    intros h P
    specialize h P
    constructor
    exact h.left
    have hR := h.right
    tauto

-- TODO: P5.L1 allows an 'arbitrary ray' construction, given P, obtain PQ a random ray from P.
-- some macro? I don't know how to do this exactly, I feel like it might be a `def`?

-- p71. "For every point P, there are at least two distinct lines through P"
theorem P5 {G : IncidenceGeometry} :
    ∀ P : G.Point, ∃ L M : G.Line,
    L ≠ M ∧ (P on L) ∧ (P on M) := by
        intro P
        obtain ⟨Q, PneQ⟩ := P5.L1 P
        obtain ⟨PQ, ⟨PonPQ, QonPQ⟩, PQuniq⟩ := G.ia_1_unique_line P Q PneQ
        -- So we have an arbitrary ray PQ, by P2.3 there is a point R not on it.
        obtain ⟨R, RoffPQ⟩ := Geometry.Ch2.Prop.P3 PQ
        -- Since PQ avoids R, P ≠ R
        have PneR : P ≠ R := by
            by_contra! hNeg
            rw [<- hNeg] at RoffPQ
            tauto
        -- So we have PR ≠ PQ
        obtain ⟨PR, ⟨PonPR, RonPR⟩, PRuniq⟩ := G.ia_1_unique_line P R PneR
        -- Let's stake our claim
        use PQ, PR
        have PQnePR : PQ ≠ PR := by
            rw [P5.L2.C1]
            use R; tauto
        /- without the corollary, this is a few lines longer.
        -- 5.2.1 should have a much better proof, I just don't know enough lean to do it.
        have PQnePR : PQ ≠ PR := by
            by_contra! hNeg
            rw [P5.L2] at hNeg
            specialize hNeg R
            tauto -/
        -- trivial from here
        tauto

end Geometry.Ch2.Prop
