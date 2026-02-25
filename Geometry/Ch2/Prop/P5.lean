import Geometry.Tactics

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Point.Ch1

import Geometry.Ch2.Prop.P2
import Geometry.Ch2.Prop.P3

namespace Geometry.Ch2.Prop

open Geometry.Theory

-- TODO: Move to Theory.Line
/-- Ed. Lemma "Two lines are coincident iff every point on one is on the other." -/
lemma P5.L2 : ∀ L M : Line,
     L = M ↔ ∀ P : Point, (P on L) ↔ (P on M) := by
     intros L M
     constructor
     -- Forward Case
     intros LeqM P
     rw [LeqM]
     -- Backward Case
     intro hAllPonLonM
     obtain ⟨A,B,AneB,AonL,BonL⟩ := I2 L
     obtain ⟨C,D,CneD,ConM,DonM⟩ := I2 M
     have ABonM : (A on M) ∧ (B on M) := by
        have AonM := hAllPonLonM A
        have BonM := hAllPonLonM B
        tauto
     -- Idea: Above, we show that under this case, A,B are on M, so let's construct the unique line AB from AB
     -- This is obviously equal to both L and M, since it's uniquely defined by A and B
     obtain ⟨AB, ⟨AonAB, BonAB⟩, ABuniq⟩ := I1 A B AneB
     have ABeqL := ABuniq L ⟨AonL, BonL⟩
     have ABeqM := ABuniq M ABonM
     rw [ABeqL, ABeqM]

-- TODO: Move to Theory.Line
/-- Ed. Corollary "Two lines are distinct iff they have at least one point not in common" -/
lemma P5.L2.C1 : ∀ L M : Line,
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

/-- p71. "For every point P, there are at least two distinct lines through P" -/
theorem P5 :
    ∀ P : Point, ∃ L M : Line,
    L ≠ M ∧ (P on L) ∧ (P on M) := by
        intro P
        have ⟨Q, PneQ⟩ := Point.distinct_points_exist P
        have ⟨PQ, _⟩ := I1 P Q PneQ
        -- So we have an arbitrary ray PQ, by P2.3 there is a point R not on it.
        obtain ⟨R, RoffPQ⟩ := Geometry.Ch2.Prop.P3 PQ
        -- Since PQ avoids R, P ≠ R
        have PneR : P ≠ R := by
            by_contra! hNeg
            rw [<- hNeg] at RoffPQ
            tauto
        -- So we have PR ≠ PQ
        obtain ⟨PR, ⟨PonPR, RonPR⟩, PRuniq⟩ := I1 P R PneR
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
