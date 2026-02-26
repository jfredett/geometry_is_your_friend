/- Lemmas relating to lines that do not require any theory besides the basic axioms available in Ch1. -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Tactics

namespace Geometry.Theory.Line

open Set
open Geometry.Theory

/-- Author suggests a lemma, "... to prove it, I could first prove a lemma that if three lines
are concurrent, the point at which they meet is unique." p.71 -/
lemma concurrence_of_three_lines_is_unique :
        L ≠ M ∧ M ≠ N ∧ L ≠ N ->
        Concurrent L M N ->
        ∃! P : Point,
        (P on L) ∧ (P on M) ∧ (P on N)
:= by
    intros hDistinct hConcurrent
    unfold Concurrent at *
    obtain ⟨P, hPonL, hPonM, hPonN⟩ := hConcurrent
    refine ⟨P, ?cEx, ?cUniq⟩
    -- existence
    exact ⟨hPonL, hPonM, hPonN⟩
    -- uniqueness
    intro Q ⟨hQonL, hQonM, hQonN⟩
    by_contra! hNeg
    have ⟨PQ, _, hPQUniq⟩ := I1 P Q hNeg.symm
    have hPQisL := hPQUniq L ⟨hPonL, hQonL⟩
    have hPQisM := hPQUniq M ⟨hPonM, hQonM⟩
    have hLeqM : L = M := by
        rw [hPQisL, hPQisM]
    have hLneqM : L ≠ M := hDistinct.left
    contradiction

/-- We need to be able to establish that two intersecting lines are never parallel -/
lemma intersecting_lines_are_not_parallel {L M : Line} {P : Point} : (P on L) -> (P on M) -> (L ∦ M) := by
      intros hPonM hPonL
      unfold Parallel; push_neg
      intro hLMDistinct
      use P

/-- Two lines are coincident iff every point on one is on the other. -/
lemma coincidence_is_coincidence_of_all_points : ∀ L M : Line,
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

/-- Two lines are distinct iff they have at least one point not in common -/
lemma distinguishing_point : ∀ L M : Line,
    L ≠ M ↔ ∃ P, ((P on L) ∧ (P off M)) ∨ ((P off L) ∧ (P on M)) := by
    -- TODO: This is ugly, and it's essentially just !P5.L2, but I couldn't cajole it into place.
    intros L M
    contrapose!
    rw [coincidence_is_coincidence_of_all_points]
    constructor
    intros LMCoincident P
    have LeqM : L = M := by
      rw [coincidence_is_coincidence_of_all_points]; trivial
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

end Geometry.Theory.Line
