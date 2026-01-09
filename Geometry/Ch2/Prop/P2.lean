module

public import Geometry.Tactics
public import Geometry.Ch2.Theory
public import Geometry.Ch2.Defs

open Geometry.Ch2.Defs

@[expose] public section

open Geometry.Ch2.Theory
open Geometry.Ch2.Defs

variable (G : IncidenceGeometry)

-- Author suggests a lemma, "... to prove it, I could first prove a lemma that if three lines
-- are concurrent, the point at which they meet is unique." p.71
lemma lemma_2_2_1_three_concurrent_line_unique_intersection {G : IncidenceGeometry} (L M N : G.Line) :
        L ≠ M ∧ M ≠ N ∧ L ≠ N ->
        Concurrent L M N ->
        ∃! P : G.Point,
        G.Incident P L ∧ G.Incident P M ∧ G.Incident P N
:= by
    intros hDistinct hConcurrent
    unfold Concurrent at *
    obtain ⟨P, hPonL, hPonM, hPonN⟩ := hConcurrent
    refine ⟨P, ?cEx, ?cUniq⟩
    -- existence
    exact ⟨hPonL, hPonM, hPonN⟩
    -- uniqness
    intro Q ⟨hQonL, hQonM, hQonN⟩
    by_contra hNeg
    push_neg at hNeg
    have ⟨PQ, _, hPQUniq⟩ := G.ia_1_unique_line P Q hNeg.symm
    have hPQisL := hPQUniq L ⟨hPonL, hQonL⟩
    have hPQisM := hPQUniq M ⟨hPonM, hQonM⟩
    have hLeqM : L = M := by
        rw [hPQisL, hPQisM]
    have hLneqM : L ≠ M := hDistinct.left
    contradiction

-- p71, "There exist three distinct lines that are not concurrent."
theorem prop_2_2_three_distinct_lines {G : IncidenceGeometry} :
        ∃ L M N : G.Line, L ≠ M ∧ M ≠ N ∧ L ≠ N
    := by
    obtain ⟨A, B, C, hDistinct, hNC⟩ := G.ia_3_three_noncolinear_points
    rcases hDistinct with ⟨hAneB, hAneC, hBneC⟩
    obtain ⟨AB, hABonAB, hABUniq⟩ := G.ia_1_unique_line A B hAneB
    obtain ⟨BC, hBConBC, hBCUniq⟩ := G.ia_1_unique_line B C hBneC
    obtain ⟨AC, hAConAC, hACUniq⟩ := G.ia_1_unique_line A C hAneC

    use AB
    use BC
    use AC


    sorry
