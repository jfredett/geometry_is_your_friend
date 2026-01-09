import GeometryIsYourFriend.Hilbert
import Mathlib

open GeometryIsYourFriend.Hilbert

-- this I don't care about
set_option linter.style.longLine false
-- FIXME: this I don't understand
set_option linter.style.multiGoal false



namespace HilbertPlane

-- p. 70, "Three or more points A, B, C are _collinear_ if there exists a line incident with all of them."
def Collinear {G : HilbertPlane} (A B C : G.Point) : Prop :=
    ∃ L : G.Line, G.Incident A L ∧ G.Incident B L ∧ G.Incident C L
-- p. 70, "Three or more lines `l, m, n` are _concurrent_ if there exists a point incident with all of them."
def Concurrent {G : HilbertPlane} (L M N : G.Line) : Prop :=
    ∃ P : G.Point, G.Incident P L ∧ G.Incident P M ∧ G.Incident P N

-- p. 20, "Two lines `l` and `m` are parallel if they do not intersect, i.e., if no point lies on both
-- of them. We denote this by `l || m`"
-- p. 70, "Lines `l` and `m` are _parallel_ if they are distinct lines and no point is incident to both
-- of them."
-- TODO: implement the notation
def Parallel {G : HilbertPlane} (L M : G.Line) : Prop := L ≠ M ->
  ∀ P : G.Point, ¬(G.Incident P L ∧ G.Incident P M)

-- pp. 71: If `l` and `m` are distinct lines that are not parallel, then `l` and
-- `m` have a unique point in common
theorem prop_2_1_nonparallel_intersection {G : HilbertPlane} (L M : G.Line) :
  L ≠ M → ¬(Parallel L M) → ∃! P : G.Point,
     G.Incident P L ∧ G.Incident P M
:= by
    intro hDistinctLines
    unfold Parallel
    push_neg
    rintro ⟨_, ⟨P, hPonLM⟩⟩
    refine ⟨P, ?cEx, ?cUniq⟩
    -- existence
    exact hPonLM
    -- uniqueness
    intro Q
    by_contra! ⟨hQonLM, hNeg⟩
    -- idea, PQ = L, PQ = M, but L != M
    obtain ⟨PQ, _, hPQUniq⟩ := G.ia_1_unique_line P Q hNeg.symm
    have hLisPQ := hPQUniq L ⟨hPonLM.left, hQonLM.left⟩
    have hMisPQ := hPQUniq M ⟨hPonLM.right, hQonLM.right⟩
    have hLeqM : (L = M) := by
        rw [hMisPQ, hLisPQ]
    contradiction


-- Author suggests a lemma, "... to prove it, I could first prove a lemma that if three lines
-- are concurrent, the point at which they meet is unique." p.71
lemma lemma_2_2_1_three_concurrent_line_unique_intersection {G : HilbertPlane} (L M N : G.Line) :
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

theorem prop_2_2_three_distinct_lines {G : HilbertPlane} :
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


end HilbertPlane
