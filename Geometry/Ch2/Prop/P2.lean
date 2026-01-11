module

public import Geometry.Tactics
public import Geometry.Ch2.Theory
public import Geometry.Ch2.Defs
public import Geometry.Ch2.Prop.P1

open Geometry.Ch2.Defs

@[expose] public section

namespace Geometry.Ch2.Prop

open Geometry.Ch2.Theory
open Geometry.Ch2.Defs

variable (G : IncidenceGeometry)

-- Author suggests a lemma, "... to prove it, I could first prove a lemma that if three lines
-- are concurrent, the point at which they meet is unique." p.71
lemma P2.L1 {G : IncidenceGeometry} (L M N : G.Line) :
        L ≠ M ∧ M ≠ N ∧ L ≠ N ->
        Concurrent L M N ->
        ∃! P : G.Point,
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
    have ⟨PQ, _, hPQUniq⟩ := G.ia_1_unique_line P Q hNeg.symm
    have hPQisL := hPQUniq L ⟨hPonL, hQonL⟩
    have hPQisM := hPQUniq M ⟨hPonM, hQonM⟩
    have hLeqM : L = M := by
        rw [hPQisL, hPQisM]
    have hLneqM : L ≠ M := hDistinct.left
    contradiction

-- Editor's Lemma: We need to be able to establish that two intersecting lines are never
-- parallel
lemma P2.L2 {G : IncidenceGeometry} (L M : G.Line) :
    L ≠ M -> ∀ P : G.Point, (P on L) -> (P on M) -> (L ∦ M) := by
      intros hLMDistinct P hPonM hPonL
      unfold NotParallel
      -- L ≠ M by assumption
      constructor
      exact hLMDistinct
      -- incidence
      use P

-- p71, "There exist three distinct lines that are not concurrent."
theorem P2 {G : IncidenceGeometry} :
        ∃ L M N : G.Line, (L ≠ M ∧ M ≠ N ∧ L ≠ N) ∧ ¬Concurrent L M N
    := by
    -- Idea: Use the 3 non-collinear points to build three lines, we can prove they're distinct with
    -- some RAA, and then use the lemma to do the rest.
    obtain ⟨A, B, C, hDistinct, hNC⟩ := G.ia_3_three_noncolinear_points
    rcases hDistinct with ⟨hAneB, hAneC, hBneC⟩
    obtain ⟨AB, ⟨hAonAB, hBonAB⟩, hABUniq⟩ := G.ia_1_unique_line A B hAneB
    obtain ⟨BC, ⟨hBonBC, hConBC⟩, hBCUniq⟩ := G.ia_1_unique_line B C hBneC
    obtain ⟨AC, ⟨hAonAC, hConAC⟩, hACUniq⟩ := G.ia_1_unique_line A C hAneC
    -- establish distinctness of lines
    have hABneBC : AB ≠ BC := by
      by_contra! hABeqBC
      have hCoffBC := hNC AB hAonAB hBonAB
      rw [hABeqBC] at hCoffBC
      contradiction
    have hABneAC : AB ≠ AC := by
      by_contra! hABeqAC
      have hCoffAC := hNC AB hAonAB hBonAB
      rw [hABeqAC] at hCoffAC
      contradiction
    have hBCneAC : BC ≠ AC := by
      by_contra! hBCeqAC
      rw [hBCeqAC] at hBonBC
      have hCoffAC := hNC AC hAonAC hBonBC
      contradiction
    -- Use our constructed apparatus
    use AB, BC, AC
    -- distinctness is already proven above
    constructor; trivial
    -- Now that everything is built, we proceed by contradiction
    by_contra! hNeg
    -- Let's find the Point the Author talks about in the proposed lemma
    obtain ⟨P, ⟨hPonAB, hPonBC, hPonAC⟩, hPUniq⟩ := P2.L1 AB BC AC ⟨hABneBC,hBCneAC,hABneAC⟩ hNeg
    -- This lemma was not suggested by the author, but is handy. The proof is not long and simply establishes the
    -- 'NotParallel' fact for each pair of lines. We need the unique point and the negative condition to build
    -- these
    have hABnotparBC : NotParallel AB BC := P2.L2 AB BC hABneBC P hPonAB hPonBC
    have hABnotparAC : NotParallel AB AC := P2.L2 AB AC hABneAC P hPonAB hPonAC
    have hBCnotparAC : NotParallel BC AC := P2.L2 BC AC hBCneAC P hPonBC hPonAC
    -- Idea: If P is on AB and BC, then P must be the intersection of those two lines, we already know B is on
    -- both AB and BC, and by P1, we know the intersection is unique, so P = B, but that means B is on AC, which
    -- which is false.
    -- We can use 2.1 to find the unique intersection, we mostly care about the uniqueness condition, not the
    -- incidence on.
    obtain ⟨X, _, hXUniq⟩ := Geometry.Ch2.Prop.P1 G AB BC hABneBC hABnotparBC
    -- This condition makes proving this a matter of plug and chug
    have hPeqB : P = B := by
      have BeqX := hXUniq B ⟨hBonAB, hBonBC⟩
      have PeqX := hXUniq P ⟨hPonAB, hPonBC⟩
      rw [BeqX, PeqX]
    -- If P = B, the B on AC, since P on AC
    have hBonAC : G.Incident B AC := by
      rw [hPeqB] at hPonAC
      exact hPonAC
    -- Use Non-collinearity to show non-concurrence
    specialize hNC AC hAonAC hBonAC
    contradiction
