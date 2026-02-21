import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Tactics

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1
import Geometry.Ch3.Prop.B4iii
import Geometry.Ch3.Prop.A

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop


/- p112. "Every line bounds exactly two half-planes, and these half-planes have no point in common."

B4 is the plane-separation axiom, 3.2 here is on the path toward proving the more useful line-separation property later in 3.4.
I've chosen to notate the halfplanes in the theorem as 'Hl' and 'Hr' for 'left' and 'right' half-plane, respectively.
-/
theorem P2.i (L : Line) : ∃ Hl Hr : Set Point,
  ∀ P : Point, (P on L) -> (P ∉ Hl) ∧ (P ∉ Hr)
:= by
  /- p.112 "(1) There is a point A not lying on l, (Proposition 2.3 [Ch2.Prop.P3])." -/
  obtain ⟨A, AoffL⟩ := Ch2.Prop.P3 L
  /- "(2) There is a point O lying on l (Incidence Axiom 2 [I2])."-/
  obtain ⟨O, _, _, OonL, _⟩ := I2 L
  /- "(3) There is a point B such that B * O * A (Betweenness Axiom 2 [B2])"-/
  have AneO : A ≠ O := by -- author omits this step
    by_contra!; rw [this] at AoffL; tauto
  obtain ⟨B, _, _, _, _, hDistinctBOA, bBOA, _, _⟩ := B2 O A AneO.symm -- this is the author's approach, I've tucked it away in a lemma below
  /- author omits these, but they are necessary for the 'by definition' below. -/
  have AneB : A ≠ B := Ne.symm (Betweenness.abc_imp_anec bBOA)
  have BoffL : B off L := by
    -- idea: since A is off L, and O is on, the AO intersects L at O, extend AO, since AOB, then B is on this extension.
    sorry
  /- "(4) Then A and B are on opposite sides of l (by definition), ..." -/
  have LsplitsAB : L splits A and B := by
    unfold SameSide
    push_neg
    constructor
    · exact ⟨AoffL, BoffL⟩
    · constructor
      · exact AneB
      · use O;
        constructor
        · unfold Segment; simp only [mem_setOf_eq];
          left; exact (B1b B O A).mp bBOA
        · exact OonL
  /- "so L has at least two sides." -/
  /- "(5) Let C be any point distinct from A and B not lying on l..."

  Ed. Construct point C off L and distinct from A and B as follows.

  1. Take AB and find it's intersection by L, call it O (since that's where it is)
  2. Examine segment A O with B2, we want C with A - C - O
  3. Use C.
  -/
  have LneAB : L ≠ segment A B := by
    by_contra! hNeg;
    rw [hNeg] at AoffL;
    have AonAB : A on segment A B := by tauto
    contradiction
  have LnoparAB : L ∦ segment A B := by
    by_contra! hNeg
    unfold Parallel at hNeg
    specialize hNeg LneAB O
    push_neg at hNeg
    specialize hNeg OonL
    unfold Segment at hNeg; simp only [mem_setOf_eq, not_or] at hNeg
    obtain ⟨nAOB, _, _⟩ := hNeg
    have AOB := (B1b B O A).mp bBOA
    contradiction
  /- Define these here for use below. -/
  let Hl : Set Point := {P | L guards A and P}
  let Hr : Set Point := {P | L guards B and P}
  let PsoffL : Set Point := {P | P off L}

  use Hl
  use Hr

  /- "So the set of points not on L is the union of side Hₐ of A and the side Hₐ of B."
      Ed. Note, to formalize this, we need to state the claim first. -/
  have claim1 : PsoffL = Hl ∪ Hr := by
    apply Subset.antisymm
    · intro C CinPsoffL
      have CoffL : C off L := by tauto
      simp only [mem_union]
      /- "If C and B are not on the same side of L, -/
      have AseparatefromB : (L splits B and C) -> (L guards A and C) := by
        intro LsplitsBC
        /- then C and A are on the same side of L (by the law of the excluded middle and Betweenness Axiom 4(ii))." -/
        by_contra LsplitsAC
        have LguardsAB := B4ii ⟨AoffL, CoffL, BoffL⟩ ⟨LsplitsAC, B4iii.L1.splits L B C LsplitsBC⟩
        contradiction
      by_cases suppose: L splits B and C
      · specialize AseparatefromB suppose
        have CinHl : C ∈ Hl := by tauto
        tauto
      · tauto
    /- "(6) If C were on both sides (RAA Hypothesis), then A and B would be on the
    same side (Axiom 4(i) [B4i]), contradicting step 4; hence the two sides are
    disjoint." -/
    · sorry





  sorry

end Geometry.Ch3.Prop
