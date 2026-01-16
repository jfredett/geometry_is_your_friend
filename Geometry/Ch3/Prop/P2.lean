import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Tactics

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1
import Geometry.Ch3.Prop.B4iii

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop


/- If L splits A and B, then L avoids A and B -/
lemma P2.Lz {A B : Point} {L : Line} : (L splits A and B) -> (L avoids A) ∧ (L avoids B) := by
  intro LsplitsAB
  unfold SameSide at LsplitsAB
  push_neg at LsplitsAB
  obtain ⟨⟨AoffL, BoffL⟩, AneB, ⟨P, PonAB, PonL⟩⟩ := LsplitsAB
  unfold Segment at PonAB; simp only [mem_setOf_eq] at PonAB
  tauto


/- This is true too, I think my formulation may be a little off. -/
lemma P2.Lz2 {A B : Point} {L : Line} : (L guards A and B) -> (L avoids A) ∧ (L avoids B) := by
  by_contra! hNeg
  unfold SameSide at hNeg
  simp_all only [mem_setOf_eq, and_imp]
  obtain ⟨h, h0⟩ := hNeg
  simp_all only [not_false_eq_true, not_true_eq_false, IsEmpty.forall_iff, implies_true]
  sorry

/- Ed. If L splits A and B, there is a unique X at which L and the segment A B intersect.
that is, L ∩ segment A B = {X}. This effectively extends Ch2.P1 over segments, similar
could be done for rays/extensions as well. -/
lemma P2.Ly {A B : Point} {L : Line} : (L splits A and B) -> ∃! X : Point, X on L ∧ X on segment A B := by
  intro LsplitsAandB
  unfold SameSide at LsplitsAandB
  push_neg at LsplitsAandB
  obtain ⟨⟨AoffL, BoffL⟩, AneB, X, ⟨XonAB, XonL⟩⟩ := LsplitsAandB
  use X
  simp only [mem_setOf_eq, and_imp]
  constructor; constructor
  trivial
  exact XonAB
  intro Y YonL
  by_contra! ⟨AYBorAeqYorBeqY, YneX⟩
  --
  have LneAB : L ≠ segment A B := by
    by_contra! hNeg
    unfold Segment at hNeg; simp only [P5.L2, mem_setOf_eq] at hNeg
    specialize hNeg A
    simp at hNeg
    contradiction
  have LnparAB : L ∦ segment A B := by tauto
  have YonAB : Y on segment A B := AYBorAeqYorBeqY
  obtain ⟨P, _, PUniq⟩ := Ch2.Prop.P1 L (segment A B) LneAB LnparAB
  simp only [mem_setOf_eq, and_imp] at PUniq
  have Xuniq := (PUniq X XonL XonAB)
  have Yuniq := (PUniq Y YonL YonAB)
  rw [<- Xuniq] at Yuniq; contradiction


/- Ed. If L splits A and B at the point X, then there is a point C such that A - C - X, C ≠ A, C off L -/
-- lemma P2.Lx : L splits A and B -> ∃ C : Point, A - O - B


/- p112. "Every line bounds exactly two half-planes, and these half-planes have no point in common."

B4 is the plane-separation axiom, 3.2 here is on the path toward proving the more useful line-separation property later in 3.4.
I've chosen to notate the halfplanes in the theorem as 'Hl' and 'Hr' for 'left' and 'right' half-plane, respectively.
-/
theorem P2 (L : Line) : ∃ Hl Hr : Set Point, Hl ∩ Hr = ∅ ∧
  ∀ P : Point, (P on L) -> (P ∉ Hl) ∧ (P ∉ Hr)
:= by
  /- p.112 "(1) There is a point A not lying on l, (Proposition 2.3 [Ch2.Prop.P3])." -/
  obtain ⟨A, AoffL⟩ := Ch2.Prop.P3 L
  /- "There is a point O lying on l (Incidence Axiom 2 [I2])."-/
  obtain ⟨O, _, _, OonL, _⟩ := I2 L
  /- "There is a point B such that B * O * A (Betweenness Axiom 2 [B2])"-/
  have AneO : A ≠ O := by -- author omits this step
    by_contra!; rw [this] at AoffL; tauto
  obtain ⟨B, _, _, _, _, bBOA, _, _⟩ := B2 O A AneO.symm
  /- "Then A and B are on opposite sides of l (by definition), ..."-/
  have ⟨⟨BneO,OneA,BneA⟩, ⟨_, BOACol⟩⟩ := B1a bBOA -- author omits this step.
  have BoffL : B off L := by
    -- idea, three colinear points, one off a line and the other on, means the third point is off the line or
    -- is the on-line point.
    sorry;
  have LsplitsAB : L splits A and B := by
    push_neg; constructor; constructor; exact AoffL
    exact BoffL; constructor; exact BneA.symm
    use O; unfold Segment; simp only [mem_setOf_eq]
    constructor
    left; rw [B1b]; tauto
    tauto
  /- "so L has at least two sides." -/
  /- "Let C be any point distinct from A and B not lying on l"

  Ed. Construct point C off L and distinct from A and B as follows.

  1. Take AB and find it's intersection by L, call it X
  2. Examine segment A X with B2, we want C with A - C - X
  3. Use C.

  obtain ⟨C, CoffL, CneA⟩ := by sorry
  obtain ⟨C, CoffL⟩ := Ch2.Prop.P3 L
  have ⟨CneA, CneB⟩  : C ≠ A ∧ C ≠ B := by
    unfold SameSide at LsplitsAB; push_neg at LsplitsAB
    have ⟨AneB, ⟨P, PonAB, PonL⟩⟩ := LsplitsAB
    constructor;
  -/



/-
    by_contra! CeqA
    -- Idea: B-O-A is B-O-C under the AeqB assumption, so BC and AB both pass through L at O, AOB and BOC are collinear
    --  -- lemma, if ABC are Col, and BCD are col, then ABD are col -- I might have this already?
    --  -- lemma, if ABC, B is on the segment A C
    --  -- idea, if A-O-B and B-O-C -- this is the contradiction, I don't know how to prove it, but it's the contradiction.
    have bBOC : B - O - C := by
      rwa [<- CeqA] at bBOA;
    have bAOB : A - O - B := by
      sorry
-/



  /- "If C and B are not on the same side of L, then C and A are on the same
  side of L (by the law of the excluded middle and Betweenness Axiom 4(ii))." -/
  by_cases LsplitsBC : L splits B and C
  have BoffL : B off L := by sorry
  have LguardsAC : L guards A and C := by
    by_contra LsplitsAC
    have LguardsAB := B4ii ⟨AoffL, CoffL, BoffL⟩ ⟨LsplitsAC, B4iii.L1.splits L B C LsplitsBC⟩
    contradiction
  /- "So the set of points not on L is the union of side Hₐ of A and the side Hₐ of B." -/



  sorry




  /- "" -/



end Geometry.Ch3.Prop
