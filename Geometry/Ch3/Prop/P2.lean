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

lemma P2.Lb : A - B - C ∧ A - C - B -> False := by
  intro ⟨ABC, ACB⟩
  obtain ⟨⟨AneB, BneC, AneC⟩, ⟨⟨L, AonL, BonL, ConL⟩, ABCCol⟩⟩ := B1a ABC
  obtain ⟨⟨AneC, CneB, AneB⟩, ⟨⟨M, AonM, ConM, BonM⟩, ACBCol⟩⟩ := B1a ACB
  rcases B3 A B C ⟨AneB, BneC, AneC, ABCCol⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  contradiction; contradiction; contradiction

lemma P2.Lc : distinct A C X B -> Collinear A C X ∧ Collinear A X B -> Collinear A C B := by
  intro_distinct hACXDistinct
  intro ⟨ACXCol, AXBCol⟩
  unfold PairwiseDistinct at hACXDistinct; simp at hACXDistinct;
  have b3ConditionACX : A ≠ C ∧ C ≠ X ∧ A ≠ X ∧ Collinear A C X := by tauto
  have b3ConditionAXB : A ≠ X ∧ X ≠ B ∧ A ≠ B ∧ Collinear A X B := by tauto
  obtain ⟨ACB, _⟩ := B3 A C X b3ConditionACX
  obtain ⟨AXB, _⟩ := B3 A X B b3ConditionAXB
  unfold Collinear at *; simp_all only [not_false_eq_true, and_self, true_and, and_true, ne_eq, B1a]


  sorry

lemma P2.Lk : A - C - X -> C - A - B -> A - X - B -> False := by
  intro ACX CAB AXB
  by_contra!
  obtain ⟨⟨AneC, CneX, AneX⟩, ⟨⟨L, AonL, ConL, XonL⟩, ACXCol⟩⟩ := B1a ACX
  obtain ⟨⟨CneA, CneB, AneB⟩, ⟨⟨M, ConM, AonM, BonM⟩, CABCol⟩⟩ := B1a CAB
  obtain ⟨_, ⟨_, AXBCol⟩⟩ := B1a AXB
  rcases B3 A C X ⟨AneC, CneX, AneX, ACXCol⟩ with ⟨ACX, nCAX, nAXC⟩ | ⟨nACX, CAX, nAXC⟩ | ⟨nACX, nCAX, AXC⟩



  sorry

lemma P2.Lj : A - B - C -> A - C - B -> False := by
  intro ABC ACB
  by_contra!
  exact P2.Lb ⟨ABC, ACB⟩



lemma P2.La {A B C X : Point} : A - C - X -> A - X - B -> A - C - B := by
  intro ACX AXB
  obtain ⟨⟨AneC, CneX, AneX⟩, ⟨⟨L, AonL, ConL, XonL⟩, ACXCol⟩⟩ := B1a ACX
  obtain ⟨⟨AneX, XneB, AneB⟩, ⟨⟨M, AonM, XonM, BonM⟩, AXBCol⟩⟩ := B1a AXB
  --
  have CneB : C ≠ B := by
    by_contra! hNeg
    rw [hNeg] at ACX
    -- need A B X and A X B are a contradiction
    exact P2.Lb ⟨ACX, AXB⟩

  have hDistinct : A ≠ B ∧ A ≠ C ∧ A ≠ X ∧ B ≠ X ∧ B ≠ X ∧ C ≠ X := by sorry
  have LcCondition : distinct A C X B := by sorry
  have ACBCol : Collinear A C B := Lc LcCondition ⟨ACXCol, AXBCol⟩
  -- the diagram is:  A - C - X - B
  --
  -- the options are ACB, CAB (rejected by ACX, since i)
  rcases B3 A C B ⟨AneC, CneB, AneB, ACBCol⟩ with ⟨ACB, nCAB, nABC⟩ | ⟨nACB, CAB, nABC⟩ | ⟨nACB, nCAB, ABC⟩
  exact ACB
  exfalso; sorry -- ACX contradicts CAB, since A is 'to the left' of C
  exfalso; sorry -- ACX contradicts ABC, since




lemma P2.Lzz : A - X - B -> segment A B = segment A X ∪ segment X B := by
  intro AXB
  unfold Segment; simp only [P5.L2, mem_setOf_eq, mem_union]
  intro P
  constructor
  intro h0
  rcases h0 with APB | AeqP | BeqP


  sorry




  sorry

/-
Ed. If L splits A and B at the point X, then there is a point C such that A - C - X, C ≠ A, C off L

The 'L intersects M at X' notation that is introduced here is not one the author
defines directly anywhere I have seen. He mentions it in _Undefined Terms_
(p.13) but does not provide a formal defintion.
The details of the property in action can be seen below, the assertion I think will be non-controversial.
-/
lemma P2.Lx {A B X : Point} {L : Line} :
  (L splits A and B) ∧ (L intersects (segment A B) at X) ->
  ∃ C : Point, A - C - X ∧ C ≠ A ∧ C off L := by
  rintro ⟨hLsplitsAB, LcrossesABatX⟩
  obtain ⟨XonL, XonAB, Xuniq, XintABeqX⟩ := LcrossesABatX
  have AoffL : A off L := by
    by_contra! hNeg
    specialize Xuniq A
    unfold SameSide at hLsplitsAB; push_neg at hLsplitsAB
    obtain ⟨⟨AoffL, _⟩, _⟩ := hLsplitsAB
    contradiction
  have AneX : A ≠ X := by
    by_contra
    rw [this] at AoffL
    contradiction
  have ⟨D,C,E, AX, ⟨_, AonAX, ConAX, XonAX, _⟩, hDistinctACX, DAX, ACX, AXE⟩ := B2 A X AneX
  -- This is ugly, I am not very good at inductive datatypes in lean yet.
  unfold PairwiseDistinct at hDistinctACX ; simp only [ne_eq, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true,
    List.Pairwise.nil, and_self, and_true] at hDistinctACX
  have ⟨⟨DneA, DneC, DneX, DneE⟩, ⟨AneC, AneX, AneE⟩, ⟨CneX, CneE⟩, XneX⟩ := hDistinctACX
  use C
  constructor; exact ACX;
  constructor; tauto
  by_contra! ConL
  have ConAB : C on segment A B := by
    unfold Segment; simp only [mem_setOf_eq];
    constructor
    unfold Segment at XonAB; simp only [mem_setOf_eq] at XonAB
    rcases XonAB with AXB | AeqX | BeqX
    exact La ACX AXB
    contradiction;
    rw [BeqX]; exact ACX
  obtain CeqX := (Xuniq C ⟨ConL, ConAB⟩);
  rw [CeqX] at CneX
  contradiction
/- p112. "Every line bounds exactly two half-planes, and these half-planes have no point in common."

B4 is the plane-separation axiom, 3.2 here is on the path toward proving the more useful line-separation property later in 3.4.
I've chosen to notate the halfplanes in the theorem as 'Hl' and 'Hr' for 'left' and 'right' half-plane, respectively.
-/
theorem P2 (L : Line) : ∃ Hl Hr : Set Point, Hl ∩ Hr = ∅ ∧
  ∀ P : Point, (P on L) -> (P ∉ Hl) ∧ (P ∉ Hr)
:= by
  /- p.112 "(1) There is a point A not lying on l, (Proposition 2.3 [Ch2.Prop.P3])." -/
  obtain ⟨A, AoffL⟩ := Ch2.Prop.P3 L
  /- "(2) There is a point O lying on l (Incidence Axiom 2 [I2])."-/
  obtain ⟨O, _, _, OonL, _⟩ := I2 L
  /- "(3) There is a point B such that B * O * A (Betweenness Axiom 2 [B2])"-/
  have AneO : A ≠ O := by -- author omits this step
    by_contra!; rw [this] at AoffL; tauto
  obtain ⟨B, _, _, _, _, hDistinctBOA, bBOA, _, _⟩ := B2 O A AneO.symm
  /- "(4) Then A and B are on opposite sides of l (by definition), ..."-/
  have ⟨⟨BneO,OneA,BneA⟩, ⟨_, BOACol⟩⟩ := B1a bBOA -- author omits this step.
  have BoffL : B off L := by
    -- idea, three colinear points, one off a line and the other on, means the third point is off the line or
    -- is the on-line point.
    sorry;
  have LsplitsAB : L splits A and B := by
    push_neg;
    constructor; exact Classical.not_imp.mp fun a ↦ BoffL (a AoffL)
    constructor; exact Ne.intro (id (Ne.symm BneA))
    use O;
    constructor; unfold Segment; simp_all only [ne_eq, B1b, B1a, mem_setOf_eq, or_self, or_false]
    exact OonL
  /- "so L has at least two sides." -/
  /- "(5) Let C be any point distinct from A and B not lying on l..."

  Ed. Construct point C off L and distinct from A and B as follows.

  1. Take AB and find it's intersection by L, call it X
  2. Examine segment A X with B2, we want C with A - C - X
  3. Use C.
  -/
  obtain ⟨X, XintersectsABandL, Xuniq⟩ : ∃! X : Point, L intersects segment A B at X := by
    sorry
  have XneA : X ≠ A := by
    by_contra! ;
    rw [<- this] at AoffL
    unfold Intersects at XintersectsABandL
    tauto
  have XneB : X ≠ B := by
    by_contra! ;
    rw [<- this] at BoffL
    unfold Intersects at XintersectsABandL
    tauto
  have ⟨C, CoffL, ConAB, ACB, ACX⟩ : ∃ C : Point, (C off L) ∧ (C on segment A B) ∧ (A - C - B) ∧ (A - C - X) := by
    have ⟨_, C, _, AX, ⟨_, AonAX, ConAX, XonAX, _⟩, distinctACX, _, ACX, _⟩ := B2 A X XneA.symm
    use C
    have AXsubAB : segment A X ⊆ segment A B := by sorry
    have ConAB : C on segment A B := by
      apply AXsubAB; tauto
    have CoffL : C off L := by
      -- idea: C ∈ AX, but AX ∩ L = {X}, so if C ∈ L, then C = X, but ACX distinct.
      obtain ⟨XonL, XonAB, XuniqIntersection, LintABeqX⟩ := XintersectsABandL
      by_contra! hNeg
      have ConIntLandAB : C on (L ∩ segment A B) := by tauto
      have CinSingleX : C ∈ ({X} : Set Point) := by tauto
      have CeqX : C = X := by tauto
      have CneX : C ≠ X := by
        simp at distinctACX; tauto
      contradiction
    have ACB : A - C - B := by
      unfold Segment at ConAB; simp at ConAB;
      rcases ConAB with ACB | AeqC | BeqC
      -- easy case
      exact ACB;
      -- A can't equal C
      exfalso; simp at distinctACX; have AneC : A ≠ C := by tauto;
      contradiction
      -- B can't equal C
      -- should follow from AXB and ACX, 
      sorry


    tauto
  have ⟨CneA, CneB⟩  : C ≠ A ∧ C ≠ B := by
    have h := B1a ACB; tauto
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
