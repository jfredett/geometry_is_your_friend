
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Tactics

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1
import Geometry.Ch3.Prop.B4iii
import Geometry.Ch3.Ex.Ex1
import Geometry.Theory.Betweenness.Ch1
import Geometry.Theory.Betweenness.Ch2
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex

/-- p112. Given A - B - C and A - C - D, then B - C - D and A - B - D (see Figure 3.9) -/
theorem P3.left : ∀ A B C D : Point, (A - B - C) ∧ (A - C - D) -> B - C - D := by 
  /- (1) A, B, C, and D are distinct, collinear points (see Exercise 1). -/
  intro A B C D ⟨ABC, ACD⟩
  have distinctABCD := Ex1.a ⟨ABC, ACD⟩
  have ⟨colABC, colBCD⟩ := Ex1.b ⟨ABC, ACD⟩
  /- (2) There exists a point E not on the line through A,B,C,D (Proposition 2.3) -/
  -- NOTE: WLOG, we can pick either of colABC or colBCD because all these points are collinear
  have ⟨L, AonL, BonL, ConL⟩ := colABC
  have AneB : A ≠ B := by distinguish distinctABCD A B
  have AneC : A ≠ C := by distinguish distinctABCD A C
  have BneC : B ≠ C := by distinguish distinctABCD B C
  have CneD : C ≠ D := by distinguish distinctABCD C D
  have LeqAB : L = line A B := Line.equiv AneB
    ⟨AonL, Line.line_has_definition_points.left, BonL, Line.line_has_definition_points.right⟩
  have ⟨E, EoffL⟩ := Ch2.Prop.P3 L
  /- (3) Consider line EC. Since (by hypothesis) AD meets this line in point C,... -/
  let EC := line E C
  -- <Ed> Missing these simple conditions
  have ConEC : C on EC := Line.line_has_definition_points.right
  have LneEC : L ≠ EC := by
    have EonEC : E on EC := Line.line_has_definition_points.left
    by_contra! hNeg; rw [hNeg] at EoffL; contradiction
  have ConLintEC : C on L ∩ EC := ⟨ConL, ConEC⟩
  have LnparEC : L ∦ EC := by
    by_contra! hNeg
    have emptyInter := Intersection.parallel_intersection_is_empty L EC LneEC hNeg
    rw [emptyInter] at ConLintEC
    contradiction
  have LintECatC : L intersects EC at C := (Intersection.single_point_of_intersection C L EC ⟨LneEC, LnparEC⟩).mp ConLintEC
  have AoffEC : A off EC := by
    by_contra! hNeg
    have AonInt : A ∈ L ∩ EC := ⟨AonL, hNeg⟩
    exfalso
    have AeqC := Intersection.intersection_is_unique L EC LneEC LnparEC ⟨AonInt, ConLintEC⟩
    contradiction
  have BoffEC : B off EC := by
    by_contra! hNeg
    have BonInt : B ∈ L ∩ EC := ⟨BonL, hNeg⟩
    have BneC : B ≠ C := by simp_all only [B1a, ne_eq, not_false_eq_true]
    have BeqC := Intersection.intersection_is_unique L EC LneEC LnparEC ⟨BonInt, ConLintEC⟩
    contradiction
  have DonL : D on L := by rw [LeqAB]; unfold LineThrough; simp only [mem_setOf_eq]; sorry
  have DoffEC : D off EC := by
    by_contra! hNeg
    have DonInt : D ∈ L ∩ EC := ⟨DonL, hNeg⟩
    have DneC : D ≠ C := Ne.symm (Betweenness.abc_imp_distinct.bnec ACD)
    have DeqC := Intersection.intersection_is_unique L EC LneEC LnparEC ⟨DonInt, ConLintEC⟩
    contradiction 
  -- </Ed>
  /- ... points A and D are on opposite sides of EC -/
  have ECsplitsAandD : EC splits A and D := by
    unfold SameSide; push_neg
    intro AoffEC DoffEC
    have AneD : A ≠ D := by distinguish distinctABCD A D
    refine ⟨AneD, ?_⟩
    use C
    -- TODO: This gets cleaner with better collinearity
    sorry
  /- (4) We claim A and B are on the same side of EC. Assume on the contrary that A and B are on opposite sides of EC
     (RAA Hypothesis) -/
  by_cases raa : EC splits A and B
  · /- p113. (5) Then EC meets AB in a point between A and B (definition of "opposite sides" [ed. "splits" in our parlance]). -/
    have ⟨X, LintECatX, Xuniq⟩ : ∃! X : Point, (L intersects EC at X) := by
      rcases Line.line_trichotomy L EC with LparEC | LintECatX | LeqEC
      · exfalso; rwa [LparEC] at ConLintEC
      · exact LintECatX
      · exfalso; rw [<- LeqEC] at AoffEC; contradiction
    -- <Ed> need this for a step below
    have XinIntLine : X ∈ L ∩ EC := by
      simp only [mem_inter_iff]; simp only at LintECatX;
      refine (mem_inter_iff X L EC).mp ?_
      rw [LintECatX]
      exact mem_singleton X
    have ⟨XonL, XonEC⟩ := XinIntLine
    -- </Ed>
    have AXB : A - X - B := by
      have colAXB : Collinear A X B := by
        use L
      have AneX : A ≠ X := by
        by_contra! hNeg
        rw [hNeg] at AoffEC
        contradiction
      have BneX : B ≠ X := by
        by_contra! hNeg
        rw [hNeg] at BoffEC
        contradiction
      -- TODO: I think a better argument exists here to reject the two alternative cases.
      rcases B3 A X B ⟨AneX, BneX.symm, AneB, colAXB⟩ with ⟨AXB, _⟩ | ⟨_, XAB, _⟩ | ⟨_, _, ABX⟩
      · exact AXB
      · exfalso
        have ECguardsAB : EC guards A and B := by
          refine ⟨AoffEC, BoffEC, Or.inr ?_⟩
          by_contra! hNeg
          have ⟨P, PonAB, PonEC⟩ := hNeg
          have PinIntSeg : P ∈ EC ∩ (segment A B) := ⟨PonEC, PonAB⟩
          have PinIntLine : P ∈ EC ∩ (line A B) := Set.inter_subset_inter_right EC Line.seg_sub_line PinIntSeg
          rw [<- LeqAB] at PinIntLine
          have PeqX : P = X := Intersection.intersection_is_unique L EC LneEC LnparEC ⟨PinIntLine.symm, XinIntLine⟩
          rw [<- PeqX] at XAB
          have APB : A - P - B := by
            unfold Segment at PonAB
            rcases PonAB with APB | AeqP | BeqP
            · exact APB
            · exfalso; rw [<- AeqP] at PonEC; contradiction
            · exfalso; rw [<- BeqP] at PonEC; contradiction
          exact Betweenness.absurdity_abc_bac ⟨XAB, APB⟩
        contradiction
      · exfalso
        have ECguardsAB : EC guards A and B := by
          refine ⟨AoffEC, BoffEC, Or.inr ?_⟩
          by_contra! hNeg
          have ⟨P, PonAB, PonEC⟩ := hNeg
          have PinIntSeg : P ∈ EC ∩ (segment A B) := ⟨PonEC, PonAB⟩
          have PinIntLine : P ∈ EC ∩ (line A B) := Set.inter_subset_inter_right EC Line.seg_sub_line PinIntSeg
          rw [<- LeqAB] at PinIntLine
          have PeqX : P = X := Intersection.intersection_is_unique L EC LneEC LnparEC ⟨PinIntLine.symm, XinIntLine⟩
          rw [<- PeqX] at ABX
          have APB : A - P - B := by
            unfold Segment at PonAB
            rcases PonAB with APB | AeqP | BeqP
            · exact APB
            · exfalso; rw [<- AeqP] at PonEC; contradiction
            · exfalso; rw [<- BeqP] at PonEC; contradiction
          exact Betweenness.absurdity_abc_acb ⟨APB, ABX⟩
        contradiction
    /- (6) That point must be C (Proposition 2.1) -/
    have CeqX : C = X := Intersection.uniq ⟨LintECatC, LintECatX⟩
    /- (7) Thus A - B - C and A - C - B, which contradicts Betweenness Axiom 3. -/
    have ACB : A - C - B := by rwa [<- CeqX] at AXB
    exfalso
    exact Betweenness.absurdity_abc_acb ⟨ABC, ACB⟩
  · /- (8) Hence, A and B are on the same side of EC (RAA conclusion) -/
    push_neg at raa
    /- (9) B and D are on opposite sides of EC (steps 3 and 8 and the corrolary to Betweenness Axiom 4). -/
    have ECsplitsBandD : EC splits B and D := by
      by_contra! ECguardsBandD
      have h := B4i ⟨AoffEC, BoffEC, DoffEC⟩ ⟨raa, ECguardsBandD⟩
      contradiction
    /- (10) Hence, the point C of intersection of lines EC and BD lies between B and D (definition of "opposite sides";
       Proposition 2.1, i.e., that the point of intersection is unique). -/
    have BCD : B - C - D := by 
      unfold SameSide at ECsplitsBandD
      push_neg at ECsplitsBandD
      specialize ECsplitsBandD BoffEC DoffEC
      have ⟨BneD, P, ⟨PonSegBD, PonEC⟩⟩ := ECsplitsBandD
      have PinBDintEC : P ∈ line B D ∩ EC := by sorry
      have LeqBD : L = line B D := by sorry
      rw [LeqBD] at LintECatC
      rw [LintECatC] at PinBDintEC
      have PeqC : P = C := by tauto
      rw [<- PeqC]
      rcases PonSegBD with BPD | BeqP | DeqP
      · exact BPD
      · rw [BeqP, <- PeqC] at BneC; contradiction
      · rw [DeqP, <- PeqC] at CneD; contradiction
    exact BCD
  /- A similar argument involving EB proves that A - B - D -/

  /- TODO: Ed: time to break out `suffices` or some other clever thing... -/
  

-- theorem P3.right : ∀ A B C D : Point, (A - B - C) ∧ (A - C - D) -> B - C - D := by sorry
-- theorem P3.left : ∀ A B C D : Point, (A - B - C) ∧ (A - C - D) -> A - B - D := by sorry


end Geometry.Ch3.Prop
