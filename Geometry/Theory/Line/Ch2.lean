
/- General Theory about lines and line-parts using facts from Ch1 and Ch2 of the text -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Collinear.Ch1
import Geometry.Tactics
import Geometry.Ch2.Prop

namespace Geometry.Theory

open Set
open Geometry.Theory
open Geometry.Ch2.Prop

namespace Line

/-- An intersection is either empty, a singleton, or the lines are equal. -/
lemma line_trichotomy : ∀ L M : Set Point, (L ∩ M = ∅) ∨ (∃! X, L ∩ M = {X}) ∨ L = M := by
  intro L M
  by_cases suppose : (L ≠ M) ∧ (L ∦ M)
  · right; left
    exact Ch2.Prop.P1 suppose.left suppose.right
  · simp only [not_and_or, not_not] at suppose
    rcases suppose with LeqM | other
    · right; right; exact LeqM
    · left; push_neg at *
      obtain ⟨_, LparM⟩ := other
      apply Subset.antisymm
      · intro e eInInt
        specialize LparM e
        obtain ⟨eInL, eInM⟩ := by
          rw [Set.mem_inter_iff] at eInInt
          exact eInInt
        tauto
      · tauto

/-- If two distinct points are found on two lines, those lines are equal. -/
lemma equiv {L M : Line} {A B : Point} : A ≠ B -> ((A on L) ∧ (A on M) ∧ (B on L) ∧ (B on M) -> L = M) := by
  intro AneB ⟨AonL, AonM, BonL, BonM⟩
  have Aexists : A ∈ L ∩ M := by tauto
  have Bexists : B ∈ L ∩ M := by tauto
  -- Ed. This is a _sweet_ use of trichotomy. This proof was much longer prior to this.
  rcases line_trichotomy L M with LparM | LintMatX | LeqM
  · -- the intersection is nonempty by assumption
    exfalso
    rw [LparM] at Aexists
    contradiction
  · obtain ⟨X, Xinter, Xuniq⟩ := LintMatX
    exfalso
    -- A and B are both in the intersection by hypothesis
    rw [Xinter] at Aexists Bexists
    have AeqX : A = X := by tauto
    have BeqX : B = X := by tauto
    rw [AeqX, BeqX] at AneB
    contradiction
  · exact LeqM

/-- A segment contains the points that define it -/
lemma seg_has_endpoints.left : A on segment A B := by tauto
/-- A segment contains the points that define it -/
lemma seg_has_endpoints.right : B on segment A B := by tauto

/-- A ray contains the points that define it -/
lemma ray_has_endpoints.left : A on ray A B := by
  simp only [mem_union, mem_setOf_eq, true_or, or_true, ne_eq, not_true_eq_false, false_and, and_false, or_false]
/-- A ray contains the points that define it -/
lemma ray_has_endpoints.right : B on ray A B := by
  simp only [mem_union, mem_setOf_eq, or_true, ne_eq, not_true_eq_false, and_false, or_false]

/-
/- A extension excludes the points that define it -/
lemma extension_has_endpoints.left : A off extension A B := by sorry
/- A extension excludes the points that define it -/
lemma extension_excludes_endpoints.right : B off extension A B := by sorry
-/

/-- A line contains the points that define it -/
lemma line_has_definition_points.left : A on line A B := by
  simp only [mem_setOf_eq]
  by_cases AneB : A ≠ B
  · exact Collinear.any_two_points_are_collinear_ABA A B AneB
  · push_neg at AneB ; rw [<- AneB]
    unfold Collinear
    exact Collinear.any_point_is_self_collinear A

/-- A line contains the points that define it -/
lemma line_has_definition_points.right : B on line A B := by
  simp only [mem_setOf_eq]
  by_cases AneB : A ≠ B
  · exact Collinear.any_two_points_are_collinear_ABB A B AneB
  · push_neg at AneB ; rw [<- AneB]
    exact Collinear.any_point_is_self_collinear A

/-- A line contains the points that define it -/
lemma line_has_definition_points : A on line A B ∧ B on line A B :=
  ⟨line_has_definition_points.left, line_has_definition_points.right⟩

/-- All points on a extension are collinear -/
lemma all_points_on_an_extension_are_collinear {A B : Point} : P on extension A B -> Collinear A B P := by tauto

/-- All points on a segment are collinear -/
lemma all_points_on_a_segment_are_collinear : P on segment A B -> Collinear A B P := by tauto

/-- All points on a ray are collinear -/
lemma all_points_on_a_ray_are_collinear : P on ray A B -> Collinear A B P := by tauto

/-- All points on a line are collinear -/
lemma all_points_on_a_line_are_collinear : P on line A B -> Collinear A B P := by tauto

/--
p109. the author refers to the definition of these things, but the definitions are pretty loose and assume
undergrad set theory is a familiar topic. These are some of the formalizations of those basic facts.

"By the definition of segment and ray, `the segment A B ⊆ the ray A B`" -/
lemma seg_sub_ray : segment A B ⊆ ray A B := by simp_all only [subset_union_left]

/-- A ray A B is a subset of the line A B -/
lemma ray_sub_line : ray A B ⊆ line A B := by
  intro P PonRay
  unfold LineThrough
  simp only [mem_setOf_eq]
  exact all_points_on_a_ray_are_collinear PonRay

/-- A segment is a subset of the line A B -/
lemma seg_sub_line : segment A B ⊆ line A B := by
  have h₁ : segment A B ⊆ ray A B := seg_sub_ray
  have h₂ : ray A B ⊆ line A B := ray_sub_line
  tauto

/-- Every `line A B` is a whole line `L` -/
lemma linethrough_lift_line : ∀ L : Line, ∃ A B : Point, A ≠ B ∧ L = line A B := by
  intro L
  have ⟨A, B, AneB, AonL, BonL⟩ := I2 L
  use A
  use B
  refine ⟨AneB, ?_⟩
  unfold LineThrough
  apply Subset.antisymm
  · intro P PonL
    have colABP : Collinear A B P := by tauto
    exact mem_setOf.mpr colABP
  · intro P PinAB
    have colABP : Collinear A B P := by tauto
    unfold Collinear at colABP
    have ⟨L', AonL', BonL', ConL'⟩ := colABP
    have ⟨M, _, Muniq⟩ := I1 A B AneB
    have MeqL := Muniq L ⟨AonL, BonL⟩
    have MeqL' := Muniq L' ⟨AonL', BonL'⟩
    rw [<- MeqL] at MeqL'
    rw [<- MeqL']
    exact ConL'

/- Given any segment AC, we can find B such that AC ⊆ AB -/
/- lemma seg_extension : ∀ A C : Point, A ≠ C -> ∃ B : Point, (A - C - B ∧ B ≠ A ∧ B ≠ C -> segment A C ⊆ segment A B) := by -/
/-   intro A C AneC -/
/-   -- different IDEA: seg AC ⊆ ray AC, ray AC contains all points to the right of C, which includes B by assumption, -/
/-   -- so ray AC = ray AB, so seg AC ⊆ ray AB, but we know A - C - B now, so C ∈ seg AB. -/
/-   have B : Point := by tauto; -/
/-   use B -/
/-   intro ⟨ACB, BneA, BneC⟩ -/
/-   have BonRayAC : B on ray A C := by tauto -/
/-   unfold Ray at BonRayAC -/
/-   rcases BonRayAC with BonSeg | BonExt -/
/-   -- B is not on the segment. -/
/-   exfalso -/
/-   simp only [mem_setOf_eq] at BonSeg -/
/-   rcases BonSeg with ABC | BeqA | BeqC -/
/-   · exact Betweenness.absurdity_abc_acb ⟨ABC, ACB⟩ -/
/-   · tauto -/
/-   · tauto -/
/-   -- So B is on the extension, which means ACB -/
/-   unfold Extension at BonExt; simp only [ne_eq, mem_setOf_eq] at BonExt -/
/-   have ⟨ACB, _, _⟩ := BonExt -/
/-   have ConSegAB : C on segment A B := by tauto -/
/-   sorry -- idea: if seg A B and seg C D are colinear, and A on CD and B on CD, then AB ⊆ CD -/

/-- A line is 'bigger' than a segment in the sense that, even if the segment is coincident with a line, it
 is possible to find a point on L that is off the segment -/
lemma line_is_bigger_than_segment : ∀ L : Line, ∀ A B : Point, A ≠ B -> segment A B ≠ L := by
  intro L A B AneB
  by_cases suppose : (A off L) ∨ (B off L)
  · -- one of the points is not collinear with L,
    by_contra! hNeg
    rw [<- hNeg] at suppose
    simp only [mem_setOf_eq, true_or, or_true, not_true_eq_false, or_self] at suppose
  · -- AB is collinear with L, so we must use B2 to construct a point outside of AB, but on L
    -- have ⟨D, ABD⟩
    -- have h : ∃ D : Point, A - B - D
    push_neg at suppose
    have ⟨AonL, BonL⟩ := suppose
    have ⟨_, _, D, L', ⟨_, AonL', _, BonL', DonL'⟩, distinctABD, _, _, ABD⟩ := B2 A B AneB
    -- need to prove L' and L are the same, we can use the Line.equiv
    have L'eqL := Line.equiv AneB ⟨AonL, AonL', BonL, BonL'⟩
    -- FIXME: This is very bad.
    simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
      and_true] at distinctABD
    have ⟨_, ⟨_, AneB, AneD⟩, _, BneD⟩ := distinctABD
    have colABD : Collinear A B D := by tauto
    have DoffAB : D off segment A B := by
      unfold Segment
      simp only [mem_setOf_eq, not_or]
      rcases B3 A B D ⟨AneB, BneD, AneD, colABD⟩ with l | c | r
      repeat tauto
    by_contra! hNeg
    rw [L'eqL] at hNeg
    rw [hNeg] at DoffAB
    contradiction

/- A line is 'bigger' than an extension in the same way that a line is bigger than a segment -/
/- lemma line_is_bigger_than_extension : ∀ L : Line, ∀ A B : Point, A ≠ B -> extension A B ≠ L := by -/
/-   intro L A B AneB -/
/-   sorry -/

lemma segment_int_extension_is_empty : segment A B ∩ extension A B = ∅ := by
  apply Subset.antisymm
  · intro P ⟨PonSeg, PonExt⟩
    have ⟨ABP, AneP, BneP⟩ := PonExt
    rcases PonSeg with APB | AeqP | BeqP
    · exfalso; exact Betweenness.absurdity_abc_acb ⟨ABP, APB⟩
    · contradiction
    · contradiction
  · intro _ absurdity; exfalso; contradiction

/-- A line is the set of all points on it -/
lemma line_by_definition : ∀ L : Line, L = {P : Point | P on L} := by
  intro L
  apply Subset.antisymm
  repeat tauto

/-- A line is 'bigger' than a ray in the same way that a line is bigger than a segment -/
lemma line_is_bigger_than_ray : ∀ L : Line, ∀ A B : Point, A ≠ B -> ray A B ≠ L := by
  intro L A B AneB
  -- there are three cases:
  -- 1. L ∥ ray A B, in which case they are not equal because A and B aren't on L.
  -- 2. L intersects ray A B, in which case at least one of A or B aren't on L
  -- 3. L is line A B, which is not equal to ray A B because it contains points on extension B A
  have AonRayAB : A on ray A B := Line.ray_has_endpoints.left
  have BonRayAB : B on ray A B := Line.ray_has_endpoints.right
  have ⟨C, D, _, lineCD⟩ := (linethrough_lift_line L)
  rcases line_trichotomy L (ray A B) with LparRay | LintRay | LextendsRay
  · by_contra! hNeg
    rw [<- hNeg] at LparRay
    simp only [inter_self] at LparRay
    rw [LparRay] at AonRayAB
    contradiction
  · obtain ⟨X, LintABatX, Xuniq⟩ := LintRay
    have AorBoffL : (A off L) ∨ (B off L) := by
      by_contra! ⟨AonL, BonL⟩
      have AinInt : A ∈ L ∩ ray A B := by tauto
      have BinInt : B ∈ L ∩ ray A B := by tauto
      rw [LintABatX] at *
      have AeqB : A = B := by
        have AeqX : A = X := by tauto
        have BeqX : B = X := by tauto
        rw [<- BeqX] at AeqX
        exact AeqX
      contradiction
    by_contra! hNeg
    rw [<- hNeg] at AorBoffL
    tauto
  · exfalso
    have LisPsonL : L = { P | P on L } := line_by_definition L
    rw [<- LextendsRay] at AonRayAB BonRayAB
    have LeqLineAB : L = line A B := Line.equiv AneB
      ⟨AonRayAB, line_has_definition_points.left, BonRayAB, line_has_definition_points.right⟩
    have lABeqlCD : line A B = line C D := by
      rwa [LeqLineAB] at lineCD
    rw [LeqLineAB] at LextendsRay
    have ⟨X, L', XonL', AonL', BonL', XneA, XneB, XAB⟩ := B2.left A B AneB
    have L'eqL : L' = line A B := Line.equiv AneB
      ⟨AonL', line_has_definition_points.left, BonL', line_has_definition_points.right⟩
    have XonL : X on L := by rwa [LeqLineAB, <- L'eqL]
    -- by construction, X is off the ray
    have XoffRayAB : X off ray A B := by
      unfold Ray;
      -- TODO: This could be done under the rcases below, probably cleaner
      have XoffSegmentAB : X off segment A B := by 
        unfold Segment
        simp only [mem_setOf_eq]
        by_contra! hNeg
        rcases hNeg with AXB | AeqX | BeqX
        · exact Betweenness.absurdity_abc_bac ⟨AXB, XAB⟩
        · tauto
        · tauto
      have XoffExtensionAB : X off extension A B := by
        unfold Extension
        simp only [mem_setOf_eq]
        push_neg
        intro ABX
        exfalso;
        exact Betweenness.absurdity_abc_cab ⟨ABX, XAB⟩
      by_contra! hNeg
      rcases hNeg with XinSeg | XinExt
      repeat contradiction
    -- so X is off the ray but on the line, which can't be if the two things are equal.
    rw [<- LextendsRay] at XoffRayAB
    rw [L'eqL] at XonL'
    contradiction

/- It helps to be able to commute these around, when we get to congruence this will make part of it trivial -/
lemma segment_AB_eq_segment_BA : segment A B = segment B A := by
  unfold Segment
  ext P
  rw [@mem_setOf]; simp_all only [mem_setOf_eq]
  constructor
  intro h; rcases h with h0 | h1 | h2; rw [B1b];
  repeat tauto
  intro h; rcases h with h0 | h1 | h2; rw [B1b]
  repeat tauto

/-- The endpoint B is in common here. -/
lemma segment_AB_sub_ray_BA : segment A B ⊆ ray B A := by
  intro P hPinSegAB
  simp_all only [mem_setOf_eq, mem_union, segment_AB_eq_segment_BA, true_or]

lemma APB_imp_P_on_segment_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - P - B -> P on the segment A B := by intro h; unfold Segment; simp; tauto;

lemma APB_imp_P_on_ray_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - P - B -> P on the ray A B := by intro h; unfold Ray; simp; tauto;

lemma ABP_imp_P_on_ext_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - B - P -> P on the extension A B := by 
  intro h; unfold Extension; simp only [ne_eq, mem_setOf_eq, B1b];
  rw [B1b] at h
  tauto

lemma ABP_imp_P_on_line_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - B - P -> P on the line A B := by
    intro hABP;
    have hPonExtAB : P on extension A B := ABP_imp_P_on_ext_AB PneAB hABP
    unfold LineThrough; simp only [mem_setOf_eq]
    exact Line.all_points_on_an_extension_are_collinear hPonExtAB

lemma APB_imp_P_on_line_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - P - B -> P on the line A B := by
    intro hABP;
    have hPonSegAB : P on segment A B := APB_imp_P_on_segment_AB PneAB hABP
    unfold LineThrough; simp only [mem_setOf_eq]
    exact Line.all_points_on_a_segment_are_collinear hPonSegAB

end Line

end Geometry.Theory
