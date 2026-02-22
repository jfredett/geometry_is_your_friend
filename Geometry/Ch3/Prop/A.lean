-- TODO: This should probably be a couple files, there's a lot of theory in here, also things are all mixed together.


/- Interpendix 3-A

On Intersections, Extensions, and other simple Line Properties.

Chapter 3, Prop 2 has a missing step, in particular it assumes on step 4 that A
and B are on opposite sides of L "by definition" -- except that we have not
assumed that B-O-A implies L splits A and B.

As I started to unwind this, I found it quite difficult, and it also revealed a structural
problem, in particular, the way I talk about intersections makes it difficult to access
the various properties without bringing in _every_ property. This "Interpendix"[1] provides
a number of useful properties in a way that makes it simple to say something like:

`have relevantProperty := Intersection.relevantPropertyLemma hIntersection`

these lemma will not be numbered, like in the book or previous chapters (indeed, many such
lemmas may be refactored into these interpendices), I think this will improve the ergonomics
working in these theories.



[1] Interpendix, from latin `inter` -- between, and `pendere` "to hang", cf
appendix, prependix, etc

-/
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

namespace Line

/-- If two distinct points are found on two lines, those lines are equal.  -/
@[simp] lemma equiv : ∀ L M : Line, ∀ A B : Point, A ≠ B -> ((A on L) ∧ (A on M) ∧ (B on L) ∧ (B on M) -> L = M) := by
  intro L M A B AneB ⟨AonL, AonM, BonL, BonM⟩
  -- idea, assume L intersects M at X, then X on L and X on M; and X is unique, so X = A and X = B, but A ≠ B
  by_contra! hNeg
  by_cases LnoparM : L ∦ M
  have ⟨X, Xexists, Xuniq⟩ := P1 hNeg LnoparM
  -- Little clean up to make these more useful
  simp only [P5.L2, mem_inter_iff, mem_singleton_iff] at Xexists
  simp only [P5.L2, mem_inter_iff, mem_singleton_iff] at Xuniq
  have AeqX : A = X := (Xexists A).mp ⟨AonL, AonM⟩
  have BeqX : B = X := (Xexists B).mp ⟨BonL, BonM⟩
  rw [AeqX, BeqX] at AneB
  contradiction
  -- if L and M are parallel, then A cannot be on both L and M, because Parallel lines share no points in common.
  push_neg at LnoparM
  obtain ⟨_, LnoparM⟩ := LnoparM
  specialize LnoparM A
  push_neg at LnoparM
  specialize LnoparM AonL
  contradiction

end Line

namespace Distinct

-- TODO: Some sort of thing for concluding A_i ≠ A_j for i ≠ j in a distinct block

-- TODO: There should be some way to take a `distinct` object and two putative elements of that object and
-- conclude the ≠ condition, ideally something like `distinct.conclude hDist A B -> A ≠ B` -- this might just be
-- a function I need to write? Not sure how to do this, below is a broken attempt
-- def conclude {α : Type} (distinct : List.Pairwise (fun x1 x2 ↦ x1 ≠ x2) α) : ∀ A B : α, A ∈ distinct -> B ∈ distinct -> A ≠ B := by sorry

end Distinct

namespace Collinear

/-- If for A B C X points, if are A C X is collinear, and  A X B are collinear, then A C B is collinear -/
@[simp] lemma inclusion : distinct A B C D -> Collinear A B C ∧ Collinear A C D -> Collinear A B D := by
  unfold Collinear
  intro distinctABCD ⟨colABC, colACD⟩
  -- FICME: Given the above `Distinct.conclude` or whatever I come up with, refactor this.
  have AneC : A ≠ C := by
    simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
      and_true] at distinctABCD
    tauto
  obtain ⟨L, AonL, BonL, ConL⟩ := colABC
  obtain ⟨M, AonM, ConM, DonM⟩ := colACD
  have LeqM : L = M := Line.equiv L M A C AneC ⟨AonL, AonM, ConL, ConM⟩
  use L
  rw [<- LeqM] at DonM
  tauto

/-- There is a line between any two points, so by definition any two points are collinear -/
@[simp] lemma any_two_points_are_collinear_ABA : ∀ A B : Point, A ≠ B -> Collinear A B A := by
  intro A B AneB
  unfold Collinear
  have ⟨L, hIncidence, hUniq⟩ := I1 A B AneB
  simp at hIncidence
  use L; tauto

/-- There is a line between any two points, so by definition any two points are collinear -/
@[simp] lemma any_two_points_are_collinear_ABB : ∀ A B : Point, A ≠ B -> Collinear A B B := by
  intro A B AneB
  unfold Collinear
  have ⟨L, hIncidence, hUniq⟩ := I1 A B AneB
  simp at hIncidence
  use L; tauto

/-- There is a line between any two points, so by definition any two points are collinear -/
@[simp] lemma any_two_points_are_collinear_AAB : ∀ A B : Point, A ≠ B -> Collinear A A B := by
  intro A B AneB
  unfold Collinear
  have ⟨L, hIncidence, hUniq⟩ := I1 A B AneB
  simp at hIncidence
  use L; tauto

end Collinear

namespace Betweenness

/-- With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another -/
@[simp] lemma absurdity_abc_bac : A - B - C ∧ B - A - C -> False := by
  intro ⟨ABC, BAC⟩
  obtain ⟨⟨AneB, BneC, AneC⟩, ⟨⟨L, AonL, BonL, ConL⟩, ABCCol⟩⟩ := B1a ABC
  obtain ⟨⟨BneA, AneC, BneC⟩, ⟨⟨M, BonM, AonM, ConM⟩, BACCol⟩⟩ := B1a BAC
  rcases B3 A B C ⟨AneB, BneC, AneC, ABCCol⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  contradiction; contradiction; contradiction

/-- With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another -/
@[simp] lemma absurdity_abc_acb : A - B - C ∧ A - C - B -> False := by
  intro ⟨ABC, ACB⟩
  obtain ⟨⟨AneB, BneC, AneC⟩, ⟨⟨L, AonL, BonL, ConL⟩, ABCCol⟩⟩ := B1a ABC
  obtain ⟨⟨AneC, CneB, AneB⟩, ⟨⟨M, AonM, ConM, BonM⟩, ACBCol⟩⟩ := B1a ACB
  rcases B3 A B C ⟨AneB, BneC, AneC, ABCCol⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  contradiction; contradiction; contradiction

/-- betweeness implies distinctness -/
@[simp] lemma abc_imp_anec : A - B - C -> A ≠ C := by
  intro ABC
  have ⟨⟨_, _, AneC⟩, _⟩ := (B1a ABC)
  exact AneC

end Betweenness

namespace Intersection

/-- If two lines intersect, their intersection is unique. -/
@[simp] lemma uniq : (L intersects M at X) ∧ (L intersects M at Y) -> X = Y := by
  unfold Intersects
  intro ⟨LMatX, LMatY⟩
  rw [LMatX] at LMatY
  exact singleton_eq_singleton_iff.mp LMatY

/-- L intersects M is the same as M intersects L. -/
@[simp] lemma symm : (L intersects M at X) ↔ (M intersects L at X) := by
  unfold Intersects
  refine Eq.congr ?_ rfl
  exact inter_comm L M

/-- If L intersects M at X, then X is on L -/
@[simp] lemma inter_touch_left : (L intersects M at X) -> (X on L) := by
  simp_all only [P5.L2, mem_inter_iff, mem_singleton_iff]
  intro h; specialize h X; tauto

/-- If L intersects M at X, then X is on M -/
@[simp] lemma inter_touch_right : (L intersects M at X) -> (X on M) := by
  simp_all only [P5.L2, mem_inter_iff, mem_singleton_iff]
  intro h; specialize h X; tauto

/-- If L intersects M at X, then forall P not equal to X, if P on L, then P off M. -/
@[simp] lemma uniq_solitary : (L ≠ M) ∧ (L intersects M at X) -> (∀ P : Point, (P ≠ X) ∧ (P on L) -> (P off M)) := by
  intro ⟨LneM, LintMatX⟩ P ⟨PneX, PonL⟩
  unfold Intersects at LintMatX
  by_contra! PonM
  have PinLintM : P ∈ (L ∩ M) := by tauto
  rw [LintMatX] at PinLintM
  contradiction

end Intersection

namespace Line

/-- A segment contains the points that define it -/
@[simp] lemma seg_has_endpoints.left : A on segment A B := by tauto
/-- A segment contains the points that define it -/
@[simp] lemma seg_has_endpoints.right : B on segment A B := by tauto

/-- A ray contains the points that define it -/
@[simp] lemma ray_has_endpoints.left : A on ray A B := by
  simp only [mem_union, mem_setOf_eq, true_or, or_true, ne_eq, not_true_eq_false, false_and, and_false, or_false]
/-- A ray contains the points that define it -/
@[simp] lemma ray_has_endpoints.right : B on ray A B := by
  simp only [mem_union, mem_setOf_eq, or_true, ne_eq, not_true_eq_false, and_false, or_false]

/-
/- A extension excludes the points that define it -/
@[simp] lemma extension_has_endpoints.left : A off extension A B := by sorry
/- A extension excludes the points that define it -/
@[simp] lemma extension_excludes_endpoints.right : B off extension A B := by sorry
-/

/-- A line contains the points that define it -/
@[simp] lemma line_has_definition_points.left : A ≠ B -> A on line A B := by
  intro AneB
  simp only [mem_setOf_eq]
  exact Collinear.any_two_points_are_collinear_ABA A B AneB

/-- A line contains the points that define it -/
@[simp] lemma line_has_definition_points.right : A ≠ B -> B on line A B := by
  intro AneB
  simp only [mem_setOf_eq]
  exact Collinear.any_two_points_are_collinear_ABB A B AneB

/-- All points on a segment are collinear -/
@[simp] lemma all_points_in_a_segment_are_collinear : P on segment A B -> Collinear A B P := by
  intro PonSeg
  have AonSeg : A on segment A B := seg_has_endpoints.left
  have BonSeg : B on segment A B := seg_has_endpoints.right
  tauto

/-- All points on a ray are collinear -/
@[simp] lemma all_points_in_a_ray_are_collinear : P on ray A B -> Collinear A B P := by
  intro PonRay
  use ray A B
  have AonRay : A on ray A B := ray_has_endpoints.left
  have BonRay : B on ray A B := ray_has_endpoints.right
  tauto

/-- All points on a line are collinear -/
@[simp] lemma all_points_in_a_line_are_collinear : P on line A B -> Collinear A B P := by tauto

/-- A segment A B is a subset of the ray A B -/
@[simp] lemma seg_sub_ray : segment A B ⊆ ray A B := by simp_all only [subset_union_left]

/-- A ray A B is a subset of the line A B -/
@[simp] lemma ray_sub_line : ray A B ⊆ line A B := by
  intro P PonRay
  unfold LineThrough
  simp only [mem_setOf_eq]
  exact all_points_in_a_ray_are_collinear PonRay

-- FIXME: I think this needs the line-sep property. Prop 3.3 covers this?
/- @[simp] lemma seg_inclusion : ∀ A B C D : Point, (distinct A B C D) -/
/-   -> A on segment C D ∧ B on segment C D -> segment A B ⊆ segment C D := by -/
/-   unfold Segment; simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, -/
/-     forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self, -/
/-     and_true, mem_setOf_eq, setOf_subset_setOf, and_imp] -/
/-   intro A B C D AneB AneC AneD BneC BneD CneD AonCD BonCD E hOpts -/
/-   rcases hOpts with AEB | AeqE | BeqE -/
/-   · obtain ⟨⟨AneE, BneE, _⟩, ⟨L, AonL, EonL, BonL⟩, colAEB⟩ := B1a AEB -/
/-     have ConL : C on L := by sorry -/
/-     have DonL : D on L := by sorry -/
/-     sorry -/
/-   · rw [<- AeqE]; exact AonCD -/
/-   · rw [<- BeqE]; exact BonCD -/

/-- Every `line A B` is a whole line `L` -/
@[simp] lemma linethrough_lift_line : ∀ L : Line, ∃ A B : Point, A ≠ B -> L = line A B := by
  intro L
  have ⟨A, B, AneB, AonL, BonL⟩ := I2 L
  use A
  use B
  intro _
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
/- @[simp] lemma seg_extension : ∀ A C : Point, A ≠ C -> ∃ B : Point, (A - C - B ∧ B ≠ A ∧ B ≠ C -> segment A C ⊆ segment A B) := by -/
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
@[simp] lemma line_is_bigger_than_segment : ∀ L : Line, ∀ A B : Point, A ≠ B -> segment A B ≠ L := by
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
    have L'eqL := Line.equiv L L' A B AneB ⟨AonL, AonL', BonL, BonL'⟩
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
/- @[simp] lemma line_is_bigger_than_extension : ∀ L : Line, ∀ A B : Point, A ≠ B -> extension A B ≠ L := by -/
/-   intro L A B AneB -/
/-   sorry -/

lemma segment_int_extension_is_empty : segment A B ∩ extension A B = ∅ := by
  unfold Segment; unfold Extension
  simp?
  sorry


/-- A line is 'bigger' than a ray in the same way that a line is bigger than a segment -/
@[simp] lemma line_is_bigger_than_ray : ∀ L : Line, ∀ A B : Point, A ≠ B -> ray A B ≠ L := by
  intro L A B AneB
  -- there are three cases:
  -- 1. L ∥ ray A B, in which case they are not equal because A and B aren't on L.
  -- 2. L intersects ray A B, in which case at least one of A or B aren't on L
  -- 3. L is line A B, which is not equal to ray A B because it contains points on extension B A
  have AonSegAB : A on segment A B := by tauto
  have AonRayAB : A on ray A B := by unfold Ray; tauto
  have BonSegAB : B on segment A B := by tauto
  have BonRayAB : B on ray A B := by unfold Ray; tauto
  by_cases suppose : (L ∥ ray A B) ∨ (∃! X : Point, L intersects ray A B at X) ∨ (L = line A B)
  rcases suppose with LparRay | LintRay | LextendsRay
  · by_contra! hNeg
    have AoffL : A off L := by tauto
    rw [<- hNeg] at AoffL
    contradiction
  · obtain ⟨X, LintABatX, Xuniq⟩ := LintRay
    have AorBoffL : (A off L) ∨ (B off L) := by
      by_contra! ⟨AonL, BonL⟩
      have AinInt : A ∈ L ∩ ray A B := by tauto
      have BinInt : B ∈ L ∩ ray A B := by tauto
      rw [LintABatX] at *
      have AeqB : A = B := by
        sorry
    by_contra! hNeg
    rw [<- hNeg] at AorBoffL
    tauto
  · by_contra! RayABeqLineAB
    rw [LextendsRay, <- (P1.ii AneB)] at *
    rw [eq_comm, Set.union_eq_left] at RayABeqLineAB
    unfold Ray at RayABeqLineAB
    rw [P1.L2] at RayABeqLineAB
    sorry
  · push_neg at suppose
    obtain ⟨LnoparAB, noIntersection, LnotLine⟩ := suppose
    -- there are two contradictions to choose from, non-parallel lines intersect, but there is no intersection, but
    -- even simpler, 
    
    sorry
    
  
   

end Line


namespace Intersection

/-- No points are contained on the intersection of a segment and it's related extension -/
@[simp] lemma seg_inter_ext_empty : segment A B ∩ extension A B = ∅ := by
  unfold Segment; unfold Extension
  ext P
  constructor
  -- Forward case.
  · simp only [ne_eq, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, imp_false, not_and,
    not_not] ; intro opts ABP AneP
    rcases opts with APB | AeqP | BeqP
    · exfalso ; exact Betweenness.absurdity_abc_acb ⟨ABP, APB⟩
    · contradiction
    · exact BeqP
  -- Reverse
  · simp only [mem_empty_iff_false, ne_eq, mem_inter_iff, mem_setOf_eq, IsEmpty.forall_iff]

/-- Points on a segment are not included in the related extension -/
@[simp] lemma seg_inter_ext_empty' : X on segment A B -> X off extension A B := by
  intro XonAB
  by_contra! hNeg
  have interEmpty : segment A B ∩ extension A B = ∅ := seg_inter_ext_empty
  have XinInter : X ∈ (segment A B ∩ extension A B) := by tauto
  rw [interEmpty] at XinInter
  contradiction

/-- Points on an extension are off the related segment -/
@[simp] lemma ext_inter_seg_empty : X on extension A B -> X off segment A B := by
  intro XonAB
  by_contra! hNeg
  have interEmpty : segment A B ∩ extension A B = ∅ := seg_inter_ext_empty
  have XinInter : X ∈ (segment A B ∩ extension A B) := by tauto
  rw [interEmpty] at XinInter
  contradiction

/-- If L and M are distinct, nonparallel lines, and X and Y are found in their intersection, X and Y are equal -/
@[simp] lemma intersection_is_unique : ∀ L M : Line, L ≠ M -> (L ∦ M) -> X ∈ L ∩ M ∧ Y ∈ L ∩ M -> X = Y := by
  intro L M LneM LnparM ⟨XonInt, YonInt⟩
  have ⟨P, LinterMatP, Puniq⟩ : ∃! X : Point, L intersects M at X := Ch2.Prop.P1 LneM LnparM
  specialize LinterMatP
  rw [LinterMatP] at XonInt
  rw [LinterMatP] at YonInt
  have XeqP : X = P := by tauto
  have YeqP : Y = P := by tauto
  rw [XeqP, YeqP]

/-- If L and M are distinct, parallel lines, their intersection is empty -/
@[simp] lemma parallel_intersection_is_empty : ∀ L M : Line, (L ≠ M) -> (L ∥ M) -> L ∩ M = ∅ := by
  intro L M LneM LparM
  apply Subset.antisymm
  · tauto
  · tauto

/-- Intersections of distinct, nonparallel lines contain exactly one point -/
@[simp] lemma single_point_of_intersection : ∀ P : Point, ∀ L M : Line, L ≠ M ∧ (L ∦ M) -> (P ∈ L ∩ M ↔ L intersects M at P) := by
  intro P L M ⟨LneM, LnparM⟩
  constructor
  · intro PinInter
    unfold Intersects
    apply Subset.antisymm
    · intro Q QinInter
      have h := intersection_is_unique L M LneM LnparM ⟨QinInter, PinInter⟩
      trivial
    · intro Q QisP
      have QeqP : Q = P := by tauto
      rw [QeqP]; exact PinInter
  · intro LintMatP
    rw [LintMatP]
    trivial

/-- If a line intersects a segment, then it intersects the ray containing that segment -/
-- TODO: I think some of the non-equality conditions are provable in general.
@[simp] lemma lift_seg_ray :
  (A ≠ B) -> (L intersects segment A B at X) -> (L intersects ray A B at X) := by
  intro AneB LintABatX
  have XonSegAB : X on segment A B := inter_touch_right LintABatX
  have XonL : X on L := inter_touch_left LintABatX
  have XonRayAB : X on ray A B := by unfold Ray; tauto
  have LneRayAB : L ≠ ray A B := by
    by_contra! hNeg
    rw [hNeg] at LintABatX
    unfold Intersects at LintABatX
    have AonSegAB : A on segment A B := by tauto
    have AonRayAB : A on ray A B := by unfold Ray; tauto
    have AonIntRaySeg : A ∈ ray A B ∩ segment A B := by tauto
    rw [LintABatX] at AonIntRaySeg
    have AeqX : A = X := by tauto
    have BonSegAB : B on segment A B := by tauto
    have BonRayAB : B on ray A B := by unfold Ray; tauto
    have BonIntRaySeg : B ∈ ray A B ∩ segment A B := by tauto
    rw [LintABatX] at BonIntRaySeg
    have BeqX : B = X := by tauto
    have AeqB : A = B := by rw [BeqX, AeqX]
    contradiction
  have LnparRayAB : L ∦ ray A B := by tauto
  -- assume there is some point not X that intersects the ray.
  by_cases counter : ∃ P : Point, (L intersects ray A B at P) ∧ (P ≠ X)
  · obtain ⟨P, LintRayABatP, PneX⟩ := counter
    have XinInter : X ∈ L ∩ ray A B := by tauto
    unfold Intersects at LintRayABatP
    rw [LintRayABatP] at XinInter
    have XeqP : P = X := by tauto
    contradiction
  · push_neg at counter
    apply Subset.antisymm
    · intro P PonLintRay
      have XonLintRay : X ∈ L ∩ ray A B := by tauto
      have PeqX : P = X := intersection_is_unique L (ray A B) LneRayAB LnparRayAB ⟨PonLintRay, XonLintRay⟩
      rw [PeqX]
      trivial
    · intro P PinSingleX
      have PeqX : P = X := by tauto
      rw [PeqX]; trivial

/- If a line intersects a segment, then it _does not_ intersect the extension of that segment. -/
/-lemma reject_seg_ext {AneB : A ≠ B} : (L intersects segment A B at X) -> ∀ X : Point, ¬(L intersects extension A B at X) := by sorry -/

/1-- If L intersects M anywhere, then L cannot be parallel to M -1/ -/
lemma intersections_are_not_parallel : (L intersects M at P) -> (L ∦ M) := by sorry

/-lemma par_lift_seg_line : (L ∦ segment A B) ↔ (L ∦ line A B) := by sorry -/
lemma par_lift_ray_line : (L ∦ ray A B) ↔ (L ∦ line A B) := by sorry

/-- If two lines intersect, they are distinct. -/
lemma intersecting_lines_are_not_equal {AneB : A ≠ B} : (L intersects line A B at X) -> L ≠ line A B := by
  intro LintABatX
  have colABX : Collinear A B X := by tauto
  have AonAB : A on line A B := Line.line_has_definition_points.left AneB
  have BonAB : B on line A B := Line.line_has_definition_points.right AneB
  have XonL : X on L := inter_touch_left LintABatX
  have XonAB : X on line A B := inter_touch_right LintABatX
  by_contra! hNeg
  rw [hNeg] at LintABatX
  unfold Intersects at LintABatX
  simp only [inter_self, P5.L2, mem_setOf_eq, mem_singleton_iff] at LintABatX
  have AeqX : A = X := (LintABatX A).mp (Collinear.any_two_points_are_collinear_ABA A B AneB)
  have BeqX : B = X := (LintABatX B).mp (Collinear.any_two_points_are_collinear_ABB A B AneB)
  rw [AeqX, BeqX] at AneB
  contradiction

/- lemma intersecting_rays_are_not_equal {AneB : A ≠ B} : (L intersects ray A B at X) -> L ≠ ray A B := by -/
/-   sorry -/

/-- If a line intersects a ray, then it intersects the line containing the ray -/
@[simp] lemma lift_ray_line {AneB : A ≠ B} : (L intersects ray A B at X) -> (L intersects line A B at X) := by
  intro LintRay
  have XonRayAB : X on ray A B := inter_touch_right LintRay
  have XonL : X on L := inter_touch_left LintRay
  have XABCol := P1.L5.ray AneB X XonRayAB
  have XonLineAB : X on line A B := by tauto
  have XonRayAB : X on ray A B := by tauto
  have XinInter : X ∈ L ∩ line A B := by tauto
  have LnparRayAB : L ∦ ray A B := intersections_are_not_parallel LintRay
  have LnparLineAB : L ∦ line A B := par_lift_ray_line.mp LnparRayAB
  have LneRayAB := Ne.symm (Line.line_is_bigger_than_ray L A B AneB)
  have LneLineAB : L ≠ line A B := by
    by_contra! hNeg
    have AonLineAB : A on line A B := Line.line_has_definition_points.left AneB
    have AonRayAB : A on ray A B := Line.ray_has_endpoints.left
    have AonL : A on L := by rw [<- hNeg] at AonLineAB; tauto
    have BonLineAB : B on line A B := Line.line_has_definition_points.right AneB
    have BonRayAB : B on ray A B := Line.ray_has_endpoints.right
    have BonL : B on L := by rw [<- hNeg] at BonLineAB; tauto
    have AinIntLine : A ∈ L ∩ line A B := by tauto
    have BinIntLine : B ∈ L ∩ line A B := by tauto
    have AinIntRay : A ∈ L ∩ ray A B := by tauto
    have BinIntRay : B ∈ L ∩ ray A B := by tauto
    have LintABatA : L intersects ray A B at A := (single_point_of_intersection A L (Ray A B) ⟨LneRayAB, LnparRayAB⟩).mp AinIntRay
    have LintABatB : L intersects ray A B at B := (single_point_of_intersection B L (Ray A B) ⟨LneRayAB, LnparRayAB⟩).mp BinIntRay
    unfold Intersects at *
    rw [LintRay] at LintABatA
    rw [LintRay] at LintABatB
    rw [LintABatB] at LintABatA
    simp only [singleton_eq_singleton_iff] at LintABatA
    rw [LintABatA] at AneB
    contradiction
  by_cases counter : ∃ P : Point, (L intersects line A B at P) ∧ (P ≠ X)
  · obtain ⟨P, LintABatP, PneX⟩ := counter
    have PinInter : P ∈ L ∩ line A B := by
      rw [LintABatP]
      trivial
    have PeqX : P = X := intersection_is_unique L (line A B) LneLineAB LnparLineAB ⟨PinInter, XinInter⟩
    contradiction
  · push_neg at counter
    apply Subset.antisymm
    · intro P PinInter
      exact counter P ((single_point_of_intersection P L (line A B) ⟨LneLineAB, LnparLineAB⟩).mp PinInter)
    · intro P PisX
      have PeqX : P = X := by tauto
      rw [PeqX]
      trivial

/- If a line intersects a segment, then it intersects the line containing the segment -/
@[simp] lemma lift_seg_line {AneB : A ≠ B} : (L intersects segment A B at X) -> (L intersects line A B at X) := by
  intro LintSeg
  apply lift_seg_ray at LintSeg
  apply lift_ray_line at LintSeg
  exact LintSeg
  repeat exact AneB

end Intersection


end Geometry.Ch3.Prop
