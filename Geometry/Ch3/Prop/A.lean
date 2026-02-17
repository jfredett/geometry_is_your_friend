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
  unfold Parallel at LnoparM
  specialize LnoparM hNeg A
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

/- FIXME: Naming. -/
@[simp] lemma inclusion : distinct A C X B -> Collinear A C X ∧ Collinear A X B -> Collinear A C B := by
  unfold Collinear
  intro distinctACBX ⟨ColACX, ColAXB⟩
  -- FIXME: Given the above `Distinct.conclude` or whatever I come up with, refactor this.
  have AneX : A ≠ X := by
    simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
      and_true] at distinctACBX
    tauto
  obtain ⟨L, AonL, ConL, XonL⟩ := ColACX
  obtain ⟨M, AonM, XonM, BonM⟩ := ColAXB
  have LeqM : L = M := Line.equiv L M A X AneX ⟨AonL, AonM, XonL, XonM⟩
  use L
  rw [<- LeqM] at BonM
  tauto
  sorry

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




end Betweenness


namespace Line


-- FIXME: I think this needs the line-sep property. Prop 3.3 covers this?
@[simp] lemma seg_inclusion : ∀ A B C D : Point, (distinct A B C D)
  -> A on segment C D ∧ B on segment C D -> segment A B ⊆ segment C D := by
  unfold Segment; simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
    and_true, mem_setOf_eq, setOf_subset_setOf, and_imp]
  intro A B C D AneB AneC AneD BneC BneD CneD AonCD BonCD E hOpts
  rcases hOpts with AEB | AeqE | BeqE
  · obtain ⟨⟨AneE, BneE, _⟩, ⟨L, AonL, EonL, BonL⟩, colAEB⟩ := B1a AEB
    have ConL : C on L := by sorry
    have DonL : D on L := by sorry
    sorry
  · rw [<- AeqE]; exact AonCD
  · rw [<- BeqE]; exact BonCD


/-- Given any segment AC, we can find B such that AC ⊆ AB -/
@[simp] lemma seg_extension : ∀ A C : Point, A ≠ C -> ∃ B : Point, (A - C - B ∧ B ≠ A ∧ B ≠ C -> segment A C ⊆ segment A B) := by
  intro A C AneC
  -- different IDEA: seg AC ⊆ ray AC, ray AC contains all points to the right of C, which includes B by assumption,
  -- so ray AC = ray AB, so seg AC ⊆ ray AB, but we know A - C - B now, so C ∈ seg AB.
  have B : Point := by tauto;
  use B
  intro ⟨ACB, BneA, BneC⟩
  have BonRayAC : B on ray A C := by tauto
  unfold Ray at BonRayAC
  rcases BonRayAC with BonSeg | BonExt
  -- B is not on the segment.
  exfalso
  simp only [mem_setOf_eq] at BonSeg
  rcases BonSeg with ABC | BeqA | BeqC
  · exact Betweenness.absurdity_abc_acb ⟨ABC, ACB⟩
  · tauto
  · tauto
  -- So B is on the extension, which means ACB
  unfold Extension at BonExt; simp only [ne_eq, mem_setOf_eq] at BonExt
  have ⟨ACB, _, _⟩ := BonExt
  have ConSegAB : C on segment A B := by tauto
  sorry -- idea: if seg A B and seg C D are colinear, and A on CD and B on CD, then AB ⊆ CD




@[simp] lemma ray_sub_line : ∀ A B : Point, ray A B ⊆ line A B := by
  intro A B E EonRayAB
  unfold LineThrough; unfold Ray at EonRayAB
  simp_all only [mem_union, mem_setOf_eq, ne_eq]
  rcases EonRayAB with (h1 | h2 | h3) | ⟨h4, h5, h6⟩
  obtain ⟨_, _, hCol⟩ := B1a h1;
  repeat tauto



end Line

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

@[simp] lemma seg_inter_ext_empty' : X on segment A B -> X off extension A B := by
  intro XonAB
  by_contra! hNeg
  have interEmpty : segment A B ∩ extension A B = ∅ := seg_inter_ext_empty
  have XinInter : X ∈ (segment A B ∩ extension A B) := by tauto
  rw [interEmpty] at XinInter
  contradiction

@[simp] lemma ext_inter_seg_empty : X on extension A B -> X off segment A B := by
  intro XonAB
  by_contra! hNeg
  have interEmpty : segment A B ∩ extension A B = ∅ := seg_inter_ext_empty
  have XinInter : X ∈ (segment A B ∩ extension A B) := by tauto
  rw [interEmpty] at XinInter
  contradiction


@[simp] lemma intersection_is_unique : ∀ L M : Line, L ≠ M -> (L ∦ M) -> X ∈ L ∩ M ∧ Y ∈ L ∩ M -> X = Y := by
  intro L M LneM LnparM ⟨XonInt, YonInt⟩
  have ⟨P, LinterMatP, Puniq⟩ : ∃! X : Point, L intersects M at X := Ch2.Prop.P1 LneM LnparM
  specialize LinterMatP
  rw [LinterMatP] at XonInt
  rw [LinterMatP] at YonInt
  have XeqP : X = P := by tauto
  have YeqP : Y = P := by tauto
  rw [XeqP, YeqP]

@[simp] lemma parallel_intersection_is_empty : ∀ L M : Line, (L ≠ M) -> (L ∥ M) -> L ∩ M = ∅ := by
  intro L M LneM LparM
  unfold Parallel at LparM
  specialize LparM LneM
  apply Subset.antisymm
  · trivial
  · tauto


-- Lines are never equal to segments, extensions, or rays
-- These seem intuitive, but I have no idea how to prove them. Probably relates to the 'extension' theorems.
--@[simp] lemma line_is_bigger_than_segment : ∀ L : Line, ∀ A B : Point, segment A B ≠ L := by sorry
--@[simp] lemma line_is_bigger_than_extension : ∀ L : Line, ∀ A B : Point, extension A B ≠ L := by sorry
--@[simp] lemma line_is_bigger_than_ray : ∀ L : Line, ∀ A B : Point, ray A B ≠ L := by sorry


/-- If a line intersects a segment, then it intersects the ray containing that segment -/
-- TODO: I think some of the non-equality conditions are provable.
@[simp] lemma lift_seg_ray {AneB : A ≠ B} :
  (L intersects segment A B at X) -> (L intersects ray A B at X) := by
  intro LintABatX
  have XonSegAB : X on segment A B := inter_touch_right LintABatX
  have XonL : X on L := inter_touch_left LintABatX
  have XonRayAB : X on ray A B := by
    unfold Ray; tauto
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
lemma reject_seg_ext {AneB : A ≠ B} : (L intersects segment A B at X) -> ∀ X : Point, ¬(L intersects extension A B at X) := by sorry

/- If a line intersects a ray, then it intersects the line containing the ray-/
@[simp] lemma lift_ray_line {AneB : A ≠ B} : (L intersects ray A B at X) -> (L intersects line A B at X) := by
  intro LintRay
  sorry

/- If a line intersects a segment, then it intersects the line containing the segment -/
@[simp] lemma lift_seg_line {AneB : A ≠ B} : (L intersects segment A B at X) -> (L intersects line A B at X) := by
  intro LintSeg
  apply lift_seg_ray at LintSeg
  apply lift_ray_line at LintSeg
  exact LintSeg
  repeat tauto







end Intersection


end Geometry.Ch3.Prop
