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

/- If two distinct points are found on two lines, those lines are equal.  -/
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

end Collinear

namespace Betweenness

/- With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another -/
@[simp] lemma absurdity_abc_bac : A - B - C ∧ B - A - C -> False := by
  intro ⟨ABC, BAC⟩
  obtain ⟨⟨AneB, BneC, AneC⟩, ⟨⟨L, AonL, BonL, ConL⟩, ABCCol⟩⟩ := B1a ABC
  obtain ⟨⟨BneA, AneC, BneC⟩, ⟨⟨M, BonM, AonM, ConM⟩, BACCol⟩⟩ := B1a BAC
  rcases B3 A B C ⟨AneB, BneC, AneC, ABCCol⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  contradiction; contradiction; contradiction

/- ibid -/
@[simp] lemma absurdity_abc_acb : A - B - C ∧ A - C - B -> False := by
  intro ⟨ABC, ACB⟩
  obtain ⟨⟨AneB, BneC, AneC⟩, ⟨⟨L, AonL, BonL, ConL⟩, ABCCol⟩⟩ := B1a ABC
  obtain ⟨⟨AneC, CneB, AneB⟩, ⟨⟨M, AonM, ConM, BonM⟩, ACBCol⟩⟩ := B1a ACB
  rcases B3 A B C ⟨AneB, BneC, AneC, ABCCol⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  contradiction; contradiction; contradiction




end Betweenness


namespace Line

@[simp] lemma seg_inclusion : ∀ A B C D : Point, (distinct A B C D)
  -> A on segment C D ∧ B on segment C D -> segment A B ⊆ segment C D := by
  unfold Segment; simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
    and_true, mem_setOf_eq, setOf_subset_setOf, and_imp]
  intro A B C D AneB AneC AneD BneC BneD CneD AonCD BonCD
  intro E hOpts
  rcases hOpts with AEB | AeqE | BeqE
  · obtain ⟨⟨AneE, BneE, _⟩, ⟨L, AonL, EonL, BonL⟩, colAEB⟩ := B1a AEB
    have ConL : C on L := by sorry
    have DonL : D on L := by sorry

    sorry
  · rw [<- AeqE]; exact AonCD
  · rw [<- BeqE]; exact BonCD




  sorry

/- Given any segment AC, we can find B such that AC ⊆ AB -/
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
/- Idea: Intersection is reduced _entirely_ to set intersection. All these facts should follow from that.
   This will certainly break a lot of proofs that use intersection, but the upside should be much easier proving
   later on. -/


/- If two lines intersect, their intersection is unique. -/
@[simp] lemma uniq : (L intersects M at X) ∧ (L intersects M at Y) -> X = Y := by
  unfold Intersects
  intro ⟨LMatX, LMatY⟩
  rw [LMatX] at LMatY
  exact singleton_eq_singleton_iff.mp LMatY

/- L intersects M is the same as M intersects L. -/
@[simp] lemma symm : (L intersects M at X) ↔ (M intersects L at X) := by
  unfold Intersects
  refine Eq.congr ?_ rfl
  exact inter_comm L M

/- If L intersects M at X, then X is on L -/
@[simp] lemma inter_touch_left : (L intersects M at X) -> (X on L) := by
  simp_all only [P5.L2, mem_inter_iff, mem_singleton_iff]
  intro h; specialize h X; tauto

/- If L intersects M at X, then X is on M -/
@[simp] lemma inter_touch_right : (L intersects M at X) -> (X on M) := by
  simp_all only [P5.L2, mem_inter_iff, mem_singleton_iff]
  intro h; specialize h X; tauto

/- If a line intersects a segment, then it intersects the ray containing that segment -/
@[simp] lemma lift_seg_ray : (L intersects segment A B at X) -> (L intersects ray A B at X) := by
  unfold Intersects
  intro h
  sorry
/- If a line intersects a segment, then it _does not_ intersect the extension of that segment.
 FIXME: Statement is a little weird with the custom syntax. don't think I'll need this in the short term
 so come back later. -/
-- lemma reject_seg_ext : (L intersects segment A B at X) -> ¬(L intersects extension A B) := by sorry
/- If a line intersects a segment, then it intersects the line containing the segment -/
@[simp] lemma lift_seg_line : (L intersects segment A B at X) -> (L intersects line A B at X) := by sorry
/- If a line intersects a ray, then it intersects the line containing the ray-/
@[simp] lemma lift_ray_line : (L intersects ray A B at X) -> (L intersects line A B at X) := by sorry





end Intersection


end Geometry.Ch3.Prop
