import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Tactics

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory


--
/-
p109. the author refers to the definition of these things, but the definitions are pretty loose and assume
undergrad set theory is a familiar topic. These are some of the formalizations of those basic facts.

"By the definition of segment and ray, `the segment A B ⊆ the ray A B`"
-/
@[simp] lemma P1.L1 (A B : Point) : segment A B ⊆ ray A B := by simp_all
/-
It helps to be able to commute these around
-/
@[simp] lemma P1.L2 (A B : Point) : segment A B = segment B A := by
  unfold Segment
  ext P
  rw [@mem_setOf]; simp_all only [mem_setOf_eq]
  constructor
  intro h; rcases h with h0 | h1 | h2; rw [B1b];
  repeat tauto
  intro h; rcases h with h0 | h1 | h2; rw [B1b]
  repeat tauto
/-
Useful for dealing with the trivial cases.
-/
@[simp] lemma P1.L3 (A B : Point) : (A on ray A B) ∧ (B on ray A B) := by
  constructor
  repeat simp only [mem_union, mem_setOf_eq, true_or, or_true]
/-
The endpoint B is in common here.
-/
@[simp] lemma P1.L4 (A B : Point) : segment A B ⊆ ray B A := by
  intro P hPinSegAB
  simp_all only [mem_setOf_eq, mem_union, L2, true_or]


/-
p.109, "For any two points A and B:
(i) Ray A B ∩ Ray B A = Segment A B ..."
-/
@[simp]
theorem P1.i (A B : Point) : A ≠ B ->
  -- Ed. I'm inserting this `A ≠ B` condition because the author never clearly
  -- states, but definitely implies, that `the ray A A` is degenerate because `A
  -- - A - B` and the like are degenerate
  (Segment A B) = (Ray A B) ∩ (Ray B A)  := by
  /-
  "
  Proof of (i):

  (1) By the definition of segment and ray, the segment A B ⊆ the ray A B [and ⊆ ray B A],
  so by definition of intersection, the segment AB ⊆ (ray A B ∩ ray B A)." [Ed. Here I just
  let `simp` handle the simple case, it ultimately just does the underlying set theory]
  -/
  intro AneB
  ext C
  constructor
  simp_all only [mem_setOf_eq, L2, mem_inter_iff, mem_union, true_or, and_self, implies_true]
  /-
  (2) Conversely, let the point C belone to the intersection, `(ray A B ∩ ray B A)`; we wish
  to show that C belongs to the segment A B.
  (3) If C = A or C = B, C is an endpoint of the segment A B ..."
  -/
  by_cases hSuppose : (C = A ∨ C = B)
  tauto;
  push_neg at hSuppose; have ⟨CneA, CneB⟩ := hSuppose
  /-
  "... Otherwise, A B and C are three collinear points (by the definition of ray and Axiom B-1)..."
  Ed. TODO: this should be a lemma of its own.
  -/
  intro hCinIntersection
  have hABCCollinear : Collinear A B C := by
    unfold Collinear
    use ray A B;
    -- Ed. It turns out simp can solve this with set trickery and B1b (by way of L2) as expected.
    -- The geometric argument is more like, "C is selected from the ray A B, so it's on the ray A B"
    simp_all only [ne_eq, not_false_eq_true, and_self, mem_inter_iff, mem_union, mem_setOf_eq, L2,
      true_or, or_true]
  /-
  "so exactly one of A - C - B, A - B - C, or C - A - B holds (Axiom B-3). ..."
  -/
  obtain (⟨bABC, nBAC, nACB⟩ | ⟨nABC, bBAC, nACB⟩ | ⟨nABC, nBAC, bACB⟩) := B3 A B C ⟨AneB, CneB.symm, CneA.symm, hABCCollinear⟩
  /-
  "... (4) If A - B - C holds, then C is not on the ray B A; ..."
  -/
  exfalso; simp_all; tauto
  /-
  "... if C - A - B holds, then C is not on the ray A B. ..."
  -/
  exfalso; simp_all; tauto
  /-
  "... In either case, C does not belong to both rays.
  (5) Hence, the relation A - C - B must hold, so C belongs to the segment A B (definition of the
  segment A B, proof by cases)."
  -/
  tauto


-- (ii) Ray A B ∪ Ray B A = LineThrough A B"
@[simp]
theorem P1.ii (A B : Point) :
  (ray A B) ∪ (ray B A) = (segment A B) := by
  sorry

-- Ed: I split these in a bit of an abnormal way, but


end Geometry.Ch3.Prop
