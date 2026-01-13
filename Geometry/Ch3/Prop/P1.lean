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


@[simp] lemma P1.L5.segment {A B : Point} : A ≠ B ->
  ∀ C : Point, C on segment A B -> Collinear A B C := by
  intro AneB C ConSeg; unfold Collinear
  tauto

@[simp] lemma P1.L5.ray {A B : Point} : A ≠ B ->
  ∀ C : Point, C on ray A B -> Collinear A B C := by
  intro AneB C ConRay; unfold Collinear
  unfold Ray at ConRay
  tauto

@[simp] lemma P1.L5.extension {A B : Point} : A ≠ B ->
  ∀ C : Point, C on extension A B -> Collinear A B C := by
  intro AneB C ConExt; unfold Collinear
  simp_all; tauto

@[simp] lemma P1.L5.line {A B : Point} : A ≠ B ->
  ∀ C : Point, C on line A B -> Collinear A B C := by
  simp only [ne_eq, mem_setOf_eq, imp_self, implies_true]

/-
Ed. Collinearity commutes
-/
@[simp] lemma P1.L6.i {A B C : Point} (hABCDistinct : A ≠ B ∧ B ≠ C ∧ A ≠ C) :
  (Collinear A B C) ↔ (Collinear B A C) := by
  unfold Collinear;
  constructor
  intro hL
  have ⟨L, hInc, hUniq⟩ := hL
  use L
  tauto
  --
  intro hL
  have ⟨L, hInc, hUniq⟩ := hL
  use L
  tauto

/-
Ed. Collinearity commutes in both argument pairs
-/
@[simp] lemma P1.L6.ii {A B C : Point} : A ≠ B ∧ B ≠ C ∧ A ≠ C ->
  (Collinear A B C) ↔ (Collinear A C B) := by
  unfold Collinear; simp_all only [ne_eq, and_imp]
  tauto

@[simp] lemma P1.L7.segment {A B P : Point} (PneAB : P ≠ A ∧ P ≠ B) :
  A - P - B -> P on the segment A B := by intro h; unfold Segment; simp; tauto;

@[simp] lemma P1.L7.ray {A B P : Point} (PneAB : P ≠ A ∧ P ≠ B) :
  A - P - B -> P on the ray A B := by intro h; unfold Ray; simp; tauto;

@[simp] lemma P1.L7.extension {A B P : Point} (PneAB : P ≠ A ∧ P ≠ B) :
  A - B - P -> P on the extension A B := by intro h; unfold Extension; simp; tauto

@[simp] lemma P1.L7.line.i {A B P : Point} (PneAB : P ≠ A ∧ P ≠ B) (AneB : A ≠ B) :
  A - B - P -> P on the line A B := by
    intro hABP;
    have hPonExtAB : P on extension A B := P1.L7.extension PneAB hABP
    unfold LineThrough; simp only [mem_setOf_eq]
    exact P1.L5.extension AneB P hPonExtAB

-- (ii) Ray A B ∪ Ray B A = LineThrough A B"
@[simp] theorem P1.ii (A B : Point) : A ≠ B -> -- Ed. Same as above.
  (ray A B) ∪ (ray B A) = (line A B) := by
  intro AneB
  ext P
  constructor
  -- Forward Case: Idea, unfold all the set stuff and apply some commutativity rules
  -- to build everything
  intro hPonRayUnion
  rcases hPonRayUnion with hPonRayAB | hPonRayBA
  simp only [mem_setOf_eq]; exact L5.ray AneB P hPonRayAB
  simp only [mem_setOf_eq]; unfold Ray at hPonRayBA;
  rcases hPonRayBA with hPonSegmentBA | hPonExtensionBA
  rw [L2] at hPonSegmentBA; exact L5.segment AneB P hPonSegmentBA
  rw [L6.i]; exact L5.extension (id (Ne.symm AneB)) P hPonExtensionBA
  constructor; trivial; unfold Extension at hPonExtensionBA; simp_all
  -- Backward Case: Just check all the cases.
  intro hPonLine
  unfold LineThrough at *;
  have ⟨L, ⟨AonL, BonL, PonL⟩⟩ := hPonLine
  by_cases suppose: P = A ∨ P = B
  -- Easy case first, this is degenerate
  -- now if P = A, and P = B, then A = B, which is false.
  rcases suppose with PeqA | PeqB
  rw [PeqA]; simp only [mem_union, mem_setOf_eq, true_or, or_true, ne_eq, not_true_eq_false, false_and, and_false, or_false, L2, or_self]
  rw [PeqB]; simp only [mem_union, mem_setOf_eq, or_true, ne_eq, not_true_eq_false, and_false, or_false, L2, false_and, or_self]
  -- Now we have that A B and P are distinct
  have hABPdistinct := by push_neg at suppose; exact suppose
  -- Assuming P distinct, B3 + Collinearity means only one betweenness is possible:
  obtain (⟨bABP, nBAP, nAPB⟩ | ⟨nABP, bBAP, nAPB⟩ | ⟨nABP, nBAP, bAPB⟩) := B3 A B P ⟨AneB, hABPdistinct.right.symm, hABPdistinct.left.symm, hPonLine⟩
  -- the first assumption here is that P is on the extension
  obtain hPonExtAB : P on the extension A B := L7.extension hABPdistinct bABP
  -- so it's easy to fulfill the definition and do the set algebra
  unfold Ray; rw [<- L2]; rw [@union_union_union_comm, union_self, union_comm];
  -- then we just have to dig a little.
  constructor; left; exact hPonExtAB
  --
  -- B - A - P is the same argument in the other direction.
  obtain hPonExtBA : P on the extension B A := L7.extension (id (And.symm hABPdistinct)) bBAP
  unfold Ray; rw [<- L2]; rw [@union_union_union_comm, union_self, union_comm];
  constructor; right; exact hPonExtBA
  --
  -- APB means we're on the segment, not the extension, otherwise a similar argument
  obtain hPonsegAB : P on the segment A B := L7.segment hABPdistinct bAPB
  unfold Ray; tauto

end Geometry.Ch3.Prop
