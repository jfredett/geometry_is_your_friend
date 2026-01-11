module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Geometry.Tactics
public import Geometry.Ch2.Theory
public import Geometry.Ch2.Defs
public import Geometry.Ch3.Theory
public import Geometry.Ch3.Defs

@[expose] public section

namespace Geometry.Ch3.Prop

open Set
open Geometry.Ch2.Theory
open Geometry.Ch2.Defs
open Geometry.Ch3.Theory
open Geometry.Ch3.Defs

variable (G : BetweenGeometry)

set_option maxRecDepth 10000


-- p.109 "By the definition of a segment and ray, Segment A B ⊆ Ray A B"
-- Ed. Have to lift those definitions the author talks about, no rest for the wicked.
@[simp]
lemma P1.L1 (A B : G.Point) :
  (Segment A B) ⊆ (Ray A B) := by
  intro x xinAB
  unfold Ray
  simp_all only [mem_union, mem_setOf_eq, true_or]

@[simp]
lemma P1.L2 (A B : G.Point) :
  (Segment A B) ⊆ (Ray B A) := by
    intro X XinAB
    unfold Ray
    unfold Segment at *
    simp_all only [mem_union, mem_setOf_eq]
    -- aesop was here
    cases XinAB with
    | inl h =>
      cases h with
      | inl h_1 => simp_all only [or_true, true_or]
      | inr h_2 => simp_all only [true_or]
    | inr h_1 => {
      simp_all only [G.ba_1b_between_comm]
      tauto
    }

@[simp]
lemma P1.L3 {A B : G.Point} :
  { P | G.Between A P B } = {P | G.Between B P A } := by
  apply Subset.antisymm
  -- forward
  intro e hEinSet
  rw [@mem_setOf] at *
  rw [G.ba_1b_between_comm]
  exact hEinSet
  -- reverse
  intro e hEinSet
  rw [@mem_setOf] at *
  rw [G.ba_1b_between_comm]
  exact hEinSet

@[simp]
lemma P1.L4 {A B : G.Point} :
  (Segment A B) = (Segment B A) := by
  unfold Segment
  apply Subset.antisymm
  intro e hEinUnion
  simp_all only [L3, mem_union, mem_setOf_eq]
  tauto
  intro e hEinUnion
  simp_all only [L3, mem_union, mem_setOf_eq]
  tauto

@[simp]
-- Ed. P1.L5.{i,ii,iii}: "Given a {i: Segment, ii: Ray, iii: LineThrough} A B, there is a Line containing A and B"
lemma P1.L5.i (A B : G.Point) :
  (Segment A B) -> A ≠ B -> ∃! L : G.Line, (A on L) ∧ (B on L) := by
  intro AB hDistinct
  obtain ⟨L, h0, h1⟩ := G.ia_1_unique_line A B hDistinct
  use L

@[simp]
lemma P1.L5.ii {A B : G.Point} :
  A ≠ B -> (Ray A B) -> ∃! L : G.Line, (A on L) ∧ (B on L) := by
  intro hDistinct AB
  obtain ⟨L, h0, h1⟩ := G.ia_1_unique_line A B hDistinct
  use L

@[simp]
lemma P1.L5.iii {A B : G.Point} :
  (LineThrough A B) -> A ≠ B -> ∃! L : G.Line, (A on L) ∧ (B on L) := by
  intro AB hDistinct
  obtain ⟨L, h0, h1⟩ := G.ia_1_unique_line A B hDistinct
  use L

@[simp]
-- Ed. P1.L6: "If Segment A B, then A is on Segment A B, and B is on Segment A B"
lemma P1.L6 {A B : G.Point} :
  let AB := Segment A B; A ∈ AB ∧ B ∈ AB := by
  intro AB
  apply And.intro
  subst AB; unfold Segment; tauto
  subst AB; unfold Segment; simp; tauto

@[simp]
-- Ed. P1.L7: "If D is between B and B, then B = D"
lemma P1.L7 {B D : G.Point} :
  G.Between B D B -> B = D := by
  intro hBDB
  by_contra! hNeg
  obtain ⟨A, C, E, BD, hIncidence, ⟨bABD, bBCD, bBDE⟩⟩ := G.ba_2_density B D hNeg
  obtain ⟨⟨_, _, hContraWitness⟩, _, _⟩  := G.ba_1a_distinct_colinear B D B hBDB
  contradiction

/-
@[simp]
-- Ed. P1.L8.{i,ii,iii}: "If distinct points A, B, and C lie on the same {i: Segment, ii: Ray, iii: LineThrough}, they are collinear"
lemma P1.L8.i {A B C X Y : G.Point}:
  let XY := Segment X Y;
  A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ X ≠ Y ->
  XY ->
  A ∈ XY ∧ B ∈ XY ∧ C ∈ XY -> Collinear A B C := by
  simp only [and_imp];
  intro AneB BneC AneC XneY XY AonXY BonXY ConXY
  unfold Collinear
  obtain ⟨L, hIncidence, hUniq⟩ := (P1.L5.i G X Y) XY XneY
  use L
  -- TODO: 
-/

-- p.109, "For any two points A and B:
-- (i) Ray A B ∩ Ray B A = Segment A B
@[simp]
theorem P1.i (A B : G.Point) : A ≠ B -> -- Ed: Note the addition of distinction here. I don't think it's _needed_, but `Ray` is degenerate without it.
  (Ray A B) ∩ (Ray B A) = (Segment A B) := by
  intro AneB
  -- p.109 "Proof of (i):
  -- (1) By the definition of segment and ray [Ed: Lemmas 1 and 2], Seg AB ⊆ Ray AB and Seg AB ⊆ Ray BA
  -- so by definition of intersection, Seg AB ⊆ Ray AB ∩ Ray BA
  have hSegSubInterRays : (Segment A B) ⊆ ((Ray A B) ∩ (Ray B A)) := by
    simp_all only [L1, L2, subset_inter_iff, and_self]
  -- (2) Conversely, let the point C belong to Ray AB ∩ Ray BA, we want to show C belongs to Seg AB..."
  -- Ed. For lean's sake, showing this isn't as easy as the author has it as we need to unwind some things
  -- to get into a state to continue the author's proof.
  rw [@Subset.antisymm_iff]
  constructor
  unfold Ray
  intro C hCinInter
  rcases hCinInter with ⟨hConRayAB, hConRayBA⟩
  -- "... (3) If C = A or C = B"
  by_cases hSuppose : C = A ∨ C = B --
  aesop -- Ed: aesop easily resolves "... C is an endpoint of AB."
  push_neg at hSuppose
  obtain ⟨CneA, CneB⟩ := hSuppose
  -- "otherwise, A,B, and C are three Collinear points (by def of Ray and Axiom B-1)"
  -- missing the betweenness hypothesis here. I could get it from B3, potentially?
  obtain h := G.ba_1a_distinct_colinear A B C ?hBetweenABC
  obtain ⟨h0, h1, h2⟩ := G.ba_3_lines_arent_circles A B C ⟨AneB, CneB.symm, CneA.symm, ?hCol⟩
  sorry



-- (ii) Ray A B ∪ Ray B A = LineThrough A B"
@[simp]
theorem P1.ii (A B : G.Point) :
  (Ray A B) ∪ (Ray B A) = (Segment A B) := by
  sorry

-- Ed: I split these in a bit of an abnormal way, but


end Geometry.Ch3.Prop
