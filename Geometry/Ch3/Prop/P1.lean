module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
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
-- Ed. Promoting between commutativity into the set definition. I don't love the
-- use of sets for Ray/Segment, I feel like it might've been easier to just use
-- betweenness directly.
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
-- Ed. Segments commute their endpoints, so do lines, technically, but I don't have a lemma for that.
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
  A ≠ B -> (Segment A B) -> ∃! L : G.Line, (A on L) ∧ (B on L) := by
  intro hDistinct AB
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
-- Ed. P1.L6: "For any Segment A B, then A is on Segment A B, and B is on Segment A B"
lemma P1.L6 {A B : G.Point} :
  let AB := Segment A B; A ∈ AB ∧ B ∈ AB := by
  intro AB
  apply And.intro
  subst AB; unfold Segment; tauto
  subst AB; unfold Segment; simp;

@[simp]
-- Ed. P1.L7: "If D is between B and B, then B = D"
lemma P1.L7 {B D : G.Point} :
  G.Between B D B -> B = D := by
  intro hBDB
  by_contra! hNeg
  obtain ⟨A, C, E, BD, hIncidence, ⟨bABD, bBCD, bBDE⟩⟩ := G.ba_2_density B D hNeg
  obtain ⟨⟨_, _, hContraWitness⟩, _, _⟩  := G.ba_1a_distinct_colinear B D B hBDB
  contradiction

@[simp]
-- Ed. P1.L8: "C ∈ Segment A B -> C on AB (where AB : Line that passes through AB)"
lemma P1.L8 {A B C : G.Point}:
  A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ C ∈ (Segment A B) ->
  ∃! L : G.Line, (C on L) := by
  intro ⟨AneB, BneC, AneC, ConSegAB⟩
  obtain hAB : ∃! L : G.Line, (A on L) ∧ (B on L) := by
    apply L5.i
    exact AneB
    exact ⟨C, ConSegAB⟩
  obtain ⟨AB, ⟨AonAB, BonAB⟩, ABUniq⟩ := hAB
  use AB
  constructor
  unfold Segment at ConSegAB
  sorry

  -- Ed. This is a pain, because this sudden move to make a Line a concrete set of points,
  -- we end up in conversion hell just to have a psuedo-model inside the theory? Makes sense
  -- on paper, not formally though, I think. Adding another class of objects to manage is
  -- redundant.
  --
  -- A potentially better model would be to drop the two absurdities w/ Between, and just define
  -- Segment, Ray, and LineThrough as properties of Between, something like:
  --
  -- Segment A B := ∀ C : Point, Between A C B    -- "All the points between A and B"
  -- Extension A B := ∀ C : Point, Between A B C  -- "All the points to one side of Segment AB"
  -- Ray A B := Segment A B ∨ Extension A B       -- "All the points in the Segment or Extension
  -- LineThrough A B := Ray A B ∨ Ray B A         -- "All the points in each ray through Segment AB"
  --
  -- notation:80 P " on " (Segment A B) => Between A P B ∨ P = A ∨ P = B
  -- notation:80 P " on " (Extension A B) => Between A B P -- no endpoints
  -- notation:80 P " on " (Ray A B) => (Segment A B) ∨ (Extension A B)
  -- notation:80 P " on " (LineThrough A B) => (Ray A P) ∨ (Ray P A)
  --
  -- these are now just propositions, not sets, and this means we can't use Set Theory at them,
  -- which is a loss I do not expect to feel at any point ever.

  -- I made an attempt at this in `refactor-1`, but failed, I think due to the way I've structured
  -- the theory.

  -- I might make a big change here, copying over Tao's approach with _Analysis I_, taking a
  -- '1 chapter, 1 lean file' approach rather than my admittedly more computer-science-y
  -- method here of breaking things into lots of small files.

  -- Would also be an opportunity to try verso. :)


lemma test : ∀ L : G.Line, ∃ S : Set G.Point, S = { P | P on L } := by
  intro L
  simp only [↓existsAndEq]



@[simp]
-- Ed. P1.L9.{i,ii,iii}: "If C is on {i: Segment, ii: Ray, iii: LineThrough} A B, then Collinear A B C"
lemma P1.L9.i {A B C : G.Point}:
  A ≠ B -> (C ∈ Segment A B) -> Collinear A B C := by
    intro AneB ConAB
    -- FIXME: Some weird type issue here when I just try to pass (L5.i A B AneB) directly results in a type error
    obtain hAB : ∃! L : G.Line, (A on L) ∧ (B on L) := by
      apply L5.i
      exact AneB
      exact ⟨C, ConAB⟩
    obtain ⟨AB, ⟨AonAB, BonAB⟩, ABUniq⟩ := hAB
    -- Let's check the simple case where C is A or B; which is easy since two points are always collinear with each
    -- other.
    by_cases hSuppose : A = C ∨ B = C
    unfold Collinear; use AB;
    rcases hSuppose with AeqC | BeqC
    rw [<- AeqC]; tauto
    rw [<- BeqC]; tauto
    push_neg at hSuppose
    unfold Segment at *; unfold Collinear at *
    dsimp at *
    use AB, AonAB, BonAB
    simp_all only [mem_union, mem_insert_iff, mem_singleton_iff, mem_setOf_eq, and_imp];
    rcases ConAB with (hCinSetA | hCinSetB) | hBetween
    -- hCinSetA,
    tauto
    -- hCinSetB
    tauto
    -- hBetween, Idea, C ∈ Segment A B -> C on AB:Line
    have ConSegAB : C ∈ Segment A B := by
      unfold Segment; simp; tauto
    have ConAB : C on AB := by
      have l8 := L8
      specialize l8 G A B C


    trivial




    sorry


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
  intro C hCinInter
  rcases hCinInter with ⟨hConRayAB, hConRayBA⟩
  -- "... (3) If C = A or C = B"
  by_cases hSuppose : C = A ∨ C = B --
  aesop -- Ed: aesop easily resolves "... C is an endpoint of AB.", but it's an ugly proof, FIXME.
  push_neg at hSuppose
  obtain ⟨CneA, CneB⟩ := hSuppose
  -- "otherwise, A,B, and C are three Collinear points (by def of Ray and Axiom B-1), ..."
  obtain hCol : Collinear A B C := by
    unfold Collinear
    have hBetweenABC : G.Between A B C := by
      -- we know C is neither A nor B by supposition above, so it must be that C ∈ {P | A * B * P}
      have CinExtension : C ∈ {P | G.Between A B P} := by
        sorry -- TODO: I think betweenness may be establishable, but I suspect I'll need a lemma

      simp_all only [ne_eq, subset_inter_iff, L1, L2, and_self, mem_setOf_eq]
    obtain ⟨hDistinct, L, hCollinearABC⟩ := G.ba_1a_distinct_colinear A B C hBetweenABC
    exact hCollinearABC
  -- "... so exactly one of the releation A * C * B, A * B * C, or C * A * B holds (Axiom B-3)."
  rcases G.ba_3_lines_arent_circles A B C ⟨AneB, CneB.symm, CneA.symm, hCol⟩ with hABC | hCAB | hACB
  -- "(4) If A * B * C holds, then C is not on Ray B A; ..."
  exfalso ; unfold Ray at hConRayBA ; unfold Segment at hConRayBA ; simp_all; tauto
  -- "... if C * A * B holds, then C is not on Ray A B."
  exfalso ; unfold Ray at hConRayAB ; unfold Segment at hConRayAB; simp_all; tauto
  -- "... In either case, C does not belone to both rays.
  -- (5) Hence, the relation A * C * B must hold, so C belongs to Segment AB (definition of Segment AB, proof by cases)"
  obtain ⟨nbABC, nbBAC, bACB⟩ := hACB
  unfold Segment; simp_all
  -- Ed. The author doesn't do the reverse here, probably because it's pretty trivial:
  trivial


/-
  unfold Segment
  have CnotinSetA : C ∉ ({A} : Set G.Point) := by tauto
  have CnotinSetB : C ∉ ({B} : Set G.Point) := by tauto
  have CnotinAuB : C ∉ (({A} : Set G.Point) ∪ {B}) := by
    simp_all only [ne_eq, not_false_eq_true, subset_inter_iff, L1, L2, and_self, mem_union, mem_setOf_eq, or_true, L4,
      or_false, or_self]
-/









  sorry



-- (ii) Ray A B ∪ Ray B A = LineThrough A B"
@[simp]
theorem P1.ii (A B : G.Point) :
  (Ray A B) ∪ (Ray B A) = (Segment A B) := by
  sorry

-- Ed: I split these in a bit of an abnormal way, but


end Geometry.Ch3.Prop
