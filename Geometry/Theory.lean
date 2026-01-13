import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs

namespace Geometry.Theory

open Set

/--
The core geometric theory presented in the text is contained here as simple structures/axia taken as needed into proofs.
-/
axiom Point : Type
-- Ed: In the text, the author ends up using the 'Line is a Set of points' to define segments, rays, and implicitly
-- uses the intuitive idea ("A line is the set of collinear points that contain at least two known points"). However,
-- Ch2 uses an opaque 'Line' type and reasons only about it's properties without definition. I try to replicate this in
-- my implementation of Ch2, but do define it as a set 'up front'
@[reducible] def Line := Set Point
axiom Between : Point -> Point -> Point -> Prop
-- Ed: In the text, the author uses `*`, but Lean reserves that, so I've chosen `-`. `∗` is available, but I don't want
-- to type `\ast` every time.
notation:65 A:66 " - " B:66 " - " C:65 => Between A B C
-- Segment, Ray, Extension, LineThrough


-- TODO: Review binding values for all this notation
syntax:50 (name := onNotation) term:51 " on " term:50 : term
-- Keep segment/ray/etc as separate term syntax
syntax:max "segment " term:max term:max : term
syntax:max "ray " term:max term:max : term
syntax:max "extension " term:max term:max : term
syntax:max "line " term:max term:max : term

-- Even higher for "the" forms
syntax:1000 "the " "segment " term:max term:max : term
syntax:1000 "the " "ray " term:max term:max : term
syntax:1000 "the " "extension " term:max term:max : term
syntax:1000 "the " "line " term:max term:max : term

notation:80 P " off " L => P ∉ L
notation:80 L " has " P => P ∈ L
notation:80 L " avoids " P => P ∉ L

-- Macro rules for "on" notation - we need to specify these rules incrementally, so that
-- I can introduce collinear as a definition.
macro_rules (kind := onNotation)
  | `($P on $L) => `($P ∈ $L)

-- p. 70, "Three or more points A, B, C are _collinear_ if there exists a line incident with all of them."
def Collinear (A B C : Point) : Prop := ∃ L : Line, (A on L) ∧ (B on L) ∧ (C on L)

@[reducible] def Segment (A B : Point) := {C | (A - C - B) ∨ A = C ∨ B = C}
@[reducible] def Extension (A B : Point) := {C | A - B - C ∧ A ≠ C ∧ B ≠ C}
@[reducible] def Ray (A B : Point) := (Segment A B) ∪ (Extension A B)
@[reducible] def LineThrough (A B : Point) := {C | Collinear A B C}

-- Re-running
macro_rules (kind := onNotation)
  | `($P on segment $A $B) => `($P ∈ Segment $A $B)
  | `($P on ray $A $B) => `($P ∈ Ray $A $B)
  | `($P on extension $A $B) => `($P ∈ Extension $A $B)
  | `($P on line $A $B) => `($P ∈ LineThrough $A $B)
  | `($P on $L) => `($P ∈ $L)

-- Macro rules for standalone geometric objects (without "the")
macro_rules
  | `(segment $A $B) => `(Segment $A $B)
  | `(ray $A $B) => `(Ray $A $B)
  | `(extension $A $B) => `(Extension $A $B)
  | `(line $A $B) => `(LineThrough $A $B)
  | `(the segment $A $B) => `(Segment $A $B)
  | `(the ray $A $B) => `(Ray $A $B)
  | `(the extension $A $B) => `(Extension $A $B)
  | `(the line $A $B) => `(LineThrough $A $B)


-- -- GEOMETRIC AXIOMS

-- -- -- INCIDENCE GEOMETRY

-- TODO: Better Docs
-- p. 69-70, IncidenceGeometry
axiom I1 : ∀ P Q : Point, P ≠ Q -> ∃! L : Line, (P on L) ∧ (Q on L)
axiom I2 : ∀ L : Line, ∃ A B : Point, A ≠ B ∧ (A on L) ∧ (B on L)
axiom I3 : ∃ A B C : Point, (A ≠ B ∧ A ≠ C ∧ B ≠ C) ∧ (∀ (L : Line), (A on L) → (B on L) → (C off L))

def Concurrent (L M N : Line) : Prop :=
    ∃ P : Point, (P on L) ∧ (P on M) ∧ (P on N)

-- p. 20, "Two lines `l` and `m` are parallel if they do not intersect, i.e., if no point lies on both
-- of them. We denote this by `l ‖ m`"
-- p. 70, "Lines `l` and `m` are _parallel_ if they are distinct lines and no point is incident to both
-- of them."
def Parallel (L M : Line) : Prop := L ≠ M -> ∀ P : Point, ¬((P on L) ∧ (P on M))

notation:20 L " ∥ " M => Parallel L M
notation:20 L " ∦ " M => ¬(Parallel L M)

-- -- -- BETWEENNESS GEOMETRY


/-- p.108a "If A * B * C, then A,B,C are distinct points on the same line... TODO Finish -/
axiom B1a : ∀ A B C : Point, A - B - C ->
      (A ≠ B ∧ B ≠ C ∧ A ≠ C) ∧
      (∃ L : Line, (A on L) ∧ (B on L) ∧ (C on L)) ∧
      Collinear A B C

-- p.108b ... and C * B * A."" Ed. Note, I separated these parts of the axiom to make rewriting
-- a bit easier. The author even notes, "The second part (C * B * A) makes the obvious remark
-- that 'betwen A and C' means the same as 'between C and A'" Making it a separate axiom means
-- I won't have to dig it out of the pile of parts that is 1a.
axiom B1b : ∀ A B C : Point, A - B - C ↔ C - B - A

-- p.108 "Given any two distinct points B and D, there exist points A, C, and E lying on →ₗBD such that
-- A * B * D, B * C * D, and B * D * E".
--
-- Ed. Here I introduce the line BD explicitly with it's incidence conditions
-- then posit the proposed points with _their_ incidence conditions, and then
-- finally state the between condition.
--
-- I like to call this the 'density' axiom because, used recursively, it posits
-- something like the density of rationals -- for any two distinct points on a
-- line, there is always a point between them.
axiom B2 : ∀ B D : Point, B ≠ D ->
  ∃ A C E : Point, ∃ BD : Line,
  ((A on BD) ∧ (B on BD) ∧ (C on BD) ∧ (D on BD) ∧ (E on BD)) ∧
  (A - B - D) ∧ (B - C - D) ∧ (B - D - E)
-- p.108 "If A, B, and C are three distinct points lying on the same line,
-- then one and only one of the points is between the other two."
axiom B3 : ∀ A B C : Point, A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Collinear A B C ->
  ( (A - B - C) ∧ ¬(B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧  (B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧ ¬(B - A - C) ∧  (A - C - B))




end Geometry.Theory
