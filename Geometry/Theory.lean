import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.List.Basic

namespace Geometry.Theory

open Set

-- Helper to check if an identifier is accessible
-- FIXME: doesn't really do what I want, which is to hide all the generated conditions that have daggers or underscores.
open Lean in
def isAccessible (id : TSyntax `ident) : Bool :=
  let name := id.getId.toString
  !name.startsWith "_" && !name.contains "✝"

-- Custom syntax category for the distinct binder
declare_syntax_cat distinct_binder
syntax ident+ " : " term : distinct_binder


-- TODO: Maybe replace this with a non-recursive version that just generates `≠` conditions.
syntax "distinct " ident+ : term
macro_rules
  | `(distinct $[$xs]*) => do
    let accessible := (xs.toList.filter isAccessible).toArray
    `(List.Pairwise (· ≠ ·) [$[$accessible],*])


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
-- TODO: Refactor to use a list?
@[reducible] def Collinear (A B C : Point) : Prop := ∃ L : Line, (A on L) ∧ (B on L) ∧ (C on L)
@[reducible] def CollinearL (Sₚ : List Point) : Prop := ∃ L : Line, ∀ A : Point, (A ∈ Sₚ) ↔ (A on L)

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

-- p. 69-70, Ed. The author provides these as very terse statements, I've tried to give informal
-- respellings as documentation.
/--
For any two distinct points P and Q, there exists a unique line L which has P and Q
-/
@[simp] axiom I1 : ∀ P Q : Point, P ≠ Q -> ∃! L : Line, (P on L) ∧ (Q on L)
/-- For any line, there are at least two distinct points on it -/
@[simp] axiom I2 : ∀ L : Line, ∃ A B : Point, A ≠ B ∧ (A on L) ∧ (B on L)
/-- There exists three distinct points not on any single line ("There exists
three non-collinear points", but without mentioning the undefined notion of
collinearity) -/
@[simp] axiom I3 : ∃ A B C : Point, (A ≠ B ∧ A ≠ C ∧ B ≠ C) ∧ (∀ (L : Line), (A on L) → (B on L) → (C off L))

/--
p.70 "Three ... lines ... are _concurrent_ if there exists a point incident with all of them"

Ed. Author technically makes this apply to any number of lines, if it ever comes up maybe it's worth
a refactor to any finite set of lines?
-/
@[reducible] def Concurrent (L M N : Line) : Prop :=
    ∃ P : Point, (P on L) ∧ (P on M) ∧ (P on N)

/--
p. 20, "Two lines `l` and `m` are parallel if they do not intersect, i.e., if no point lies on both
of them. We denote this by `l ‖ m`"

p. 70, "Lines `l` and `m` are _parallel_ if they are distinct lines and no point is incident to both
of them."

Ed. This gets defined twice, the definitions are equivalent
-/
@[reducible] def Parallel (L M : Line) : Prop := L ≠ M -> ∀ P : Point, ¬((P on L) ∧ (P on M))

notation:20 L " ∥ " M => Parallel L M
notation:20 L " ∦ " M => ¬(Parallel L M)

-- -- -- BETWEENNESS GEOMETRY


/--
p.108a "If A - B - C, then A,B,C are distinct points on the same line...
-/
@[simp] axiom B1a {A B C : Point} :
      A - B - C -> (A ≠ B ∧ B ≠ C ∧ A ≠ C) ∧
      -- ed. this and next condition may be redundant
      (∃ L : Line, (A on L) ∧ (B on L) ∧ (C on L)) ∧
      Collinear A B C

/--
p.108b ... and [A - B - C iff] C - B - A.""

Ed. Note, I separated these parts of the axiom to make rewriting
a bit easier. The author even notes, "The second part (C * B * A) makes the obvious remark
that 'betwen A and C' means the same as 'between C and A'" Making it a separate axiom means
I won't have to dig it out of the pile of parts that is 1a.
-/
@[simp] axiom B1b : ∀ A B C : Point, A - B - C ↔ C - B - A


/--
p.108 "Given any two distinct points B and D, there exist points A, C, and E lying on →ₗBD such that
A * B * D, B * C * D, and B * D * E".

Ed. Here I introduce the line BD explicitly with it's incidence conditions
then posit the proposed points with _their_ incidence conditions, and then
finally state the between condition.

I like to call this the 'density' axiom because, used recursively, it posits
something like the density of rationals -- for any two distinct points on a
line, there is always a point between them.
-/
@[simp] axiom B2 : ∀ B D : Point, B ≠ D ->
  ∃ A C E : Point, ∃ seg : Line,
  ((A on seg) ∧ (B on seg) ∧ (C on seg) ∧ (D on seg) ∧ (E on seg)) ∧
  distinct A B C D E ∧
  (A - B - D) ∧ (B - C - D) ∧ (B - D - E)

/-- p.108 "If A, B, and C are three distinct points lying on the same line, then
 one and only one of the points is between the other two."
-/
@[simp] axiom B3 : ∀ A B C : Point, A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Collinear A B C ->
  ( (A - B - C) ∧ ¬(B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧  (B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧ ¬(B - A - C) ∧  (A - C - B))

/--
p.110 "Definition. Let L be any line, and A and B points that do not lie on L. If A = B or if the segment A B
contains no points that lie on L, we say that A and B are _on the same side_ of L; whereas, if A ≠ B and segment A B
does intersect L, we say that A and B are _on opposite sides_ of L (see Figure 3.6). The law of the excluded middle
(Logic Rule 10) tells us that A and B are either on the same side or on opposite sides of L"
-/
-- FIXME: I think this might be incorrect; we should assume A and B are off L by definition, not ask for it
-- in implication
@[reducible] def SameSide (A B : Point) (L : Line)
  := (A off L) ∧ (B off L)
  -> ((A = B) ∨ (∀ P : Point, (P on segment A B) -> (L avoids P)))

/--
"Splits" and "Guards", L "splits" A and B if A and B are on opposite sides of the 'wall' L, it 'guards'
them if they are both on the same side of the wall (we presume all points are allied with other points
on their side of the line).
-/
notation:20 L " splits " A " and " B => ¬(SameSide A B L)
notation:20 L " guards " A " and " B => SameSide A B L

/--
Ed. The author refers to the law of the excluded middle, Lean does not include it by default and
generally I want to avoid including it everywhere, this is a limited application of it which
should help our purpose.
-/
@[simp] axiom LotEMGuards : (L splits A and B) ∨ (L guards A and B)

/--
p.110 "Betweenness Axiom 4 (Plane Separation). For every line L and for any
three points A, B, and C not on L: (i) If A and B are on the same side of L and
if B and C are on the same side of L, the A and C are on the same side of L..."
-/
@[simp] axiom B4i {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L guards A and B) ∧ (L guards B and C) -> (L guards A and C)
/--
"... (ii) If A and B are on opposite sides of L and if B and C are opposite
sides of L, then A and C are on the same side of L."
-/
@[simp] axiom B4ii {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L splits A and B) ∧ (L splits B and C) -> (L guards A and C)

@[reducible] def Intersects (L M : Line) (X : Point) : Prop := L ∩ M = {X}

-- Syntax for "L intersects M at X"
syntax (name := intersectsAt) term " intersects " term " at " term : term

macro_rules (kind := intersectsAt)
  | `($L intersects $M at $X) => `(Intersects $L $M $X)



end Geometry.Theory
