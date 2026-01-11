module

public import Geometry.Syntax
public import Geometry.Tactics
public import Geometry.Ch2.Theory
public import Geometry.Ch2.Defs

@[expose] public section

namespace Geometry.Ch3.Theory

open Geometry.Syntax
open Geometry.Ch2.Theory
open Geometry.Ch2.Defs

variable [FreeGeometry]
variable [IncidenceGeometry]


-- notation "line" A B => ∃! AB : Line A B
-- notation "→ₗ" A B => Line A B

-- p.108
public class BetweenGeometry extends IncidenceGeometry where
  -- p.108a "If A * B * C, then A,B,C are distinct points on the same line...
  (Between : Point -> Point -> Point -> Prop)
  (ba_1a_distinct_colinear :
    ∀ A B C : Point, Between A B C ->
      (A ≠ B ∧ B ≠ C ∧ A ≠ C) ∧
      (∃ L : Line, (A on L) ∧ (B on L) ∧ (C on L)) ∧
      Collinear A B C)
  -- p.108b ... and C * B * A."" Ed. Note, I separated these parts of the axiom to make rewriting
  -- a bit easier. The author even notes, "The second part (C * B * A) makes the obvious remark
  -- that 'betwen A and C' means the same as 'between C and A'" Making it a separate axiom means
  -- I won't have to dig it out of the pile of parts that is 1a.
  (ba_1b_between_comm :
    ∀ A B C : Point, Between A B C ↔ Between C B A)
  -- p.108 "Given any two distinct points B and D, there exist points A, C, and E lying on →ₗBD such that
  -- A * B * D, B * C * D, and B * D * E".
  --
  -- Ed. Here I introduce the line BD explicitly with it's incidence conditions
  -- then posit the proposed points with _their_ incidence conditions, and then
  -- finally state the between condition.
  --
  -- I called this 'density' because, used recursively, it posits something like
  -- the density of rationals -- for any two distinct points on a line, there is
  -- always a point between them.
  (ba_2_density :
    ∀ B D : Point, B ≠ D -> ∃ A C E : Point,
    ∃ BD : Line,
    ((A on BD) ∧ (B on BD) ∧ (C on BD) ∧ (D on BD) ∧ (E on BD)) ∧
    (Between A B D) ∧ (Between B C D) ∧ (Between B D E))
  -- p.108 "If A, B, and C are three distinct points lying on the same line,
  -- then one and only one of the points is between the other two."
  (ba_3_lines_arent_circles :
    ∀ A B C : Point, A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Collinear A B C ->
    let bABC := Between A B C; let bBAC := Between B A C; let bACB := Between A C B;
    (bABC ∧ ¬bBAC ∧ ¬bACB) ∨ (¬bABC ∧ ¬bBAC ∧ bACB) ∨ (¬bABC ∧ bBAC ∧ ¬bACB))

variable [G : BetweenGeometry]

nonrec def between (A B C : G.Point) := G.Between A B C

-- TODO: in a language this absolutely batshit flexible, there must be a way to introduce the
-- "A * B * C" so that I can use it in the definitions of the axioms and elsewhere. I don't know how to
-- do that just yet
/-
notation:20 "≬" => between
variable (A B C : FreeGeometry.Point)
#check between A B C
-/


end Geometry.Ch3.Theory
