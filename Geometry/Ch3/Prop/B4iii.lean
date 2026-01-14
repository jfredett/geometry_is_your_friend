
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Tactics

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1

namespace Geometry.Ch3.Prop

-- open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop.P1

-- p111

/- The only point between A and itself is A. -/
@[simp] lemma B4iii.L0 (A P : Point) : A - P - A -> P = A := by
  intro hAPA
  have ⟨hDistinct, _⟩ := B1a hAPA
  tauto

/- a line doesn't care about the order of the points it guards -/
@[simp] lemma B4iii.L1.guards (L : Line) (A B : Point) :
  (L guards A and B) -> (L guards B and A) := by
    intro LguardsAB
    unfold SameSide at *; rw [<- L2] ; tauto

/- a line doesn't care about the order of the points it splits -/
@[simp] lemma B4iii.L1.splits (L : Line) (A B : Point) :
  (L splits A and B) -> (L splits B and A) := by
    intro LsplitsAB
    unfold SameSide at *; rw [<- L2] ; tauto

/-
"Corollary. (iii) If A and B are on opposite sides of L and if B and C are on the
same side of L, then A and C are on opposite sides of L"

Ed. This gets shown here since it's a corollary and I need a lemma from the
previous proposition

-/
@[simp] theorem B4iii (A B C : Point) (L : Line) :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L splits A and B) ∧ (L guards B and C) -> (L splits A and C) := by
  intro ⟨AoffL, BoffL, CoffL⟩ ⟨LsplitsAB, LguardsBC⟩
  by_contra! LguardsAC
  have h := B4i ⟨AoffL, CoffL, BoffL⟩ ⟨LguardsAC, B4iii.L1.guards L B C LguardsBC⟩
  contradiction

/-

As is often the case, the above theorem once looked like a 5 page epic, but was
rapidly reduced when I found the correct way to think about it.

When I was a kid, I was homeschooled, and I was frustrated by that because I never
had much chance to make what I usually thought of as 'academic friends.' The sort of
people who were interested in the same kinds of weird niche things I was -- linguistics,
mathematics, philosophy, art, music.

My Dad liked those things too, well, he preferred programming to pure math, and religion
subsumed and subsumes his philosphy, art, and music; but he was close enough. Trouble was
he wasn't around much, so -- being a bright homeschooled kid with nothing better to do, I
hatched a little plan.

-/
end Geometry.Ch3.Prop
