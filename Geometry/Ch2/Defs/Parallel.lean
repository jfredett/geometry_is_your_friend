module

public import Geometry.Ch2.Theory

open Geometry.Ch2.Theory

namespace Geometry.Ch2.Defs

-- p. 20, "Two lines `l` and `m` are parallel if they do not intersect, i.e., if no point lies on both
-- of them. We denote this by `l ‖ m`"
-- p. 70, "Lines `l` and `m` are _parallel_ if they are distinct lines and no point is incident to both
-- of them."
-- TODO: implement the notation
@[expose] public def Parallel {G : IncidenceGeometry} (L M : G.Line) : Prop := L ≠ M ->
  ∀ P : G.Point, ¬(G.Incident P L ∧ G.Incident P M)

-- NOTE: This is useful for the formalization, since the conjunction is convenient and a bit of a pain to unfold in situ
@[expose] public def NotParallel {G : IncidenceGeometry} (L M : G.Line) : Prop :=
  ¬(L ≠ M -> ∀ P : G.Point, ¬(G.Incident P L ∧ G.Incident P M))
--  ∃ P : G.Point, (G.Incident P L ∧ G.Incident P M)


public lemma ed_0_not_parallel_equiv {G : IncidenceGeometry} (L M : G.Line) : ¬(Parallel L M) ↔ NotParallel L M := by
  unfold Parallel
  unfold NotParallel
  tauto
