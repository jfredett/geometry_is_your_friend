module

public import Geometry.Ch2.Theory

@[expose] public section

namespace Geometry.Ch2.Defs

open Geometry.Ch2.Theory

variable {G : FreeGeometry}

-- p. 20, "Two lines `l` and `m` are parallel if they do not intersect, i.e., if no point lies on both
-- of them. We denote this by `l ‖ m`"
-- p. 70, "Lines `l` and `m` are _parallel_ if they are distinct lines and no point is incident to both
-- of them."
@[expose] public def Parallel (L M : G.Line) : Prop := L ≠ M ->
  ∀ P : G.Point, ¬((P on L) ∧ (P on M))

-- NOTE: This is useful for the formalization, since the conjunction is convenient and a bit of a pain to unfold in situ
@[expose] public def NotParallel (L M : G.Line) : Prop :=
  L ≠ M ∧ ∃ P, ((P on L) ∧ (P on M))

@[simp]
public lemma ed_0_not_parallel_equiv (L M : G.Line) : ¬(Parallel L M) ↔ NotParallel L M := by
  unfold NotParallel
  unfold Parallel
  push_neg
  tauto

notation:20 L " ∥ " M => Parallel L M
notation:20 L " ∦ " M => NotParallel L M

-- TODO: A `simp` extension or something that just unfolds and pushnegs definitions, then I can probably
-- drop the `NotParallel` def.

end Geometry.Ch2.Defs
