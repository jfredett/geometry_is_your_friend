module

public import Geometry.Tactics
public import Geometry.Ch2.Theory
public import Geometry.Ch2.Defs

@[expose] public section

namespace Geometry.Ch2.Prop

open Geometry.Ch2.Theory
open Geometry.Ch2.Defs

variable (G : IncidenceGeometry)


-- pp. 71: If `l` and `m` are distinct lines that are not parallel, then `l` and
-- `m` have a unique point in common
theorem P1 (L M : G.Line) :
  L ≠ M → NotParallel L M → ∃! P : G.Point,
     G.Incident P L ∧ G.Incident P M
:= by
    intro hDistinctLines
    unfold NotParallel
    rintro ⟨_, ⟨P, hPonLM⟩⟩
    refine ⟨P, ?cEx, ?cUniq⟩
    -- existence
    exact hPonLM
    -- uniqueness
    intro Q
    by_contra! ⟨hQonLM, hNeg⟩
    -- idea, PQ = L, PQ = M, but L != M
    obtain ⟨PQ, _, hPQUniq⟩ := G.ia_1_unique_line P Q hNeg.symm
    have hLisPQ := hPQUniq L ⟨hPonLM.left, hQonLM.left⟩
    have hMisPQ := hPQUniq M ⟨hPonLM.right, hQonLM.right⟩
    have hLeqM : (L = M) := by
        rw [hMisPQ, hLisPQ]
    contradiction

end Geometry.Ch2.Prop
