import Geometry.Tactics
import Geometry.Theory

namespace Geometry.Ch2.Prop

open Geometry.Theory

-- pp. 71: If `l` and `m` are distinct lines that are not parallel, then `l` and
-- `m` have a unique point in common
@[simp] theorem P1 (L M : Line) :
  L ≠ M → (L ∦ M) → ∃! P : Point,
     (P on L) ∧ (P on M)
:= by
    intro hDistinctLines
    unfold Parallel; push_neg
    rintro ⟨_, ⟨P, hPonLM⟩⟩
    refine ⟨P, ?cEx, ?cUniq⟩
    -- existence
    exact hPonLM
    -- uniqueness
    intro Q
    by_contra! ⟨hQonLM, hNeg⟩
    -- idea, PQ = L, PQ = M, but L != M
    obtain ⟨PQ, _, hPQUniq⟩ := I1 P Q hNeg.symm
    have hLisPQ := hPQUniq L ⟨hPonLM.left, hQonLM.left⟩
    have hMisPQ := hPQUniq M ⟨hPonLM.right, hQonLM.right⟩
    have hLeqM : (L = M) := by
        rw [hMisPQ, hLisPQ]
    contradiction

end Geometry.Ch2.Prop
