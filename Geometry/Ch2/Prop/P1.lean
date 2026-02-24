import Geometry.Tactics
import Geometry.Theory

namespace Geometry.Ch2.Prop

open Set
open Geometry.Theory

/-- pp. 71: If `l` and `m` are distinct lines that are not parallel, then `l` and
 `m` have a unique point in common -/
@[simp] theorem P1.direct {L M : Line} :
  L ≠ M → (L ∦ M) → ∃! P : Point,
     (P on L) ∧ (P on M)
:= by
    intro hDistinctLines
    unfold Parallel; push_neg
    intro hypP; specialize hypP hDistinctLines
    obtain ⟨P, hPonLM⟩ := hypP
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

/-- A corrolary of the main theorem that is more useful since it uses the syntax directly. -/
@[simp] theorem P1 (LneM : L ≠ M) (LnoparM : L ∦ M) : ∃! X : Point, L intersects M at X := by
    obtain ⟨P, ⟨PonL, PonM⟩, Puniq⟩ := P1.direct LneM LnoparM
    use P
    simp only
    constructor
    · unfold Intersects
      apply Subset.antisymm
      · intro Q QinInt
        have ⟨QonL, QonM⟩ := QinInt
        specialize Puniq Q ⟨QonL, QonM⟩
        rw [Puniq]
        tauto
      · intro Q QinSingle
        have QeqP : Q = P := by tauto
        rw [QeqP]
        tauto
    · intro Q LintMatQ
      unfold Intersects at LintMatQ
      specialize Puniq Q
      have QinLintM : Q ∈ L ∩ M := by rw [LintMatQ]; tauto
      tauto

end Geometry.Ch2.Prop
