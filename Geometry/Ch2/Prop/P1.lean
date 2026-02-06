import Geometry.Tactics
import Geometry.Theory

namespace Geometry.Ch2.Prop

open Geometry.Theory

-- pp. 71: If `l` and `m` are distinct lines that are not parallel, then `l` and
-- `m` have a unique point in common
@[simp] theorem P1.direct (L M : Line) :
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

-- A corrolary of the main theorem that is more useful since it uses the syntax directly.
@[simp] theorem P1 (LneM : L ≠ M) (LnoparM : L ∦ M) : ∃! X : Point, L intersects M at X := by
    obtain ⟨P, ⟨PonL, PonM⟩, Puniq⟩ := P1.direct L M LneM LnoparM
    unfold Intersects
    use P
    simp_all only [ne_eq, not_false_eq_true, nonempty_prop, forall_const, not_and, not_forall,
      not_not, and_imp]
    by_cases suppose: ∃ C : Point, C ∈ L ∩ M ∧ C ≠ P
    obtain ⟨C, ConLintM, CneP⟩ := suppose
    have ConL : C on L := by simp_all only [exists_prop, Set.mem_inter_iff]
    have ConM : C on M := by simp_all only [exists_prop, Set.mem_inter_iff]
    specialize Puniq C ConL ConM; contradiction
    push_neg at suppose
    simp_all only [exists_prop, Set.mem_inter_iff, and_self, implies_true, and_imp]
    obtain ⟨w, h⟩ := LnoparM
    obtain ⟨left, right⟩ := h
    sorry
/-
    simp_all only [Set.mem_inter_iff, Set.mem_singleton_iff]
    apply Iff.intro
    · intro a
      simp_all only
    · intro a
      subst a
      simp_all only [and_self]
-/

end Geometry.Ch2.Prop
