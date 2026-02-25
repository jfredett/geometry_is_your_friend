import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

namespace Set

open Set

/-- If S is disjoint from T and V, then S ∪ T ⊆ S ∪ V implies T ⊆ V -/
lemma subtract_disjoint_union_subset : ∀ S T V : Set α, S ∪ T ⊆ S ∪ V ∧ S ∩ T = ∅ ∧ S ∩ V = ∅ -> T ⊆ V := by
  intro S T V ⟨SuTsubSuV, SintTempty, SintVempty⟩ e eInT
  have eInSuT : e ∈ S ∪ T := (mem_union e S T).mpr (Or.inr eInT)
  have eInSuV : e ∈ S ∪ V := (mem_union e S V).mpr (SuTsubSuV eInSuT)
  rcases eInSuV with eInS | eInV
  · exact absurd ⟨eInS, eInT⟩ (Set.eq_empty_iff_forall_notMem.mp SintTempty e)
  · exact eInV

/-- If S is disjoint from T and V, then S ∪ T = S ∪ V implies T = V (TODO: may be iff) -/
lemma subtract_disjoint_union : ∀ S T V : Set α,  S ∪ T = S ∪ V ∧ S ∩ T = ∅ ∧ S ∩ V = ∅ -> T = V := by
  intro S T V ⟨SuTeqSuV, SintTempty, SintVempty⟩
  -- This is a cool technique, similar to the 'by symmetry' or 'up to variable naming'.
  suffices h : ∀ A B : Set α, S ∪ A ⊆ S ∪ B ∧ S ∩ A = ∅ ∧ S ∩ B = ∅ → A ⊆ B by
    exact Subset.antisymm 
      (h T V ⟨(Eq.subset SuTeqSuV), SintTempty, SintVempty⟩)
      (h V T ⟨(Eq.subset SuTeqSuV.symm), SintVempty, SintTempty⟩)
  exact subtract_disjoint_union_subset S

end Set
