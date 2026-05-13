import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Tactics

namespace Geometry.Theory

open Set
open Geometry.Theory

namespace Betweenness

/-- With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another -/
lemma absurdity_abc_bac : A - B - C ∧ B - A - C -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC⟩ := B1a ABC
  rcases B3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  repeat contradiction

/-- With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another -/
lemma absurdity_abc_acb : A - B - C ∧ A - C - B -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC⟩ := B1a ABC
  rcases B3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  repeat contradiction

/-- With respect to a pair of fixed points, another point is either 'to the left' or 'to the right' of the pair -/
lemma absurdity_abc_cab : A - B - C ∧ C - A - B -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC⟩ := B1a ABC
  rcases B3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  rw [B1b] at nBAC;
  repeat contradiction

-- TODO: use the `distinct` condition here
/-- betweeness implies distinctness -/
lemma abc_imp_distinct : A - B - C -> distinct A B C := by
  intro ABC
  have ⟨h,  _⟩ := (B1a ABC)
  exact h

/-- betweeness implies collinearity -/
lemma abc_imp_collinear : A - B - C -> collinear A B C := by 
  intro ABC
  exact (B1a ABC).right
  
end Betweenness

end Geometry.Theory
