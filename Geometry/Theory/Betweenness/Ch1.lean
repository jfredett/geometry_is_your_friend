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
  intro ⟨ABC, BAC⟩
  obtain ⟨⟨AneB, BneC, AneC⟩, ⟨⟨L, AonL, BonL, ConL⟩, ABCCol⟩⟩ := B1a ABC
  obtain ⟨⟨BneA, AneC, BneC⟩, ⟨⟨M, BonM, AonM, ConM⟩, BACCol⟩⟩ := B1a BAC
  rcases B3 A B C ⟨AneB, BneC, AneC, ABCCol⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  contradiction; contradiction; contradiction

/-- With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another -/
lemma absurdity_abc_acb : A - B - C ∧ A - C - B -> False := by
  intro ⟨ABC, ACB⟩
  obtain ⟨⟨AneB, BneC, AneC⟩, ⟨⟨L, AonL, BonL, ConL⟩, ABCCol⟩⟩ := B1a ABC
  obtain ⟨⟨AneC, CneB, AneB⟩, ⟨⟨M, AonM, ConM, BonM⟩, ACBCol⟩⟩ := B1a ACB
  rcases B3 A B C ⟨AneB, BneC, AneC, ABCCol⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  contradiction; contradiction; contradiction

/-- With respect to a pair of fixed points, another point is either 'to the left' or 'to the right' of the pair -/
lemma absurdity_abc_cab : A - B - C ∧ C - A - B -> False := by
  intro ⟨ABC, CAB⟩
  obtain ⟨⟨AneB, BneC, AneC⟩, ⟨⟨L, AonL, BonL, ConL⟩, ABCCol⟩⟩ := B1a ABC
  obtain ⟨⟨CneA, CneB, BneC⟩, ⟨⟨M, ConM, AonM, BonM⟩, CABCol⟩⟩ := B1a CAB
  rcases B3 A B C ⟨AneB, BneC.symm, AneC, ABCCol⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  rw [B1b] at nBAC; contradiction; contradiction; contradiction

/-- betweeness implies distinctness -/
lemma abc_imp_distinct.anec : A - B - C -> A ≠ C := by
  intro ABC
  have ⟨⟨_, _, AneC⟩, _⟩ := (B1a ABC)
  exact AneC


end Betweenness

end Geometry.Theory
