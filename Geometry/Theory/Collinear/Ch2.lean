
/- Lemmas relating to collinearity requiring only the content of Ch1 -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Line.Ch2

import Geometry.Tactics
import Geometry.Ch2.Prop

namespace Geometry.Theory

open Set
open Geometry.Theory
open Geometry.Ch2.Prop

namespace Collinear


/-- If for A B C X points, if are A C X is collinear, and  A X B are collinear, then A C B is collinear -/
lemma inclusion : distinct A B C D -> Collinear A B C ∧ Collinear A C D -> Collinear A B D := by
  unfold Collinear
  intro distinctABCD ⟨colABC, colACD⟩
  -- FIXME: Given the above `Distinct.conclude` or whatever I come up with, refactor this.
  have AneC : A ≠ C := by
    simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
      and_true] at distinctABCD
    tauto
  obtain ⟨L, AonL, BonL, ConL⟩ := colABC
  obtain ⟨M, AonM, ConM, DonM⟩ := colACD
  have LeqM : L = M := Line.equiv AneC ⟨AonL, AonM, ConL, ConM⟩
  use L
  rw [<- LeqM] at DonM
  tauto

end Collinear

end Geometry.Theory
