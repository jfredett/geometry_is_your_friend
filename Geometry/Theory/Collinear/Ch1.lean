
/- Lemmas relating to collinearity requiring only the content of Ch1 -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Tactics
import Geometry.Theory.Axioms

-- There is no overlap here, so it's fine to import
import Geometry.Theory.Point.Ch1

namespace Geometry.Theory

open Set
open Geometry.Theory

namespace Collinear

/-- Collinearity commutes -/
lemma commutes.left : (Collinear A B C) ↔ (Collinear B A C) := by
  unfold Collinear;
  constructor
  · intro hL
    have ⟨L, hInc, hUniq⟩ := hL
    use L
    tauto
  · intro hL
    have ⟨L, hInc, hUniq⟩ := hL
    use L
    tauto

/- Collinearity commutes -/
lemma commutes.right : (Collinear A B C) ↔ (Collinear A C B) := by tauto

/- Collinearity commutes -/
lemma commutes.outer : (Collinear A B C) ↔ (Collinear C B A) := by tauto

/-- A point is collinear with itself -/
lemma any_point_is_self_collinear : Collinear A A A := by tauto

/-- There is a line between any two points, so by definition any two points are collinear -/
lemma any_two_points_are_collinear_ABA : A ≠ B -> Collinear A B A := by
  intro AneB
  have ⟨L, hIncidence, hUniq⟩ := I1 A B AneB
  simp only at hIncidence
  use L;
  simp_all only [ne_eq, and_imp, and_self]

/-- There is a line between any two points, so by definition any two points are collinear -/
lemma any_two_points_are_collinear_ABB : A ≠ B -> Collinear A B B := by
  intro AneB
  have ⟨L, hIncidence, hUniq⟩ := I1 A B AneB
  simp at hIncidence
  use L;
  simp_all only [ne_eq, and_imp, and_self]

/-- There is a line between any two points, so by definition any two points are collinear -/
lemma any_two_points_are_collinear_AAB : A ≠ B -> Collinear A A B := by
  intro AneB
  have ⟨L, hIncidence, hUniq⟩ := I1 A B AneB
  simp at hIncidence
  use L;
  simp_all only [ne_eq, and_imp, and_self]

end Collinear

end Geometry.Theory
