
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Tactics

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1
import Geometry.Ch3.Prop.B4iii
import Geometry.Theory.Ch1
import Geometry.Theory.Ch2
import Geometry.Theory.Betweenness.Ch2

namespace Geometry.Ch3.Ex

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex

/-- (b) Prove that A,B,C, and D are collinear -/
theorem Ex1.b : A - B - C ∧ A - C - D -> (Collinear A B C) ∧ (Collinear B C D) := by
  intro ⟨ABC, ACD⟩
  have colABC := Betweenness.abc_imp_collinear ABC
  have AonAD : A on line A D := Line.line_has_definition_points.left
  have BonAD : B on line A D := by unfold LineThrough; simp only [mem_setOf_eq] ; tauto
  have ConAD : C on line A D := by unfold LineThrough; simp only [mem_setOf_eq] ; tauto
  tauto
  
/-- p146. Given A-B-C and A-C-D:
  (a) Prove that A,B,C, and D are four distinct points (the proof requires and axiom)

Ed. it's easier to prove this if we have the second part first.
-/
theorem Ex1.a : A - B - C ∧ A - C - D -> distinct A B C D := by
  intro ⟨ABC, ACD⟩
  have colBCD : Collinear B C D := (Ex1.b ⟨ABC, ACD⟩).right
  have ⟨AneB, BneC, AneC⟩ := Betweenness.abc_imp_distinct ABC
  have ⟨_, CneD, AneD⟩ := Betweenness.abc_imp_distinct ACD
  simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self, and_true]
  by_cases suppose : B = D
  · rw [<- suppose] at ACD; exfalso; exact Betweenness.absurdity_abc_acb ⟨ABC, ACD⟩
  · tauto
  
/-- (c) Prove the corrolary to B4
Ed. Note that (c) is covered by the B4iii lemma in it's own file. -/
alias Ex1.c := B4iii

end Geometry.Ch3.Ex
