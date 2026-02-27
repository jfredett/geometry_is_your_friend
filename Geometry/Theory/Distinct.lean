/- Lemmas relating to the `distinct` condition -/

import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

namespace Geometry.Theory.Distinct

open Set

-- Custom syntax category for the distinct binder
declare_syntax_cat distinct_binder
syntax ident+ " : " term : distinct_binder

syntax "distinct " ident+ : term
macro_rules
  | `(distinct $[$xs]*) => do
    `(List.Pairwise (· ≠ ·) [$[$xs],*])

open Lean Elab Tactic Meta in
elab "distinguish" h:ident x:ident y:ident : tactic => do
  evalTactic (← `(tactic| (
    have : $x:ident ≠ $y:ident := by
      simp only [List.pairwise_cons, List.mem_cons] at $h:ident
      -- FIXME: I don't love the simp_all here, it's better than a bare simp_all but
      -- I feel like there is a way to more systematically prove this
      simp_all only [
        ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_false_eq_true, implies_true, not_true_eq_false, and_self, forall_eq_or_imp, 
        forall_eq, IsEmpty.forall_iff, List.Pairwise.nil, and_true
      ]
    try assumption
  )))

-- TODO: Make the `h` optional by searching the proofstate
-- TODO: Maybe make the X and Y optional as well

-- gut check
example (A B C D : Point) (h : distinct A B C D) : A ≠ B ∧ B ≠ C ∧ A ≠ D := by
  have AneB := by distinguish h A B
  constructor
  · exact AneB
  constructor
  · distinguish h B C
  · distinguish h A D

end Geometry.Theory.Distinct
