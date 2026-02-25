/-- Lemmas relating to the `distinct` condition -/
import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.List.Basic

namespace Geometry.Theory.Distinct

open Set

-- Helper to check if an identifier is accessible
-- FIXME: doesn't really do what I want, which is to hide all the generated conditions that have daggers or underscores.
open Lean in
def isAccessible (id : TSyntax `ident) : Bool :=
  let name := id.getId.toString
  !name.startsWith "_" && !name.contains "✝"

-- Custom syntax category for the distinct binder
declare_syntax_cat distinct_binder
syntax ident+ " : " term : distinct_binder


-- TODO: Maybe replace this with a non-recursive version that just generates `≠` conditions.
syntax "distinct " ident+ : term
macro_rules
  | `(distinct $[$xs]*) => do
    let accessible := (xs.toList.filter isAccessible).toArray
    `(List.Pairwise (· ≠ ·) [$[$accessible],*])


-- TODO: Some sort of thing for concluding A_i ≠ A_j for i ≠ j in a distinct block

-- TODO: There should be some way to take a `distinct` object and two putative elements of that object and
-- conclude the ≠ condition, ideally something like `distinct.conclude hDist A B -> A ≠ B` -- this might just be
-- a function I need to write? Not sure how to do this, below is a broken attempt
-- def conclude {α : Type} (distinct : List.Pairwise (fun x1 x2 ↦ x1 ≠ x2) α) : ∀ A B : α, A ∈ distinct -> B ∈ distinct -> A ≠ B := by sorry

end Geometry.Theory.Distinct
