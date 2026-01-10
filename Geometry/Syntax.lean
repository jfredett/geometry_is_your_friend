module

import Lean

/-
  =====================================================
  Textbook-style declarations with informal statements
  =====================================================
-/

/-- proposition ch.p "informal statement" name := proof -/
syntax "proposition" num "." num str term : command

/-- exercise ch.e "informal statement" name := proof -/
syntax "exercise" num "." num str term : command

/-
macro_rules
  | `(proposition $ch:num . $p:num $doc:str $val:term) =>
      `(
        namespace Geometry.Chapter.C$ch.Prop
        theorem P$p : _ := $val
        @[doc $doc]
        end Geometry.Chapter.C$ch.Prop
      )

macro_rules
  | `(exercise $ch:num . $e:num $doc:str $val:term) =>
      `(
        namespace Geometry.Chapter.C$ch.Ex
        theorem E$e : _ := $val
        @[doc $doc]
        end Geometry.Chapter.C$ch.Ex
      )
-/

/-
  ==========================
  refer (term macro)
  ==========================
-/

syntax "refer" " prop " num "." num : term
syntax "refer" " ex " num "." num : term

/-
macro_rules
  | `(refer prop $ch:num . $p:num) =>
      `(Geometry.Chapter.C$ch.Prop.P$p)

macro_rules
  | `(refer ex $ch:num . $e:num) =>
      `(Geometry.Chapter.C$ch.Ex.E$e)
-/

/-
  ==========================
  precisely! (tactic macro)
  ==========================
-/

syntax "precisely!" " prop " num "." num : tactic
syntax "precisely!" " ex " num "." num : tactic

macro_rules
  | `(tactic| precisely! prop $ch:num . $p:num) =>
      `(tactic| exact (refer prop $ch.$p))

macro_rules
  | `(tactic| precisely! ex $ch:num . $e:num) =>
      `(tactic| exact (refer ex $ch.$e))
