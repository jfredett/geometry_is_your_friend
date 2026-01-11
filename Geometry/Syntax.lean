module

import Lean
import MathLib.Data.List.Basic

open Lean

@[expose] public section

-- TODO: some kind of shorthand for all the relevant properties of a line between two points

namespace Geometry.Syntax

def distinct {α : Type*} (l : List α) : Prop :=
  ∀ (x y : α), x ∈ l → y ∈ l → x ≠ y

/-- proposition ch.p statement := proof -/
syntax (name := propositionDecl)
  "proposition" num "." num term ":=" term : command
/-- exercise ch.e name := proof -/
syntax (name := exerciseDecl)
  "exercise" num "." num term ":=" term : command

syntax (name := corrolaryDecl)
  "corollary" num "." num "." num term ":=" term : command

syntax (name := lemmaDecl)
  "lemma" num "." num "." num term ":=" term : command

-- FIXME: Should probably parse directly, also this screws up the implicit def,
-- I think probably it's `terms : command`, as in, multiple terms, then the
-- command?
-- FIXME: Technically lemma is already taken, but this should parse it correctly anyway
-- TODO: I dropped the 'informal statement as part of the proposition command itself', leaving
-- the documentation as just a normal doc comment; I don't know that I care enough to implement
-- it for real.
macro_rules
  | `(proposition $chapter . $prop $stmt := $proof) =>
      let rawStr := s!"Geometry.Ch{chapter}.Prop.P{prop}"
      let name := Lean.mkIdent rawStr.toName
      `(theorem $name : $stmt := $proof)
  | `(exercise $chapter . $ex $stmt := $proof) =>
      let rawStr := s!"Geometry.Ch{chapter}.Prop.Ex{ex}"
      let name := Lean.mkIdent rawStr.toName
      `(theorem $name : $stmt := $proof)
  | `(corollary $chapter . $prop . $co $stmt := $proof) =>
      let rawStr := s!"Geometry.Ch{chapter}.Prop.P{prop}.C{co}"
      let name := Lean.mkIdent rawStr.toName
      `(theorem $name : $stmt := $proof)
  | `(lemma $chapter . $prop . $lem $stmt := $proof) =>
      let rawStr := s!"Geometry.Ch{chapter}.Prop.P{prop}.L{lem}"
      let name := Lean.mkIdent rawStr.toName
      `(theorem $name : $stmt := $proof)



/-
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

end Geometry.Syntax
