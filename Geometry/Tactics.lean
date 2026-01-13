module

public import Aesop
public import Mathlib.Logic.ExistsUnique

public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.ByCases
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Use
public import Mathlib.Tactic.WLOG
public import Mathlib.Tactic.Contrapose


syntax (name := unfoldDefs) "unfold_defs" (ppSpace ident)* : tactic

macro_rules
  | `(tactic| unfold_defs $ids*) =>
    `(tactic| repeat (unfold $ids*))
