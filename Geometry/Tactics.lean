import Aesop
import Mathlib.Logic.ExistsUnique

import Mathlib.Tactic.Basic
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Use
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.Contrapose

import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.List.Basic

/-- Simp set for `obvious` — see `Geometry/Theory/Axioms.lean` for the
    macro that uses it. Tag chapter-by-chapter as you encounter
    canonical normalizations that Greenberg treats as background.

    Lean requires `register_simp_attr` and `attribute [obvious]` to
    live in *separate* files, hence the registration lives here while
    the actual tagging happens in `Axioms.lean` and downstream.

    The attribute name `obvious` deliberately shadows nothing: tactics
    and attributes live in disjoint namespaces, so `@[obvious]` on a
    decl and `obvious` in tactic mode coexist without ambiguity. -/
register_simp_attr obvious

/-- Stage-specific simp set used by `obvious`'s `unfold Parallel` stage.
    Tag with `@[obvious.parallel]` any reducible def whose unfolding is
    safe-but-expensive (so we don't want it in the main `obvious` set).
    The macro-hygiene escape hatch — `simp only [obvious.parallel]` in
    the cascade resolves the set name without needing to escape the
    underlying constant identifiers.

    Sibling stage-sets follow the `obvious.<class>` convention
    (`obvious.betweenness`, `obvious.incidence`, etc.) as they're added. -/
register_simp_attr obvious.parallel

