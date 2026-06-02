/-
Geometry/Construction/AtlasField.lean — `construction { … }` figure
field for atlas commentary blocks.

Sugar over `intermediate_representation (Geometry.Construction.DSL.construction { … })`.
Atlas's `elabFigureFields` evaluates the term, then pushes the IR
Expr keyed by the commentary's target (kind, num) into
`Atlas.baseIRExprExt` — so the progressive figure widget can read it
back keyed by target instead of via fragile mutable state.
-/

import Atlas
import Geometry.Construction.Syntax
import Geometry.Construction.Lowering

open Lean Atlas

syntax (name := afConstruction)
  "construction" "{" constructionStmt* "}" : atlasFigureField

macro_rules
  | `(atlasFigureField| construction { $stmts:constructionStmt* }) =>
    `(atlasFigureField|
       intermediate_representation (construction { $stmts:constructionStmt* }))
