/-
Geometry/Construction/AtlasField.lean — `construction { … }` figure
field for atlas commentary blocks.

Wires the Construction DSL into atlas's `figure := by …` syntax as
sugar over `intermediate_representation`. The user writes

  figure := by
    construction {
      exists A B C : Point
      assert distinct A B C
      …
    }
    title "…"

and the macro rewrites the field to
`intermediate_representation (Geometry.Construction.DSL.construction { … })`,
which atlas handles via the `Renderable Construction String` instance.

The figure-field keyword and the term-level macro share the name
`construction`; they live in different syntax categories so there's no
conflict. Reads well in either reading: "this figure IS a
construction" or "this figure is built BY a construction".
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
