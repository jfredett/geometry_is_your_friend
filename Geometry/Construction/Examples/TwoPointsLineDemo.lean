import Atlas
import Geometry.Construction.Examples.TwoPointsLine

open Atlas
open Geometry.Construction.Examples

atlas commentary := by
  via theorem 999.1
  name "DSL direct_rep smoke test"
  preface "Smoke test for `figure := by direct_rep <Construction>`. The
`Construction` AST is lowered to `Scene Pos2` by the `Renderable
Construction String` instance, which then dispatches to the SVG
backend. End-to-end: DSL → IR → SVG → widget."

  figure := by
    direct_rep twoPointsLine
    title "Two points determine a line (DSL)"
    index 1
    caption "Construction DSL → lowering → Scene → SVG. Positions of P and Q come from the lowering's layout pool; the line is constructed through them."

atlas theorem 999.1 "DSL direct_rep smoke test placeholder"
  : True := by trivial
