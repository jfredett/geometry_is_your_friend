import Atlas
import Geometry.Construction.Pasch

open Atlas
open Geometry.Construction.Examples

atlas commentary := by
  via theorem 999.0
  name "direct_rep smoke test"
  preface "Smoke test for `figure := by direct_rep <Scene>` — hands the
hand-coordinated Pasch `Scene` to atlas's `direct_rep` field, which
dispatches polymorphically via `Figures.Renderable α String` to find
the SVG backend instance and produce the figure's SVG body."

  figure := by
    direct_rep pasch
    title "Pasch (direct_rep)"
    index 1
    caption "Hand-coordinated Scene. X lies on segment AB, L passes through X — positions chosen by us, since the geometric DSL that would compute these from declarative constraints isn't built yet."

atlas theorem 999.0 "direct_rep smoke test placeholder"
  : True := by trivial
