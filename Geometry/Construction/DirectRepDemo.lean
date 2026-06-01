/-
Geometry/Construction/DirectRepDemo.lean — End-to-end smoke test of
the `figure := by direct_rep <term>` field added to atlas.

Imports `Geometry.Construction.Pasch` (the hand-encoded Pasch IR),
declares a stub atlas theorem to serve as the figure's host, and
attaches the Pasch construction's `.toSvg` output to that theorem via
the new `direct_rep` field. Exercises:

  giyf IR  →  giyf .toSvg  →  atlas direct_rep field  →
  atlas SvgParser.parse  →  atlas Figure widget

Lake-build green here means the cross-repo wiring works. Once we have
the actual DSL → IR parser, this file's role is just regression
coverage for the bypass / debug path.
-/

import Atlas
import Geometry.Construction.Pasch

open Atlas
open Geometry.Construction.Examples

atlas commentary := by
  via theorem 999.0
  name "direct_rep smoke test"
  preface "Smoke test for `figure := by direct_rep <IR>` — hands the
hand-encoded Pasch `Construction` to atlas's `direct_rep` field, which
internally renders to SVG and attaches via the figure widget.
Geometric placement is intentionally wrong (pure-naive layout); the
point is to prove the pipeline."

  figure := by
    direct_rep pasch
    title "Pasch (direct_rep)"
    index 1
    caption "Pure-naive layout via direct_rep. Geometric placement is wrong (X isn't on AB, L doesn't pass through X) — constraint-aware layout is a follow-up. Renders correctly via libresvg now that SVG output is duplicate-attribute-free."

/-- Stub theorem to host the commentary above. Tactic-mode proof (not
just `:= trivial`) so atlas's `with_atlas_panels` wrapper fires and the
figure appears in the InfoView on the proof side too. -/
atlas theorem 999.0 "direct_rep smoke test placeholder"
  : True := by trivial
