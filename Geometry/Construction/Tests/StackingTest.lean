/-
Geometry/Construction/Tests/StackingTest.lean — artificial test for the
progressive figure widget.

Theorem `stacking_test` has two nested rcases (outer A/B, inner
left/right) and an `auxillary { … }` at each branch entry. Cursor
should reveal seven distinct figures as it walks the proof:

  base                — segment AB
  base + A            — adds point C and segment AC
  base + A + left     — adds segment BC
  base + A + right    — adds ray AB
  base + B            — adds point D and segment BD
  base + B + left     — adds ray AD
  base + B + right    — adds ray BA

Auxillaries in the A subtree must NOT leak into the B subtree (and
vice versa); each inner-branch aux must NOT leak into its sibling.
-/

import Geometry.Construction.DSL
import Geometry.Construction.Syntax
import Geometry.Construction.Lowering
import Geometry.Construction.AtlasField
import Geometry.Construction.AtlasTactic
import Geometry.Construction.ProgressiveFigure
import Atlas

open Atlas

atlas commentary := by
  via theorem 99.0
  name "Progressive-figure stacking test"
  preface "Two-layer rcases with an auxillary at each branch entry. Cursor through the proof to see the figure progressively stack and unstack."

  figure := by
    construction {
      exists A B : Point
      construct segAB := segment A B
    }
    title "Stacking test base"
    index 1
    caption "Base figure — segment AB, no auxillaries."

atlas theorem 99.0 "stacking-test placeholder"
  : ∀ (_h1 : True ∨ True) (_h2 : True ∨ True), True := by
  -- EXPECT: base — segment AB only.
  intro h1 h2
  -- EXPECT: base — segment AB only.
  rcases h1 with _hA | _hB
  · auxillary {
      exists C : Point
      construct segAC := segment A C
    }
    -- EXPECT: base + A — adds point C and segment AC.
    rcases h2 with _hL | _hR
    · auxillary {
        construct segBC := segment B C
      }
      -- EXPECT: base + A + left — adds segment BC. Must NOT show ray AB.
      trivial
    · auxillary {
        construct rayAB := ray A B
      }
      -- EXPECT: base + A + right — adds ray AB. Must NOT show segment BC.
      trivial
  · auxillary {
      exists D : Point
      construct segBD := segment B D
    }
    -- EXPECT: base + B — adds point D and segment BD. Must NOT show C/AC/etc.
    rcases h2 with _hL | _hR
    · auxillary {
        construct rayAD := ray A D
      }
      -- EXPECT: base + B + left — adds ray AD. Must NOT show ray BA.
      trivial
    · auxillary {
        construct rayBA := ray B A
      }
      -- EXPECT: base + B + right — adds ray BA. Must NOT show ray AD.
      trivial
