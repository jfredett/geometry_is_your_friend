import Figures
import Figures.SVG
import Geometry.Construction.DSL
import Geometry.Construction.Syntax
import Geometry.Construction.Lowering

namespace Geometry.Construction.Examples

open Figures
open Geometry.Construction.DSL
open Geometry.Construction.Lowering

def twoPointsLine : Construction := construction {
  exists P Q : Point
  assert distinct P Q
  construct lPQ := line_through P Q
}

def twoPointsLineScene : Scene Pos2 := lower twoPointsLine

-- DSL print (audit checkpoint #1: does this match the theorem?).
#eval IO.println (printConstruction twoPointsLine)

-- Lowered scene → SVG (audit checkpoint #2: does the rendering match the DSL?).
#eval IO.println (Renderable.render (out := String) twoPointsLineScene)

end Geometry.Construction.Examples
