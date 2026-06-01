/-
Geometry/Construction/Lowering.lean — Construction → Scene Pos2.

First-cut lowering. Handles the patterns we need for "two points
determine a line" and the immediate next examples; the heavy
constraint-solving (positions discovered to satisfy quantitative
relations like `between A X B`) is stubbed and will land as a separate
pass when an example forces it.

Strategy:
- `exists … : Point` → allocate a position from a deterministic
  layout pool. Lines / circles / segments declared via `exists` get
  no position; they're expected to come in through `construct`.
- `construct name := expr` → dispatch on the expression head. Known
  shape constructors (`line_through`, `segment`, `circle`) emit the
  corresponding `Shape Pos2` referencing previously-allocated
  positions. Unknown constructors are recorded as Scene constraints
  (so they survive the lowering as metadata even when we can't
  realize them visually).
- `assert claim desc` → recorded verbatim into `Scene.constraints`.
  Asserts that constrain positions (e.g. `between`) currently shape
  no positions — solver land.

Labels for each named Point are emitted automatically. Names not
introduced via `exists Point` get no auto-label; if you want a label
for a constructed object you can add it explicitly later (e.g. via
an annotation pass).
-/

import Figures
import Figures.SVG
import Geometry.Construction.DSL

namespace Geometry.Construction.Lowering

open Figures
open Geometry.Construction.DSL


/-! ## Layout pool

Deterministic position allocation for free `exists Point` declarations.
A cycle through the canvas at radius ~150 from center; good enough to
give visually-distinguishable initial placements for up to ~8 points
without overlap. Solver pass would adjust these to satisfy asserts. -/

private def defaultLayout (i : Nat) : Pos2 :=
  let cx : Float := 240
  let cy : Float := 240
  let r  : Float := 150
  let θ  : Float := 2 * 3.14159265358979 * i.toFloat / 6
  (cx + r * θ.cos, cy - r * θ.sin)


/-! ## State

A small append-only state threaded through the statement walk. Maps
each declared name to its assigned `Pos2` (for points) plus an emitted
shape (for constructed objects). The sort tag lets us auto-label
points without needing to inspect the source statement later. -/

private structure Bindings where
  positions   : List (Name × Pos2)    := []
  sorts       : List (Name × Name)    := []
  shapes      : Array (Shape Pos2)    := #[]
  annotations : Array Annotation      := #[]
  constraints : Array Constraint      := #[]
  pointCount  : Nat                   := 0


/-! ## Statement dispatch -/

private def lookupArg (b : Bindings) : ConstraintExpr → Option Pos2
  | .name n => (b.positions.find? (fun p => p.1 == n)).map (·.2)
  | _       => none

private def addShape (b : Bindings) (s : Shape Pos2) : Bindings :=
  { b with shapes := b.shapes.push s }

private def addAnnotation (b : Bindings) (a : Annotation) : Bindings :=
  { b with annotations := b.annotations.push a }

private def addConstraint (b : Bindings) (c : Constraint) : Bindings :=
  { b with constraints := b.constraints.push c }

/-- Try to realize a `construct name := expr` as a shape. Returns the
updated bindings on success; on unknown expression heads (or missing
referenced positions) falls back to recording the construct as a
constraint so nothing is silently dropped. -/
private def applyConstruct (b : Bindings) (name : Name) : ConstraintExpr → Bindings
  | .app "line_through" [a, b'] =>
    match lookupArg b a, lookupArg b b' with
    | some pa, some pb => addShape b (.line name pa pb)
    | _, _ => addConstraint b ⟨.app "line_through" [a, b'], s!"construct {name} (unresolved)"⟩
  | .app "segment" [a, b'] =>
    match lookupArg b a, lookupArg b b' with
    | some pa, some pb => addShape b (.segment name pa pb)
    | _, _ => addConstraint b ⟨.app "segment" [a, b'], s!"construct {name} (unresolved)"⟩
  | .app "circle" [c, .num r] =>
    match lookupArg b c with
    | some pc => addShape b (.circle name pc r)
    | none    => addConstraint b ⟨.app "circle" [c, .num r], s!"construct {name} (unresolved)"⟩
  | other =>
    addConstraint b ⟨other, s!"construct {name} (unknown shape)"⟩

private def applyStmt (b : Bindings) : Stmt → Bindings
  | .«exists» names sort =>
    names.foldl (init := b) fun acc n =>
      match sort with
      | "Point" =>
        let pos := defaultLayout acc.pointCount
        let acc := { acc with
          positions := (n, pos) :: acc.positions
          sorts := (n, sort) :: acc.sorts
          pointCount := acc.pointCount + 1
        }
        let acc := addShape acc (.point n pos)
        addAnnotation acc (.label n n)
      | _ =>
        { acc with sorts := (n, sort) :: acc.sorts }
  | .construct name expr =>
    applyConstruct b name expr
  | .assert claim desc =>
    addConstraint b ⟨claim, desc⟩


/-! ## Top-level lowering -/

/-- Lower a `Construction` to a 2D scene. Positions for free points
come from `defaultLayout`; asserts are passed through to
`Scene.constraints` for backends (and the future solver) to consume. -/
def lower (c : Construction) : Scene Pos2 :=
  let b := c.stmts.foldl applyStmt {}
  {
    shapes      := b.shapes
    annotations := b.annotations
    constraints := b.constraints
  }


end Geometry.Construction.Lowering


namespace Geometry.Construction

open Figures
open Geometry.Construction.DSL
open Geometry.Construction.Lowering

/-- DSL → SVG via the lowering pass. Lets atlas's `direct_rep` accept
a `Construction` literal directly (instance lookup picks this up by
type), without callers needing to invoke `lower` themselves. -/
instance : Renderable Construction String where
  render c := Renderable.render (lower c)

end Geometry.Construction
