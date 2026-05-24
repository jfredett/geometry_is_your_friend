import Geometry.Tactics
import Geometry.Theory.Primitives
import Geometry.Theory.Constructors
import Geometry.Tactics.NormalizeEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

/-!
# `obvious` tactic — v2 (stage-based cascade)

Each *stage* has a `preamble` (run once) and a list of `closers` (tried
one-by-one on the post-preamble state). A stage closes the goal iff some
closer succeeds. If preamble fails (e.g. `simp_all made no progress`),
closers still run against the *original* state — more permissive than
v1's strict `simp_all ; tauto`, which now also closes goals where the
simp_all step was unnecessary.

The structure makes "try a different closer after the same preamble" the
default operation: `simp_all only [obvious]` now runs once per `obvious`
call regardless of whether `done` or `tauto` ultimately closes.

## Tracing

`set_option trace.obvious true`:
- Success: `closed by <stage> → <closer> (preamble Xms, closer Yms)`
- Failure: per-stage breakdown with preamble + each closer's elapsed ms.
-/

initialize Lean.registerTraceClass `obvious

namespace Geometry.Theory

attribute [obvious]
  -- set
  Set.mem_setOf_eq Set.mem_union Set.mem_inter_iff Set.mem_singleton_iff
  -- finset
  Finset.mem_insert Finset.mem_singleton Finset.mem_erase Finset.notMem_empty
  -- propositional
  ne_eq true_or or_true false_or or_false or_self
  true_and and_true false_and and_false and_self
  not_true_eq_false not_false_eq_true not_or not_and not_not

attribute [obvious]
  Set.subset_def
  Set.subset_inter_iff

/-! ## Cascade structure -/

open Lean Lean.Elab.Tactic in
/-- A single stage: shared `preamble` runs once, then each `closer` is
    tried in turn against the saved post-preamble state. -/
private structure ObviousStage where
  name : String
  preamble : TSyntax `tactic
  closers : Array (String × TSyntax `tactic)

open Lean Lean.Elab.Tactic in
/-- Run `tac` with explicit save/restore on failure. Returns `(succeeded?, ms)`.
    On failure the proof state is rolled back; on success state changes stand. -/
private def tryTimed (tac : TSyntax `tactic) : TacticM (Bool × Nat) := do
  let s ← saveState
  let startMs ← IO.monoMsNow
  let ok ← try evalTactic tac; pure true catch _ => s.restore; pure false
  let endMs ← IO.monoMsNow
  return (ok, endMs - startMs)

open Lean Lean.Elab.Tactic in
/-- The cascade stages, in priority order. Each stage represents a *class
    of intuition* — a kind of reasoning the author would take for granted.
    Long-term, stage selection will be driven by the theorem graph / goal
    shape; for now stages are tried in fixed order. -/
private def obviousStages : TacticM (Array ObviousStage) := do
  let simpAll ← `(tactic| simp_all (config := { maxSteps := 2000 }) only [obvious])
  let unfoldParallel ← `(tactic| simp only [obvious.parallel] at *)
  let memDef ← `(tactic|
    simp only [Segment.mem_def, Ray.mem_def, Extension.mem_def, LineThrough.mem_def])
  let memDefAt ← `(tactic|
    simp only [Segment.mem_def, Ray.mem_def, Extension.mem_def, LineThrough.mem_def] at *)
  let finsetExt ← `(tactic|
    (ext; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, ne_eq]))
  let doneT ← `(tactic| done)
  let assumptionT ← `(tactic| assumption)
  let decideT ← `(tactic| decide)
  let tautoT ← `(tactic| tauto)
  -- Cheap closers tried before tauto: done (simp_all already closed),
  -- assumption (hypothesis match), decide (decidable-instance reduction).
  -- Each is fast-to-fail when inapplicable, so paying them per-stage is cheap.
  let cheapThenTauto := #[
    ("done", doneT), ("assumption", assumptionT),
    ("decide", decideT), ("tauto", tautoT)
  ]
  return #[
    { name := "simp_all",
      preamble := simpAll,
      closers := cheapThenTauto },
    { name := "unfold Parallel",
      preamble := unfoldParallel,
      closers := cheapThenTauto },
    { name := "mem_def goal",
      preamble := memDef,
      closers := cheapThenTauto },
    { name := "mem_def at*",
      preamble := memDefAt,
      closers := cheapThenTauto },
    { name := "Finset ext",
      preamble := finsetExt,
      closers := cheapThenTauto }
  ]

open Lean Lean.Elab.Tactic in
elab "obvious" : tactic => do
  try evalTactic (← `(tactic| intros)) catch _ => pure ()
  try evalTactic (← `(tactic| normalize_eq)) catch _ => pure ()
  let stages ← obviousStages
  let original ← saveState
  let mut stageReports : Array (String × Bool × Nat × Array (String × Nat)) := #[]
  for stage in stages do
    original.restore
    let (preOk, preMs) ← tryTimed stage.preamble
    -- Strict: if preamble fails, skip closers. Matches v1 semantics where
    -- `simp_all only [obvious]; tauto` only runs tauto if simp_all
    -- succeeds. Permissive (run closers anyway) blew up tauto search on
    -- goals where simp_all was the gatekeeping cheap check.
    if !preOk then
      stageReports := stageReports.push (stage.name, false, preMs, #[])
      continue
    let postPreamble ← saveState
    let mut closerReports : Array (String × Nat) := #[]
    let mut closed := false
    for (cName, cTac) in stage.closers do
      postPreamble.restore
      let (ok, cMs) ← tryTimed cTac
      if ok then
        if ← isTracingEnabledFor `obvious then
          addTrace `obvious
            m!"closed by {stage.name} → {cName} (preamble {preMs}ms, closer {cMs}ms)"
        closed := true
        break
      closerReports := closerReports.push (cName, cMs)
    if closed then return
    stageReports := stageReports.push (stage.name, true, preMs, closerReports)
  original.restore
  if ← isTracingEnabledFor `obvious then
    let rows := stageReports.toList.map fun (n, ok, preMs, closers) =>
      let preTag := if ok then m!"preamble {preMs}ms" else m!"preamble FAILED {preMs}ms"
      let cRows := closers.toList.map (fun (cn, cms) => m!"\n      {cn}: {cms}ms")
      m!"  {n}: {preTag}{MessageData.joinSep cRows m!""}"
    addTrace `obvious
      m!"all alternatives failed:\n{MessageData.joinSep rows m!"\n"}"
  throwError "obvious: no alternative closed the goal"

/-- Term-position form: `(obvious : T)` desugars to `(by obvious : T)`. -/
macro "obvious" : term => `(by obvious)

/-! ## Examples -/

section Examples
example (A B : Point) : A on segment A B := by obvious
example (A B : Point) : B on segment A B := by obvious
example (A B : Point) : A on segment A B := obvious
end Examples

end Geometry.Theory
