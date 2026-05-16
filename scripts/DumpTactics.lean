/-
Dump per-decl tactic occurrences as JSON.

STATUS: stub. Emits an empty `blueprint/tactics.json` so the ingest pipeline
keeps working; the real InfoTree walk is deferred.

TODO: walk `Lean.Elab.Frontend.processCommands` output and collect
`TacticInfo` nodes per top-level decl. The mechanics (InfoTree API,
`enableInitializersExecution` unsafe ripple, command-state plumbing) shifted
across recent Lean versions and the prior attempt hit several friction
points. Easier path is to either: (a) use `subverso-extract-mod`'s JSON
output and post-process the highlighted-token info to extract `(decl,
tactic, line)` triples; or (b) re-attempt a direct frontend walk once
this codebase is on a stable Lean toolchain.

Until then the `Tactic` / `USED_TACTIC` tables in Kuzu will be empty, and
the `tactic_hotspots.cypher` query returns no rows.
-/

import Lean

def main : IO Unit := do
  IO.FS.createDirAll "blueprint"
  IO.FS.writeFile "blueprint/tactics.json" "[]\n"
  IO.eprintln "Wrote 0 decl×tactic-set records to blueprint/tactics.json (stub; see TODO in scripts/DumpTactics.lean)"
