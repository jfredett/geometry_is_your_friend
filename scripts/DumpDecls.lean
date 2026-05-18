import Lean
import Geometry
import Atlas

/-! Dump every atlas-tagged declaration to `blueprint/decls.json`.

    Filter scope = atlas tagging. A declaration only appears in the
    output if it carries an `@[atlas …]` attribute (i.e. was introduced
    via the `atlas <kind> …` command in `Atlas.lean`). Untagged
    declarations — Mathlib helpers, structural projections like
    `Collinear.on_line`, compiler-emitted `match_*` / `proof_*` /
    `rec` / `casesOn` stubs — are ignored entirely. This replaces the
    earlier heuristic denylist with a single explicit signal.

    Edge scope = atlas tagging. For each atlas-tagged decl we walk its
    proof/def body, collect referenced constants, and keep only the
    ones that are themselves atlas-tagged. Concretely this means a
    `ref lemma 1.0.31` (which elaborates to the title-named constant
    `Geometry.…«Pointed intersection is symmetric …»`) shows up as a
    dependency edge, while a reference to `Eq.symm` or `tauto` does
    not. -/

namespace DumpDecls

open Lean Meta

/-- Module path of the declaration, e.g. `Geometry.Ch3.Prop.P4`. -/
def declModule? (env : Environment) (name : Name) : Option String := do
  let idx ← env.getModuleIdxFor? name
  let modName := env.allImportedModuleNames[idx]?
  modName.map Name.toString

/-- Convert a module name `Geometry.Ch3.Prop.P4` to a path `Geometry/Ch3/Prop/P4.lean`. -/
def moduleToFile (m : String) : String :=
  m.replace "." "/" ++ ".lean"

/-- Transitive `sorry` detector. Lean factors sorry-bearing subterms into
    `_proof_N` auxiliaries, so a one-shot check on the outer value
    misses sorries that live inside them. -/
partial def hasSorryTransitive
    (env : Environment) (visited : Std.HashSet Name) (name : Name)
    : Std.HashSet Name × Bool := Id.run do
  if visited.contains name then return (visited, false)
  let visited := visited.insert name
  match env.find? name with
  | none => return (visited, false)
  | some info =>
    let exprs : List Expr := match info with
      | .thmInfo  t => [t.value, t.type]
      | .defnInfo d => [d.value, d.type]
      | _ => [info.type]
    let mut visited := visited
    for e in exprs do
      if e.find? (·.isConstOf ``sorryAx) |>.isSome then
        return (visited, true)
      for n in e.getUsedConstants do
        let (v', found) := hasSorryTransitive env visited n
        visited := v'
        if found then return (visited, true)
    return (visited, false)

def hasSorry (env : Environment) (name : Name) : Bool :=
  (hasSorryTransitive env {} name).2

/-- Constants referenced in a decl's body, filtered to only those that
    are themselves atlas-tagged. The atlas tag is the membership signal
    for the graph — non-atlas refs (Mathlib lemmas, projections,
    structural lemmas like `Collinear.on_line`) are dropped on purpose. -/
def atlasDeps (atlasNames : NameSet) (info : ConstantInfo) : List String :=
  let expr := match info with
    | .thmInfo  t => some t.value
    | .defnInfo d => some d.value
    | _ => none
  match expr with
  | none => []
  | some e =>
    e.getUsedConstants.toList
      |>.filter atlasNames.contains
      |>.map Name.toString

/-- Escape for JSON. -/
def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\"
    |>.replace "\"" "\\\""
    |>.replace "\n" "\\n"
    |>.replace "\r" "\\r"
    |>.replace "\t" "\\t"

/-- Build one JSON record for an atlas-tagged declaration. -/
def buildEntry (env : Environment) (atlasNames : NameSet)
    (name : Name) (info : ConstantInfo) (atlasEntry : Atlas.AtlasEntry) :
    MetaM String := do
  -- Lean's intrinsic decl kind (axiom/def/theorem/opaque). Kept as
  -- `kind` for schema compat with `scripts/schema.cypher` and
  -- `scripts/ingest.py`; the atlas kind is a separate `atlas_kind`
  -- field below.
  let kind := match info with
    | .axiomInfo  _ => "axiom"
    | .defnInfo   _ => "def"
    | .thmInfo    _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | _             => "other"
  let docstring ← findDocString? env name
  let doc := jsonEscape (docstring.getD "")
  let typeRaw := jsonEscape (toString info.type)
  let typePp ← try (·.pretty) <$> ppExpr info.type catch _ => pure (toString info.type)
  let typePpStr := jsonEscape typePp
  let deps := atlasDeps atlasNames info
  let depsJson := "[" ++
    (deps.map (fun d => "\"" ++ d ++ "\"") |> String.intercalate ",") ++ "]"
  let ns := jsonEscape name.getPrefix.toString
  let modOpt := declModule? env name
  let modStr := jsonEscape (modOpt.getD "")
  let fileStr := jsonEscape (modOpt.map moduleToFile |>.getD "")
  let range ← findDeclarationRanges? name
  let (lineStart, lineEnd) :=
    match range with
    | some r => (toString r.range.pos.line, toString r.range.endPos.line)
    | none => ("null", "null")
  let sorryFlag := if hasSorry env name then "true" else "false"
  let isProp ← try isProp info.type catch _ => pure false
  let propFlag := if isProp then "true" else "false"
  let nc := if Lean.isNoncomputable env name then "true" else "false"
  let fields : Array String := #[
    s!"\"name\":\"{jsonEscape name.toString}\"",
    s!"\"kind\":\"{kind}\"",
    s!"\"atlas_kind\":\"{jsonEscape atlasEntry.kind}\"",
    s!"\"atlas_number\":\"{jsonEscape atlasEntry.number}\"",
    s!"\"atlas_title\":\"{jsonEscape atlasEntry.title}\"",
    s!"\"namespace\":\"{ns}\"",
    s!"\"module\":\"{modStr}\"",
    s!"\"file\":\"{fileStr}\"",
    s!"\"line_start\":{lineStart}",
    s!"\"line_end\":{lineEnd}",
    s!"\"doc\":\"{doc}\"",
    s!"\"type\":\"{typeRaw}\"",
    s!"\"type_pp\":\"{typePpStr}\"",
    s!"\"has_sorry\":{sorryFlag}",
    s!"\"is_proposition\":{propFlag}",
    s!"\"is_noncomputable\":{nc}",
    s!"\"deps\":{depsJson}"
  ]
  return "{" ++ String.intercalate "," fields.toList ++ "}"

/-- Every `Geometry/**/*.lean` we can find with a built `.olean`. Used
    to import work-in-progress files that aren't transitively reached
    from `Geometry.lean` yet but have nonetheless been compiled. -/
partial def discoverGeometryModules (root : String) : IO (Array Name) := do
  let mut out : Array Name := #[]
  let entries ← System.FilePath.readDir root
  for entry in entries do
    let path := entry.path
    if (← path.isDir) then
      out := out ++ (← discoverGeometryModules path.toString)
    else if path.extension == some "lean" then
      let rel := path.toString
      let cleaned := if rel.startsWith "./" then rel.drop 2 else rel
      let withoutExt := if cleaned.endsWith ".lean" then cleaned.dropRight 5 else cleaned
      let dotted := withoutExt.replace "/" "."
      out := out.push dotted.toName
  return out

end DumpDecls

open Lean Meta DumpDecls

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let discovered ← discoverGeometryModules "Geometry"
  let oleanRoot := ".lake/build/lib/lean"
  let buildable ← discovered.filterM fun n => do
    let p := s!"{oleanRoot}/{n.toString.replace "." "/"}.olean"
    return (← System.FilePath.pathExists p)
  let imports : Array Import :=
    (#[{ module := `Geometry }] : Array Import) ++
    buildable.map fun n => { module := n : Import }
  let env ← importModules imports {}

  -- Merge the current and imported atlas state into a single
  -- `NameMap AtlasEntry`. (`addImportedFn` is unreliable across module
  -- boundaries, hence the manual `getModuleEntries` walk in
  -- `Atlas.atlasStateFromImports`.)
  let importedSt := Atlas.atlasStateFromImports env
  let liveSt     := Atlas.atlasExt.getState env
  let byName : NameMap Atlas.AtlasEntry :=
    importedSt.byName.foldl (init := liveSt.byName) fun acc n e =>
      match acc.find? n with
      | some _ => acc
      | none   => acc.insert n e

  let atlasNames : NameSet :=
    byName.foldl (init := {}) fun acc n _ => acc.insert n

  -- One entry per atlas-tagged decl, in stable name order.
  let entriesIn : Array (Name × Atlas.AtlasEntry) :=
    byName.toArray.qsort (fun (a, _) (b, _) => a.toString < b.toString)

  let coreCtx : Core.Context := { fileName := "<dumpdecls>", fileMap := default }
  let coreState : Core.State := { env := env }
  let metaAction : MetaM (Array String) := do
    let mut entries : Array String := #[]
    for (name, atlasEntry) in entriesIn do
      match env.find? name with
      | none => continue   -- atlas tag references a name that no longer resolves
      | some info =>
        entries := entries.push (← buildEntry env atlasNames name info atlasEntry)
    return entries
  let (entries, _) ← metaAction.run'.toIO coreCtx coreState

  let json := "[\n" ++ String.intercalate ",\n" entries.toList ++ "\n]"
  IO.FS.createDirAll "blueprint"
  IO.FS.writeFile "blueprint/decls.json" json
  IO.eprintln s!"Wrote {entries.size} atlas-tagged declarations to blueprint/decls.json"
