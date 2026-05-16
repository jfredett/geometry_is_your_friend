import Lean
import Geometry

/-- Filter out compiler-generated / parser-machinery declarations so the graph
    contains user-authored content. -/
def isUserDecl (n : Lean.Name) : Bool :=
  let s := n.toString
  -- Final dotted component, with French quote markers (`«` / `»`) stripped
  -- so the prefix check below sees the underlying name. Used to filter the
  -- auto-emitted `term*` / `tactic*` / `inst*` stubs from `syntax` /
  -- `notation` / `instance` declarations.
  let lastDotted := (s.splitOn ".").getLast? |>.getD s
  let lastComponent :=
    lastDotted.replace "«" "" |>.replace "»" ""
  let containsDenylist := [
    "_simp_", "._aux_", "«_aux_", "_auto_",
    ".match_", ".extract", "._eq_", ".eq_", "._uniq",
    "_flat_ctor", "_sparseCasesOn", "_unsafe_rec",
    ".quot", "_binder.quot"
  ]
  let endsWithDenylist := [
    ".inj", ".inj_iff", ".sizeOf_spec",
    ".rec", ".recOn", ".casesOn", ".brecOn",
    ".noConfusion", ".noConfusionType",
    ".proof_1", ".proof_2", ".proof_3",
    ".unexpander"
  ]
  let kindDenylist := [
    "ParserDescr", "TrailingParserDescr", "Parser", "Macro", "Unexpander"
  ]
  -- Last-component prefix denylist. Catches the names Lean auto-emits for
  -- `syntax "..." : tactic` (→ `tactic<kind>`), `notation` (→ `term<kind>`),
  -- and `instance` declarations (→ `inst<...>`).
  let lastStartsWithDenylist := [
    "term", "tactic", "instance", "inst"
  ]
  !containsDenylist.any (fun sub => s.contains sub) &&
  !endsWithDenylist.any (fun suffix => s.endsWith suffix) &&
  !kindDenylist.any (fun k => s.contains k) &&
  !lastStartsWithDenylist.any (fun pre => lastComponent.startsWith pre)

/-- Constants referenced in a decl's value (proof body for theorems, RHS for
    defs), filtered to project-local `Geometry.*` names. -/
def getProofDeps (info : Lean.ConstantInfo) : List String :=
  let expr := match info with
    | .thmInfo  t => some t.value
    | .defnInfo d => some d.value
    | _ => none
  match expr with
  | none => []
  | some e =>
    e.getUsedConstants.toList
      |>.map Lean.Name.toString
      |>.filter (·.startsWith "Geometry")

/-- Module path of the declaration, e.g. `Geometry.Ch3.Prop.P4`. -/
def declModule? (env : Lean.Environment) (name : Lean.Name) : Option String := do
  let idx ← env.getModuleIdxFor? name
  let modName := env.allImportedModuleNames[idx]?
  modName.map Lean.Name.toString

/-- Convert a module name `Geometry.Ch3.Prop.P4` to a path `Geometry/Ch3/Prop/P4.lean`. -/
def moduleToFile (m : String) : String :=
  m.replace "." "/" ++ ".lean"

/-- Transitive has-sorry detector. Walks the proof term collecting used
    constants, recursively visits each, and reports `true` if any visited
    expression directly references `sorryAx`. This is needed because Lean
    sometimes factors out sorry-bearing subterms into `_proof_N` auxiliaries,
    so a one-shot check on the outer value misses sorries that live in them. -/
partial def hasSorryTransitive
    (env : Lean.Environment) (visited : Std.HashSet Lean.Name) (name : Lean.Name)
    : Std.HashSet Lean.Name × Bool := Id.run do
  if visited.contains name then return (visited, false)
  let visited := visited.insert name
  match env.find? name with
  | none => return (visited, false)
  | some info =>
    let exprs : List Lean.Expr := match info with
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

/-- Wrapper: drop the visited-set, just return the boolean. -/
def hasSorry (env : Lean.Environment) (name : Lean.Name) : Bool :=
  (hasSorryTransitive env {} name).2

/-- Escape for JSON. -/
def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\"
    |>.replace "\"" "\\\""
    |>.replace "\n" "\\n"
    |>.replace "\r" "\\r"
    |>.replace "\t" "\\t"

open Lean Meta

/-- Build one JSON record (without braces) for a single declaration. Runs in
    `MetaM` so `ppExpr` and `isProp` are available. -/
def buildEntry (env : Environment) (name : Name) (info : ConstantInfo) :
    MetaM String := do
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
  let deps := getProofDeps info
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
    s!"\"name\":\"{name}\"",
    s!"\"kind\":\"{kind}\"",
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

/-- Discover every `Geometry/**/*.lean` file (relative to the project root)
    and convert each to its module name. Used to populate the import list so
    decls not transitively reached by `Geometry.lean` (in-progress work, etc.)
    still show up in the dump. -/
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

def main : IO Unit := do
  initSearchPath (← findSysroot)
  -- Import the umbrella plus every `Geometry/**/*.lean` we can find with a
  -- built `.olean`, so the dump includes work-in-progress files that aren't
  -- transitively reached from `Geometry.lean` yet but have nonetheless been
  -- compiled (e.g. via `lake build Geometry.Ch3.Prop.Pasch`).
  let discovered ← discoverGeometryModules "Geometry"
  let oleanRoot := ".lake/build/lib/lean"
  let buildable ← discovered.filterM fun n => do
    let p := s!"{oleanRoot}/{n.toString.replace "." "/"}.olean"
    return (← System.FilePath.pathExists p)
  let imports : Array Import :=
    (#[{ module := `Geometry }] : Array Import) ++
    buildable.map fun n => { module := n : Import }
  let env ← importModules imports {}

  let decls := env.constants.toList.filter fun (n, _) =>
    n.toString.startsWith "Geometry" && isUserDecl n

  -- Drive the per-decl entry construction inside MetaM via CoreM scaffolding.
  let coreCtx : Core.Context := { fileName := "<dumpdecls>", fileMap := default }
  let coreState : Core.State := { env := env }
  let metaAction : MetaM (Array String) := do
    let mut entries : Array String := #[]
    for (name, info) in decls do
      entries := entries.push (← buildEntry env name info)
    return entries
  let (entries, _) ← metaAction.run'.toIO coreCtx coreState

  let json := "[\n" ++ String.intercalate ",\n" entries.toList ++ "\n]"
  IO.FS.createDirAll "blueprint"
  IO.FS.writeFile "blueprint/decls.json" json
  IO.eprintln s!"Wrote {entries.size} declarations to blueprint/decls.json"
