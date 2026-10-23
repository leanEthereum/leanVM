import LeanVM.Guest.Data.Source
import LeanVM.Guest.Expand
import LeanVM.Guest.Interp
import LeanVM.Guest.Renumber

/-!
# `guest-core`: the guest's core IR as data

`lake exe guest-core` expands the guest's source (`Expand.expandProgram Data.guest`), renumbers
each function's values (`Fn.renumber`: value `n` is `V.n n = ⟨[], 0, n⟩`, written `.n n`) and writes the result to
`LeanVM/Guest/Data/Core*.lean`: function `j` of the compiler's order is `Data.core{j}`, its body
`core{j}.body`, and the definitions a long body is split into live in the namespace `core{j}`,
named by position: `c3` is chunk 3 of the body, `s40_a3` arm 3 of statement 40 (`_t`, `_e` the
branches of an `if`), `s40_a3_c0` a chunk of that arm. `lake exe guest-core --check` writes
nothing and fails when the files differ; `lake exe guest-core --values f` prints the expansion's
name of each value of the function `f`. Run it from `formal/lean_vm`.
-/

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

namespace GuestCore

/-- A definition is split once its text is longer than this. -/
def maxDef : Nat := 24000

/-- A statement's nested blocks get definitions of their own once longer than this together. -/
def maxNested : Nat := 6000

/-- A file is closed once longer than this. -/
def maxFile : Nat := 1500000

def dataDir : System.FilePath := "LeanVM/Guest/Data"

/-! ## Values -/

def pSeg : Seg → String
  | .s i => s!".s {i}"
  | .u j => s!".u {j}"
  | .t => ".t"
  | .e => ".e"
  | .a j => s!".a {j}"
  | .i f k => s!".i {f.quote} {k}"

/-- A value in a list. -/
def pItem (v : V) : String :=
  if v.path.isEmpty && v.tag == 0 then s!".n {v.idx}"
  else s!"⟨[{", ".intercalate (v.path.map pSeg)}], {v.tag}, {v.idx}⟩"

/-- A value as an argument. -/
def pV (v : V) : String :=
  if v.path.isEmpty && v.tag == 0 then s!"(.n {v.idx})" else pItem v

/-- Lean's list literal elaborates a list of 32 or more through `have`s: such a list is written
with `::`, its term then plain constructors. -/
def shortList : Nat := 32

def pList (items : List String) : String :=
  if items.length < shortList then s!"[{", ".intercalate items}]"
  else s!"({" :: ".intercalate items} :: [])"

def pVs (vs : List V) : String := pList (vs.map pItem)

def pStrs (ss : List String) : String := pList (ss.map String.quote)

def pE (x : E) : String :=
  let (c0, c1, c2) := limbsOf x
  s!"(word {c0} {c1} {c2})"

def pDest : Dest → String
  | .stack cs => s!"(.stack {pVs cs})"
  | .heap p off len => s!"(.heap {pV p} {off} {len})"

def pHint : Hint → String
  | .witness s d => s!"(.witness {s.quote} {pDest d})"
  | .bits v st n d => s!"(.bits {pV v} {st} {n} {pDest d})"
  | .bitsExp v n d => s!"(.bitsExp {pV v} {n} {pDest d})"
  | .limbs v d => s!"(.limbs {pV v} {pVs d})"
  | .log2Ceil b n fl dst => s!"(.log2Ceil {pDest b} {n} {fl} {pV dst})"
  | .inverse x d => s!"(.inverse {pV x} {pV d})"
  | .alloc d n => s!"(.alloc {pV d} {n})"
  | .allocDyn d s => s!"(.allocDyn {pV d} {pV s})"

def pAtom : Atom → String
  | .const d k => s!".const {pV d} {pE k}"
  | .add d a b => s!".add {pV d} {pV a} {pV b}"
  | .mul d a b => s!".mul {pV d} {pV a} {pV b}"
  | .copy d s => s!".copy {pV d} {pV s}"
  | .load d p off => s!".load {pV d} {pV p} {off}"
  | .assertEq a b => s!".assertEq {pV a} {pV b}"
  | .assertNe x inv p => s!".assertNe {pV x} {pV inv} {pV p}"
  | .rangeCheck x y t1 t2 k => s!".rangeCheck {pV x} {pV y} {pV t1} {pV t2} {pV k}"
  | .assertInK a b => s!".assertInK {pV a} {pV b}"
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
      ".blake2s " ++ " ".intercalate ([m0, m1, m2, m3, cv0, cv1, o0, o1, md].map pV)
  | .frameAddr p run => s!".frameAddr {pV p} {pVs run}"
  | .hint h => s!".hint {pHint h}"

/-! ## Blocks

A term is a list of lines. -/

abbrev Lines := List String

def len (ls : Lines) : Nat := ls.foldl (fun n l => n + l.length + 1) 0

def indent (ls : Lines) : Lines := ls.map ("  " ++ ·)

/-- `a b`, the first line of `b` after the last of `a`. -/
def hjoin (a b : Lines) : Lines :=
  match a.getLast?, b with
  | none, _ => b
  | _, [] => a
  | some l, b0 :: bs => a.dropLast ++ ((l ++ " " ++ b0) :: bs)

def suffix (ls : Lines) (s : String) : Lines :=
  match ls.getLast? with
  | none => [s]
  | some l => ls.dropLast ++ [l ++ s]

/-- A list, one item per line. -/
def listLit (items : List Lines) : Lines :=
  match items with
  | [] => ["[]"]
  | _ =>
      let n := items.length
      if n < shortList then
        let body := (items.zipIdx.map fun (it, k) => if k + 1 = n then it else suffix it ",").flatten
        "[" :: suffix (indent body) "]"
      else "(" :: indent ((items.map (suffix · " ::")).flatten ++ ["[])"])

/-- A definition in a function's namespace, and the definitions of the function it refers to. -/
structure Def where
  doc : String
  name : String
  ty : String
  term : Lines
  refs : List String := []

def Def.text (d : Def) : String :=
  let t := match d.term with
    | l :: ls => s!"noncomputable def {d.name} : {d.ty} := {l}" :: ls
    | [] => []
  s!"/-- {d.doc} -/\n" ++ "\n".intercalate t ++ "\n"

def Def.size (d : Def) : Nat := d.text.length

structure Ctx where
  fnName : String

abbrev M := ReaderT Ctx (StateM (Array Def))

def define (doc name : String) (term : Lines) : M Unit := do
  let fnName := (← read).fnName
  modify (·.push { doc := s!"`{fnName}`: {doc}.", name, ty := "List Core.Stmt", term })

/-- The definitions `m` emits, apart. -/
def captured {α : Type} (m : M α) : M (α × Array Def) := do
  let saved ← get
  set (#[] : Array Def)
  let r ← m
  let ds ← get
  set saved
  return (r, ds)

def child (n x : String) : String := if n.isEmpty then x else s!"{n}_{x}"

mutual
/-- The block named `n` (the body is `""`): its list literal, or the concatenation of its chunks
once too long. -/
partial def pBlock (n : String) (b : List Stmt) : M Lines := do
  let items ← b.zipIdx.mapM fun (s, i) => captured (pStmt n i s)
  if len (listLit (items.map (·.1))) ≤ maxDef then
    for (_, ds) in items do modify (· ++ ds)
    return listLit (items.map (·.1))
  let mut chunks : Array (Nat × Array (Lines × Array Def)) := #[]
  let mut cur : Array (Lines × Array Def) := #[]
  let mut size := 0
  let mut start := 0
  for (it, i) in items.zipIdx do
    if size + len it.1 > maxDef && !cur.isEmpty then
      chunks := chunks.push (start, cur)
      cur := #[]
      size := 0
      start := i
    cur := cur.push it
    size := size + len it.1
  chunks := chunks.push (start, cur)
  let mut names := #[]
  for ((st, c), k) in chunks.toList.zipIdx do
    for (_, ds) in c do modify (· ++ ds)
    let name := child n s!"c{k}"
    define s!"statements {st} to {st + c.size - 1} of {if n.isEmpty then "the body" else n}"
      name (listLit (c.toList.map (·.1)))
    names := names.push name
  return [" ++ ".intercalate names.toList]

/-- Nested blocks, defined apart when they are long together. -/
partial def pNested (bs : List (String × List Stmt)) : M (List Lines) := do
  let ts ← bs.mapM fun (m, b) => captured (pBlock m b)
  if (ts.map (len ·.1)).sum ≤ maxNested then
    for (_, ds) in ts do modify (· ++ ds)
    return ts.map (·.1)
  (bs.zip ts).mapM fun ((m, _), (t, ds)) => do
    modify (· ++ ds)
    define s!"block {m}" m t
    return [m]

/-- Statement `i` of the block `n`. -/
partial def pStmt (n : String) (i : Nat) : Stmt → M Lines
  | .atom a => return [s!".atom ({pAtom a})"]
  | .ite c z e => do
      let ts ← pNested [(child n s!"s{i}_t", z), (child n s!"s{i}_e", e)]
      return ts.foldl hjoin [s!".ite {pV c}"]
  | .match_ x arms => do
      let ts ← pNested (arms.zipIdx.map fun (a, k) => (child n s!"s{i}_a{k}", a))
      return hjoin [s!".match_ {pV x}"] (listLit ts)
  | .call f args rets => do
      return [s!".call {f.quote} {pVs args} {pVs rets}"]
  | .callIf c f args => do
      return [s!".callIf {pV c} {f.quote} {pVs args}"]
  | .dispatch x fs args rets => do
      return [s!".dispatch {pV x} {pStrs fs} {pVs args} {pVs rets}"]
  | .ret vs => return [s!".ret {pVs vs}"]
end

/-- The identifiers of a text. -/
def tokens (s : String) : List String :=
  let (acc, cur) := s.toList.foldl (fun (acc, cur) c =>
    if c.isAlphanum || c == '_' then (acc, cur.push c)
    else (if cur.isEmpty then acc else acc.push cur, "")) ((#[] : Array String), "")
  (if cur.isEmpty then acc else acc.push cur).toList

/-- A function: the definitions of its body (the body last), and its own definition, which
sits outside its namespace. -/
structure FnDefs where
  name : String
  body : List Def
  fn : String

/-- The definitions of `f`, renumbered, as function `j`. -/
def pFn (j : Nat) (f : Fn) : FnDefs :=
  let f := f.renumber
  let (body, defs) := ((pBlock "" f.body).run { fnName := f.name }).run #[]
  let defs := defs.push
    { doc := s!"`{f.name}`: the body.", name := "body", ty := "List Core.Stmt", term := body }
  let names : Std.HashSet String := defs.foldl (·.insert ·.name) {}
  let withRefs (d : Def) : Def :=
    { d with refs := ((tokens (String.join d.term)).filter fun t =>
        names.contains t && t != d.name).eraseDups }
  let fn := s!"/-- `{f.name}`. -/
noncomputable def core{j} : Core.Fn where
  name := {f.name.quote}
  params := {pVs f.params}
  body := core{j}.body
"
  { name := s!"core{j}", body := defs.toList.map withRefs, fn }

/-! ## Files -/

def header (mod what : String) : String :=
  s!"/-
  LeanVM.Guest.Data.{mod}

  Generated by `lake exe guest-core` (formal/lean_vm/cli/GuestCore.lean); do not edit.
  {what}
-/

module

"

def fileName (k : Nat) : String := if k < 10 then s!"Core0{k}" else s!"Core{k}"

/-- A file: the files it imports, and its parts, each a definition in a function's namespace
or (`""`) a function's own definition. -/
structure File where
  imports : List Nat := []
  parts : Array (String × String) := #[]
  size : Nat := 0
  deriving Inhabited

/-- Consecutive parts of one namespace, in one block. -/
def blocks (parts : List (String × String)) : List String :=
  let groups := parts.splitBy (·.1 == ·.1)
  groups.map fun g =>
    let ns := g.head!.1
    let body := "\n".intercalate (g.map (·.2))
    if ns.isEmpty then body else s!"namespace {ns}\n\n{body}\nend {ns}\n"

def File.text (k : Nat) (f : File) : String :=
  header (fileName k) "Core IR functions of the aggregation guest." ++
  "public import LeanVM.Guest.Renumber\n" ++
  String.join (f.imports.map fun i => s!"public import LeanVM.Guest.Data.{fileName i}\n") ++ "
namespace LeanVM.Guest.Data

open LeanVM.Guest

set_option maxRecDepth 20000
set_option linter.all false

@[expose] public section

" ++ "\n".intercalate (blocks f.parts.toList) ++ "
end
end LeanVM.Guest.Data
"

/-- A long function's definitions by level, a block coming after the blocks it refers to; a file
holds one level, so the files of a level import only the levels below. -/
def ordered (f : FnDefs) : List (List Def) := Id.run do
  let mut lvl : Std.HashMap String Nat := {}
  for d in f.body do
    lvl := lvl.insert d.name ((d.refs.filterMap fun r => (lvl.get? r).map (· + 1)).foldl max 0)
  let top := f.body.foldl (fun m d => max m (lvl.getD d.name 0)) 0
  return (List.range (top + 1)).map fun l => f.body.filter (lvl.getD ·.name 0 == l)

/-- Pack the functions into files in order, a file closed once longer than `maxFile`, a function
that fits kept in one file; a file imports those holding the definitions it refers to. -/
def pack (fns : List FnDefs) : Array File := Id.run do
  let mut files : Array File := #[{}]
  for f in fns do
    let whole := f.body.foldl (· + ·.size) 0 + f.fn.length
    let groups := if whole ≤ maxFile then [f.body] else ordered f
    if files.back!.size + whole > maxFile && files.back!.size > 0 then files := files.push {}
    let mut loc : Std.HashMap String Nat := {}
    for g in groups do
      if whole > maxFile && files.back!.size > 0 then files := files.push {}
      for d in g do
        if files.back!.size + d.size > maxFile && files.back!.size > 0 then files := files.push {}
        let i := files.size - 1
        let imps := (d.refs.filterMap loc.get?).filter (· != i)
        files := files.modify i fun fl => { fl with
          imports := fl.imports ++ (imps.filter (!fl.imports.contains ·)).eraseDups,
          parts := fl.parts.push (f.name, d.text), size := fl.size + d.size }
        loc := loc.insert d.name i
    let i := files.size - 1
    let imps := ((loc.get? "body").toList).filter (· != i)
    files := files.modify i fun fl => { fl with
      imports := fl.imports ++ (imps.filter (!fl.imports.contains ·)).eraseDups,
      parts := fl.parts.push ("", f.fn), size := fl.size + f.fn.length }
  return files.map fun fl => { fl with imports := fl.imports.mergeSort }

def indexFile (nFiles nFns : Nat) : String :=
  let imports := (List.range nFiles).map fun k => s!"public import LeanVM.Guest.Data.{fileName k}\n"
  let names := (List.range nFns).map fun j => s!"core{j}"
  let rows := (List.range ((nFns + 15) / 16)).map fun r =>
    "  " ++ " ".intercalate (((names.drop (16 * r)).take 16).map (· ++ " ::"))
  header "Core" "The core IR of the aggregation guest, `Expand.expandProgram Data.guest`." ++
  String.join imports ++ "
namespace LeanVM.Guest.Data

open LeanVM.Guest

set_option maxRecDepth 20000

@[expose] public section

/-- The core functions, in the compiler's order: `main` first. -/
noncomputable def coreFunctions : List Core.Fn :=
" ++ "\n".intercalate rows ++ " []

end
end LeanVM.Guest.Data
"

/-- The files, by name. -/
def files (P : Core.Program) : List (String × String) :=
  let fs := pack (P.zipIdx.map fun (f, j) => pFn j f)
  (fs.toList.zipIdx.map fun (f, k) => (fileName k, f.text k)) ++
    [("Core", indexFile fs.size P.length)]

/-- The generated files on disk. -/
def existing : IO (List String) := do
  let es ← dataDir.readDir
  return (es.toList.map (·.fileName)).filter fun n =>
    let cs := n.toList
    cs.take 4 == "Core".toList && cs.reverse.take 5 == ".lean".toList.reverse &&
      ((cs.drop 4).take (cs.length - 9)).all Char.isDigit

end GuestCore

open GuestCore in
def main (args : List String) : IO UInt32 := do
  let P ← match Expand.expandProgram Data.guest with
    | .ok P => pure P
    | .error e => do IO.eprintln s!"expansion failed: {e}"; return 1
  if let ["--values", name] := args then
    let some f := P.find? name | do IO.eprintln s!"no function {name}"; return 1
    for (v, n) in f.numbering.2.toList.zipIdx do
      IO.println s!"{n}: {Interp.showV v}"
    return 0
  let check := args == ["--check"]
  unless args.isEmpty || check do
    IO.eprintln "usage: guest-core [--check | --values FUNCTION]"
    return 2
  unless ← dataDir.isDir do
    IO.eprintln s!"{dataDir} not found: run from formal/lean_vm"
    return 2
  let fs := files P
  let names := fs.map fun (n, _) => n ++ ".lean"
  let stale := (← existing).filter (!names.contains ·)
  let mut bad := false
  for (n, text) in fs do
    let path := dataDir / (n ++ ".lean")
    if check then
      let old ← if ← path.pathExists then IO.FS.readFile path else pure ""
      if old != text then
        IO.eprintln s!"{path} is stale"
        bad := true
    else
      IO.FS.writeFile path text
  for n in stale do
    if check then
      IO.eprintln s!"{dataDir / n} is not generated"
      bad := true
    else
      IO.FS.removeFile (dataDir / n)
  if bad then
    IO.eprintln "regenerate with `lake exe guest-core`"
    return 1
  unless check do
    IO.println s!"{P.length} functions in {fs.length} files"
  return 0
