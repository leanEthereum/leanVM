import LeanVM.Guest.Data.Source
import LeanVM.Guest.Expand
import LeanVM.Guest.Interp
import LeanVM.Guest.Renumber
import LeanVM.Guest.PackHash

/-!
# `guest-core`: the guest's core IR as data

`lake exe guest-core` expands the guest's source (`Expand.expandProgram Data.guest`), renumbers
each function's values (`Fn.renumber`: value `n` is `V.n n = ⟨[], 0, n⟩`, written `.n n`) and writes
each function, keyed by its stable name (below), as `Fn.<key>.core`, its body `Fn.<key>.core.body`;
the definitions a long body is split into live in the namespace `Fn.<key>.core`, named by position:
`c3` is chunk 3 of the body, `s40_a3` arm 3 of statement 40 (`_t`, `_e` the branches of an `if`),
`s40_a3_c0` a chunk of that arm. The functions sit in packs (`packCount`): function `key` in
`LeanVM/Guest/Pack/P{packOf packCount key}/Core.lean`, or, when long, in its own
`LeanVM/Guest/Pack/<key>/Core.lean`, continued in `Core1.lean`, `Core2.lean`, … beside it. The glue
`LeanVM/Guest/Data/Core.lean` lists the functions in the compiler's order (`coreFunctions`) and
keeps `Data.core{j}` and `Data.core{j}.body` as abbreviations of function `j`. `lake exe guest-core --check` writes
nothing and fails when the files differ; `lake exe guest-core --values f` prints the expansion's
name of each value of the function `f`, and `--show f` the function, renumbered. Run it from `lean_vm`.
-/

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

namespace GuestCore

/-- A definition is split once its text is longer than this. -/
def maxDef : Nat := 24000

/-- A statement's nested blocks get definitions of their own once longer than this together. -/
def maxNested : Nat := 6000

/-- A file is closed once longer than this. -/
def maxFile : Nat := 750000

def dataDir : System.FilePath := "LeanVM/Guest/Data"

def fnDir : System.FilePath := "LeanVM/Guest/Fn"

def packDir : System.FilePath := "LeanVM/Guest/Pack"

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
  let (c0, c1) := limbsOf x
  s!"(word {c0} {c1})"

def pDest : Dest → String
  | .stack cs => s!"(.stack {pVs cs})"
  | .heap p off len => s!"(.heap {pV p} {off} {len})"

def pHint : Hint → String
  | .witness s d => s!"(.witness {s.quote} {pDest d})"
  | .bits v st n d => s!"(.bits {pV v} {st} {n} {pDest d})"
  | .bitsExp v n d => s!"(.bitsExp {pV v} {n} {pDest d})"
  | .digitsExp v nb nd db st sc d =>
      let psc := match sc with
        | some c => s!"(some {pV c})"
        | none => "none"
      s!"(.digitsExp {pV v} {nb} {nd} {db} {st} {psc} {pDest d})"
  | .windowsExp v st w n d => s!"(.windowsExp {pV v} {st} {w} {n} {pDest d})"
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
  | .keccak ins outs inOdd outOdd => s!".keccak {pVs ins} {pVs outs} {inOdd} {outOdd}"
  | .frameAddr p run => s!".frameAddr {pV p} {pVs run}"
  | .hint h => s!".hint {pHint h}"
  | .touch t p => s!".touch {pV t} {pV p}"

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
  /-- The function's stable name, for the documentation. -/
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

/-- The definitions of `f`, renumbered, of stable name `key`. -/
def pFn (key : String) (f : Fn) : FnDefs :=
  let f := f.renumber
  let (body, defs) := ((pBlock "" f.body).run { fnName := key }).run #[]
  let defs := defs.push
    { doc := s!"`{key}`: the body.", name := "body", ty := "List Core.Stmt", term := body }
  let names : Std.HashSet String := defs.foldl (·.insert ·.name) {}
  let withRefs (d : Def) : Def :=
    { d with refs := ((tokens (String.join d.term)).filter fun t =>
        names.contains t && t != d.name).eraseDups }
  let fn := s!"/-- `{key}`. -/
noncomputable def core : Core.Fn where
  name := {f.name.quote}
  params := {pVs f.params}
  body := core.body
"
  { name := "core", body := defs.toList.map withRefs, fn }

/-! ## Files -/

def header (mod what : String) : String :=
  s!"/-
  LeanVM.Guest.{mod}

  Generated by `lake exe guest-core` (lean_vm/cli/GuestCore.lean); do not edit.
  {what}
-/

module

"

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

/-- The module of a function's file `i` of `n`: the last, holding the function, `Core`, the
others `Core{i + 1}`. -/
def fnFileName (n i : Nat) : String := if i + 1 = n then "Core" else s!"Core{i + 1}"

/-- File `i` of the `n` files of the function of stable name `key`. -/
def File.text (key : String) (n i : Nat) (f : File) : String :=
  header s!"Pack.{key}.{fnFileName n i}" s!"The core IR of `{key}`." ++
  "public import LeanVM.Guest.Renumber\n" ++
  String.join (f.imports.map fun k => s!"public import LeanVM.Guest.Pack.{key}.{fnFileName n k}\n") ++ s!"
namespace LeanVM.Guest.Fn.«{key}»

open LeanVM.Guest

set_option maxRecDepth 20000
set_option linter.all false

@[expose] public section

" ++ "\n".intercalate (blocks f.parts.toList) ++ s!"
end
end LeanVM.Guest.Fn.«{key}»
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
that fits kept in one file; a file imports those holding the definitions it refers to. The
functions after one split over files start a file of their own, which so imports none of them. -/
def pack (fns : List FnDefs) : Array File := Id.run do
  let mut files : Array File := #[{}]
  let mut split := false
  for f in fns do
    let whole := f.body.foldl (· + ·.size) 0 + f.fn.length
    let groups := if whole ≤ maxFile then [f.body] else ordered f
    if (split || files.back!.size + whole > maxFile) && files.back!.size > 0 then
      files := files.push {}
    split := whole > maxFile
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

/-- The glue: every function's module, the functions in the compiler's order, and function `j` as
`Data.core{j}`, its body `Data.core{j}.body`. -/
def indexFile (keys : List String) (mods : List String) : String :=
  let imports := mods.map fun m => s!"public import LeanVM.Guest.{m}\n"
  let refs := keys.map fun k => s!"Fn.«{k}».core"
  let rows := (List.range ((keys.length + 7) / 8)).map fun r =>
    "  " ++ " ".intercalate (((refs.drop (8 * r)).take 8).map (· ++ " ::"))
  let compat := keys.zipIdx.map fun (k, j) =>
    s!"noncomputable abbrev core{j} : Core.Fn := Fn.«{k}».core\n" ++
    s!"noncomputable abbrev core{j}.body : List Core.Stmt := Fn.«{k}».core.body\n"
  header "Data.Core" "The core IR of the aggregation guest, `Expand.expandProgram Data.guest`." ++
  String.join imports ++ "
namespace LeanVM.Guest.Data

open LeanVM.Guest

set_option maxRecDepth 20000
set_option linter.all false

@[expose] public section

/-- The core functions, in the compiler's order: `main` first. -/
noncomputable def coreFunctions : List Core.Fn :=
" ++ "\n".intercalate rows ++ " []

/-! Function `j` by its index, for the modules that name it so. -/

" ++ String.join compat ++ "
end
end LeanVM.Guest.Data
"

/-! ## Stable names

A proof names a core function by its name, not by its index, which an added function shifts; a
loop helper (`__loop{n}`, numbered over the whole program by the compiler) by its caller and its
place among the caller's loops: `{caller}_loop{k}`, the `k`-th loop the caller's body names. -/

/-- The functions a block names, in order. -/
partial def callees : List Stmt → List String
  | [] => []
  | s :: ss =>
    let here := match s with
      | .call f _ _ => [f]
      | .callIf _ f _ => [f]
      | .dispatch _ fs _ _ => fs
      | .ite _ z e => callees z ++ callees e
      | .match_ _ arms => arms.flatMap callees
      | .atom _ | .ret _ => []
    here ++ callees ss

def isLoop (name : String) : Bool := name.startsWith "__loop"

/-- Each function's stable name: its own, a loop's from its first caller (`{caller}_loop{k}`). -/
partial def stableNames (P : Core.Program) : Array String := Id.run do
  let names := P.toArray.map (·.name)
  -- a loop's first caller other than itself, and its place among that caller's loops
  let mut parent : Std.HashMap String (Nat × Nat) := {}
  for (f, j) in P.zipIdx do
    let loops := ((callees f.body).filter fun g => isLoop g && g != f.name).eraseDups
    for (g, k) in loops.zipIdx do
      if !parent.contains g then parent := parent.insert g (j, k)
  let rec go (fuel j : Nat) : String :=
    match fuel, parent.get? (names.getD j "") with
    | fuel + 1, some (p, k) => if isLoop (names.getD j "") then s!"{go fuel p}_loop{k}" else names.getD j ""
    | _, _ => names.getD j ""
  return (List.range names.size).toArray.map (go names.size)

def namesFile (P : Core.Program) : String :=
  let st := stableNames P
  let rows (f : String → Nat → String) : String :=
    String.join ((P.zipIdx.map fun (_, j) => f (st.getD j "") j))
  header "Data.Names" "The core functions by their stable names." ++ "public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Data.NameStrings

/-!
# The core functions by stable name

`F.«s»` is the core function of stable name `s` and `I.«s»` its index in `coreProgram`
(`NameStrings`: `N.«s»` its name): a function's own name, a loop helper's `{caller}_loop{k}` (the
`k`-th loop its first caller names). Proofs name functions so, through `fn% s`, `idx% s` and
`name% s` (`Guest/CoreRef.lean`), which elaborate to these values, and an added or removed
function changes no proof.
-/

namespace LeanVM.Guest.Data

set_option linter.all false

@[expose] public section

namespace F
" ++ rows (fun s _ => s!"noncomputable abbrev «{s}» : Core.Fn := Fn.«{s}».core\n") ++ "end F

namespace I
" ++ rows (fun s j => s!"abbrev «{s}» : Nat := {j}\n") ++ "end I

end
end LeanVM.Guest.Data
"

def nameStringsFile (P : Core.Program) : String :=
  let st := stableNames P
  header "Data.NameStrings" "The core functions' names by their stable names." ++ "public import LeanVM.Guest.CoreRef

/-!
# The core functions' names by stable name

`N.«s»` is the name of the core function of stable name `s` (`Names`), without the core IR: what a
template naming a callee imports. `coreCount` is the number of core functions (`core_count%`).
-/

namespace LeanVM.Guest.Data

set_option linter.all false

@[expose] public section

abbrev coreCount : Nat := " ++ toString P.length ++ "

namespace N
" ++ String.join (P.zipIdx.map fun (fn, j) => s!"abbrev «{st.getD j ""}» : String := {fn.name.quote}\n") ++ "end N

end
end LeanVM.Guest.Data
"

/-! ## Packs -/

/-- **The layout's one choice**: the core IR's `packCount` packs, `Pack/P{i}/Core.lean`, function
`key` in pack `packOf packCount key` (`PackHash.lean`, shared with the other per-function
generators), so that an edit of one function rebuilds its pack only and an added, removed or
renumbered function moves no other; a function longer than `ownSize`, or split over files, is a
pack of its own, `Pack/<key>/Core.lean` (`Core1.lean`, … beside it). -/
def packCount : Nat := 64

/-- A function longer than this has a pack of its own. -/
def ownSize : Nat := 300000

/-- A pack's file: its functions, in the order of their stable names, each in its namespace. -/
def packText (i : Nat) (fs : List (String × String)) : String :=
  header s!"Pack.P{i}.Core" s!"The core IR of the functions of pack {i}." ++
  "public import LeanVM.Guest.Renumber\n\n" ++
  "set_option maxRecDepth 20000\nset_option linter.all false\n" ++
  String.join (fs.map fun (key, body) => s!"
namespace LeanVM.Guest.Fn.«{key}»

open LeanVM.Guest

@[expose] public section

" ++ body ++ s!"
end
end LeanVM.Guest.Fn.«{key}»
")

/-- The files, by path below `LeanVM/Guest`: the own packs', the packs', then the glue's. -/
def files (P : Core.Program) : List (String × String) :=
  let st := stableNames P
  let keys := (List.range P.length).map fun j => st.getD j ""
  let defs := (P.zip keys).map fun (f, key) => (key, pack [pFn key f])
  let text (fs : Array File) : String := "\n".intercalate (blocks fs[0]!.parts.toList)
  let own (fs : Array File) : Bool := fs.size > 1 || (text fs).length > ownSize
  let ownFiles := defs.flatMap fun (key, fs) =>
    if own fs then fs.toList.zipIdx.map fun (fl, i) =>
      (s!"Pack/{key}/{fnFileName fs.size i}.lean", fl.text key fs.size i)
    else []
  let packed := (defs.filter fun (_, fs) => !own fs).map fun (k, fs) => (packOf packCount k, k, text fs)
  let packFiles := (List.range packCount).filterMap fun i =>
    let fs := ((packed.filter (·.1 == i)).map (·.2)).mergeSort fun a b => a.1 ≤ b.1
    if fs.isEmpty then none else some (s!"Pack/P{i}/Core.lean", packText i fs)
  let mods := (defs.map fun (k, fs) =>
    if own fs then s!"Pack.{k}.Core" else s!"Pack.P{packOf packCount k}.Core").eraseDups
  ownFiles ++ packFiles ++ [("Data/Core.lean", indexFile keys mods),
    ("Data/Names.lean", namesFile P), ("Data/NameStrings.lean", nameStringsFile P)]

/-- The generated files on disk, by path below `LeanVM/Guest`: the old `Data/Core{k}` and
`Fn/<key>/Core*.lean`, and the packs' `Pack/*/Core*.lean`. -/
def existing : IO (List String) := do
  let numbered (pre n : String) : Bool :=
    let cs := n.toList
    cs.take pre.length == pre.toList && cs.reverse.take 5 == ".lean".toList.reverse &&
      ((cs.drop pre.length).take (cs.length - pre.length - 5)).all Char.isDigit
  let isCore (n : String) : Bool := numbered "Core" n
  let data := ((← dataDir.readDir).toList.map (·.fileName)).filter fun n => isCore n && n != "Core.lean"
  let mut fns : List String := []
  for (dir, top) in [(fnDir, "Fn"), (packDir, "Pack")] do
    if ← dir.isDir then
      for d in ← dir.readDir do
        if ← d.path.isDir then
          for e in ← d.path.readDir do
            if isCore e.fileName then fns := s!"{top}/{d.fileName}/{e.fileName}" :: fns
  return data.map ("Data/" ++ ·) ++ fns

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
  if let ["--show", name] := args then
    let some f := P.find? name | do IO.eprintln s!"no function {name}"; return 1
    IO.println (Interp.showFn f.renumber)
    return 0
  let check := args == ["--check"]
  unless args.isEmpty || check do
    IO.eprintln "usage: guest-core [--check | --values FUNCTION | --show FUNCTION]"
    return 2
  unless ← dataDir.isDir do
    IO.eprintln s!"{dataDir} not found: run from lean_vm"
    return 2
  let guest : System.FilePath := "LeanVM/Guest"
  let fs := files P
  let names := fs.map (·.1)
  let stale := (← existing).filter (!names.contains ·)
  let mut bad := false
  for (n, text) in fs do
    let path := guest / n
    let old ← if ← path.pathExists then IO.FS.readFile path else pure ""
    if old != text then
      if check then
        IO.eprintln s!"{path} is stale"
        bad := true
      else
        if let some dir := path.parent then IO.FS.createDirAll dir
        IO.FS.writeFile path text
  for n in stale do
    if check then
      IO.eprintln s!"{guest / n} is not generated"
      bad := true
    else
      IO.FS.removeFile (guest / n)
  if bad then
    IO.eprintln "regenerate with `lake exe guest-core`"
    return 1
  unless check do
    IO.println s!"{P.length} functions in {fs.length - 3} files"
  return 0
