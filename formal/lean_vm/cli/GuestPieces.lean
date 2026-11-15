import Statement.Data.Bytecode
import LeanVM.Guest.Backend.Guest.Input
import LeanVM.Guest.Backend.Cut
import LeanVMTests.Guest.Programs

/-!
# `guest-pieces`: the kernel-checked pieces of the guest's compilation

Run from `lean_vm`.

`lake exe guest-pieces` compiles the guest's traced input (`guestTraced`, as `guest-traced` writes
it) with the back end, natively, and writes what the kernel checks of it, function by function:

* `Backend/Guest/Piece/Outs.lean`: what placement and emission give of each function (`FnOut`: the
  jump tables' length after it, the shared tables it made, the slots it fills, its frame and code
  sizes), as flat lists, `outsG`;
* `Backend/Guest/Piece/Tables.lean`, `Layout.lean`: the loop and signature tables of the program,
  the layout of its functions and the jump tables' slots, each computed once by the kernel
  (`kernel_lit`);
* `Backend/Guest/Piece/P{k}.lean`: the pieces, `piecesIn … a b = true` by `decide +kernel`, one
  declaration for a run of functions of at most `maxDecl` instructions, `maxModule` instructions a
  module; `Backend/Guest/Piece/Jt{c}.lean`: chunk `c` of `__jump_tables`, in `jtParts` parts;
  `Backend/Guest/Piece/Checks.lean` and `Names.lean`: the checks on numbers and names;
* `Backend/Guest/Compiled.lean`: `GuestCompiles guestFns guestSlots` from them
  (`compiles_of_pieces`), given the pieces of the functions `bigNames` lists, which are not written
  as one piece (`BigPieces`).

`lake exe guest-pieces --check` writes nothing, fails when a file is stale, and evaluates every
piece natively first. `--extra NAME MODULE` makes the piece of each function `j` also check
`NAME j : VMap Loc → Bool` (from `MODULE`) on its placed locations (`pieceAtWith`), and
`Compiled.lean` conclude it for every function (`guest_extra`).

`lake exe guest-pieces test` writes `tests/LeanVMTests/Guest/BackendPieces.lean`: the same for the
compiler's test program `match_arms`, its traced functions written out, and its compilation proved
by `compiles_of_pieces` there.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend
  LeanVM.Guest.Backend.GuestInput

namespace GuestPieces

/-- A run of functions in one declaration has at most this many instructions. -/
def maxDecl : Nat := 2000

/-- A module of pieces has at most this many instructions. -/
def maxModule : Nat := 16000

/-- The functions whose one piece is past the memory a module may take: not written as one piece
(`BigPieces`). -/
def bigNames : List String := ["verify_tables", "verify_sig_lean_sphincs", "sp_wots", "__loop2"]

/-- The functions of `bigNames` whose piece is written in parts, its walk cut between top-level
statements (`Piece/C{j}.lean`); the others are `BigPieces`. -/
def cutNames : List String := ["verify_tables", "verify_sig_lean_sphincs"]

/-- A definition of data is split once its text is longer than this. -/
def maxDef : Nat := 24000

def pieceDir : System.FilePath := "LeanVM/Guest/Backend/Guest/Piece"
def compiledPath : System.FilePath := "LeanVM/Guest/Backend/Guest/Compiled.lean"
def testPath : System.FilePath := "tests/LeanVMTests/Guest/BackendPieces.lean"

/-! ## Text -/

def pList (items : List String) : String :=
  if items.length < 32 then s!"[{", ".intercalate items}]"
  else s!"({" :: ".intercalate items} :: [])"

def pStrs (ss : List String) : String := pList (ss.map String.quote)

def pFills (o : FnOut) : List String := o.fills.map fun (a, b) => s!"({a}, {b})"

def pFnOutWith (o : FnOut) (fills : String) : String :=
  let sh := o.shared.map fun (cs, n) => s!"({pStrs cs}, {n})"
  s!"⟨{o.len}, {pList sh}, {fills}, {o.frame}, {o.size}⟩"

def pFnOut (o : FnOut) : String := pFnOutWith o (pList (pFills o))

partial def pTrie {α : Type} (pa : α → String) : Trie α → String
  | .nil => "Trie.nil"
  | .node v l r =>
      let pv := match v with
        | some a => s!"(some {pa a})"
        | none => "none"
      s!"(Trie.node {pv} {pTrie pa l} {pTrie pa r})"

def pKMap {κ α : Type} (pk : κ → String) (pa : α → String) (m : KMap κ α) : String :=
  s!"⟨{pTrie (fun b => pList (b.map fun (k, a) => s!"({pk k}, {pa a})")) m.t}⟩"

def pPair (x : Nat × Nat) : String := s!"({x.1}, {x.2})"

def pLoopInfo (li : LoopInfo) : String :=
  s!"⟨{li.registered}, {match li.hi with | some h => s!"some {h}" | none => "none"}⟩"

def pKVal : KVal → String
  | .frameSize => "KVal.frameSize"
  | .const a b => s!"(KVal.const {a} {b})"
  | .entry f => s!"(KVal.entry {f.quote})"
  | .endSentinel => "KVal.endSentinel"
  | .local i => s!"(KVal.local {i})"
  | .at f i => s!"(KVal.at {f.quote} {i})"

def pLayout (l : Layout) : String :=
  s!"\{ entry := {pKMap String.quote toString l.entry},\n    frame := {pKMap String.quote toString l.frame},\n" ++
  s!"    tablesBase := {l.tablesBase}, sentinel := {l.sentinel}, gpow := #[] }"

/-- Data split into definitions: `name_c{i}`, and `name` their concatenation. -/
def chunkedDefs (doc name ty : String) (items : List String) : String := Id.run do
  let mut chunks : Array (List String) := #[]
  let mut cur : Array String := #[]
  let mut size := 0
  for it in items do
    if size + it.length + 4 > maxDef && !cur.isEmpty then
      chunks := chunks.push cur.toList
      cur := #[]
      size := 0
    cur := cur.push it
    size := size + it.length + 4
  if !cur.isEmpty || chunks.isEmpty then chunks := chunks.push cur.toList
  let names := (List.range chunks.size).map fun i => s!"{name}_c{i}"
  let parts := (chunks.toList.zip names).map fun (c, n) =>
    s!"/-- Part of `{name}`. -/\ndef {n} : List {ty} :=\n  {pList c}\n\n"
  return String.join parts ++ s!"/-- {doc} -/\ndef {name} : List {ty} :=\n  List.flatten {pList names}\n\n"

def header (mod what : String) : String :=
  s!"/-
  {mod}

  Generated by `lake exe guest-pieces` (lean_vm/cli/GuestPieces.lean); do not edit.
  {what}
-/
"

/-! ## The functions' outputs -/

/-- What placement and emission give of each function of `P`, in order. -/
def outsOf (P : List TracedFn) : Except String (List FnOut) := do
  let loops := loopTable P
  let sigs := sigTable P
  let mut t : Tables := {}
  let mut outs : Array FnOut := #[]
  for tf in P do
    let (pf, t') ← placeFn loops sigs t tf
    let e := emitFn pf.fn
    let fresh := t'.shared.length - t.shared.length
    unless t'.shared.drop fresh == t.shared do
      throw s!"{tf.core.name}: the shared tables are not extended at the front"
    let fills ← e.2.toList.mapM fun (s, k) => match k with
      | .at f i => if f == tf.core.name then pure (s, i) else throw s!"{tf.core.name}: a fill of {f}"
      | _ => throw s!"{tf.core.name}: a fill that is no instruction of it"
    outs := outs.push ⟨t'.len, t'.shared.take fresh, fills, pf.fn.frameSize, e.1.code.size⟩
    t := t'
  return outs.toList

/-- Ranges `[a, b)` of the functions, each of at most `maxDecl` instructions or one function; the
functions `isBig` names are alone, and listed apart. -/
def ranges (sizes : List Nat) (isBig : Nat → Bool) : List (Nat × Nat) × List Nat := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut big : Array Nat := #[]
  let mut start := 0
  let mut acc := 0
  for (sz, j) in sizes.zipIdx do
    if isBig j then
      if start < j then out := out.push (start, j)
      big := big.push j
      start := j + 1
      acc := 0
    else
      if start < j && maxDecl < acc + sz then
        out := out.push (start, j)
        start := j
        acc := 0
      acc := acc + sz
  if start < sizes.length then out := out.push (start, sizes.length)
  return (out.toList, big.toList)

/-- The ranges grouped in modules of at most `maxModule` instructions. -/
def modules (sizes : List Nat) (rs : List (Nat × Nat)) : List (List (Nat × Nat)) := Id.run do
  let sizeOf (r : Nat × Nat) : Nat := ((sizes.drop r.1).take (r.2 - r.1)).sum
  let mut out : Array (List (Nat × Nat)) := #[]
  let mut cur : Array (Nat × Nat) := #[]
  let mut acc := 0
  for r in rs do
    if !cur.isEmpty && maxModule < acc + sizeOf r then
      out := out.push cur.toList
      cur := #[]
      acc := 0
    cur := cur.push r
    acc := acc + sizeOf r
  if !cur.isEmpty then out := out.push cur.toList
  return out.toList

/-! ## The guest's files -/

/-- The test on placed locations each piece also makes: its name and module. -/
structure Extra where
  name : String
  mod : String

def piecesFn (extra : Option Extra) : String :=
  match extra with
  | some x => s!"piecesInWith {x.name}"
  | none => "piecesIn"

def pieceArgs : String := "loopsG sigsG layG guestTraced outsG Data.functions.tail"

def outsFile (outs : List FnOut) : String :=
  header "LeanVM.Guest.Backend.Guest.Piece.Outs"
    "What placement and emission give of each of the guest's functions, in order." ++
  "\nmodule\n\npublic import LeanVM.Guest.Backend.Piece\n\n" ++
  "set_option maxRecDepth 20000\nset_option linter.all false\n\n" ++
  "namespace LeanVM.Guest.Backend.GuestPiece\n\nopen LeanVM.Guest.Backend\n\n@[expose] public section\n\n" ++
  String.join (outs.zipIdx.filterMap fun (o, j) =>
    if (pList (pFills o)).length ≤ maxDef then none
    else some (chunkedDefs s!"The jump table slots function {j} fills." s!"fillsG{j}" "(Nat × Nat)" (pFills o))) ++
  chunkedDefs "What placement and emission give of each of the guest's functions, in order (`FnOut`)."
    "outsG" "FnOut" (outs.zipIdx.map fun (o, j) =>
      if (pList (pFills o)).length ≤ maxDef then pFnOut o else pFnOutWith o s!"fillsG{j}") ++
  "end\nend LeanVM.Guest.Backend.GuestPiece\n"

def tablesFile (loops : Loops) (sigs : SMap (Nat × Nat)) : String :=
  header "LeanVM.Guest.Backend.Guest.Piece.Tables"
    "The guest's loop and signature tables, and the kernel's checks that they are the program's." ++
  "\nmodule\n\npublic import LeanVM.Guest.Backend.Guest.Program\npublic import LeanVM.Guest.Backend.Piece\n" ++
  "public meta import LeanVM.Guest.KernelLit\n\n" ++
  "set_option maxRecDepth 100000\nset_option linter.all false\n\n" ++
  "namespace LeanVM.Guest.Backend.GuestPiece\n\nopen LeanVM.Guest.Backend\n\n@[expose] public section\n\n" ++
  s!"/-- The guest's loop helpers. -/\ndef loopsG : Loops :=\n  {pKMap String.quote pLoopInfo loops}\n\n" ++
  s!"/-- The guest's functions' argument and return cells. -/\ndef sigsG : SMap (Nat × Nat) :=\n  {pKMap String.quote pPair sigs}\n\n" ++
  "kernel_rfl loopsG_eq : loopTable guestTraced = loopsG\n\n" ++
  "kernel_rfl sigsG_eq : sigTable guestTraced = sigsG\n\n" ++
  "end\nend LeanVM.Guest.Backend.GuestPiece\n"

def layoutFile (l : Layout) (slots : Array KVal) : String :=
  header "LeanVM.Guest.Backend.Guest.Piece.Layout"
    "The guest's layout and jump table slots, the kernel's checks of them, and its placed locations." ++
  "\nmodule\n\npublic import LeanVM.Guest.Backend.Guest.Piece.Outs\npublic import LeanVM.Guest.Backend.Guest.Piece.Tables\n" ++
  "public meta import LeanVM.Guest.KernelLit\n\n" ++
  "set_option maxRecDepth 100000\nset_option linter.all false\n\n" ++
  "namespace LeanVM.Guest.Backend.GuestPiece\n\nopen LeanVM.Guest.Backend\n\n@[expose] public section\n\n" ++
  s!"/-- The layout of the guest's functions, `__jump_tables` first. -/\ndef layG : Layout :=\n  {pLayout l}\n\n" ++
  chunkedDefs "The guest's jump table slots, as a list." "slotsL" "KVal" (slots.toList.map pKVal) ++
  "/-- The guest's jump table slots. -/\ndef slotsG : Array KVal := slotsL.toArray\n\n" ++
  "kernel_rfl layG_eq : layoutInfo (infoOfOuts guestTraced outsG) (baseOf outsG) = layG\n\n" ++
  "kernel_rfl slotsOfOuts_eq : slotsOfOuts guestTraced outsG = slotsG\n\n" ++
  "/-- **The locations of function `j`'s values**, placed from the jump tables the functions before it\nleave. -/\n" ++
  "noncomputable def placedLocs (j : Nat) : VMap Loc := placedLocsAt loopsG sigsG guestTraced outsG j\n\n" ++
  "end\nend LeanVM.Guest.Backend.GuestPiece\n"

def pieceFile (k : Nat) (rs : List (Nat × Nat)) (names : List String) (sizes : List Nat)
    (extra : Option Extra) : String :=
  let decls := rs.map fun (a, b) =>
    let fns := (names.drop a).take (b - a)
    let n := ((sizes.drop a).take (b - a)).sum
    let what := if b = a + 1 then s!"`{fns.headD ""}`" else s!"`{fns.headD ""}` to `{fns.getLastD ""}`"
    s!"/-- The pieces of functions {a} to {b - 1} ({what}, {n} instructions). -/\n" ++
    s!"theorem pieces_{a}_{b} :\n    {piecesFn extra} {pieceArgs} {a} {b} = true := by\n  decide +kernel\n\n"
  let extraImport := match extra with
    | some x => s!"public import {x.mod}\n"
    | none => ""
  header s!"LeanVM.Guest.Backend.Guest.Piece.P{k}" "The kernel's checks of some of the guest's functions' pieces." ++
  "\nmodule\n\npublic import LeanVM.Guest.Backend.Guest.Piece.Layout\npublic import Statement.Data.Bytecode\n" ++
  extraImport ++ "\nset_option Elab.async false\nset_option maxRecDepth 100000\n\n" ++
  "namespace LeanVM.Guest.Backend.GuestPiece\n\nopen LeanVM.Guest.Backend\n\n@[expose] public section\n\n" ++
  String.join decls ++ "end\nend LeanVM.Guest.Backend.GuestPiece\n"

def jtFile (c : Nat) : String :=
  header s!"LeanVM.Guest.Backend.Guest.Piece.Jt{c}" s!"The kernel's checks of chunk {c} of `__jump_tables`." ++
  "\nmodule\n\npublic import LeanVM.Guest.Backend.Guest.Piece.Layout\npublic import Statement.Data.Bytecode\n\n" ++
  "set_option Elab.async false\nset_option maxRecDepth 100000\n\n" ++
  "namespace LeanVM.Guest.Backend.GuestPiece\n\nopen LeanVM.Guest.Backend\n\n@[expose] public section\n\n" ++
  String.join ((List.range jtParts).map fun q =>
    s!"/-- Part {q} of chunk {c} of `__jump_tables` is the statement's. -/\n" ++
    s!"theorem jt_{c}_{q} : jtPartOk layG (baseOf outsG) slotsG Data.f0 {c} {q} = true := by\n  decide +kernel\n\n") ++
  "end\nend LeanVM.Guest.Backend.GuestPiece\n"

/-- The proof of `∀ c < m, ∀ q < jtParts, jtPartOk … c q = true` from the theorems `jt_{c}_{q}`
(`name c q` names them). -/
def jtCases (indent : String) (m : Nat) (name : Nat → Nat → String) : String :=
  let pat (n : Nat) := " | ".intercalate ((List.range n).map fun _ => "_") ++ " | c"
  s!"{indent}rcases c with {pat m}\n" ++
  String.join ((List.range m).map fun c =>
    s!"{indent}· rcases q with {pat jtParts}\n" ++
    s!"{indent}  exacts [{", ".intercalate ((List.range jtParts).map fun q => name c q)}, absurd hq (by rw [show jtParts = {jtParts} from rfl]; omega)]\n") ++
  s!"{indent}· exact absurd hc (by omega)\n"

def namesFile : String :=
  header "LeanVM.Guest.Backend.Guest.Piece.Names" "The kernel's check of the guest's names." ++
  "\nmodule\n\npublic import LeanVM.Guest.Backend.Guest.Piece.Tables\n\n" ++
  "set_option maxRecDepth 100000\n\n" ++
  "namespace LeanVM.Guest.Backend.GuestPiece\n\nopen LeanVM.Guest.Backend\n\n@[expose] public section\n\n" ++
  "/-- `main` first, no function named `__jump_tables`, the names distinct, `main` no loop helper. -/\n" ++
  "theorem checks_ok : progChecks guestTraced loopsG = true := by decide +kernel\n\n" ++
  "end\nend LeanVM.Guest.Backend.GuestPiece\n"

def checksFile (logSize : Nat) : String :=
  header "LeanVM.Guest.Backend.Guest.Piece.Checks" "The kernel's checks of the guest's names, slots and sizes." ++
  "\nmodule\n\npublic import LeanVM.Guest.Backend.Guest.Piece.Layout\npublic import Statement.Data.Bytecode\n\n" ++
  "set_option maxRecDepth 100000\n\n" ++
  "namespace LeanVM.Guest.Backend.GuestPiece\n\nopen LeanVM.Guest.Backend\n\n@[expose] public section\n\n" ++
  "theorem guestTraced_length : guestTraced.length = 1601 := by decide +kernel\n\n" ++
  "theorem outs_length : outsG.length = guestTraced.length := by decide +kernel\n\n" ++
  "theorem cfs_length : Data.functions.tail.length = guestTraced.length := by decide +kernel\n\n" ++
  "theorem slots_ok : slotsOk outsG = true := by decide +kernel\n\n" ++
  "theorem slots_ne : (tablesEnd outsG).len ≠ 0 := by decide +kernel\n\n" ++
  s!"theorem size_ok : nextPow2 ((tablesEnd outsG).len + (outsG.map (·.size)).sum + 1) = 2 ^ {logSize} := by\n  decide +kernel\n\n" ++
  "theorem jt_head : jtHead slotsG Data.f0 = true := by decide +kernel\n\n" ++
  "theorem functions_eq : Data.functions = Data.f0 :: Data.functions.tail := rfl\n\n" ++
  "end\nend LeanVM.Guest.Backend.GuestPiece\n"

/-- The proof of `piecesIn … 0 n`, gluing the ranges and the big functions' pieces in order. -/
def glueTerm (n : Nat) (rs : List (Nat × Nat)) (big cut : List Nat) (extra : Option Extra) : String := Id.run do
  let glue := match extra with
    | some _ => "piecesInWith_glue"
    | none => "piecesIn_glue"
  let single := match extra with
    | some _ => "piecesInWith_single"
    | none => "piecesIn_single"
  let mut items : Array (Nat × Nat × String) := #[]
  for (a, b) in rs do items := items.push (a, b, s!"pieces_{a}_{b}")
  for j in big do items := items.push (j, j + 1, s!"({single} (hbig {j} (by decide)))")
  for j in cut do items := items.push (j, j + 1, s!"({single} piece_{j})")
  let sorted := items.toList.mergeSort fun x y => x.1 ≤ y.1
  let mut term := ""
  let mut first := true
  let mut hi := 0
  for (_, b, t) in sorted do
    if first then
      term := t
      first := false
    else
      term := s!"({glue} {term}\n      {t} (by decide) (by decide))"
    hi := b
  if hi != n then term := term ++ " -- incomplete"
  return term

def compiledFile (n : Nat) (rs : List (Nat × Nat)) (big : List Nat) (cuts : List (Nat × String × Nat))
    (mods jts : Nat) (extra : Option Extra) : String :=
  let cut := cuts.map (·.1)
  let imports := String.join ((List.range mods).map fun k => s!"public import LeanVM.Guest.Backend.Guest.Piece.P{k}\n") ++
    String.join ((List.range jts).map fun c => s!"public import LeanVM.Guest.Backend.Guest.Piece.Jt{c}\n") ++
    String.join (cuts.map fun (j, _, m) => String.join ((List.range m).map fun k =>
      s!"public import LeanVM.Guest.Backend.Guest.Piece.C{j}P{k}\n")) ++
    (if cut.isEmpty then "" else "public import LeanVM.Guest.Backend.Sound.Cut\n")
  let cutPieces := String.join (cuts.map (·.2.1))
  let bigNames := pList (big.map toString)
  let bigDef := match extra with
    | some x => s!"/-- The pieces of the guest's functions too large for one piece, not checked here. -/\n" ++
        s!"def BigPieces : Prop :=\n  ∀ j ∈ ({bigNames} : List Nat), pieceAtWith {x.name} {pieceArgs} j = true\n\n"
    | none => s!"/-- The pieces of the guest's functions too large for one piece, not checked here. -/\n" ++
        s!"def BigPieces : Prop :=\n  ∀ j ∈ ({bigNames} : List Nat), pieceAt {pieceArgs} j = true\n\n"
  let piecesAll := match extra with
    | some x => s!"/-- Every function's piece, with the test `{x.name}`. -/\n" ++
        s!"theorem guest_pieces_with (hbig : BigPieces) :\n    ∀ j < guestTraced.length, pieceAtWith {x.name} {pieceArgs} j = true := by\n" ++
        s!"  rw [guestTraced_length]\n  exact fun j hj => piecesInWith_spec (a := 0) (b := {n})\n    {glueTerm n rs big cut extra} j (Nat.zero_le _) hj\n\n" ++
        "/-- **Every function's piece.** -/\n" ++
        s!"theorem guest_pieces (hbig : BigPieces) :\n    ∀ j < guestTraced.length, pieceAt {pieceArgs} j = true :=\n" ++
        "  fun j hj => pieceAt_of_with (guest_pieces_with hbig j hj)\n\n" ++
        s!"/-- **Every function's placed locations pass the test `{x.name}`.** -/\n" ++
        s!"theorem guest_extra (hbig : BigPieces) :\n    ∀ j < guestTraced.length, {x.name} j (placedLocs j) = true :=\n" ++
        "  fun j hj => extra_of_with (guest_pieces_with hbig j hj)\n\n"
    | none => "/-- **Every function's piece.** -/\n" ++
        s!"theorem guest_pieces (hbig : BigPieces) :\n    ∀ j < guestTraced.length, pieceAt {pieceArgs} j = true := by\n" ++
        s!"  rw [guestTraced_length]\n  exact fun j hj => piecesIn_spec (a := 0) (b := {n})\n    {glueTerm n rs big cut extra} j (Nat.zero_le _) hj\n\n"
  let hbigDoc := if big.isEmpty then "every function is a piece checked here, so `BigPieces` holds trivially (`bigPieces`)"
    else s!"the {big.length} functions too large for one piece (`BigPieces`) are a hypothesis"
  let bigThm := if big.isEmpty then "theorem bigPieces : BigPieces := fun _ h => nomatch h\n\n" else ""
  header "LeanVM.Guest.Backend.Guest.Compiled" "The back end compiles the guest to the statement's bytecode, from the kernel-checked pieces." ++
  "\nmodule\n\npublic import LeanVM.Guest.Backend.Guest.World\npublic import LeanVM.Guest.Backend.Sound.Compiles\n" ++
  "public import LeanVM.Guest.Backend.Guest.Piece.Checks\npublic import LeanVM.Guest.Backend.Guest.Piece.Names\n" ++ imports ++
  s!"\n/-!\n# The guest compiled\n\n`guest_compiles`: `GuestCompiles guestFns guestSlots`, by `compiles_of_pieces` from the pieces of\n`Guest/Piece/` and the checks of `Guest/Piece/Checks.lean`; {hbigDoc}.\n`guest_program_sound_compiled` is `guest_program_sound` without `GuestCompiles`, and\n`guestWorld_locs` says function `j`'s places in the guest's world are `placedLocs j`, which the\nkernel evaluates.\n-/\n\n" ++
  "set_option maxRecDepth 100000\n\n" ++
  "namespace LeanVM.Guest.Backend\n\nopen LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core GuestPiece\n\n@[expose] public section\n\n" ++
  bigDef ++ bigThm ++ cutPieces ++ piecesAll ++
  "/-- The labelled code of the guest's functions, as the back end lowers them. -/\n" ++
  "noncomputable def guestFns : List Lowered := fnsOf (lowerProgram guestTraced)\n\n" ++
  "/-- The guest's jump table slots. -/\ndef guestSlots : Array KVal := slotsG\n\n" ++
  "theorem guest_jt :\n    Data.f0 = ⟨\"__jump_tables\", 0, (slotsOfOuts guestTraced outsG).size,\n" ++
  "      chunked (resolvedFn layG 0 (jtOf (baseOf outsG) (slotsOfOuts guestTraced outsG)))⟩ := by\n" ++
  "  rw [slotsOfOuts_eq]\n  refine jt_of_chunks jt_head fun c hc q hq => ?_\n" ++
  s!"  have hn : Data.f0.chunks.length = {jts} := rfl\n  rw [hn] at hc\n" ++
  jtCases "  " jts (fun c q => s!"jt_{c}_{q}") ++ "\n" ++
  "/-- **The back end compiles the guest to the statement's bytecode.** -/\n" ++
  "theorem guest_compiles (hbig : BigPieces) : GuestCompiles guestFns guestSlots := by\n" ++
  "  obtain ⟨fns, hlow, hfun, hsize⟩ := compiles_of_pieces (cfJt := Data.f0) (k := 19) loopsG_eq sigsG_eq\n" ++
  "    layG_eq checks_ok outs_length cfs_length (guest_pieces hbig) slots_ok slots_ne guest_jt size_ok\n" ++
  "    (by norm_num)\n" ++
  "  have hf : guestFns = fns := by rw [guestFns, hlow]; rfl\n" ++
  "  rw [slotsOfOuts_eq] at hlow hfun hsize\n" ++
  "  rw [hf, show guestSlots = slotsG from rfl]\n" ++
  "  refine ⟨hlow, ?_, hsize⟩\n  rw [hfun]\n  exact functions_eq.symm\n\n" ++
  "variable {κ : ℕ} {L : MemoryImage κ} {U : String → List E → Prop}\n\n" ++
  "/-- **At the guest**, `guest_program_sound` with the guest compiled: given every function's\nobligations, a halting run of the statement's `guestProgram` from `(g^0, 1)` makes `main`'s core body\nhold at frame `1`. -/\n" ++
  "theorem guest_program_sound_compiled (hbig : BigPieces) (hκ : κ < 64)\n" ++
  "    (hobl : ∀ tf ∈ guestTraced, (guestWorld guestFns guestSlots L U).Obligations tf)\n" ++
  "    (hU : ∀ tf ∈ guestTraced, tf.core.name = \"main\" → U \"main\" (frameWords L 1 2 (sigOf tf).1))\n" ++
  "    {k : ℕ} (hs : Safe guestProgram L k ⟨addressOfIndex 0, 1⟩) :\n" ++
  "    (guestWorld guestFns guestSlots L U).MainHolds :=\n" ++
  "  guest_program_sound (guest_compiles hbig) hκ hobl hU hs\n\n" ++
  "/-- **Function `j`'s places in the guest's world** are `placedLocs j`. -/\n" ++
  "theorem guestWorld_locs (hbig : BigPieces) {j : ℕ} (hj : j < guestTraced.length) :\n" ++
  "    (guestWorld guestFns guestSlots L U).locs (guestTraced.getD j default).core.name = placedLocs j :=\n" ++
  "  world_locs_of_pieces _ guestWorld_p loopsG_eq sigsG_eq checks_ok outs_length cfs_length (guest_pieces hbig) hj\n\n" ++
  "end\nend LeanVM.Guest.Backend\n\n" ++
  "/-- info: 'LeanVM.Guest.Backend.guest_compiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/\n#guard_msgs in\n#print axioms LeanVM.Guest.Backend.guest_compiles\n\n" ++
  "/-- info: 'LeanVM.Guest.Backend.guest_program_sound_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/\n#guard_msgs in\n#print axioms LeanVM.Guest.Backend.guest_program_sound_compiled\n\n" ++
  "/-- info: 'LeanVM.Guest.Backend.guestWorld_locs' depends on axioms: [propext, Classical.choice, Quot.sound] -/\n#guard_msgs in\n#print axioms LeanVM.Guest.Backend.guestWorld_locs\n"

/-! ## The test program -/

def pSeg : Seg → String
  | .s i => s!".s {i}"
  | .u j => s!".u {j}"
  | .t => ".t"
  | .e => ".e"
  | .a j => s!".a {j}"
  | .i f k => s!".i {f.quote} {k}"

def pV (v : V) : String := s!"⟨[{", ".intercalate (v.path.map pSeg)}], {v.tag}, {v.idx}⟩"

def pVs (vs : List V) : String := pList (vs.map pV)

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

partial def pStmt : Stmt → String
  | .atom a => s!"(.atom ({pAtom a}))"
  | .ite c z nz => s!"(.ite {pV c} {pList (z.map pStmt)} {pList (nz.map pStmt)})"
  | .match_ x arms => s!"(.match_ {pV x} {pList (arms.map fun a => pList (a.map pStmt))})"
  | .call f args rets => s!"(.call {f.quote} {pVs args} {pVs rets})"
  | .callIf c f args => s!"(.callIf {pV c} {f.quote} {pVs args})"
  | .dispatch x fs args rets => s!"(.dispatch {pV x} {pStrs fs} {pVs args} {pVs rets})"
  | .ret vs => s!"(.ret {pVs vs})"

def pKind : Kind → String
  | .cell => ".cell" | .pooled => ".pooled" | .site => ".site" | .addr => ".addr"
  | .ret => ".ret" | .padRun => ".padRun" | .spongeRun => ".spongeRun"

def pEvent : Event → String
  | .alloc vs k => s!"(.alloc {pVs vs} {pKind k})"
  | .emit => ".emit"
  | .enter => ".enter"
  | .leave => ".leave"
  | .use v => s!"(.use {pV v})"
  | .shift v e => s!"(.shift {pV v} {e})"
  | .chain => ".chain"
  | .note n => s!"(.note {n})"

def pTraced (tf : TracedFn) : String :=
  let loop := match tf.loop.2 with
    | some h => s!"some {h}"
    | none => "none"
  s!"⟨⟨{tf.core.name.quote}, {pVs tf.core.params}, {pList (tf.core.body.map pStmt)}⟩,\n" ++
  s!"    {pList (tf.trace.toList.map pEvent)}.toArray,\n    {tf.rets}, ({tf.loop.1}, {loop})⟩"

def pMode : DerefMode → String
  | .cell => ".cell" | .pc => ".pc" | .fp => ".fp"

def pCells : KeccakOutputCells → String
  | .one => ".one" | .two => ".two" | .all => ".all"

def pInstr : OffsetInstruction → String
  | .xor a b c => s!".xor {a} {b} {c}"
  | .mul a b c => s!".mul {a} {b} {c}"
  | .set o k0 k1 => s!".set {o} {k0} {k1}"
  | .deref a b c m => s!".deref {a} {b} {c} {pMode m}"
  | .jump a b c => s!".jump {a} {b} {c}"
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd cells =>
      s!".keccak {m0} {m1} {m2} {m3} {tail} {b8} {cap} {out} {inOdd} {outOdd} {pCells cells}"

def pCompiled (cf : CompiledFunction) : String :=
  s!"⟨{cf.name.quote}, {cf.entryPc}, {cf.instructionCount}, {pList (cf.chunks.map fun c => pList (c.map pInstr))}⟩"

/-- The smallest `k` with `2 ^ k ≥ n`. -/
def logOf (n : Nat) : Nat := Id.run do
  let mut k := 0
  while 2 ^ k < n do k := k + 1
  return k

/-- The test file for the test program `name`. -/
def testFile (name : String) : IO String := do
  let some t := LeanVMTests.Guest.Programs.all.find? (·.name == name)
    | throw (IO.userError s!"no test program {name}")
  let P := renamed (← orThrow (ExpandTrace.expandProgram t.program))
  let outs ← orThrow (outsOf P)
  let (fns, slots) ← orThrow (lowerProgram P)
  let a := assemble fns slots
  let cfs := a.toFunctions
  let k := logOf a.size
  unless 2 ^ k == a.size do throw (IO.userError "the size is no power of two")
  if slots.isEmpty then throw (IO.userError s!"{name} has no jump table")
  let n := P.length
  let jts := (cfs.headD noFunction).chunks.length
  let nameId := name.replace "_" ""
  return header s!"LeanVMTests.Guest.BackendPieces"
      s!"The compiler's test program `{name}` compiled by the back end, from its kernel-checked pieces." ++
    "\nimport LeanVM.Guest.Backend.Sound.Compiles\nimport LeanVM.Guest.KernelLit\n\n" ++
    s!"/-!\n# A program compiled from its pieces\n\n`{name}.py`'s traced functions, their values renamed as `guest-traced` renames the guest's, written out, and what placement and emission give of each; its\ncompilation by the back end (`lowerProgram`, `assemble`) is `{nameId}_compiles`, by\n`compiles_of_pieces` from the kernel's checks of its pieces: the composition the guest's\n`Backend/Guest/Compiled.lean` makes, on a program small enough to check in one module.\n-/\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    "namespace LeanVMTests.Guest.BackendPieces\n\nopen LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend\n\n" ++
    s!"/-- `{name}.py`, traced. -/\ndef prog : List TracedFn := {pList (P.map pTraced)}\n\n" ++
    s!"/-- What placement and emission give of its functions. -/\ndef outs : List FnOut := {pList (outs.map pFnOut)}\n\n" ++
    s!"/-- Its compiled functions. -/\ndef cfs : List CompiledFunction := {pList (cfs.map pCompiled)}\n\n" ++
    "kernel_lit loops : Loops := loopTable prog\n\nkernel_lit sigs : SMap (Nat × Nat) := sigTable prog\n\n" ++
    "kernel_lit lay : Layout := layoutInfo (infoOfOuts prog outs) (baseOf outs)\n\n" ++
    s!"theorem pieces : piecesIn loops sigs lay prog outs cfs.tail 0 {n} = true := by decide +kernel\n\n" ++
    s!"theorem jt : cfs.headD noFunction = ⟨\"__jump_tables\", 0, (slotsOfOuts prog outs).size,\n" ++
    "    chunked (resolvedFn lay 0 (jtOf (baseOf outs) (slotsOfOuts prog outs)))⟩ :=\n" ++
    "  jt_of_chunks (by decide +kernel) fun c hc q hq => by\n" ++
    s!"    have hn : (cfs.headD noFunction).chunks.length = {jts} := rfl\n    rw [hn] at hc\n" ++
    jtCases "    " jts (fun _ _ => "by decide +kernel") ++ "\n" ++
    s!"/-- **`{name}.py` compiled from its pieces.** -/\n" ++
    s!"theorem {nameId}_compiles : ∃ fns, lowerProgram prog = .ok (fns, slotsOfOuts prog outs) ∧\n" ++
    s!"    (assemble fns (slotsOfOuts prog outs)).toFunctions = cfs ∧\n    (assemble fns (slotsOfOuts prog outs)).size = 2 ^ {k} := by\n" ++
    s!"  have h := compiles_of_pieces (k := {k}) loops_eq sigs_eq lay_eq (by decide +kernel) (by decide +kernel)\n" ++
    "    (by decide +kernel) (fun j hj => piecesIn_spec pieces j (Nat.zero_le _) hj) (by decide +kernel)\n" ++
    "    (by decide +kernel) jt (by decide +kernel) (by norm_num)\n" ++
    "  have hc : cfs = cfs.headD noFunction :: cfs.tail := rfl\n" ++
    "  rw [hc]\n  exact h\n\n" ++
    "end LeanVMTests.Guest.BackendPieces\n\n" ++
    s!"/-- info: 'LeanVMTests.Guest.BackendPieces.{nameId}_compiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/\n#guard_msgs in\n#print axioms LeanVMTests.Guest.BackendPieces.{nameId}_compiles\n"

/-! ## Cut pieces -/

/-- A cut piece's walk is cut once its statements since the last cut make this many instructions. -/
def cutSize : Nat := 1500

def pOpt {α : Type} (pa : α → String) : Option α → String
  | some a => s!"(some {pa a})"
  | none => "none"

def pLoc : Loc → String
  | .cell n => s!"(Loc.cell {n})"
  | .shifted n e => s!"(Loc.shifted {n} {e})"

def pBits : BitsDest → String
  | .stack b => s!"(BitsDest.stack {b})"
  | .heap p => s!"(BitsDest.heap {p})"

def pRHint : RHint → String
  | .frameAddress n => s!"(RHint.frameAddress {n})"
  | .allocFrames p sz b si t => s!"(RHint.allocFrames {p} {sz} {b} {si} {t})"
  | .alloc p sz => s!"(RHint.alloc {p} {sz})"
  | .allocDyn p sz => s!"(RHint.allocDyn {p} {sz})"
  | .witnessStack s b n => s!"(RHint.witnessStack {s.quote} {b} {n})"
  | .witnessHeap s p lo n => s!"(RHint.witnessHeap {s.quote} {p} {lo} {n})"
  | .log2Ceil b d nb fl => s!"(RHint.log2Ceil {pBits b} {d} {nb} {fl})"
  | .bitDecompose v b nb => s!"(RHint.bitDecompose {v} {pBits b} {nb})"
  | .bitDecomposeExp v b nb => s!"(RHint.bitDecomposeExp {v} {pBits b} {nb})"
  | .digitDecomposeExp v d nb nd db st sc =>
      s!"(RHint.digitDecomposeExp {v} {pBits d} {nb} {nd} {db} {st} {pOpt toString sc})"
  | .windowsExp v d sk st w c => s!"(RHint.windowsExp {v} {pBits d} {sk} {st} {w} {c})"
  | .fieldLimbs v b n => s!"(RHint.fieldLimbs {v} {b} {n})"
  | .inverse v d => s!"(RHint.inverse {v} {d})"

def pCount : LoopCount → String
  | .constant n => s!"(LoopCount.constant {n})"
  | .bound c st => s!"(LoopCount.bound {c} {st})"

def pLHint : LHint → String
  | .nextFrameAddress => "LHint.nextFrameAddress"
  | .allocLoopFrames p c n t => s!"(LHint.allocLoopFrames {p} {c.quote} {pCount n} {t})"
  | .allocFrame p c => s!"(LHint.allocFrame {p} {c.quote})"
  | .allocFrameMax p cs => s!"(LHint.allocFrameMax {p} {pStrs cs})"
  | .resolved h => s!"(LHint.resolved {pRHint h})"

def pHints (hs : List LHint) : String := pList (hs.map pLHint)

def pLOp : LOp → String
  | .mulNextFrame a b c => s!"(LOp.mulNextFrame {a} {b} {c})"
  | .set o k => s!"(LOp.set {o} {pKVal k})"
  | .xor a b c => s!"(LOp.xor {a} {b} {c})"
  | .mul a b c => s!"(LOp.mul {a} {b} {c})"
  | .deref a b c m => s!"(LOp.deref {a} {b} {c} {pMode m})"
  | .jump a b c => s!"(LOp.jump {a} {b} {c})"
  | .slot x f d => s!"(LOp.slot {x} {f} {d})"
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd cells =>
      s!"(LOp.keccak {m0} {m1} {m2} {m3} {tail} {b8} {cap} {out} {inOdd} {outOdd} {pCells cells})"

def pNats (ns : List Nat) : String := pList (ns.map toString)

partial def pPStmt : PStmt → String
  | .op hs o => s!"(PStmt.op {pHints hs} {pLOp o})"
  | .ite hs c bd sfp z he ed one nz =>
      s!"(PStmt.ite {pHints hs} {c} {bd} {sfp} {pList (z.map pPStmt)} {he} {ed} {one} {pList (nz.map pPStmt)})"
  | .chain hs join x entry one sfp firsts stages =>
      s!"(PStmt.chain {pHints hs} {join} {x} {entry} {one} {sfp} {pNats firsts} " ++
      s!"{pList (stages.map fun st => pList (st.map fun a => pList (a.map pPStmt)))})"
  | .call hs c =>
      s!"(PStmt.call {pHints hs} ⟨{c.callee.quote}, {c.nfp}, {c.entry}, {c.oc}, {pNats c.args}, " ++
      s!"{pNats c.rets}, {pOpt pCount c.loop}, {c.tail}⟩)"
  | .loopNext hs callee nfp entry oc one args =>
      s!"(PStmt.loopNext {pHints hs} {callee.quote} {nfp} {entry} {oc} {one} {pNats args})"
  | .dispatch hs callees nfp jc x entry one first args rets =>
      s!"(PStmt.dispatch {pHints hs} {pStrs callees} {nfp} {jc} {x} {entry} {one} {first} {pNats args} {pNats rets})"
  | .ret hs one => s!"(PStmt.ret {pHints hs} {one})"
  | .halt hs one dest => s!"(PStmt.halt {pHints hs} {one} {dest})"

/-- A trie's entries, by key. -/
partial def trieEntries {α : Type} (t : Trie α) : List (Nat × α) :=
  go t id
where
  go (t : Trie α) (f : Nat → Nat) : List (Nat × α) :=
    match t with
    | .nil => []
    | .node v l r =>
        (match v with
          | some a => [(f 0, a)]
          | none => []) ++ go l (fun m => f (2 * m + 1)) ++ go r (fun m => f (2 * m + 2))

/-- The entries `new` adds to `old`, in the order of insertion: each bucket only grows at its
front. -/
def kmapDelta {κ α : Type} (old new : KMap κ α) : Except String (List (κ × α)) := do
  let mut out : Array (κ × α) := #[]
  for (k, nb) in trieEntries new.t do
    let ob := (old.t.getC k).getD []
    unless ob.length ≤ nb.length do throw "a bucket shrank"
    out := out ++ (nb.take (nb.length - ob.length)).reverse.toArray
  for (k, ob) in trieEntries old.t do
    if (new.t.getC k).isNone && !ob.isEmpty then throw "a bucket went away"
  return out.toList

/-- The entries of `new` other than `old`'s. -/
def nmapDelta {α : Type} [BEq α] (old new : NMap α) : Except String (List (Nat × α)) := do
  for (k, _) in trieEntries old.t do
    if (new.t.getC k).isNone then throw "an entry went away"
  return (trieEntries new.t).filter fun (k, a) => old.t.getC k != some a

/-- The entries of `new` other than `old`'s. -/
def pmapDelta {α : Type} [BEq α] (old new : PMap α) : Except String (List ((Nat × Nat) × α)) := do
  let entries (m : PMap α) := (trieEntries m.t).flatMap fun (k1, inner) =>
    (trieEntries inner).map fun (k2, a) => ((k1, k2), a)
  for (k, _) in entries old do
    if (new.get? k).isNone then throw "an entry went away"
  return (entries new).filter fun (k, a) => old.get? k != some a

/-- A cut function's walk: the cuts, the states there, and the state at its end. -/
structure CutPlan where
  ks : List Nat
  states : List St
  final : St

/-- Function `tf`'s walk from the jump tables `t`, cut between top-level statements once the
statements since the last cut make `cutSize` instructions, never inside a chain of `match`es. -/
def planCuts (loops : Loops) (sigs : SMap (Nat × Nat)) (t : Tables) (tf : TracedFn)
    (target : Nat := cutSize) : Except String CutPlan := do
  let ctx := ctxOf loops sigs tf
  let ((), st0) ← placeParams tf ctx (initSt loops t tf)
  let body := tf.core.body
  let mut st := st0
  let mut acc := 0
  let mut size := 0
  let mut ks : Array Nat := #[]
  let mut sts : Array St := #[]
  for i in List.range body.length do
    let ((), st') ← placeBlockN (body.drop i) 1 ctx st
    let size' := blockSize st'.out.toList
    acc := acc + (size' - size)
    size := size'
    st := st'
    if target ≤ acc && st.chainIn.isNone && i + 1 < body.length then
      ks := ks.push (i + 1)
      sts := sts.push st
      acc := 0
  let (some k, some sk) := (ks.back?, sts.back?) | throw s!"{tf.core.name}: no cut"
  let ((), fin) ← placeTail tf k ctx sk
  return ⟨ks.toList, sts.toList, fin⟩

/-- The term of state `st`, written as `prev` (the state `prevSt`) with what it adds; its lists are
the definitions `{name}_…`, returned with it. -/
def stateDef (j : Nat) (name prev : String) (prevSt st : St) (traceSize : Nat) :
    Except String String := do
  let locs ← kmapDelta prevSt.locs st.locs
  let consts ← kmapDelta prevSt.constOf st.constOf
  let pc ← pmapDelta prevSt.scope.consts st.scope.consts
  let px ← pmapDelta prevSt.scope.xors st.scope.xors
  let pm ← pmapDelta prevSt.scope.muls st.scope.muls
  let pl ← pmapDelta prevSt.scope.loads st.scope.loads
  let mats ← nmapDelta prevSt.scope.mats st.scope.mats
  unless prevSt.out.size ≤ st.out.size do throw "the statements shrank"
  let out := st.out.toList.drop prevSt.out.size
  let fresh := st.tables.shared.length - prevSt.tables.shared.length
  let pPool (l : List ((Nat × Nat) × Nat)) := l.map fun (k, c) => s!"({pPair k}, {c})"
  let defs :=
    chunkedDefs "Values placed." s!"{name}_locs" "(V × Loc)" (locs.map fun (v, l) => s!"({pV v}, {pLoc l})") ++
    chunkedDefs "Constants set." s!"{name}_consts" "(V × (Nat × Nat))"
      (consts.map fun (v, k) => s!"({pV v}, {pPair k})") ++
    chunkedDefs "Statements placed." s!"{name}_out" "PStmt" (out.map pPStmt) ++
    chunkedDefs "Pooled constants." s!"{name}_pc" "((Nat × Nat) × Nat)" (pPool pc) ++
    chunkedDefs "Pooled sums." s!"{name}_px" "((Nat × Nat) × Nat)" (pPool px) ++
    chunkedDefs "Pooled products." s!"{name}_pm" "((Nat × Nat) × Nat)" (pPool pm) ++
    chunkedDefs "Pooled loads." s!"{name}_pl" "((Nat × Nat) × Nat)" (pPool pl) ++
    chunkedDefs "Shifted pointers." s!"{name}_mats" "(Nat × List (Nat × Nat))"
      (mats.map fun (k, l) => s!"({k}, {pList (l.map pPair)})")
  let sh := (st.tables.shared.take fresh).map fun (cs, n) => s!"({pStrs cs}, {n})"
  let pVOpt (o : Option (List V)) := pOpt (fun vs => pList (vs.map pV)) o
  return defs ++
    s!"/-- The walk's state at a cut. -/\nnoncomputable def {name} : St :=\n" ++
    s!"  \{ next := {st.next},\n" ++
    s!"    locs := ({prev}).locs.insertAll {name}_locs,\n" ++
    s!"    scope :=\n      \{ consts := ({prev}).scope.consts.insertAll {name}_pc,\n" ++
    s!"        xors := ({prev}).scope.xors.insertAll {name}_px,\n" ++
    s!"        muls := ({prev}).scope.muls.insertAll {name}_pm,\n" ++
    s!"        loads := ({prev}).scope.loads.insertAll {name}_pl,\n" ++
    s!"        mats := ({prev}).scope.mats.insertAll {name}_mats,\n" ++
    s!"        selfFp := {pOpt toString st.scope.selfFp} },\n" ++
    s!"    pending := #{pList (st.pending.toList.map pLHint)},\n" ++
    s!"    out := ({prev}).out.appendList {name}_out,\n" ++
    s!"    tables := \{ len := {st.tables.len}, shared := {pList sh} ++ ({prev}).tables.shared },\n" ++
    s!"    rest := (guestTraced.getD {j} default).trace.toList.drop {traceSize - st.rest.length},\n" ++
    s!"    lazy := {pOpt (fun (v, k) => s!"({pV v}, {pKind k})") st.lazy},\n" ++
    s!"    used := {pList (st.used.map pV)},\n" ++
    s!"    shift := {pOpt (fun (v, e) => s!"({pV v}, {e})") st.shift},\n" ++
    s!"    chain := {st.chain},\n" ++
    s!"    note := {st.note},\n" ++
    s!"    chainIn := {pOpt pPair st.chainIn},\n" ++
    s!"    padRun := {pVOpt st.padRun},\n" ++
    s!"    aliasRun := {pVOpt st.aliasRun},\n" ++
    s!"    constOf := ({prev}).constOf.insertAll {name}_consts }\n\n"

/-- A cut piece's checks are grouped in modules of this many declarations. -/
def cutGroup : Nat := 3

def cutHeader (mod what : String) (imports : String) : String :=
  header mod what ++ "\nmodule\n\n" ++ imports ++ "public meta import LeanVM.Guest.KernelLit\n\n" ++
    "set_option Elab.async false\nset_option maxRecDepth 100000\nset_option linter.all false\n\n" ++
    "namespace LeanVM.Guest.Backend.GuestPiece\n\nopen LeanVM.Guest.Core LeanVM.Guest.Backend\n\n@[expose] public section\n\n"

/-- Function `j`'s cut piece: the module of its walk's states (`C{j}.lean`), the modules of its
checks (`C{j}P{m}.lean`), and the theorem gluing them (in `Compiled.lean`). With `limit`, its first
`limit` states and the walk to the last of them only, for measuring. -/
def cutFiles (j : Nat) (tf : TracedFn) (t : Tables) (loops : Loops) (plan : CutPlan) (chunks : Nat)
    (extra : Option Extra) (limit : Option Nat := none) :
    Except String (List (String × String) × String) := do
  let tfT := s!"(guestTraced.getD {j} default)"
  let ctxT := s!"(ctxOf loopsG sigsG {tfT})"
  let initT := s!"(initSt loopsG (tablesAt outsG {j}) {tfT})"
  let st0 := initSt loops t tf
  let states := match limit with
    | some n => plan.states.take n
    | none => plan.states
  let names := (List.range states.length).map fun i => s!"cut{j}_{i + 1}"
  let mut defs := ""
  let mut prev := initT
  let mut prevSt := st0
  for (st, nm) in states.zip names do
    defs := defs ++ (← stateDef j nm prev prevSt st tf.trace.size)
    prev := nm
    prevSt := st
  if limit.isNone then
    defs := defs ++ (← stateDef j s!"cut{j}_end" prev prevSt plan.final tf.trace.size)
  let ks := plan.ks
  let mut checks : Array String := #[]
  if limit.isNone || states.length == 1 then
    checks := checks.push s!"kernel_rfl cut{j}_seg0 :\n    placeHead {tfT} {ks.headD 0} {ctxT} {initT} = .ok ((), cut{j}_1)\n\n"
  for i in (List.range (states.length - 1)).filter fun i => limit.isNone || i + 2 == states.length do
    let a := ks.getD i 0
    let b := ks.getD (i + 1) 0
    checks := checks.push s!"kernel_rfl cut{j}_seg{i + 1} :\n    placeBlockN ({tfT}.core.body.drop {a}) {b - a} {ctxT} cut{j}_{i + 1} =\n      .ok ((), cut{j}_{i + 2})\n\n"
  let statesImports := "public import LeanVM.Guest.Backend.Guest.Piece.Layout\npublic import LeanVM.Guest.Backend.Cut\n"
  if let some _ := limit then
    return ([("", cutHeader s!"LeanVM.Scratch.Cut{j}" "A measurement of some of a function's cut parts."
      statesImports ++ defs ++ String.join checks.toList ++ "end\nend LeanVM.Guest.Backend.GuestPiece\n")], "")
  checks := checks.push s!"kernel_rfl cut{j}_tail :\n    placeTail {tfT} {ks.getLastD 0} {ctxT} cut{j}_{ks.length} = .ok ((), cut{j}_end)\n\n"
  checks := checks.push s!"theorem cut{j}_head : cutHeadAt loopsG guestTraced outsG Data.functions.tail {j} cut{j}_end = true := by\n  decide +kernel\n\n"
  for c in List.range chunks do
    checks := checks.push s!"theorem cut{j}_chunk{c} :\n    cutChunkAt layG guestTraced outsG Data.functions.tail {j} cut{j}_end {c} = true := by\n  decide +kernel\n\n"
  if let some x := extra then
    checks := checks.push s!"theorem cut{j}_extra : {x.name} {j} (placedOf {tfT} cut{j}_end).1.locs = true := by\n  decide +kernel\n\n"
  let walk := (List.range (ks.length - 1)).foldl (fun acc i => s!"(placeHead_add {acc} cut{j}_seg{i + 1})") s!"cut{j}_seg0"
  let pat := " | ".intercalate ((List.range chunks).map fun _ => "_") ++ " | c"
  let piece := s!"/-- **The piece of function {j}** (`{tf.core.name}`), from its parts. -/\n" ++
    (match extra with
      | some x => s!"theorem piece_{j} : pieceAtWith {x.name} {pieceArgs} {j} = true :=\n" ++
          s!"  pieceAtWith_of_cut {walk}\n    cut{j}_tail cut{j}_head cut{j}_extra fun c hc => by\n"
      | none => s!"theorem piece_{j} : pieceAt {pieceArgs} {j} = true :=\n" ++
          s!"  pieceAt_of_cut {walk}\n    cut{j}_tail cut{j}_head fun c hc => by\n") ++
    s!"      have hn : (Data.functions.tail.getD {j} noFunction).chunks.length = {chunks} := rfl\n      rw [hn] at hc\n" ++
    s!"      rcases c with {pat}\n" ++
    s!"      exacts [{", ".intercalate ((List.range chunks).map fun c => s!"cut{j}_chunk{c}")}, absurd hc (by omega)]\n\n"
  let statesFile := cutHeader s!"LeanVM.Guest.Backend.Guest.Piece.C{j}"
    s!"The states of the walk of `{tf.core.name}` at its cuts between top-level statements."
    statesImports ++ defs ++ "end\nend LeanVM.Guest.Backend.GuestPiece\n"
  let groups := (List.range ((checks.size + cutGroup - 1) / cutGroup)).map fun m =>
    (checks.toList.drop (m * cutGroup)).take cutGroup
  let checkFiles := groups.zipIdx.map fun (g, m) =>
    (s!"C{j}P{m}.lean", cutHeader s!"LeanVM.Guest.Backend.Guest.Piece.C{j}P{m}"
      s!"The kernel's checks of some of the parts of the piece of `{tf.core.name}`."
      (s!"public import LeanVM.Guest.Backend.Guest.Piece.C{j}\npublic import Statement.Data.Bytecode\n" ++
        (match extra with | some x => s!"public import {x.mod}\n" | none => "")) ++
      String.join g ++ "end\nend LeanVM.Guest.Backend.GuestPiece\n")
  return ((s!"C{j}.lean", statesFile) :: checkFiles, piece)

/-! ## Native checks -/

/-- Every check the kernel makes, natively: the pieces, `__jump_tables`' chunks, the program's checks,
the slots and the size. -/
def nativeCheck (P : List TracedFn) (outs : List FnOut) (big : List Nat) : IO Bool := do
  let loops := loopTable P
  let sigs := sigTable P
  let l := layoutInfo (infoOfOuts P outs) (baseOf outs)
  let cfs := Data.functions.tail
  let mut ok := true
  for j in List.range P.length do
    unless big.contains j || pieceAt loops sigs l P outs cfs j do
      IO.eprintln s!"the piece of function {j} ({(P.getD j default).core.name}) fails"
      ok := false
  let slots := slotsOfOuts P outs
  let f0 := Data.functions.headD noFunction
  unless jtHead slots f0 && (List.range f0.chunks.length).all fun c =>
      (List.range jtParts).all (jtPartOk l (baseOf outs) slots f0 c) do
    IO.eprintln "a chunk of __jump_tables differs"
    ok := false
  unless progChecks P loops && slotsOk outs && (tablesEnd outs).len != 0 && outs.length == P.length &&
      nextPow2 ((tablesEnd outs).len + (outs.map (·.size)).sum + 1) == 2 ^ Data.logSize do
    IO.eprintln "a check of the program, its slots or its size fails"
    ok := false
  return ok

/-- Every file, by its path. -/
def files (P : List TracedFn) (outs : List FnOut) (extra : Option Extra) :
    Except String (List (System.FilePath × String) × List Nat) := do
  let sizes := outs.map (·.size)
  let names := P.map (·.core.name)
  let (rs, big0) := ranges sizes fun j => bigNames.contains (names.getD j "")
  let cutJs := big0.filter fun j => cutNames.contains (names.getD j "")
  let big := big0.filter fun j => !cutJs.contains j
  let mods := modules sizes rs
  let jts := (Data.functions.headD noFunction).chunks.length
  let mut out : Array (System.FilePath × String) := #[]
  out := out.push (pieceDir / "Outs.lean", outsFile outs)
  let loops := loopTable P
  out := out.push (pieceDir / "Tables.lean", tablesFile loops (sigTable P))
  out := out.push (pieceDir / "Layout.lean",
    layoutFile (layoutInfo (infoOfOuts P outs) (baseOf outs)) (slotsOfOuts P outs))
  out := out.push (pieceDir / "Checks.lean", checksFile Data.logSize)
  out := out.push (pieceDir / "Names.lean", namesFile)
  for (m, k) in mods.zipIdx do
    out := out.push (pieceDir / s!"P{k}.lean", pieceFile k m names sizes extra)
  for c in List.range jts do
    out := out.push (pieceDir / s!"Jt{c}.lean", jtFile c)
  let mut cuts : Array (Nat × String × Nat) := #[]
  for j in cutJs do
    let tf := P.getD j default
    let plan ← planCuts loops (sigTable P) (tablesAt outs j) tf
    let chunks := (Data.functions.tail.getD j noFunction).chunks.length
    let (fs, piece) ← cutFiles j tf (tablesAt outs j) loops plan chunks extra
    for (n, text) in fs do out := out.push (pieceDir / n, text)
    cuts := cuts.push (j, piece, fs.length - 1)
  out := out.push (compiledPath, compiledFile P.length rs big cuts.toList mods.length jts extra)
  return (out.toList, big)

end GuestPieces

open GuestPieces in
def main (args : List String) : IO UInt32 := do
  let (test, check, extra) ← match args with
    | [] => pure (false, false, none)
    | ["--check"] => pure (false, true, none)
    | ["test"] => pure (true, false, none)
    | ["test", "--check"] => pure (true, true, none)
    | ["--extra", n, m] => pure (false, false, some (⟨n, m⟩ : Extra))
    | ["--check", "--extra", n, m] => pure (false, true, some ⟨n, m⟩)
    | ["cut", j, size, n, path] =>
        -- Some cut parts of function `j`, for measuring: its first `n` cuts, at `size` instructions.
        let P ← input
        let outs ← orThrow (outsOf P)
        let j := j.toNat!
        let tf := P.getD j default
        let plan ← orThrow (planCuts (loopTable P) (sigTable P) (tablesAt outs j) tf size.toNat!)
        IO.println s!"{tf.core.name}: cuts {plan.ks} at instructions {plan.states.map fun st => blockSize st.out.toList}, events {plan.states.map fun st => tf.trace.size - st.rest.length} of {tf.trace.size}, locs {plan.states.map fun st => (trieEntries st.locs.t).length}"
        let (fs, _) ← orThrow (cutFiles j tf (tablesAt outs j) (loopTable P) plan 0 none (some n.toNat!))
        IO.FS.writeFile path ((fs.headD ("", "")).2)
        return 0
    | _ =>
        IO.eprintln "usage: guest-pieces [--check] [--extra NAME MODULE] | guest-pieces test [--check]"
        return 2
  unless ← pieceDir.parent.getD "." |>.isDir do
    IO.eprintln "run from lean_vm"
    return 2
  let fs ← if test then
      pure [(testPath, ← testFile "match_arms")]
    else
      let P ← input
      let outs ← orThrow (outsOf P)
      let (fs, big) ← orThrow (files P outs extra)
      unless ← nativeCheck P outs big do return 1
      let n := (outs.map (·.size)).sum
      let nb := ((big.map fun j => outs.getD j default).map (·.size)).sum
      IO.println s!"{P.length} functions, {n} instructions; pieces of {P.length - big.length} functions, \
        {n - nb} instructions; {big.length} functions not written ({nb} instructions): \
        {big.map fun j => (j, (P.getD j default).core.name, (outs.getD j default).size)}"
      pure fs
  let mut bad := false
  if !test then
    let existing ← if ← pieceDir.isDir then
        pure <| (← pieceDir.readDir).toList.filterMap fun e =>
          if e.fileName.endsWith ".lean" then some (pieceDir / e.fileName) else none
      else pure []
    for p in existing.filter fun p => !(fs.map (·.1)).contains p do
      if check then
        IO.eprintln s!"{p} is not generated"
        bad := true
      else IO.FS.removeFile p
  for (path, text) in fs do
    let old ← if ← path.pathExists then IO.FS.readFile path else pure ""
    if old != text then
      if check then
        IO.eprintln s!"{path} is stale: run `lake exe guest-pieces{if test then " test" else ""}`"
        bad := true
      else
        if let some dir := path.parent then IO.FS.createDirAll dir
        IO.FS.writeFile path text
  unless check do IO.println s!"wrote {fs.length} files"
  return if bad then 1 else 0
