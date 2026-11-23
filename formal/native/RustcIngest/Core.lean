module

public import Lean
public import Kraken.Layout

/-!
# Ingestion of rustc's assembly, for any architecture

The elaboration commands in `RustcIngest.Arm` and `RustcIngest.X64` parse committed assembly
and elaborate these generated declarations while the native proofs build. The architecture adapters
are separate because Kraken's AArch64 and x86-64 declare the same root names.

For each scheme, the core functions are those reachable from its entry (`<scheme>_verify`, or
`leanvm_verify` for `vm`) by calls, jumps and references to other functions, without entering the two
panic entries of `core` (`isPanic`). Each has a Lean name: the signature verifiers' functions by
`shortName`, the others by `rustc/ingest/vm-names.txt` (a line `<symbol> <Name>` each). A
function of rustc's assembly starts at `name:` followed by `.Lfunc_begin<n>:` and ends at
`.Lfunc_end<n>:`. Its text keeps instructions and labels, and the directives inside it the
architecture keeps (`Arch.bodyDirective`: x86-64's loop alignment); its local labels are renamed after
the function (`.LBB<n>_<b>` to `.L<Fn>_<b>`, `.Ltmp<k>` to `.L<Fn>_tmp<k>` when an instruction refers
to it, otherwise dropped, as is `.Lfunc_begin<n>`), so that a function rustc emits identically for two
schemes ingests identically. Such a function is written once, under `Common/`, and the ingestion fails
if two schemes' functions of one name differ.

Each function is split into basic blocks: one starts at each label (unless the block so far holds
labels only) and after each branch, call or return. A function's module holds its blocks
`b0`, `b1`, ... (big functions spread their blocks over `Part<i>` modules),
`code := List.flatten [b0, b1, ...]` and each block's index in it (`b<k>_in_code`). A scheme's module
holds `traps` (each panic entry the core calls, as its label and the bytes of a trap instruction),
`rodata` (each data label the core refers to, directly or through data words, in the assembly's
order, with its bytes and data words as the assembly gives them) and
`code := List.flatten [<core functions' code, in the assembly's order>, traps, rodata]`; its `Offsets`
module gives each function's and each block's index in `code`, its `Labels` module each label's.
The separate `Align` module records data-section alignment for the printers only; proofs do not import it.
Each function's `Names` child contains only its symbol strings. Its parent owns named block offsets,
lengths, ends, adjacency facts and every retained label's lookup fact. Scheme-qualified
`programOffset` definitions live in `Offsets`, not in function modules; scheme `Names` modules own
trap and data symbols.
Symbol declarations are abbreviations so rewriting can match the literal operands in generated instructions.
Instruction slices and the naming table remain separate from this metadata.
Every number is written with its type and every constant fully qualified and fully applied, so that
the terms elaborate the same whatever the expected type. Lemmas are proved by `decide +kernel`.
-/

open Lean

namespace Ingest

@[expose] public section

/-! ## Text utilities -/

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '$'

def trimStr (s : String) : String := s.trimAscii.toString

/-- The line without a trailing comment starting with `marker`. -/
def stripComment (marker s : String) : String :=
  match s.splitOn marker with
  | [] => ""
  | c :: _ => c

/-- `s` with every token `t` (a maximal run of identifier characters starting with `.L`) replaced
by `f t`. -/
def mapLocalTokens (f : String → String) (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let prevIdent := i > 0 && isIdentChar cs[i-1]!
    if !prevIdent && c == '.' && i + 1 < cs.size && cs[i+1]! == 'L' then
      let mut j := i
      while j < cs.size && isIdentChar cs[j]! do j := j + 1
      let tok := String.ofList (cs.extract i j).toList
      out := out ++ (f tok).toList.toArray
      i := j
    else
      out := out.push c
      i := i + 1
  return String.ofList out.toList

/-- The tokens starting with `.L` in `s`. -/
def localTokens (s : String) : Array String := Id.run do
  let mut acc := #[]
  let cs := s.toList.toArray
  let mut i := 0
  while i < cs.size do
    let prevIdent := i > 0 && isIdentChar cs[i-1]!
    if !prevIdent && cs[i]! == '.' && i + 1 < cs.size && cs[i+1]! == 'L' then
      let mut j := i
      while j < cs.size && isIdentChar cs[j]! do j := j + 1
      acc := acc.push (String.ofList (cs.extract i j).toList)
      i := j
    else
      i := i + 1
  return acc

/-- The label a line `name:` defines. -/
def labelOf? (line : String) : Option String :=
  let t := trimStr line
  if t.endsWith ":" && !t.isEmpty && (t.dropEnd 1).toString.all (fun c => isIdentChar c) then
    some (t.dropEnd 1).toString
  else none

/-! ## The assembly file -/

/-- A function of the assembly: its name and the lines from `name:` (included) to `.Lfunc_end<n>:`
(excluded). -/
structure AsmFn where
  name : String
  index : Nat
  lines : Array String

/-- The functions of rustc's assembly, in order. -/
def functions (ls : Array String) : Except String (Array AsmFn) := do
  let mut fns := #[]
  let mut i := 0
  while i + 1 < ls.size do
    match labelOf? ls[i]!, labelOf? ls[i+1]! with
    | some name, some begin =>
      if begin.startsWith ".Lfunc_begin" then
        let n := (begin.drop ".Lfunc_begin".length).toString
        let endLabel := s!".Lfunc_end{n}:"
        let mut j := i + 2
        while j < ls.size && trimStr ls[j]! != endLabel do j := j + 1
        if j == ls.size then throw s!"{name}: no {endLabel}"
        fns := fns.push { name, index := n.toNat!, lines := ls.extract i j }
        i := j
      else i := i + 1
    | _, _ => i := i + 1
  return fns

/-- The data items of the assembly: each label of a data section, with its line and the directives
after it up to its `.size`. -/
def dataItems (ls : Array String) : Std.HashMap String (Nat × Array String) := Id.run do
  let mut m := {}
  let mut i := 0
  while i < ls.size do
    match labelOf? ls[i]! with
    | some l =>
      if l.startsWith ".L" && !l.startsWith ".LBB" && !l.startsWith ".Ltmp" && !l.startsWith ".Lfunc" then
        let mut j := i + 1
        let mut body := #[]
        while j < ls.size && !(trimStr ls[j]!).startsWith ".size" do
          body := body.push (trimStr ls[j]!)
          j := j + 1
        m := m.insert l (i, body)
        i := j
      else i := i + 1
    | none => i := i + 1
  return m

/-- The data section's alignment directives before its label. -/
def dataAlignment (ls : Array String) (pos : Nat) : Except String Nat := do
  let mut i := pos
  let mut alignment := 0
  while i > 0 do
    i := i - 1
    let line := trimStr ls[i]!
    if line.startsWith ".section" then return alignment
    if line.startsWith ".p2align" then
      let arg := trimStr (stripComment "," (line.drop ".p2align".length).toString)
      let some k := arg.toNat? | throw s!"bad data alignment: {line}"
      alignment := max alignment k
  throw s!"data label at line {pos + 1} has no section"

/-! ## Data directives -/

/-- A data item's contents: bytes, and data words naming a label. -/
inductive Datum
  | bytes (bs : Array UInt8)
  | word (size : Nat) (label : String)

/-- The most bytes of one `.byteArray` directive. -/
def bytesChunk : Nat := 256

/-- The bytes of a GNU assembler string literal (without its quotes). -/
def unescape (s : String) : Except String (Array UInt8) := do
  let cs := s.toList.toArray
  let mut out : Array UInt8 := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '\\' then
      let d := cs[i+1]!
      if d.isDigit then
        let mut v := 0
        let mut j := i + 1
        while j < cs.size && j < i + 4 && cs[j]!.isDigit do
          v := v * 8 + (cs[j]!.toNat - '0'.toNat)
          j := j + 1
        out := out.push v.toUInt8
        i := j
      else
        let b ← match d with
          | 'n' => pure 10 | 't' => pure 9 | 'r' => pure 13 | 'b' => pure 8 | 'f' => pure 12
          | '"' => pure 34 | '\\' => pure 92
          | _ => throw s!"unknown escape \\{d} in {s}"
        out := out.push b
        i := i + 2
    else
      if c.toNat ≥ 128 then throw s!"non-ASCII character in {s}"
      out := out.push c.toNat.toUInt8
      i := i + 1
  return out

/-- The contents a data item's directives give; `dataSize` gives the size of a data word directive. -/
def parseData (dataSize : String → Option Nat) (label : String) (body : Array String) :
    Except String (Array Datum) := do
  let mut out : Array Datum := #[]
  for line in body do
    let line := line.replace "\t" " "
    let (dir, arg) := match line.splitOn " " with
      | d :: rest => (d, trimStr (" ".intercalate rest))
      | [] => ("", "")
    match dir, dataSize dir with
    | ".p2align", _ | ".type", _ | ".section", _ | "", _ => pure ()
    | ".ascii", _ | ".asciz", _ =>
      unless arg.startsWith "\"" && arg.endsWith "\"" do throw s!"{label}: bad string {arg}"
      let bs ← unescape ((arg.drop 1).dropEnd 1).toString
      out := out.push (.bytes (if dir == ".asciz" then bs.push 0 else bs))
    | ".zero", _ =>
      let some n := arg.toNat? | throw s!"{label}: bad .zero {arg}"
      out := out.push (.bytes (Array.replicate n 0))
    | _, some size =>
      if arg.startsWith ".L" || (arg.front.isAlpha || arg.front == '_') then
        out := out.push (.word size arg)
      else
        let some v := arg.toInt? | throw s!"{label}: bad number {arg}"
        let v := (v % (2 ^ (8 * size) : Int)).toNat -- two's complement
        out := out.push (.bytes ((List.range size).toArray.map fun k => (v / 2 ^ (8 * k) % 256).toUInt8))
    | _, none => throw s!"{label}: unsupported data directive {line}"
  -- Merge adjacent bytes, then cut them in runs of at most `bytesChunk` (a longer array literal exceeds the
  -- elaborator's recursion depth).
  let mut merged : Array Datum := #[]
  for d in out do
    match merged.back?, d with
    | some (.bytes a), .bytes b => merged := merged.pop.push (.bytes (a ++ b))
    | _, _ => merged := merged.push d
  return merged.flatMap fun
    | .bytes bs => ((List.range ((bs.size + bytesChunk - 1) / bytesChunk)).map fun k =>
        Datum.bytes (bs.extract (k * bytesChunk) ((k + 1) * bytesChunk))).toArray
    | d => #[d]

/-! ## Lean terms as source -/

/-- Whether the constant `n` has an implicit or instance argument among its first `k`. -/
def hasImplicit (env : Environment) (n : Name) (k : Nat) : Bool :=
  match env.find? n with
  | none => true
  | some ci => go ci.type k
where
  go : Expr → Nat → Bool
    | .forallE _ _ b bi, k + 1 => !bi.isExplicit || go b k
    | _, _ => false

/-- An integer literal of type `ty`, from `toExpr`'s `OfNat.ofNat ty n _` or `-(OfNat.ofNat ty n _)`. -/
def numLit? (e : Expr) : Option (Int × Expr) :=
  match e.getAppFn, e.getAppArgs with
  | .const ``OfNat.ofNat _, #[ty, .lit (.natVal n), _] => some (n, ty)
  | .const ``Neg.neg _, #[_, _, x] =>
    match x.getAppFn, x.getAppArgs with
    | .const ``OfNat.ofNat _, #[ty, .lit (.natVal n), _] => some (-n, ty)
    | _, _ => none
  | _, _ => none

/-- The source of a closed term `toExpr` builds from constructors, string and number literals: every
constant fully qualified and applied to all its arguments (`@` when some are implicit), every number
with its type, so that it elaborates the same whatever the expected type. -/
partial def termSrc (env : Environment) (e : Expr) : Except String String := do
  if let some (n, ty) := numLit? e then
    return s!"({n} : {← termSrc env ty})"
  match e with
  | .lit (.strVal s) => return s.quote
  | .lit (.natVal n) => return toString n
  | _ =>
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    let head := if hasImplicit env n args.size then s!"@{n}" else toString n
    if args.isEmpty then return head
    let srcs ← args.mapM (termSrc env)
    return s!"({head} {" ".intercalate srcs.toList})"
  | _ => throw s!"unexpected term {e}"

/-- The string literals of a term: in Kraken's syntax, the labels it names. -/
partial def labelsIn (e : Expr) : Array String :=
  match e with
  | .lit (.strVal s) => #[s]
  | _ => e.getAppArgs.foldl (fun acc a => acc ++ labelsIn a) #[]

/-! ## Architectures -/

/-- What ingestion needs to know of an architecture whose Kraken directives are
`Kraken.Directive I C`. -/
structure Arch (I C : Type) where
  /-- The Lean namespace and module prefix of its ingested code. -/
  ns : String
  /-- Whether to emit `Labels`; VM proofs instead use their distinct-label placement lemmas. -/
  labels : Bool := true
  /-- The module of Kraken's syntax the generated modules import. -/
  syntaxModule : String
  /-- The module of the `List.IsInfixAt` lemmas the generated proofs use. -/
  infixModule : String
  /-- Kraken's parser. -/
  parse : String → IO (List (Kraken.Directive I C))
  /-- A label as a constant. -/
  labelConst : String → C
  /-- Whether an instruction ends a basic block: a branch, a call or a return. -/
  endsBlock : I → Bool
  /-- The marker of a comment to the end of the line. -/
  comment : String
  /-- A directive line inside a function: dropped (`none`), or kept as the given line. -/
  bodyDirective : String → Except String (Option String)
  /-- An instruction whose label operand `l` stands for `l + c`, `c` the addend its line wrote after the
  label (`adrp x0, l+8`, which Kraken's parser does not read): Kraken's term for `l + c` in place of `l`. -/
  addend : I → Int → Except String I := fun _ _ => throw "a label with an addend"
  /-- The bytes of the trap a panic entry is replaced with, and its assembly. -/
  trap : Array UInt8
  trapAsm : String
  /-- The size of the data a data word directive gives, and the directive of a size. -/
  dataSize : String → Option Nat
  wordDirective : Nat → String

/-- The panic entries of `core` (their crate hash differs between targets): the core calls them,
the ingested program traps there. -/
def panicSuffixes : List String := ["9panicking9panic_fmt", "5slice5index16slice_index_fail",
  "6option13unwrap_failed"]

def isPanic (sym : String) : Bool := panicSuffixes.any fun p => sym.endsWith p

/-- The Lean name of each core function and panic entry. -/
def shortName (sym : String) : Option String :=
  if sym == "memcpy" then some "Memcpy"
  else if sym == "memset" then some "Memset"
  else if sym.endsWith "9panicking9panic_fmt" then some "PanicFmt"
  else if sym.endsWith "5index16slice_index_fail" then some "SliceIndexFail"
  else if sym.endsWith "6option13unwrap_failed" then some "UnwrapFailed"
  else if sym == "xmss_verify" then some "XmssVerify"
  else if sym == "sphincs_verify" then some "SphincsVerify"
  else if sym.endsWith "9keccak2568keccak_f" then some "KeccakF"
  else if sym.endsWith "6Hasher6update" then some "Update"
  else if sym.endsWith "6Hasher8finalize" then some "Finalize"
  else if sym.endsWith "4wots9wots_leaf" then some "WotsLeaf"
  else if sym.endsWith "14LayerSignature4read" then some "LayerRead"
  else none

/-- A scheme's entry: `leanvm_verify` for `vm`, else `<scheme>_verify`. -/
def entryOf (scheme : String) : String :=
  if scheme == "vm" then "leanvm_verify" else s!"{scheme}_verify"

/-- `Xmss` for `xmss`. -/
def capitalize (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

variable {I C : Type} [ToExpr I] [ToExpr C] [BEq I] [BEq C]

/-! ## Functions -/

/-- A core function, ingested. -/
structure Fn (I C : Type) where
  sym : String
  short : String
  /-- The assembly of each directive (renamed), aligned with `prog`. -/
  lines : Array String
  prog : Array (Kraken.Directive I C)
  /-- The source of each directive. -/
  srcs : Array String

/-- The lines of a function's text: instructions, labels and the directives the architecture keeps,
local labels renamed. -/
def cleanLines (arch : Arch I C) (f : AsmFn) (short : String) : Except String (Array String) := do
  let mut kept : Array String := #[]
  for raw in f.lines do
    let l := (trimStr (stripComment arch.comment raw)).replace "\t" " "
    if l.isEmpty then continue
    if l.startsWith "." && labelOf? l == none then
      match ← arch.bodyDirective l with
      | some l' => kept := kept.push l'
      | none => pure ()
      continue
    kept := kept.push l
  -- Local labels and the tokens instructions refer to.
  let defined := kept.filterMap labelOf? |>.filter (·.startsWith ".L")
  let referenced := kept.filter (labelOf? · == none) |>.flatMap localTokens
  let mut rename : Std.HashMap String String := {}
  let mut drop : Std.HashSet String := {}
  for l in defined do
    let bb := s!".LBB{f.index}_"
    if l.startsWith bb then
      rename := rename.insert l s!".L{short}_{(l.drop bb.length).toString}"
    else if l.startsWith ".Ltmp" then
      if referenced.contains l then rename := rename.insert l s!".L{short}_tmp{(l.drop 5).toString}"
      else drop := drop.insert l
    else if l == s!".Lfunc_begin{f.index}" then
      if referenced.contains l then throw s!"{f.name}: refers to {l}"
      drop := drop.insert l
    else throw s!"{f.name}: unexpected local label {l}"
  let kept' := kept.filter fun l => match labelOf? l with
    | some lab => !drop.contains lab
    | none => true
  return kept'.map (mapLocalTokens fun t => rename.getD t t)

/-- A line ending in a label with an addend, `<…><label>+<c>`: the line without `+<c>`, and `c`. -/
def splitAddend (l : String) : Option (String × Int) :=
  match l.splitOn "+" with
  | [pre, post] =>
    if !post.isEmpty && post.all Char.isDigit && (pre.back.isAlphanum || pre.back == '_') then
      some (pre, post.toNat!)
    else none
  | _ => none

/-- Kraken's parse of a function's lines, one directive per line, each parsed on its own; a line
ending in a label with an addend parsed without it, and the addend put back (`Arch.addend`). -/
def parseLines (arch : Arch I C) (name : String) (lines : Array String) :
    IO (Array (Kraken.Directive I C)) :=
  lines.mapM fun l => do
    let (src, c) := match splitAddend l with
      | some (pre, c) => (pre, some c)
      | none => (l, none)
    let prog ← try arch.parse src
      catch e => throw <| IO.userError s!"{name}: {l}: {e}"
    match prog, c with
    | [d], none => pure d
    | [.instr i], some c => match arch.addend i c with
      | .ok i' => pure (.instr i')
      | .error e => throw <| IO.userError s!"{name}: {l}: {e}"
    | _, _ => throw <| IO.userError s!"{name}: {l}: {prog.length} directives"

/-- The source of a directive. -/
def directiveSrc (env : Environment) : Kraken.Directive I C → Except String String
  | .label l => pure s!"@Kraken.Directive.label Instr ConstExpr {l.quote}"
  | .instr i => return s!"@Kraken.Directive.instr Instr ConstExpr {← termSrc env (toExpr i)}"
  | .byteArray bs =>
    let elems := bs.toList.map fun b => s!"({b} : UInt8)"
    pure s!"@Kraken.Directive.byteArray Instr ConstExpr (ByteArray.mk #[{", ".intercalate elems}])"
  | .word n e => return s!"@Kraken.Directive.word Instr ConstExpr ({n} : Nat) {← termSrc env (toExpr e)}"

/-- The labels a directive refers to. -/
def referencedLabels : Kraken.Directive I C → Array String
  | .instr i => labelsIn (toExpr i)
  | .word _ e => labelsIn (toExpr e)
  | _ => #[]

/-- The basic blocks of a function: the index of each block's first directive. -/
def blockStarts (arch : Arch I C) (prog : Array (Kraken.Directive I C)) : Array Nat := Id.run do
  let mut starts := #[0]
  let mut hasInstr := false
  for h : k in [0:prog.size] do
    match prog[k] with
    | .label _ =>
      if hasInstr then
        starts := starts.push k
        hasInstr := false
    | .instr i =>
      hasInstr := true
      if arch.endsBlock i && k + 1 < prog.size then
        starts := starts.push (k + 1)
        hasInstr := false
    | _ => hasInstr := true
  return starts

/-! ## Schemes -/

/-- A scheme's ingested program. -/
structure Scheme (I C : Type) where
  name : String
  /-- Its core functions, in the assembly's order. -/
  fns : Array (Fn I C)
  /-- The panic entries it calls, in `panicSuffixes`' order. -/
  traps : Array String
  /-- Its data labels, in the assembly's order, with their contents. -/
  rodata : Array (String × Array Datum)
  /-- Data-section alignment exponents, kept outside the proof-facing program. -/
  alignments : Array (String × Nat)

/-- Parse one function using the same representation as whole-program ingestion. -/
def ingestFunction (arch : Arch I C) (env : Environment) (names : Std.HashMap String String)
    (f : AsmFn) : IO (Fn I C) := do
  let some short := names[f.name]? <|> shortName f.name
    | throw <| IO.userError s!"no Lean name for {f.name}"
  let lines ← IO.ofExcept (cleanLines arch f short)
  let prog ← parseLines arch f.name lines
  let srcs ← IO.ofExcept (prog.mapM (directiveSrc env))
  return { sym := f.name, short, lines, prog, srcs }

/-- Ingest a scheme's assembly. -/
def ingestScheme (arch : Arch I C) (env : Environment) (names : Std.HashMap String String)
    (scheme : String) (text : String) : IO (Scheme I C) := do
  let ls := (text.splitOn "\n").toArray
  let fns ← IO.ofExcept (functions ls)
  let byName : Std.HashMap String AsmFn := fns.foldl (fun m f => m.insert f.name f) {}
  let data := dataItems ls
  -- Reachability from the entry.
  let entry := entryOf scheme
  let mut todo := #[entry]
  let mut parsed : Std.HashMap String (Fn I C) := {}
  let mut called : Array String := #[]
  let mut dataRefs : Array String := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if parsed.contains name then continue
    if isPanic name then
      unless called.contains name do called := called.push name
      continue
    let some f := byName[name]? | throw <| IO.userError s!"{scheme}: no function {name}"
    let f ← ingestFunction arch env names f
    let localLabels := f.prog.filterMap fun | .label l => some l | _ => none
    for d in f.prog do
      for l in referencedLabels d do
        if localLabels.contains l then continue
        if isPanic l || byName.contains l then todo := todo.push l
        else if data.contains l then
          unless dataRefs.contains l do dataRefs := dataRefs.push l
        else throw <| IO.userError s!"{name}: unknown label {l}"
    parsed := parsed.insert name f
  -- The core in the assembly's order; the traps in `panicSuffixes`' order.
  let core := fns.filterMap fun f => parsed[f.name]?
  let traps := panicSuffixes.toArray.filterMap fun p => called.find? (·.endsWith p)
  -- Data, closed under the labels data words name, in the assembly's order.
  let mut rodata : Array (String × Array Datum) := #[]
  let mut i := 0
  while i < dataRefs.size do
    let l := dataRefs[i]!
    let items ← IO.ofExcept (parseData arch.dataSize l (data.getD l (0, #[])).2)
    for d in items do
      if let .word _ l' := d then
        unless data.contains l' do throw <| IO.userError s!"{l}: data word names {l'}, not data"
        unless dataRefs.contains l' do dataRefs := dataRefs.push l'
    rodata := rodata.push (l, items)
    i := i + 1
  let pos (l : String) : Nat := (data.getD l (0, #[])).1
  let rodata' := rodata.qsort fun a b => pos a.1 < pos b.1
  -- Short names are distinct.
  let shorts := core.map (·.short)
  unless shorts.toList.eraseDups.length == shorts.size do
    throw <| IO.userError s!"{scheme}: two core functions with one Lean name"
  let alignments ← rodata'.mapM fun (l, _) => do
    return (l, ← IO.ofExcept (dataAlignment ls (pos l)))
  return { name := scheme, fns := core, traps, rodata := rodata', alignments }

/-! ## Emission -/

def header (doc : String) (imports : List String) : String :=
  "module\n\n" ++ String.join (imports.map (s!"public import {·}\n")) ++
  s!"\n/-!\n{doc}\n-/\n\n"

/-- Elaborate kernel-checked lemmas sequentially to bound memory use. -/
def sequential : String :=
  "set_option Elab.async false\n\n"

/-- The source of a list literal of directives, one per line with its assembly as a comment. -/
def listSrc (items : Array (String × String)) : String := Id.run do
  if items.isEmpty then return "[]"
  let mut out := "[\n"
  for h : k in [0:items.size] do
    let (src, asm) := items[k]
    let sep := if k + 1 < items.size then "," else ""
    let cmt := if asm.isEmpty then "" else s!"  -- {asm.replace "\t" " "}"
    out := out ++ s!"  {src}{sep}{cmt}\n"
  return out ++ "]"

/-- Most directives of one data list in a long one: a list literal of many large data directives exceeds the
compiler's recursion depth. -/
def rodataChunk : Nat := 8

/-- The definition of `rodata`: one list literal of at most 32 directives, or else the lists `rodata<k>` of
`rodataChunk` each, flattened. -/
def rodataSrc (items : Array (String × String)) : String :=
  let doc := "/-- The data the core refers to, directly or through data words. -/\n"
  if items.size ≤ 32 then
    doc ++ s!"def rodata : List Directive := {listSrc items}\n\n"
  else
    let n := (items.size + rodataChunk - 1) / rodataChunk
    let parts := (List.range n).map fun k =>
      s!"/-- Directives {k * rodataChunk} to {min items.size ((k + 1) * rodataChunk) - 1} of `rodata`. -/\n" ++
      s!"def rodata{k} : List Directive := {listSrc (items.extract (k * rodataChunk) ((k + 1) * rodataChunk))}\n\n"
    String.join parts ++ doc ++
      s!"def rodata : List Directive := List.flatten [{", ".intercalate ((List.range n).map (s!"rodata{·}"))}]\n\n"

/-- Largest number of directives in one module of blocks. -/
def partSize : Nat := 500

/-- A file to write: its path relative to the output root and its contents. -/
abbrev File := String × String

def modPath (mod : String) : String := (mod.replace "." "/") ++ ".lean"

def fnLabelName (f : Fn I C) (l : String) : String :=
  if l == f.sym then "entryLabel" else
    let pre := s!".L{f.short}_"
    let suffix := if l.startsWith pre then (l.drop pre.length).toString
      else if l.startsWith ".L" then (l.drop 2).toString else l
    "label_" ++ String.ofList (suffix.toList.map fun c => if c.isAlphanum then c else '_')

def fnLabels (f : Fn I C) : Array (String × String × Nat) := Id.run do
  let mut labels := #[]
  for h : i in [0:f.prog.size] do
    if let .label l := f.prog[i] then
      labels := labels.push (fnLabelName f l, l, i)
  return labels

def labelOffsetName (name : String) : String :=
  if name == "entryLabel" then "entryOffset" else name ++ "Offset"

def labelFactName (name : String) : String :=
  if name == "entryLabel" then "entry_at" else name ++ "_at"

/-- The modules of a function in `dir` (`Common`, `Xmss`, ...): its blocks and `code`, with the
offset lemmas `b<k>_in_code`. Returns the files and the function's namespace. -/
def fnModules (arch : Arch I C) (dir : String) (f : Fn I C) : Array File × String := Id.run do
  let ns := s!"{arch.ns}.{dir}.{f.short}"
  let mod := s!"{arch.ns}.Code.{dir}.{f.short}"
  let starts := blockStarts arch f.prog
  let ends := (starts.toList.drop 1).toArray.push f.prog.size
  let blocks := (starts.zip ends)
  let blockDef (k : Nat) (s e : Nat) : String :=
    let items := (List.range (e - s)).toArray.map fun j =>
      (f.srcs[s + j]!, f.lines[s + j]!)
    let first := match f.prog[s]? with
      | some (.label l) => s!"Block {k}, at `{l}`."
      | _ => s!"Block {k}, after the branch or call ending block {k - 1}."
    s!"/-- {first} -/\ndef b{k} : List Directive := {listSrc items}\n\n"
  -- Group blocks into parts.
  let mut parts : Array (Array Nat) := #[#[]]
  let mut size := 0
  for h : k in [0:blocks.size] do
    let (s, e) := blocks[k]
    if size > 0 && size + (e - s) > partSize then
      parts := parts.push #[]
      size := 0
    parts := parts.modify (parts.size - 1) (·.push k)
    size := size + (e - s)
  let docFn := s!"`{f.sym}` as rustc compiles it"
  let labels := fnLabels f
  let namesMod := s!"{mod}.Names"
  let namesSrc := labels.foldl (fun acc (name, sym, _) =>
    acc ++ s!"abbrev {name} : String := {sym.quote}\n\n") ""
  let mut files : Array File := #[(modPath namesMod,
    header "Function symbols derived from committed rustc assembly." [] ++
    s!"namespace {ns}\n\n@[expose] public section\n\n" ++ namesSrc ++ s!"end\n\nend {ns}\n")]
  let mut imports : List String := [namesMod]
  let mut blockSrc := ""
  if parts.size > 1 then
    for h : p in [0:parts.size] do
      let pmod := s!"{mod}.Part{p}"
      let body := parts[p].foldl (fun acc k => acc ++ blockDef k blocks[k]!.1 blocks[k]!.2) ""
      let doc := s!"# {docFn}, blocks {parts[p][0]!} to {parts[p].back!}"
      files := files.push (modPath pmod,
        header doc [arch.syntaxModule] ++ s!"namespace {ns}\n\n@[expose] public section\n\n" ++ body ++
        s!"end\n\nend {ns}\n")
      imports := imports ++ [pmod]
  else
    blockSrc := (List.range blocks.size).foldl (fun acc k => acc ++ blockDef k blocks[k]!.1 blocks[k]!.2) ""
    imports := imports ++ [arch.syntaxModule]
  let names := (List.range blocks.size).map (s!"b{·}")
  let mut metadata := s!"def codeLength : Nat := {f.prog.size}\n\n"
  let mut lemmas := "public theorem code_length : code.length = codeLength := by decide +kernel\n\n"
  for h : k in [0:blocks.size] do
    let (s, e) := blocks[k]
    metadata := metadata ++ s!"def b{k}Offset : Nat := {s}\n\ndef b{k}Length : Nat := {e - s}\n\ndef b{k}End : Nat := {e}\n\n"
    lemmas := lemmas ++
      s!"public theorem b{k}_in_code : b{k}.IsInfixAt code b{k}Offset :=\n  List.isInfixAt_flatten_of (i := {k}) rfl (by decide +kernel)\n\n" ++
      s!"public theorem b{k}_length : b{k}.length = b{k}Length := by decide +kernel\n\n" ++
      s!"public theorem b{k}_end : b{k}Offset + b{k}.length = b{k}End := by decide +kernel\n\n"
    if k + 1 < blocks.size then
      lemmas := lemmas ++
        s!"public theorem b{k}_next : b{k}Offset + b{k}.length = b{k + 1}Offset := by decide +kernel\n\n"
  for (name, _, offset) in labels do
    let offsetName := labelOffsetName name
    metadata := metadata ++ s!"def {offsetName} : Nat := {offset}\n\n"
    lemmas := lemmas ++
      s!"public theorem {labelFactName name} : code[{offsetName}]? = some (.label {name}) := by decide +kernel\n\n"
  let doc := s!"# {docFn}\n\nIts basic blocks `b0` to `b{blocks.size - 1}`, its code `code` and each block's index in it (`b<k>_in_code`)."
  files := files.push (modPath mod,
    header doc (imports ++ [arch.infixModule]) ++ s!"namespace {ns}\n\n@[expose] public section\n\n" ++ blockSrc ++
    s!"/-- The function's code: its blocks in order. -/\ndef code : List Directive := List.flatten [{", ".intercalate names}]\n\n" ++ metadata ++
    s!"end\n\n" ++ sequential ++ lemmas ++ s!"end {ns}\n")
  return (files, ns)

/-- A label as part of a Lean identifier. -/
def labelIdent (short : Std.HashMap String String) (l : String) : String :=
  match short[l]? with
  | some s => s
  | none =>
    let l := if l.startsWith ".L" then (l.drop 2).toString else l
    String.ofList (l.toList.map fun c => if c.isAlphanum then c else '_')

/-- All files of the ingested schemes. -/
def emit (arch : Arch I C) (env : Environment) (schemes : Array (Scheme I C)) : IO (Array File) := do
  -- Functions in several schemes: identical, written once.
  let mut count : Std.HashMap String Nat := {}
  for s in schemes do
    for f in s.fns do count := count.insert f.sym (count.getD f.sym 0 + 1)
  let mut common : Std.HashMap String (Fn I C) := {}
  for s in schemes do
    for f in s.fns do
      if count.getD f.sym 0 > 1 then
        match common[f.sym]? with
        | some g =>
          unless g.lines == f.lines && g.prog == f.prog do
            throw <| IO.userError s!"{f.sym} differs between schemes"
        | none => common := common.insert f.sym f
  let mut files : Array File := #[]
  for s in schemes do
    for f in s.fns do
      let mut seen : Std.HashSet String := {}
      for (name, _, _) in fnLabels f do
        if seen.contains name then throw <| IO.userError s!"{f.sym}: duplicate generated label name {name}"
        seen := seen.insert name
      unless (fnLabels f).any (fun (name, _, _) => name == "entryLabel") do
        throw <| IO.userError s!"{f.sym}: missing entry label"
  let mut commonNs : Std.HashMap String String := {}
  for s in schemes do
    for f in s.fns do
      if common.contains f.sym && !commonNs.contains f.sym then
        let (fs, ns) := fnModules arch "Common" f
        files := files ++ fs
        commonNs := commonNs.insert f.sym ns
  for s in schemes do
    let S := capitalize s.name
    let ns := s!"{arch.ns}.{S}"
    let mut fnNs : Array (Fn I C × String) := #[]
    for f in s.fns do
      match commonNs[f.sym]? with
      | some n => fnNs := fnNs.push (f, n)
      | none =>
        let (fs, n) := fnModules arch S f
        files := files ++ fs
        fnNs := fnNs.push (f, n)
    let fnMods := fnNs.toList.map fun (_, n) =>
      s!"{arch.ns}.Code.{(n.drop (arch.ns.length + 1)).toString}"
    -- The program.
    let trapDir : Kraken.Directive I C := .byteArray ⟨arch.trap⟩
    let trapSrc ← IO.ofExcept (directiveSrc env trapDir)
    let trapItems := s.traps.flatMap fun t =>
      #[(s!"@Kraken.Directive.label Instr ConstExpr {t.quote}", s!"{t}:"), (trapSrc, arch.trapAsm)]
    let mut dataItems : Array (String × String) := #[]
    for (l, items) in s.rodata do
      dataItems := dataItems.push (s!"@Kraken.Directive.label Instr ConstExpr {l.quote}", s!"{l}:")
      for d in items do
        let item ← match d with
          | .bytes bs => do
            let dir : Kraken.Directive I C := .byteArray ⟨bs⟩
            pure (← IO.ofExcept (directiveSrc env dir), "")
          | .word n l' => do
            let dir : Kraken.Directive I C := .word n (arch.labelConst l')
            pure (← IO.ofExcept (directiveSrc env dir), s!"{arch.wordDirective n} {l'}")
        dataItems := dataItems.push item
    let pieces := fnNs.toList.map (fun (_, n) => s!"{n}.code") ++ [s!"{ns}.traps", s!"{ns}.rodata"]
    let doc := s!"# `{entryOf s.name}` as rustc compiles it\n\n" ++
      s!"The program `code`: the core functions, a trap for each panic entry they call (`traps`), " ++
      s!"and the data they refer to (`rodata`), derived from committed rustc assembly."
    let schemeMod := s!"{arch.ns}.Code.{S}"
    let symbolNs := s!"{ns}.Symbols"
    let symbolMod := s!"{arch.ns}.Code.{S}.Names"
    let symbolPairs := (s.traps.mapIdx fun i l => (s!"trap{i}Label", l)) ++
      (s.rodata.mapIdx fun i (l, _) => (s!"rodata{i}Label", l))
    let mut symbolSrc := ""
    for (name, sym) in symbolPairs do
      symbolSrc := symbolSrc ++ s!"abbrev {name} : String := {sym.quote}\n\n"
    files := files.push (modPath symbolMod,
      header "Program data and trap symbols derived from committed rustc assembly." [] ++
      s!"namespace {symbolNs}\n\n@[expose] public section\n\n" ++ symbolSrc ++ s!"end\n\nend {symbolNs}\n")
    files := files.push (modPath schemeMod,
      header doc fnMods ++ s!"namespace {ns}\n\n@[expose] public section\n\n" ++
      s!"/-- Each panic entry the core calls: its label, then `{arch.trapAsm}`. -/\ndef traps : List Directive := {listSrc trapItems}\n\n" ++
      rodataSrc dataItems ++
      s!"/-- The program. -/\ndef code : Program := List.flatten [{", ".intercalate pieces}]\n\n" ++
      s!"end\n\nend {ns}\n")
    let alignCases := s.alignments.toList.map fun (l, k) => s!"  | {l.quote} => {k}\n"
    files := files.push (modPath s!"{schemeMod}Align",
      header "Data-section alignment for the printer only." [] ++
      s!"namespace {ns}\n\npublic def dataAlign : String → Nat\n" ++
      String.join alignCases ++ s!"  | _ => 0\n\nend {ns}\n")
    -- Offsets of every function and block.
    let mut off := 0
    let mut offLemmas := ""
    for h : p in [0:fnNs.size] do
      let (f, n) := fnNs[p]
      let starts := blockStarts arch f.prog
      offLemmas := offLemmas ++
        s!"@[expose] public def {f.short}.programOffset : Nat := {off}\n\n" ++
        s!"public theorem {f.short}.code_at : {n}.code.IsInfixAt {ns}.code {f.short}.programOffset :=\n  List.isInfixAt_flatten_of (i := {p}) rfl (by decide +kernel)\n\n"
      for h : k in [0:starts.size] do
        offLemmas := offLemmas ++
          s!"public theorem {f.short}.b{k}_at : {n}.b{k}.IsInfixAt {ns}.code ({f.short}.programOffset + {n}.b{k}Offset) :=\n  {n}.b{k}_in_code.trans {f.short}.code_at (List.cons_ne_nil _ _)\n\n"
      off := off + f.prog.size
    let trapOff := off
    let dataOff := trapOff + trapItems.size
    let total := dataOff + dataItems.size
    offLemmas := offLemmas ++
      s!"@[expose] public def trapsOffset : Nat := {trapOff}\n\n" ++
      s!"@[expose] public def rodataOffset : Nat := {dataOff}\n\n" ++
      s!"@[expose] public def programLength : Nat := {total}\n\n" ++
      s!"public theorem traps_at : {ns}.traps.IsInfixAt {ns}.code trapsOffset :=\n  List.isInfixAt_flatten_of (i := {fnNs.size}) rfl (by decide +kernel)\n\n" ++
      s!"public theorem rodata_at : {ns}.rodata.IsInfixAt {ns}.code rodataOffset :=\n  List.isInfixAt_flatten_of (i := {fnNs.size + 1}) rfl (by decide +kernel)\n\n" ++
      s!"public theorem code_length : {ns}.code.length = programLength := by decide +kernel\n\n"
    let doc := s!"# Where each block of `{entryOf s.name}`'s program is\n\n" ++
      s!"Each core function's and each block's index in `{ns}.code` (`<Fn>.code_at`, `<Fn>.b<k>_at`), the traps' and the data's."
    files := files.push (modPath s!"{schemeMod}.Offsets",
      header doc [schemeMod] ++ s!"namespace {ns}\n\n" ++ sequential ++ offLemmas ++ s!"end {ns}\n")
    -- Labels.
    let mut labels : Array (String × Nat) := #[]
    let mut k := 0
    let labelsOf (ds : Array (Kraken.Directive I C)) : Array (Option String) :=
      ds.map fun | .label l => some l | _ => none
    let all : Array (Option String) := (fnNs.flatMap fun (f, _) => labelsOf f.prog) ++
      s.traps.flatMap (fun t => #[some t, none]) ++
      s.rodata.flatMap (fun (l, items) => #[some l] ++ items.map fun _ => none)
    for d in all do
      if let some l := d then
        if labels.any (·.1 == l) then throw <| IO.userError s!"{s.name}: label {l} defined twice"
        labels := labels.push (l, k)
      k := k + 1
    unless k == total do throw <| IO.userError "internal: program size"
    let shortOf : Std.HashMap String String := s.traps.foldl
      (fun m t => match shortName t with | some n => m.insert t n | none => m)
      (fnNs.foldl (fun m (f, _) => m.insert f.sym f.short) {})
    let mut labLemmas := ""
    let mut idents : Array String := #[]
    for (l, idx) in labels do
      let id := labelIdent shortOf l
      if idents.contains id then throw <| IO.userError s!"{s.name}: two labels named {id}"
      idents := idents.push id
      labLemmas := labLemmas ++
        s!"public theorem label_{id} : {ns}.code.findIdx? (· = .label {l.quote}) = some {idx} := by decide +kernel\n\n"
    let doc := s!"# Where each label of `{entryOf s.name}`'s program is\n\n" ++
      s!"For each label, the index of its `.label` directive in `{ns}.code`, its only one (`label_<l>`, the label's\n" ++
      s!"name without `.L`)."
    if arch.labels then
      files := files.push (modPath s!"{schemeMod}.Labels",
        header doc [schemeMod] ++ s!"namespace {ns}\n\n" ++ sequential ++ labLemmas ++ s!"end {ns}\n")
  -- The root.
  let mods := schemes.toList.flatMap fun s =>
    [s!"{arch.ns}.Code.{capitalize s.name}.Offsets"] ++
      (if arch.labels then [s!"{arch.ns}.Code.{capitalize s.name}.Labels"] else [])
  let what := if schemes.all (·.name == "vm") then "the leanVM verifier" else "the signature verifiers"
  let doc := s!"# rustc's code for {what}, ingested\n\nThe programs, their blocks' indices and their labels' indices, derived during elaboration."
  files := files.push (modPath s!"{arch.ns}.Code", header doc mods)
  return files

/-- The table of Lean names: a line `<symbol> <Name>` each. -/
def readNames (path : String) : IO (Std.HashMap String String) := do
  let mut m := {}
  for line in (← IO.FS.readFile path).splitOn "\n" do
    match (trimStr line).splitOn " " with
    | [""] => pure ()
    | [sym, name] => m := m.insert sym name
    | _ => throw <| IO.userError s!"{path}: bad line {line}"
  return m


end

end Ingest
