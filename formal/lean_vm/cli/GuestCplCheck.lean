import Statement.Data.Bytecode
import LeanVM.Guest.Backend.Guest.Input
import LeanVM.Guest.Data.FrameSizes
import LeanVM.Guest.Data.CplArms
import LeanVM.Guest.Backend.Complete.Count

/-!
# `guest-cplcheck`: the back end against what the completeness proof reads of the certificates

Run from `lean_vm`, through `python3 -I scripts/cpl-crosscheck`, which writes the certificate
tables as text (`.lake/cpl-crosscheck-tables.txt`) and runs `lake exe guest-cplcheck FILE
[--detail]`. No proof: compiled execution only.

The guest is the back end's input as `guest-traced` makes it (`GuestInput.input`), placed
(`placeProgram`), emitted and assembled. For each of its functions this compares:

1. the placed frame size with `Data.frameSizes` (and the literals the proofs pin);
2. each core value's place with the certificate's cell (`(certOf j).locs`);
3. the plumbing the placed IR names (fixed cells, call sites, table jumps, chained `match`es,
   temporaries, frame runs, shared cells) with the function's `plumb`;
4. the most instructions of each opcode a path runs, and the per-arm counts of `main_loop2`'s
   `match`es, with `plumb.pmax` and `Data.cplArms`;
5. the write-once consistency of every path (below);
6. the jump table's slots with `Data.jtTrie`.

**The path walk (5).** The core body and the placed body are walked together: a block is
segments of atoms (and the instructions they and the plumbing emit) separated by control
statements, which pair one to one (a chain of `match`es with the run of `match`es it lowers). The
instructions are the assembled program's, at their pcs, run symbolically with the machine's
rules (`crates/leanvm_core/src/cpu/execute.rs`): a `MUL` back-solves one unwritten operand of a
written result, a `DEREF` carries a written side to the other, a hint writes its cells, a read of
an unwritten frame cell is reported. A word is an expression (hash-consed `Node`) of the frame
pointer, the header, the arguments, constants, hint outputs, callee returns and the memory the
frame did not write; products and sums are normalised (flattened, sorted, constants folded,
`fp · g^e` recognised), so two writes of one word are one expression. After each segment the
core atoms name their values: a value whose word is a function of others (constant, sum,
product, copy, load, frame address) must equal what its cell holds, which is how pooled cells
and `spongeInPlace` are checked; any other value takes its cell's word. Branches are walked
once each and their states merged at the join, a cell keeping every word some path gives it, so
the check is exact for a property of one cell on one path, which all of these are (a cell given
more than `maxAlts` words by the arms of a wide `match` keeps one word of its own, `many`). An
instruction meeting a cell already written is either the encoding of a core atom of its segment
on that atom's cells (`justified`: a check the path's events make hold) or a finding. Each value
whose certificate cell differs from its place is also checked at its certificate cell, the frame
the existing interface (`FrameHolds`, `Defs.C`) builds.

`--selftest` injects faults into some functions (a `SET` into an argument's cell, a `SET` past the
frame, an operand read before its write, a value or a certificate cell moved onto an argument)
and counts those the walk reports; `--detail` lists every disagreement; `--debug` also reports
the second atoms on a named value; `--progress` times each function; further arguments restrict
the run to the functions named.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend
  LeanVM.Guest.Backend.GuestInput

namespace GuestCplCheck

/-! ## The tables -/

/-- A fixed cell's word (`B2C.PC`). -/
inductive PCw where
  | k (a b : Nat)
  | f (e : Nat)
  deriving BEq, Hashable, Repr, Inhabited

def PCw.str : PCw → String
  | .k a b => s!"k {a} {b}"
  | .f e => s!"fpg {e}"

/-- A call site (`B2C.Site`). -/
structure SiteT where
  q : Nat
  r : Nat
  tgt : Nat
  args : List Nat
  rets : List Nat
  deriving BEq, Repr, Inhabited

/-- One function's certificate data. -/
structure Tab where
  j : Nat := 0
  name : String := ""
  key : String := ""
  entry : Nat := 0
  len : Nat := 0
  fs : Nat := 0
  locs : Array Nat := #[]
  env : List Nat := []
  stat : Array (Nat × PCw) := #[]
  sites : Array SiteT := #[]
  arms : Array (Nat × Nat × Nat) := #[]
  tmps : Array (Nat × Nat) := #[]
  runs : Array (Nat × Nat) := #[]
  pmax : List Nat := []
  sh : List Nat := []
  chains : Array (Nat × Nat × Nat × Nat × List Nat) := #[]
  deriving Inhabited

structure Tables where
  fns : Array Tab := #[]
  jt : Std.HashMap Nat Nat := {}
  pinned : Array (String × Nat × String) := #[]
  /-- `B2/Residual.lean`: function, value, kind. -/
  residual : Array (String × Nat × String) := #[]

def nums (s : String) : List Nat := (s.splitOn " ").filterMap String.toNat?

def parseTables (text : String) : Tables := Id.run do
  let mut t : Tables := {}
  let mut cur : Option Tab := none
  for line in text.splitOn "\n" do
    let w := line.splitOn " "
    match w with
    | "F" :: j :: name :: key :: rest =>
        if let some c := cur then t := { t with fns := t.fns.push c }
        let ns := rest.filterMap String.toNat?
        cur := some { j := j.toNat!, name, key, entry := ns.getD 0 0, len := ns.getD 1 0, fs := ns.getD 2 0 }
    | "J" :: s :: e :: _ => t := { t with jt := t.jt.insert s.toNat! e.toNat! }
    | "X" :: name :: n :: wh :: _ => t := { t with pinned := t.pinned.push (name, n.toNat!, wh) }
    | "Q" :: name :: v :: kind :: _ => t := { t with residual := t.residual.push (name, v.toNat!, kind) }
    | tag :: _ =>
        if let some c := cur then
          let body := (line.drop 2).toString
          let ns := nums body
          let parts := body.splitOn " | "
          cur := some <| match tag with
            | "L" => { c with locs := ns.toArray }
            | "E" => { c with env := ns }
            | "S" => match w with
                | [_, o, "k", a, b] => { c with stat := c.stat.push (o.toNat!, .k a.toNat! b.toNat!) }
                | [_, o, "f", e] => { c with stat := c.stat.push (o.toNat!, .f e.toNat!) }
                | _ => c
            | "T" =>
                let h := nums (parts.getD 0 "")
                let site : SiteT := ⟨h.getD 0 0, h.getD 1 0, h.getD 2 0, nums (parts.getD 1 ""), nums (parts.getD 2 "")⟩
                { c with sites := c.sites.push site }
            | "A" => { c with arms := c.arms.push (ns.getD 0 0, ns.getD 1 0, ns.getD 2 0) }
            | "P" => { c with tmps := c.tmps.push (ns.getD 0 0, ns.getD 1 0) }
            | "R" => { c with runs := c.runs.push (ns.getD 0 0, ns.getD 1 0) }
            | "M" => { c with pmax := ns }
            | "H" => { c with sh := ns }
            | "C" =>
                let h := nums (parts.getD 0 "")
                let ch := (h.getD 0 0, h.getD 1 0, h.getD 2 0, h.getD 3 0, nums (parts.getD 1 ""))
                { c with chains := c.chains.push ch }
            | _ => c
    | [] => pure ()
  if let some c := cur then t := { t with fns := t.fns.push c }
  return t

/-! ## Words -/

/-- A word, hash-consed: children are ids. -/
inductive Node where
  | k (c0 c1 : Nat)
  /-- `fp · g^e`, this frame's pointer shifted. -/
  | fpg (e : Nat)
  /-- Header cell `i`: the return pc and the caller's frame pointer. -/
  | hdr (i : Nat)
  /-- Argument `i`. -/
  | par (i : Nat)
  /-- A sum of two non-constant words, sorted. -/
  | add (xs : List Nat)
  /-- A product of two non-constant words, sorted. -/
  | mul (xs : List Nat)
  /-- The constant `c0 + c1·y` plus the non-constant word `x`. -/
  | addk (c0 c1 x : Nat)
  /-- The constant `c` of `K` times the non-constant word `x`. -/
  | scale (c x : Nat)
  | div (a b : Nat)
  /-- An uninterpreted function of words and numbers. -/
  | op (tag : String) (xs : List Nat) (ns : List Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- Where a word is. -/
inductive Addr where
  /-- This frame's cell (past the frame size: the next loop frame's). -/
  | fr (n : Nat)
  /-- The cell at the word `b` times `g^off`, `b` no frame pointer of this frame. -/
  | hp (b off : Nat)
  /-- The cell `g^n`, from a constant pointer. -/
  | ab (n : Nat)
  deriving BEq, Hashable, Repr, Inhabited

def Addr.str : Addr → String
  | .fr n => s!"fp[{n}]"
  | .hp b o => s!"[#{b}·g^{o}]"
  | .ab n => s!"[g^{n}]"

/-- What one finding is. -/
structure Finding where
  fn : String
  kind : String
  pc : Nat
  what : String
  deriving Inhabited

/-- The per-function work state: the words made, the findings, the counters. -/
structure W where
  nodes : Array Node := #[]
  ids : Std.HashMap Node Nat := {}
  phis : Nat := 0
  finds : Array Finding := #[]
  stats : Std.HashMap String Nat := {}
  best : Array Nat := #[0, 0, 0, 0, 0, 0]
  /-- Arm counts of the separately counted `match`es: selector, arms. -/
  armCosts : Array (Nat × List (List Nat)) := #[]
  /-- Call sites: core args, core rets, q, return pc, target, arg cells, ret cells. -/
  sites : Array (List Nat × List Nat × Nat × Nat × Nat × List Nat × List Nat) := #[]
  /-- Table jumps (selector value, target cell, table base). -/
  arms : Array (Nat × Nat × Nat) := #[]
  /-- Chains (top statement, selector, next selector, base, targets). -/
  chains : Array (Nat × Nat × Nat × Nat × List Nat) := #[]
  /-- Fixed cells the code writes: cell ↦ words. -/
  fixed : Std.HashMap Nat (List PCw) := {}
  /-- Cells written in more than one arm of one `match`. -/
  armShared : Nat := 0
  /-- The core atoms of the segment being run, and the returns of the call being run. -/
  seg : Array Atom := #[]
  segRets : List V := []

instance : Inhabited W := ⟨{}⟩

/-- What the walk of one function reads. -/
structure Ctx where
  name : String
  main : Bool
  fs : Nat
  nargs : Nat
  nrets : Nat
  loopFrame : Bool
  code : Array OffsetInstruction
  hints : Std.HashMap Nat (List RHint)
  logs : Std.HashMap Nat Nat
  locs : V → Option LeanVM.Guest.Backend.Loc
  certCell : Nat → Option Nat
  keyed : Bool
  tablesBase : Nat
  sentinel : Nat
  jtWords : Std.HashMap Nat Nat
  /-- The trace's kind of each value (`padRun`, `spongeRun`). -/
  kindOf : Std.HashMap Nat Kind
  lay : Layout
  pc0 : Nat
  debug : Bool := false

abbrev M := ReaderT Ctx (StateM W)

def tally (k : String) (n : Nat := 1) : M Unit :=
  modify fun w => { w with stats := w.stats.insert k (w.stats.getD k 0 + n) }

/-- A finding: counted, and kept with its text for the first few of its kind in a function. -/
def report (kind : String) (pc : Nat) (what : String) : M Unit := do
  let c ← read
  let k := s!"find:{kind}"
  let n := (← get).stats.getD k 0
  tally k
  if n < 40 then modify fun w => { w with finds := w.finds.push ⟨c.name, kind, pc, what⟩ }

def mk (n : Node) : M Nat := do
  match (← get).ids.get? n with
  | some i => pure i
  | none =>
      modifyGet fun w => (w.nodes.size, { w with nodes := w.nodes.push n, ids := w.ids.insert n w.nodes.size })

def node (i : Nat) : M Node := return (← get).nodes.getD i default

def mkK (c0 c1 : Nat) : M Nat := mk (.k c0 c1)

def mkFpg (e : Nat) : M Nat := do
  if (← read).main then mkK (gpowBits e) 0 else mk (.fpg e)

partial def showSym (i : Nat) (d : Nat := 4) : M String := do
  if d == 0 then return s!"#{i}"
  let logs := (← read).logs
  match ← node i with
  | .k a b => return if b == 0 then (match logs.get? a with
      | some e => s!"g^{e}"
      | none => s!"{a}") else s!"({a},{b})"
  | .fpg e => return s!"fp·g^{e}"
  | .hdr i => return s!"hdr{i}"
  | .par i => return s!"arg{i}"
  | .add xs => return "(" ++ " + ".intercalate (← xs.mapM (showSym · (d - 1))) ++ ")"
  | .mul xs => return "(" ++ " · ".intercalate (← xs.mapM (showSym · (d - 1))) ++ ")"
  | .div a b => return s!"({← showSym a (d - 1)} / {← showSym b (d - 1)})"
  | .addk a b x => return s!"({a},{b} + {← showSym x (d - 1)})"
  | .scale c x => return s!"({← showSym (← mkK c 0) (d - 1)} · {← showSym x (d - 1)})"
  | .op t xs ns => return s!"{t}{ns}({", ".intercalate (← xs.mapM (showSym · (d - 1)))})"

/-- A word as a constant of `K` (limb), a count of frame pointer factors, and its non-constant
part, one level deep. -/
def splitMul (x : Nat) : M (Nat × Nat × Option Nat) := do
  match ← node x with
  | .k c0 0 => return (c0, 0, none)
  | .fpg e => return (gpowBits e, 1, none)
  | .scale c y => return (c, 0, some y)
  | _ => return (1, 0, some x)

/-- A product of two words, normalised one level deep: constants of `K` folded (powers of `g`
included, so `fp · g^a · g^b` is `fp · g^(a+b)`), a quotient cancelled against its divisor, the
operands sorted. Deeper products keep their shape, as the instructions that made them. -/
def mkMul (xs : List Nat) : M Nat := do
  let main := (← read).main
  let mut coef := 1
  let mut nfp := 0
  let mut rests : Array Nat := #[]
  for x in xs do
    let (c, f, r) ← splitMul x
    coef := mulN coef c
    nfp := nfp + f
    if let some r := r then rests := rests.push r
  if coef == 0 then return ← mkK 0 0
  if main then nfp := 0
  -- a word times its inverse (the hint `inverse`, which `assert !=` reads)
  if rests.size == 2 then
    let (a, b) := (rests[0]!, rests[1]!)
    if (← node b) == .op "inv" [a] [] || (← node a) == .op "inv" [b] [] then rests := #[]
  -- a quotient times its divisor
  if rests.size == 2 then
    let (a, b) := (rests[0]!, rests[1]!)
    if let .div p q := ← node a then
      if q == b then rests := #[p]
    if rests.size == 2 then
      if let .div p q := ← node b then
        if q == a then rests := #[p]
  let fp ← mk (.fpg 0)
  for _ in [0:nfp] do rests := rests.push fp
  let core : Option Nat ← match rests.toList.mergeSort with
    | [] => pure none
    | [r] => pure (some r)
    | rs => some <$> mk (.mul rs)
  match core with
  | none => mkK coef 0
  | some r =>
      if r == fp then
        match (← read).logs.get? coef with
        | some e => return ← mkFpg e
        | none => pure ()
      if coef == 1 then pure r else mk (.scale coef r)

/-- A word as a constant and its non-constant part, one level deep. -/
def splitAdd (x : Nat) : M (Nat × Nat × Option Nat) := do
  match ← node x with
  | .k a b => return (a, b, none)
  | .addk a b y => return (a, b, some y)
  | _ => return (0, 0, some x)

/-- A sum of two words, normalised one level deep: constants added, a word plus itself
cancelled (characteristic 2), the operands sorted. -/
def mkAdd (xs : List Nat) : M Nat := do
  let mut c0 := 0
  let mut c1 := 0
  let mut rests : List Nat := []
  for x in xs do
    let (a, b, r) ← splitAdd x
    c0 := c0 ^^^ a
    c1 := c1 ^^^ b
    if let some r := r then
      rests := if rests.contains r then rests.erase r else r :: rests
  let core : Option Nat ← match rests.mergeSort with
    | [] => pure none
    | [r] => pure (some r)
    | rs => some <$> mk (.add rs)
  match core with
  | none => mkK c0 c1
  | some r => if c0 == 0 && c1 == 0 then pure r else mk (.addk c0 c1 r)

def mkDiv (a b : Nat) : M Nat := do
  if a == b then return ← mkK 1 0
  match ← node a with
  | .mul xs =>
      if xs.contains b then
        match xs.erase b with
        | [r] => pure r
        | _ => mk (.div a b)
      else mk (.div a b)
  | .scale c r => if r == b then mkK c 0 else mk (.div a b)
  | _ => mk (.div a b)

def mkOp (t : String) (xs : List Nat) (ns : List Nat := []) : M Nat := mk (.op t xs ns)

/-- The cell `p · g^off` reads. -/
def resolve (p off : Nat) : M Addr := do
  let c ← read
  match ← node p with
  | .fpg e => return .fr (e + off)
  | .k a 0 =>
      match c.logs.get? a with
      | some e => return if c.main then .fr (e + off) else .ab (e + off)
      | none => return .hp p off
  | .scale k x =>
      match c.logs.get? k with
      | some e => return .hp x (e + off)
      | none => return .hp p off
  | _ => return .hp p off

/-! ## The path state -/

/-- A cell's words on the paths reaching here: `[some s]` written `s` on every path, `none` where
a path has not written it. -/
abbrev Alts := List (Option Nat)

/-- The state of the walk at a point, merged over the paths reaching it. -/
structure PS where
  mem : Std.HashMap Addr Alts := {}
  /-- Frame cells linked unwritten by a `DEREF`. -/
  links : Std.HashMap Addr (List Addr) := {}
  /-- The word of each value named so far (by number), where one on every path. -/
  canon : Std.HashMap Nat Nat := {}
  /-- Cell ↦ the first value named at it on this path. -/
  owner : Std.HashMap Nat Nat := {}
  /-- Values named at a cell no instruction has written yet: cell ↦ value. -/
  pending : Std.HashMap Nat Nat := {}
  /-- The certificate's cells of values whose certificate cell differs: cell ↦ (value, word). -/
  certAt : Std.HashMap Nat (Nat × Nat) := {}
  cnt : Array Nat := #[0, 0, 0, 0, 0, 0]
  /-- Frame cells written since the region began (for cells shared by arms). -/
  wlog : Std.HashSet Nat := {}
  deriving Inhabited

def dedupAlts (a : Alts) : Alts := a.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- More words than this at one cell (the arms of a wide `match` reusing it) are one word, `many`
(node `0`): any later write there is then reported. -/
def maxAlts : Nat := 8

def capAlts (a : Alts) : Alts :=
  if a.length ≤ maxAlts then a else (if a.contains none then [none] else []) ++ [some 0]

def mergeMap {α : Type} [BEq α] [Hashable α] (m1 m2 : Std.HashMap α Alts) : Std.HashMap α Alts :=
  let m := m1.fold (fun m k a =>
    let b := m2.getD k [none]
    if a == b then m else m.insert k (capAlts (dedupAlts (a ++ b)))) m1
  m2.fold (fun m k a => if m1.contains k then m else m.insert k (capAlts (dedupAlts ([none] ++ a)))) m

/-- The state after a join of two paths' states. -/
def merge (a b : PS) : PS :=
  { mem := mergeMap a.mem b.mem,
    links := b.links.fold (fun m k l => m.insert k ((m.getD k []) ++ l)) a.links,
    canon := a.canon.fold (fun m k v => if b.canon.get? k == some v then m.insert k v else m) {},
    owner := a.owner.fold (fun m k v => if b.owner.get? k == some v then m.insert k v else m) {},
    pending := b.pending.fold (fun m k v => m.insert k v) a.pending,
    certAt := b.certAt.fold (fun m k v => if m.contains k then m else m.insert k v) a.certAt,
    cnt := (a.cnt.zip b.cnt).map fun (x, y) => max x y,
    wlog := b.wlog.fold (·.insert ·) a.wlog }

def mergeAll : List PS → Option PS
  | [] => none
  | s :: ss => some (ss.foldl merge s)

/-! ## The machine, symbolically -/

/-- The word of a cell whose words differ by path: one word per cell and set of words, so that
two reads of it on one path agree. -/
def phi (l : Addr) (a : Alts) : M Nat := do
  tally "phiRead"
  mkOp "phi" (a.filterMap id) [hash l |>.toNat, if a.contains none then 1 else 0]

/-- A word nothing determines here. -/
def unknownAt (l : Addr) : M Nat := mkOp "unknown" [] [hash l |>.toNat]

/-- A cell's word as an instruction reads it: its word if one on every path reaching here, else
the cell's `phi`; `none` if some path has not written it. -/
def cellWord (st : PS) (l : Addr) : M (Option Nat) := do
  match st.mem.get? l with
  | some [some s] => if s == 0 then return some (← phi l [some 0]) else return some s
  | some a => if a.contains none then return none else return some (← phi l a)
  | none => return none

def cellWordD (st : PS) (l : Addr) : M Nat := do
  match ← cellWord st l with
  | some s => pure s
  | none => unknownAt l

def inFrameCheck (pc : Nat) (l : Addr) (write : Bool) : M Unit := do
  let c ← read
  if let .fr n := l then
    if c.main then
      if n ≥ c.fs then report "frame" pc s!"{if write then "write" else "read"} of {l.str}, main's frame {c.fs}"
    else if n ≥ c.fs then
      if write && c.loopFrame && n < c.fs + 3 + c.nargs then tally "nextFrameWrite"
      else report "frame" pc s!"{if write then "write" else "read"} of {l.str} past the frame {c.fs}"
    else if write && n < 2 then report "frame" pc s!"write of the header cell {l.str}"

/-- Whether a cell is written on every path. -/
def written (st : PS) (l : Addr) : Bool :=
  match st.mem.get? l with
  | some a => !a.contains none
  | none => false

/-- The cell of a value placed in one. -/
def cellV (v : V) : M (Option Nat) := do
  match (← read).locs v with
  | some (.cell n) => return some n
  | _ => return none

/-- The core atom of the running segment whose relation the instruction at `pc` is, if any: an
instruction meeting a written cell then checks an event of the path, which the honest memory's
words satisfy. -/
def justified (pc : Nat) : M (Option String) := do
  let c ← read
  let w ← get
  let ins := c.code.getD pc .padding
  let same2 (x y a b : Option Nat) : Bool := (x == a && y == b) || (x == b && y == a)
  for at_ in w.seg do
    let hit : Option String ← match ins, at_ with
      | .mul a b d, .mul d' x y => do
          pure <| if (← cellV d') == some d && same2 (← cellV x) (← cellV y) (some a) (some b) then some "mul" else none
      | .mul a b d, .rangeCheck x y _ _ k => do
          pure <| if (← cellV k) == some d && same2 (← cellV x) (← cellV y) (some a) (some b) then some "rangeCheck" else none
      | .mul a b d, .assertNe x i p => do
          pure <| if (← cellV p) == some d && same2 (← cellV x) (← cellV i) (some a) (some b) then some "assertNe" else none
      | .mul a b d, .copy d' s' => do
          pure <| if (← cellV d') == some d && ((← cellV s') == some a || (← cellV s') == some b) then some "copy" else none
      | .mul a b d, .assertEq x y => do
          let (cx, cy) := (← cellV x, ← cellV y)
          pure <| if (cy == some d && (cx == some a || cx == some b)) || (cx == some d && (cy == some a || cy == some b)) then some "assertEq" else none
      | .xor a b d, .add d' x y => do
          let cs := [← cellV d', ← cellV x, ← cellV y]
          pure <| if [some a, some b, some d].all cs.contains then some "add" else none
      | .xor a b d, .assertEq x y => do
          let cs := [← cellV x, ← cellV y]
          pure <| if (cs.contains (some a) && cs.contains (some b)) || (cs.contains (some a) && cs.contains (some d)) then some "assertEq" else none
      | .set o _ _, .const d _ => do pure <| if (← cellV d) == some o then some "const" else none
      | .set o _ _, .assertNe _ _ p => do pure <| if (← cellV p) == some o then some "assertNe" else none
      | .deref _ _ o3 .cell, .load d _ _ => do pure <| if (← cellV d) == some o3 then some "load" else none
      | .deref _ _ o3 .cell, .touch t _ => do pure <| if (← cellV t) == some o3 then some "touch" else none
      | .deref _ _ o3 .cell, .rangeCheck _ _ t1 t2 _ => do
          pure <| if (← cellV t1) == some o3 || (← cellV t2) == some o3 then some "rangeCheck" else none
      | .keccak _ _ _ _ _ _ _ out _ _ oc, .keccak _ outs _ _ => do
          let cs ← outs.mapM cellV
          pure <| if (keccakOuts out oc.cellCount).any (fun o => cs.contains (some o)) then some "keccak" else none
      | _, _ => pure none
    if hit.isSome then return hit
  if let .deref _ _ o3 .cell := ins then
    for v in w.segRets do
      if (← cellV v) == some o3 then return some "callReturn"
  return none

/-- Write `s` at `l` (`put`): a cell written with another word on some path is a candidate
conflict. -/
partial def put (pc : Nat) (l : Addr) (s : Nat) (st : PS) (why : String) : M PS := do
  inFrameCheck pc l true
  let mut st := st
  match st.mem.get? l with
  | some a =>
      let mut differs := false
      for x in a do
        if let some s' := x then
          if s' != s then differs := true
      if differs then
        match ← justified pc with
        | some k => tally s!"check:{k}"
        | none =>
            for x in a do
              if let some s' := x then
                if s' != s then
                  let segCells ← (← get).seg.toList.mapM fun a => do
                    let cs ← (Core.Atom.vals a).mapM cellV
                    return cs
                  report "write" pc s!"{why}: {l.str} holds {← showSym s'} on some path, written {← showSym s} [{(← read).code.getD pc .padding |> reprStr}; seg {segCells.take 12}]"
      if a.contains none && a.any Option.isSome then tally "writePartial"
      -- write-once: a word already there stays; a path that had none gets this one
      st := { st with mem := st.mem.insert l (dedupAlts (a.map fun x => some (x.getD s))) }
  | none => st := { st with mem := st.mem.insert l [some s] }
  if let .fr n := l then
    let pw : Option PCw := match ← node s with
      | .k a b => some (.k a b)
      | .fpg e => some (.f e)
      | _ => none
    if let some pw := pw then
      modify fun w => { w with fixed := w.fixed.insert n (let l := w.fixed.getD n []; if l.contains pw then l else l ++ [pw]) }
    st := { st with wlog := st.wlog.insert n }
    -- a value named here before any instruction wrote it takes this word
    if let some v := st.pending.get? n then
      st := { st with pending := st.pending.erase n, canon := st.canon.insert v s }
    if let some (v, w) := st.certAt.get? n then
      if w != s then
        report "certRoute" pc s!"{l.str}: value {v} at its certificate cell holds {← showSym w}, the code writes {← showSym s}"
  -- linked cells
  match st.links.get? l with
  | some ls =>
      st := { st with links := st.links.erase l }
      for l' in ls do
        if !(written st l') then st ← put pc l' s st "link"
  | none => pure ()
  return st

/-- Read the word at `l`. An unwritten frame cell is a read before a write; memory outside the
frame not written on this path is the memory's own word. -/
def rd (pc : Nat) (l : Addr) (st : PS) : M (Nat × PS) := do
  inFrameCheck pc l false
  let c ← read
  if c.loopFrame && l == .fr (2 + c.nargs + c.nrets) then tally "loopSelfRead"
  match st.mem.get? l with
  | some [some s] => if s == 0 then return (← phi l [some 0], st) else return (s, st)
  | some a =>
      if a.contains none then
        if let .fr _ := l then report "readBeforeWrite" pc s!"{l.str} unwritten on some path"
      let s ← phi l a
      return (s, st)
  | none =>
      match l with
      | .fr n =>
          match st.pending.get? n with
          | some v =>
              tally "readNamedUnwritten"
              let s ← mkOp "val" [] [v]
              let st := { st with mem := st.mem.insert l [some s] }
              let st := { st with pending := st.pending.erase n }
              return (s, { st with canon := st.canon.insert v s })
          | none =>
              report "readBeforeWrite" pc s!"{l.str} (cell {n})"
              let s ← mkK 0 0
              return (s, { st with mem := st.mem.insert l [some s] })
      | .hp b off =>
          let s ← mkOp "mem" [b] [off]
          return (s, { st with mem := st.mem.insert l [some s] })
      | .ab n =>
          let s ← mkOp "abs" [] [n]
          return (s, { st with mem := st.mem.insert l [some s] })

def opIdx : OffsetInstruction → Nat
  | .xor .. => 0
  | .mul .. => 1
  | .set .. => 2
  | .deref .. => 3
  | .jump .. => 4
  | .keccak .. => 5

def hintRuns (pc hi : Nat) (h : RHint) (st : PS) : M PS := do
  let mut st := st
  let wr (st : PS) (l : Addr) (s : Nat) : M PS := do
    if written st l then return st else put pc l s st "hint"
  match h with
  | .frameAddress _ => pure ()
  | .allocFrames ptr .. | .alloc ptr _ | .allocDyn ptr _ =>
      if !(written st (.fr ptr)) then st ← put pc (.fr ptr) (← mkOp "alloc" [] [pc, hi]) st "alloc"
  | .witnessStack _ base len =>
      for k in [0:len] do st ← wr st (.fr (base + k)) (← mkOp "wit" [] [pc, hi, k])
  | .witnessHeap _ ptr lo len =>
      let (p, st') ← rd pc (.fr ptr) st
      st := st'
      for k in [0:len] do st ← wr st (← resolve p (lo + k)) (← mkOp "wit" [] [pc, hi, k])
  | .log2Ceil _ dst _ _ => st ← wr st (.fr dst) (← mkOp "log2" [] [pc, hi])
  | .bitDecompose value bits nbits | .bitDecomposeExp value bits nbits =>
      let v ← cellWordD st (.fr value)
      for k in [0:nbits] do
        let l ← match bits with
          | .stack b => pure (Addr.fr (b + k))
          | .heap p => do
              let ps ← cellWordD st (.fr p)
              resolve ps k
        st ← wr st l (← mkOp "bit" [v] [k])
  | .digitDecomposeExp value dst _ ndigits _ _ _ =>
      let v ← cellWordD st (.fr value)
      for k in [0:ndigits] do
        let l ← match dst with
          | .stack b => pure (Addr.fr (b + k))
          | .heap p => do
              let ps ← cellWordD st (.fr p)
              resolve ps k
        st ← wr st l (← mkOp "digit" [v] [k])
  | .windowsExp value dest skip _ _ count =>
      let v ← cellWordD st (.fr value)
      for k in [0:count] do
        let l ← match dest with
          | .stack b => pure (Addr.fr (b + skip + k))
          | .heap p => do
              let ps ← cellWordD st (.fr p)
              resolve ps (skip + k)
        st ← wr st l (← mkOp "window" [v] [k])
  | .fieldLimbs value base len =>
      let v ← cellWordD st (.fr value)
      for k in [0:len] do st ← wr st (.fr (base + k)) (← mkOp "limb" [v] [k])
  | .inverse value dst =>
      let v ← cellWordD st (.fr value)
      st ← wr st (.fr dst) (← mkOp "inv" [v])
  return st

/-- Run an instruction. -/
def step (pc : Nat) (ins : OffsetInstruction) (st : PS) : M PS := do
  match ins with
  | .set o k0 k1 => put pc (.fr o) (← mkK k0 k1) st "SET"
  | .xor a b d =>
      let (sa, st) ← rd pc (.fr a) st
      let (sb, st) ← rd pc (.fr b) st
      put pc (.fr d) (← mkAdd [sa, sb]) st "XOR"
  | .mul a b d =>
      let (wa, wb) := (written st (.fr a), written st (.fr b))
      if written st (.fr d) && (wa != wb) then
        let (sd, st) ← rd pc (.fr d) st
        let (sk, st) ← rd pc (.fr (if wa then a else b)) st
        tally "backSolve"
        put pc (.fr (if wa then b else a)) (← mkDiv sd sk) st "MUL back-solve"
      else
        let (sa, st) ← rd pc (.fr a) st
        let (sb, st) ← rd pc (.fr b) st
        put pc (.fr d) (← mkMul [sa, sb]) st "MUL"
  | .deref o1 o2 o3 mode =>
      let (p, st) ← rd pc (.fr o1) st
      let l ← resolve p o2
      match mode with
      | .pc => put pc l (← mkK (gpowBits (pc + 2)) 0) st "DEREF pc"
      | .fp => put pc l (← mkFpg 0) st "DEREF fp"
      | .cell =>
          if written st l then
            let (s, st) ← rd pc l st
            put pc (.fr o3) s st "DEREF load"
          else if written st (.fr o3) then
            let (s, st) ← rd pc (.fr o3) st
            put pc l s st "DEREF store"
          else match l with
            | .fr _ =>
                tally "link"
                let ln := st.links.insert l ((st.links.getD l []) ++ [.fr o3])
                let ln := ln.insert (.fr o3) ((ln.getD (.fr o3) []) ++ [l])
                return { st with links := ln }
            | _ =>
                let (s, st) ← rd pc l st
                put pc (.fr o3) s st "DEREF load"
  | .jump oc od ofp =>
      let (_, st) ← rd pc (.fr oc) st
      let (_, st) ← rd pc (.fr od) st
      let (_, st) ← rd pc (.fr ofp) st
      return st
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oc =>
      let mut st := st
      let mut ins : List Nat := []
      for o in keccakIns m0 m1 m2 m3 tail b8 cap do
        let (s, st') ← rd pc (.fr o) st
        st := st'
        ins := ins ++ [s]
      for (o, k) in (keccakOuts out oc.cellCount).zipIdx do
        st ← put pc (.fr o) (← mkOp "keccak" ins [k, inOdd.toNat, outOdd.toNat]) st "KECCAK"
      return st

/-- Run the instruction at `pc` (its hints first). -/
def exec (pc : Nat) (st : PS) : M PS := do
  let c ← read
  let mut st := st
  for (h, hi) in (c.hints.getD pc []).zipIdx do st ← hintRuns pc hi h st
  let ins := c.code.getD pc .padding
  st := { st with cnt := st.cnt.modify (opIdx ins) (· + 1) }
  step pc ins st

def execRange (pc n : Nat) (st : PS) : M PS := do
  let mut st := st
  for i in [0:n] do st ← exec (pc + i) st
  return st

/-! ## The core side: values and their words -/

def hintVals : Hint → List V × List V
  | .witness _ d => ([], destVals d)
  | .bits v _ _ d | .bitsExp v _ d | .windowsExp v _ _ _ d => ([v], destVals d)
  | .digitsExp v _ _ _ _ sc d => (v :: sc.toList, destVals d)
  | .limbs v d => ([v], d)
  | .log2Ceil b _ _ dst => (destIns b, dst :: destVals b)
  | .inverse x d => ([x], [d])
  | .alloc d _ => ([], [d])
  | .allocDyn d s => ([s], [d])
where
  destVals : Dest → List V
    | .stack cs => cs
    | .heap _ _ _ => []
  destIns : Dest → List V
    | .stack _ => []
    | .heap p _ _ => [p]

/-- The word a value's place holds, if its cell is written on every path; `none` otherwise. -/
def placeWord (st : PS) (v : V) : M (Option Nat) := do
  match (← read).locs v with
  | some (.cell n) => cellWord st (.fr n)
  | some (.shifted n e) =>
      match ← cellWord st (.fr n) with
      | some s => return some (← mkMul [s, ← mkK (gpowBits e) 0])
      | none => return none
  | none => return none

/-- The word of a value: its canonical word if known, else its place's. -/
def wordOf (st : PS) (v : V) : M (Option Nat) := do
  match st.canon.get? v.idx with
  | some s => return some s
  | none => placeWord st v

def wordOfD (st : PS) (v : V) : M Nat := do
  match ← wordOf st v with
  | some s => pure s
  | none => mkOp "unknownValue" [] [v.idx]

/-- A value is named with the word `r` its defining atom gives (`none`: no defining atom, it
takes its cell's word). Checks `r` against its cell (and its certificate cell). -/
def nameV (pc : Nat) (why : String) (v : V) (r : Option Nat) (st : PS) : M PS := do
  let c ← read
  let mut st := st
  -- a value named before on this path: a second atom on it is a relation the path's events
  -- state of one word, not a second word for its cell
  if let some w := st.canon.get? v.idx then
    if let some r := r then
      if r != w then
        tally s!"assertionOnValue:{why}"
        if (← read).debug then report "assertion" pc s!"value {v.idx} ({why}): named {← showSym w}, now {← showSym r}"
    return st
  let pw ← placeWord st v
  let word : Option Nat ← match r, pw with
    | some r, some p =>
        if r != p then
          report "value" pc s!"value {v.idx} ({why}): its word {← showSym r}, its cell {← showSym p}"
        else tally "valueAgrees"
        pure (some r)
    | some r, none => pure (some r)
    | none, some p => pure (some p)
    | none, none => pure none
  -- the cell: owner, sharing, pending
  match c.locs v with
  | some (.cell n) =>
      match st.owner.get? n with
      | some u =>
          if u != v.idx then
            tally s!"share:{why}"
            if c.kindOf.get? u == some .padRun then tally "share:intoPaddingRun"
      | none => st := { st with owner := st.owner.insert n v.idx }
      match word, st.mem.get? (.fr n) with
      | some w, none => st := { st with mem := st.mem.insert (.fr n) [some w] }
      | some w, some a =>
          if a.contains none then
            -- written on some paths only: the others must agree
            for x in a do
              if let some s := x then
                if s != w then report "value" pc s!"value {v.idx} ({why}) at fp[{n}]: {← showSym w}, some path wrote {← showSym s}"
          else pure ()
      | none, _ => st := { st with pending := st.pending.insert n v.idx }
  | some (.shifted _ _) => tally "shiftedValue"
  | none => tally "unplacedValue"
  if let some w := word then st := { st with canon := st.canon.insert v.idx w }
  -- the certificate's cell, where it differs
  match c.certCell v.idx, c.locs v with
  | some cc, some l =>
    if cc < 2 || cc ≥ c.fs then tally "certCellOutsideFrame" else
      let same := match l with
        | .cell n => n == cc
        | _ => false
      if !same then
        tally "certDiffNamed"
        if let some w := word then
          match st.mem.get? (.fr cc) with
          | some [some s] =>
              if s != w then
                report "certRoute" pc s!"value {v.idx} ({why}): certificate cell fp[{cc}] holds {← showSym s} on this path, the value is {← showSym w}"
              else tally "certCellSameWord"
          | some _ => report "certRoute" pc s!"value {v.idx} ({why}): certificate cell fp[{cc}] differs by path"
          | none =>
              match st.certAt.get? cc with
              | some (u, w') =>
                  if w' != w then report "certRoute" pc s!"values {u} and {v.idx} at free certificate cell fp[{cc}] with different words"
              | none =>
                  tally "certCellFree"
                  st := { st with certAt := st.certAt.insert cc (v.idx, w) }
  | _, _ => pure ()
  return st

def named (st : PS) (v : V) : Bool := st.canon.contains v.idx

/-- Name a value with no defining atom here (it takes its cell's word). -/
def nameIn (pc : Nat) (why : String) (v : V) (st : PS) : M PS :=
  if named st v then pure st else nameV pc why v none st

/-- The word at a value's load: through `p · g^off`. -/
def loadWord (pc : Nat) (p : Nat) (off : Nat) (st : PS) : M (Nat × PS) := do
  let l ← resolve p off
  match st.mem.get? l with
  | some [some s] => if s == 0 then return (← phi l [some 0], st) else return (s, st)
  | _ =>
      match l with
      | .fr _ => return (← mkOp "frameLoad" [p] [off], st)
      | _ => rd pc l st

/-- The atoms of a segment name their values. -/
def nameAtom (pc : Nat) (a : Atom) (st : PS) : M PS := do
  let mut st := st
  let known (st : PS) (v : V) : M Bool := do return (← wordOf st v).isSome
  match a with
  | .const d c =>
      let (c0, c1) := limbsOf c
      st ← nameV pc (if (← read).kindOf.get? d.idx == some .padRun then "padConst" else "const") d (some (← mkK c0 c1)) st
  | .add d x y =>
      if (← known st x) && (← known st y) then
        st ← nameIn pc "in" x st; st ← nameIn pc "in" y st
        let r ← mkAdd [(← wordOf st x).get!, (← wordOf st y).get!]
        st ← nameV pc "add" d (some r) st
      else
        st ← nameIn pc "in" d st
        if ← known st x then
          st ← nameIn pc "in" x st
          st ← nameV pc "add" y (← (← wordOf st d).mapM fun w => do mkAdd [w, (← wordOf st x).get!]) st
        else
          st ← nameIn pc "in" y st
          st ← nameV pc "add" x (← (← wordOf st d).mapM fun w => do mkAdd [w, (← wordOfD st y)]) st
  | .mul d x y =>
      if (← known st x) && (← known st y) then
        st ← nameIn pc "in" x st; st ← nameIn pc "in" y st
        let r ← mkMul [(← wordOf st x).get!, (← wordOf st y).get!]
        st ← nameV pc "mul" d (some r) st
      else
        st ← nameIn pc "in" d st
        if ← known st x then
          st ← nameIn pc "in" x st
          st ← nameV pc "div" y (← (← wordOf st d).mapM fun w => do mkDiv w (← wordOf st x).get!) st
        else
          st ← nameIn pc "in" y st
          st ← nameV pc "div" x (← (← wordOf st d).mapM fun w => do mkDiv w (← wordOfD st y)) st
  | .copy d s =>
      if ← known st s then
        st ← nameIn pc "in" s st
        let why := match (← read).locs d, (← read).locs s with
          | some (.cell m), some (.cell n) => if m == n then "spongeInPlace" else "copy"
          | _, _ => "copy"
        st ← nameV pc why d (← wordOf st s) st
      else
        st ← nameIn pc "in" d st
        st ← nameV pc "copy" s (← wordOf st d) st
  | .load d p off =>
      st ← nameIn pc "in" p st
      match ← wordOf st p with
      | some w =>
          let (r, st') ← loadWord pc w off st
          st := st'
          st ← nameV pc "load" d (some r) st
      | none => st ← nameIn pc "load" d st
  | .assertEq x y =>
      st ← nameIn pc "in" x st
      st ← nameIn pc "in" y st
  | .assertNe x inv p =>
      st ← nameIn pc "in" x st
      st ← nameIn pc "inv" inv st
      st ← nameV pc "assertNe" p (some (← mkK 1 0)) st
  | .rangeCheck x y t1 t2 k =>
      st ← nameIn pc "in" x st
      if ← known st y then
        st ← nameIn pc "in" y st
        st ← nameV pc "rangeK" k (some (← mkMul [← wordOfD st x, ← wordOfD st y])) st
      else
        st ← nameIn pc "in" k st
        st ← nameV pc "rangeY" y (← (← wordOf st k).mapM fun w => do mkDiv w (← wordOfD st x)) st
      st ← nameIn pc "tmp" t1 st
      st ← nameIn pc "tmp" t2 st
  | .assertInK x y =>
      st ← nameIn pc "in" x st
      st ← nameIn pc "in" y st
  | .keccak ins outs inOdd outOdd =>
      for v in ins do st ← nameIn pc "in" v st
      let ws ← ins.mapM (wordOfD st)
      for (v, k) in outs.zipIdx do
        st ← nameV pc "keccak" v (some (← mkOp "keccak" ws [k, inOdd.toNat, outOdd.toNat])) st
  | .frameAddr p run =>
      for v in run do st ← nameIn pc "run" v st
      let c ← read
      match run.head?.bind c.locs with
      | some (.cell b) => st ← nameV pc "frameAddr" p (some (← mkFpg b)) st
      | _ => st ← nameIn pc "frameAddr" p st
  | .hint h =>
      let (ins, outs) := hintVals h
      for v in ins do st ← nameIn pc "in" v st
      for v in outs do st ← nameIn pc "hint" v st
  | .touch t p =>
      st ← nameIn pc "in" p st
      st ← nameIn pc "tmp" t st
  return st

/-! ## The walk -/

def isOp : PStmt → Bool
  | .op .. => true
  | _ => false

def isAtom : Stmt → Bool
  | .atom _ => true
  | _ => false

def atomOf : Stmt → Option Atom
  | .atom a => some a
  | _ => none

/-- The counts are the arm's alone in a separately counted `match`. -/
def zeroCnt (st : PS) : PS := { st with cnt := #[0, 0, 0, 0, 0, 0] }

/-- A path reaching a `return`. -/
def endPath (st : PS) : M Unit :=
  modify fun w => { w with best := (w.best.zip st.cnt).map fun (x, y) => max x y }

mutual
/-- Walk a core block and its placed block from `pc`: the merged state of the paths falling
through, and the pc past the block. `top` is the index of the next top-level statement, if the
block is the body. -/
partial def walkBlock (cs : List Stmt) (ps : List PStmt) (pc : Nat) (st : PS) (top : Option Nat) :
    M (Option PS × Nat) := do
  let ops := ps.takeWhile isOp
  let ps' := ps.drop ops.length
  let atoms := cs.takeWhile isAtom
  let cs' := cs.drop atoms.length
  -- the instructions, checked against the placed statements
  let c ← read
  let mut st := st
  for (o, i) in ops.zipIdx do
    if let .op _ lo := o then
      if resolveOp c.lay c.pc0 c.fs lo != c.code.getD (pc + i) .padding then
        report "align" (pc + i) "the placed statement is not the instruction at its pc"
  modify fun w => { w with seg := (atoms.filterMap atomOf).toArray, segRets := [] }
  st ← execRange pc ops.length st
  let pc := pc + ops.length
  for a in atoms.filterMap atomOf do st ← nameAtom pc a st
  let top := top.map (· + atoms.length)
  match cs', ps' with
  | [], [] => return (some st, pc)
  | s :: csr, p :: psr =>
      let (out, pc', used) ← walkStmt s csr p pc st top
      match out with
      | none => return (none, pc' + blockSize psr)
      | some st' => walkBlock (csr.drop used) psr pc' st' (top.map (· + 1 + used))
  | _, _ =>
      report "align" pc s!"core and placed blocks part: {cs'.length} core statements, {ps'.length} placed"
      return (some st, pc + blockSize ps')

/-- A control statement and its placed form; also returns how many further core statements it
consumed (the later stages of a chain). -/
partial def walkStmt (s : Stmt) (rest : List Stmt) (p : PStmt) (pc : Nat) (st : PS)
    (top : Option Nat) : M (Option PS × Nat × Nat) := do
  let c ← read
  modify fun w => { w with seg := #[], segRets := [] }
  match s, p with
  | .ite cv z nz, .ite _ _ _ _ zero hasElse _ _ nonzero =>
      let st ← execRange pc 2 st
      let st ← nameIn pc "cond" cv st
      let base := st.wlog
      let st0 := { st with wlog := {} }
      let (oz, pz) ← walkBlock z zero (pc + 2) st0 none
      let (oz, pz) ← match oz, hasElse with
        | some sz, true => do pure (some (← execRange pz 2 sz), pz + 2)
        | _, true => pure (none, pz + 2)
        | _, false => pure (oz, pz)
      let (on, pn) ← walkBlock nz nonzero pz st0 none
      let outs := [oz, on].filterMap id
      return ((mergeAll outs).map fun m => { m with wlog := base.fold (·.insert ·) m.wlog }, pn, 0)
  | .match_ _ _, .chain _ _ _ entry _ _ firsts stages =>
      let st ← execRange pc 3 st
      let cms := (s :: rest).take stages.length
      if cms.length != stages.length then
        report "align" pc "a chain with fewer core matches than stages"
        return (some st, pc + 3 + stagesSize stages, 0)
      let mut cur : Option PS := some st
      let mut pcs := pc + 3
      let mut k := 0
      for (stage, cm) in stages.zip cms do
        let .match_ x arms := cm | do report "align" pc "a chain stage that is no match"; return (none, pc, 0)
        if arms.length != stage.length then report "align" pc "a chain stage of another arm count"
        let keyed := c.keyed && top.isSome
        if k == 0 then
          modify fun w => { w with arms := w.arms.push (x.idx, entry, c.tablesBase + firsts.headD 0) }
        let some sin := cur | break
        let before := sin.cnt
        let mut outs : List PS := []
        let mut costs : List (List Nat) := []
        let mut armCells : Array (Std.HashSet Nat) := #[]
        let mut exits : List Nat := []
        for (pa, ca) in stage.zip arms do
          let s0 := { (if keyed then zeroCnt sin else sin) with wlog := {} }
          let (o, p') ← walkBlock ca pa pcs s0 none
          pcs := p'
          -- the arm's exit through the next table: its target cell
          if let some (.op _ (.slot _ _ e)) := pa.reverse.drop 1 |>.head? then exits := exits ++ [e]
          match o with
          | some so =>
              outs := outs ++ [so]
              costs := costs ++ [so.cnt.toList]
              armCells := armCells.push so.wlog
          | none =>
              costs := costs ++ [[0, 0, 0, 0, 0, 0]]
        if keyed then modify fun w => { w with armCosts := w.armCosts.push (x.idx, costs) }
        -- cells written by two arms
        let mut seen : Std.HashMap Nat Nat := {}
        for cs in armCells do
          for n in cs do seen := seen.insert n (seen.getD n 0 + 1)
        let shared := seen.fold (fun n _ m => if m ≥ 2 then n + 1 else n) 0
        modify fun w => { w with armShared := w.armShared + shared }
        if let some (.match_ y _) := cms[k + 1]? then
          if let some t := top then
            modify fun w => { w with chains := w.chains.push (t + k, x.idx, y.idx, c.tablesBase + firsts.getD (k + 1) 0, exits) }
        cur := (mergeAll outs).map fun m =>
          { m with cnt := if keyed then before else m.cnt, wlog := sin.wlog.fold (·.insert ·) m.wlog }
        k := k + 1
      return (cur, pc + 3 + stagesSize stages, stages.length - 1)
  | .call _ args rets, .call _ cs =>
      modify fun w => { w with seg := #[], segRets := rets }
      let n := cs.args.length
      let jmp := 1 + n + (if cs.loop.isSome then 1 else 0) + 2
      let st ← execRange pc (jmp + 1) st
      let (nfp, st) ← rd pc (.fr cs.nfp) st
      let mut st := st
      for i in [0:cs.rets.length] do
        let l ← resolve nfp (2 + n + i)
        if !(written st l) then st ← put (pc + jmp) l (← mkOp "ret" [nfp] [i]) st "callee"
      st ← execRange (pc + jmp + 1) cs.rets.length st
      for v in args do st ← nameIn pc "arg" v st
      for v in rets do st ← nameIn pc "callRet" v st
      modify fun w => { w with sites := w.sites.push (args.map (·.idx), rets.map (·.idx), cs.nfp,
        pc + jmp + 1, 0, cs.args, cs.rets) }
      return (some st, pc + stmtSize p, 0)
  | .callIf cv _ args, .call _ cs =>
      let st ← execRange pc (stmtSize p) st
      let st ← nameIn pc "cond" cv st
      let mut st := st
      for v in args do st ← nameIn pc "arg" v st
      let jmp := 1 + cs.args.length + (if cs.loop.isSome then 1 else 0) + 2
      modify fun w => { w with sites := w.sites.push (args.map (·.idx), [], cs.nfp, pc + jmp + 1, 0, cs.args, []) }
      return (some st, pc + stmtSize p, 0)
  | .callIf cv _ args, .loopNext .. =>
      let st ← execRange pc (stmtSize p) st
      let mut st ← nameIn pc "cond" cv st
      for v in args do st ← nameIn pc "arg" v st
      tally "loopNext"
      return (some st, pc + stmtSize p, 0)
  | .dispatch _ _ args rets, .dispatch _ _ nfpC _ _ entry _ _ las lrs =>
      modify fun w => { w with seg := #[], segRets := rets }
      let n := las.length
      let jmp := n + 4
      let st ← execRange pc (jmp + 1) st
      let (nfp, st) ← rd pc (.fr nfpC) st
      let mut st := st
      for i in [0:lrs.length] do
        let l ← resolve nfp (2 + n + i)
        if !(written st l) then st ← put (pc + jmp) l (← mkOp "ret" [nfp] [i]) st "callee"
      st ← execRange (pc + jmp + 1) lrs.length st
      for v in args do st ← nameIn pc "arg" v st
      for v in rets do st ← nameIn pc "callRet" v st
      modify fun w => { w with sites := w.sites.push (args.map (·.idx), rets.map (·.idx), nfpC,
        pc + jmp + 1, entry, las, lrs) }
      return (some st, pc + stmtSize p, 0)
  | .ret vs, .ret .. | .ret vs, .halt .. =>
      let mut st ← execRange pc (stmtSize p) st
      for v in vs do st ← nameIn pc "ret" v st
      endPath st
      return (none, pc + stmtSize p, 0)
  | _, _ =>
      report "align" pc "a control statement and a placed statement of another kind"
      return (some st, pc + stmtSize p, 0)
end

/-- The walk of a function's body from its entry state. -/
def walkFn (params : List V) (body : List Stmt) (pbody : List PStmt) (entry : Nat) : M Unit := do
  let c ← read
  -- node `0`: the word of a cell more paths write than `maxAlts` words
  let _ ← mkOp "many" [] []
  let mut st : PS := {}
  if !c.main then
    st := { st with mem := (st.mem.insert (.fr 0) [some (← mk (.hdr 0))]).insert (.fr 1) [some (← mk (.hdr 1))] }
  for i in [0:c.nargs] do
    st := { st with mem := st.mem.insert (.fr (2 + i)) [some (← mk (.par i))] }
  if c.loopFrame then
    st := { st with mem := st.mem.insert (.fr (2 + c.nargs + c.nrets)) [some (← mkFpg 0)] }
  if c.main then
    for (n, e) in c.jtWords.toList do
      st := { st with mem := st.mem.insert (.fr n) [some (← mkK (gpowBits e) 0)] }
  for v in params do st ← nameIn entry "param" v st
  let (o, _) ← walkBlock body pbody entry st (some 0)
  if let some s := o then
    report "align" entry "a path falls off the end of the body"
    endPath s

/-! ## The comparisons -/

/-- A line of the report, and the disagreements kept. -/
structure Out where
  lines : Array String := #[]
  detail : Array String := #[]

def Out.say (o : Out) (s : String) : Out := { o with lines := o.lines.push s }
def Out.note (o : Out) (s : String) : Out := { o with detail := o.detail.push s }

/-- The values of a body's atoms of a kind: range check temporaries and touches, frame runs. -/
partial def atomsOf : List Stmt → List Atom
  | [] => []
  | .atom a :: ss => a :: atomsOf ss
  | .ite _ z n :: ss => atomsOf z ++ atomsOf n ++ atomsOf ss
  | .match_ _ arms :: ss => arms.flatMap atomsOf ++ atomsOf ss
  | _ :: ss => atomsOf ss

/-- The cell of a value placed in one. -/
def cellOfV (pf : Placed) (v : Nat) : Option Nat :=
  match pf.locs[V.n v]? with
  | some (.cell n) => some n
  | _ => none

end GuestCplCheck

open GuestCplCheck in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: guest-cplcheck TABLES [--detail]"; return 2
  let detail := args.contains "--detail"
  let progress := args.contains "--progress"
  let T := parseTables (← IO.FS.readFile path)
  let P ← input
  let (pls, tables) ← orThrow (placeProgram P)
  let fills := (fillsOf pls).toArray
  let slots := tableSlots tables.len fills tables.entries
  let lowered := pls.map fun pf => (emitFn pf.fn).1
  let (fns', base) := withTables lowered slots
  let (lay, size) := layout fns' base
  let a := assembleAt lay size fns'
  let hints : Std.HashMap Nat (List RHint) := a.hints.foldl (fun m (pc, hs) => m.insert pc hs) {}
  let tbl := gpowTable (2 ^ 20)
  let logs : Std.HashMap Nat Nat := tbl.zipIdx.foldl (fun m (x, e) => if m.contains x then m else m.insert x e) {}
  let loops := loopTable P
  -- the jump table's words, by absolute slot
  let slotPc (k : KVal) : Option Nat := match k with
    | .at f i => some (lay.entry.getD f 0 + i)
    | .entry f => some (lay.entry.getD f 0)
    | _ => none
  let jtWords : Std.HashMap Nat Nat := slots.zipIdx.foldl (fun m (k, i) => match slotPc k with
    | some e => m.insert (base + i) e
    | none => m) {}
  let tabOf : Std.HashMap String Tab := T.fns.foldl (fun m t => m.insert t.name t) {}
  let mut o : Out := {}
  let mut fsAgree := 0
  let mut fsDiff : Array String := #[]
  let mut cellsAgree := 0
  let mut cellsTotal := 0
  let mut cellDiffs : Array (String × Nat × String × Nat) := #[]
  let mut cellFns : Std.HashSet String := {}
  let mut diffKind : Std.HashMap (String × Nat) String := {}
  let mut statAgree := 0
  let mut statTotal := 0
  let mut statFns := 0
  let mut statDiffs : Array String := #[]
  let mut siteAgree := 0
  let mut siteTotal := 0
  let mut siteDiffs : Array String := #[]
  let mut armAgree := 0
  let mut armTotal := 0
  let mut armDiffs : Array String := #[]
  let mut chainAgree := 0
  let mut chainTotal := 0
  let mut chainDiffs : Array String := #[]
  let mut tmpAgree := 0
  let mut tmpTotal := 0
  let mut tmpDiffs : Array String := #[]
  let mut runAgree := 0
  let mut runTotal := 0
  let mut runDiffs : Array String := #[]
  let mut shAgree := 0
  let mut statCls : Std.HashMap String Nat := {}
  let mut shCls : Std.HashMap String Nat := {}
  let mut shDiffs : Array String := #[]
  let mut pmaxAgree := 0
  let mut pmaxDiffs : Array String := #[]
  let mut armCostAgree := 0
  let mut armCostTotal := 0
  let mut armCostDiffs : Array String := #[]
  let mut pmaxPAgree := 0
  let mut pmaxPDiffs : Array String := #[]
  let mut armsPAgree := 0
  let mut armsPDiffs : Array String := #[]
  let mut alignedN := 0
  let mut alignedDiffs : Array String := #[]
  let mut stats : Std.HashMap String Nat := {}
  let mut finds : Array Finding := #[]
  let mut armSharedTotal := 0
  let mut armSharedFns := 0
  let only := (args.drop 1).filter (!·.startsWith "--")
  let selftest := args.contains "--selftest"
  let ranges : Std.HashMap String (Nat × Nat) := a.fns.foldl (fun m (n, s, l) => m.insert n (s, l)) {}
  let mut selfRes : Std.HashMap String (Nat × Nat) := {}
  let mut selfMiss : Array String := #[]
  for (pf, tf, j0) in (pls.zip P).zipIdx.map (fun ((x, y), i) => (x, y, i)) do
    let j := j0 + 1
    let name := pf.fn.name
    if !only.isEmpty && !only.contains name then continue
    if progress then IO.eprintln s!"[{j}] {name}"
    let t := tabOf.getD name default
    let isMain := name == "main"
    -- (1) frame sizes
    let fsData := LeanVM.Guest.Data.frameSizes.getD j 0
    let fsB := pf.fn.frameSize
    let ok1 := fsB == fsData && (if isMain then fsB + slots.size == t.fs else fsB == t.fs)
    if ok1 then fsAgree := fsAgree + 1
    else fsDiff := fsDiff.push s!"{name}: back end {fsB}, Data.frameSizes {fsData}, bundle fs {t.fs}"
    -- (2) value cells
    for (cc, v) in t.locs.zipIdx do
      cellsTotal := cellsTotal + 1
      match pf.locs[V.n v]? with
      | some (.cell n) =>
          if n == cc then cellsAgree := cellsAgree + 1
          else cellDiffs := cellDiffs.push (name, v, s!"cell {n}", cc); cellFns := cellFns.insert name
      | some (.shifted n e) => cellDiffs := cellDiffs.push (name, v, s!"shifted fp[{n}]·g^{e}", cc); cellFns := cellFns.insert name
      | none => cellDiffs := cellDiffs.push (name, v, "no place", cc); cellFns := cellFns.insert name
    -- what makes the values whose places differ
    for (f, v, _, _) in cellDiffs do
      if f == name && !diffKind.contains (f, v) then
        let defs := (atomsOf tf.core.body).filterMap fun a => match a with
          | .const d _ => if d.idx == v then some "const" else none
          | .hint h => if (hintVals h).2.any (·.idx == v) then some "hint output" else none
          | .frameAddr p _ => if p.idx == v then some "addr" else none
          | _ => if (Core.Atom.vals a).any (·.idx == v) then some "other" else none
        diffKind := diffKind.insert (f, v) (", ".intercalate defs.eraseDups)
    -- (5) the path walk, which also finds the sites, table jumps, chains and counts
    let kindOf : Std.HashMap Nat Kind := tf.trace.foldl (fun m e => match e with
      | .alloc vs k => vs.foldl (fun m v => m.insert v.idx k) m
      | _ => m) {}
    let loopFrame := (loops[name]?).any (·.registered)
    let pc0 := lay.entry.getD name 0
    let ctx : GuestCplCheck.Ctx := {
      name, main := isMain, fs := if isMain then fsB + slots.size else fsB,
      nargs := (sigOf tf).1, nrets := (sigOf tf).2, loopFrame, code := a.code, hints, logs,
      locs := fun v => pf.locs[v]?, certCell := fun i => t.locs[i]?,
      keyed := t.key == "main_loop2", tablesBase := base, sentinel := size - 1,
      jtWords := if isMain then jtWords else {}, kindOf, lay, pc0,
      debug := args.contains "--debug" }
    let t0 ← IO.monoMsNow
    let ((), w) := (walkFn tf.core.params tf.core.body pf.fn.body pc0).run ctx |>.run {}
    -- the sharing mechanisms the trace names
    for e in tf.trace do
      if let .alloc _ k := e then
        match k with
        | .padRun => stats := stats.insert "trace:padRun" (stats.getD "trace:padRun" 0 + 1)
        | .spongeRun => stats := stats.insert "trace:spongeRun" (stats.getD "trace:spongeRun" 0 + 1)
        | _ => pure ()
    if loopFrame then stats := stats.insert "registeredLoopHelpers" (stats.getD "registeredLoopHelpers" 0 + 1)
    -- the self-test: faults injected into this function's code, places and certificate cells
    if selftest && j % 23 == 1 then
      let (start, len) := ranges.getD name (0, 0)
      let firstAt (p : OffsetInstruction → Option OffsetInstruction) : Option (Nat × OffsetInstruction) :=
        (List.range len).findSome? fun i => (p (a.code.getD (start + i) .padding)).map (start + i, ·)
      let run (ctx' : GuestCplCheck.Ctx) : W :=
        ((walkFn tf.core.params tf.core.body pf.fn.body pc0).run ctx' |>.run {}).2
      let newFind (w' : W) (kinds : List String) : Bool :=
        kinds.any fun k => w'.stats.getD s!"find:{k}" 0 > w.stats.getD s!"find:{k}" 0
      let mut tries : List (String × Option (Nat × OffsetInstruction) × List String) := []
      if ctx.nargs ≥ 1 then
        tries := tries ++ [("a SET into an argument's cell", firstAt (fun | .set _ k0 k1 => some (.set 2 (k0 + 1) k1) | _ => none), ["write", "value"])]
      tries := tries ++ [("a SET past the frame", firstAt (fun | .set _ k0 k1 => some (.set (ctx.fs + ctx.nargs + 10) k0 k1) | _ => none), ["frame"]),
        ("an operand read before its write", firstAt (fun
          | .mul a b d => if a != d && b != d then some (.mul d b d) else none
          | .xor a b d => if a != d && b != d then some (.xor d b d) else none
          | _ => none), ["readBeforeWrite"])]
      for (tag, m, kinds) in tries do
        if let some (pc, ins) := m then
          let w' := run { ctx with code := a.code.set! pc ins }
          let (n, d) := selfRes.getD tag (0, 0)
          let hit := newFind w' kinds
          selfRes := selfRes.insert tag (n + 1, if hit then d + 1 else d)
          if !hit then selfMiss := selfMiss.push s!"{tag}: {name} @{pc}: {reprStr (a.code.getD pc .padding)} -> {reprStr ins}; findings {w'.stats.toList.filter (·.1.startsWith "find:")}, tallies {w'.stats.toList.filter (·.1.startsWith "read")}"
      -- a constant placed in an argument's cell, at the back end's place and at the certificate's
      let consts : List V := (atomsOf tf.core.body).filterMap fun | .const d _ => some d | _ => none
      if let some v := consts.find? (fun (v : V) => match (pf.locs[v]? : Option LeanVM.Guest.Backend.Loc) with
          | some (.cell n) => n ≥ 2 + ctx.nargs + ctx.nrets
          | _ => false) then
        if ctx.nargs ≥ 1 then
          let w' := run { ctx with locs := fun u => if u == v then some (.cell 2) else pf.locs[u]? }
          let (n, d) := selfRes.getD "a value placed in an argument's cell" (0, 0)
          selfRes := selfRes.insert "a value placed in an argument's cell" (n + 1, if newFind w' ["value"] then d + 1 else d)
          let w'' := run { ctx with certCell := fun i => if i == v.idx then some 2 else t.locs[i]? }
          let (n2, d2) := selfRes.getD "a certificate cell moved to an argument's cell" (0, 0)
          selfRes := selfRes.insert "a certificate cell moved to an argument's cell" (n2 + 1, if newFind w'' ["certRoute"] then d2 + 1 else d2)
    if progress then
      IO.eprintln s!"    {(← IO.monoMsNow) - t0} ms, {w.nodes.size} words, {w.stats.fold (fun n _ v => n + v) 0} tallies"
    for (k, n) in w.stats.toList do stats := stats.insert k (stats.getD k 0 + n)
    finds := finds ++ w.finds
    armSharedTotal := armSharedTotal + w.armShared
    if w.armShared > 0 then armSharedFns := armSharedFns + 1
    -- (3) plumbing: fixed cells
    let valueCells : Std.HashMap Nat (List Nat) := (List.range (t.locs.size)).foldl (fun m v =>
      match cellOfV pf v with
      | some n => m.insert n (v :: m.getD n [])
      | none => m) {}
    let constOf : Std.HashMap Nat (Nat × Nat) := (atomsOf tf.core.body).foldl (fun m a => match a with
      | .const d c => m.insert d.idx (limbsOf c)
      | _ => m) {}
    let loadVals : Std.HashSet Nat := (atomsOf tf.core.body).foldl (fun m a => match a with
      | .load d _ _ => m.insert d.idx
      | _ => m) {}
    let mut ours : Std.HashMap Nat PCw := {}
    for (n, ws) in w.fixed.toList do
      match ws with
      | [pw] =>
          if n < ctx.fs && 2 ≤ n then
            let vs := valueCells.getD n []
            let constOk := match pw with
              | .k a b => vs.any (fun v => constOf.get? v == some (a, b)) &&
                  vs.all (fun v => constOf.get? v == some (a, b) || loadVals.contains v)
              | .f _ => false
            if vs.isEmpty || constOk then ours := ours.insert n pw
      | _ => pure ()
    if loopFrame then ours := ours.insert (2 + ctx.nargs + ctx.nrets) (.f 0)
    let theirs : Std.HashMap Nat PCw := t.stat.foldl (fun m (n, pw) => m.insert n pw) {}
    let (start, len) := ranges.getD name (0, 0)
    let selfFpPair (q o : Nat) : Bool := (List.range len).any fun i =>
      a.code.getD (start + i) .padding == .deref q 0 0 .fp &&
        a.code.getD (start + i + 1) .padding == .deref q 0 o .cell
    let shiftedAt (n : Nat) : Bool := t.locs.zipIdx.any fun (c, v) => c == n && match pf.locs[V.n v]? with
      | some (.shifted ..) => true
      | _ => false
    let bump (m : Std.HashMap String Nat) (k : String) := m.insert k (m.getD k 0 + 1)
    let mut fnStatOk := true
    for (n, pw) in theirs.toList do
      statTotal := statTotal + 1
      if ours.get? n == some pw then statAgree := statAgree + 1
      else
        fnStatOk := false
        let cls := match pw, ours.get? n with
          | .f e, none => if selfFpPair n e then "the self frame pointer's one-cell buffer: the table takes it at fp[o], the back end leaves it to the allocation hint" else "unclassified"
          | _, _ => "unclassified"
        statCls := bump statCls cls
        statDiffs := statDiffs.push s!"{name}: fp[{n}] table {pw.str}, back end {(ours.get? n).map PCw.str} (code writes {(w.fixed.getD n []).map PCw.str}) [{cls}]"
    for (n, pw) in ours.toList do
      if !theirs.contains n then
        fnStatOk := false
        let cls := if shiftedAt n then "the product cell of an addr pointer: a value cell in the certificate, a fixed cell in the back end (the pointer is placed shifted)" else "unclassified"
        statCls := bump statCls cls
        statDiffs := statDiffs.push s!"{name}: fp[{n}] back end {pw.str}, not in the table [{cls}]"
    if fnStatOk then statFns := statFns + 1
    -- sites
    let theirSites : Std.HashMap Nat SiteT := t.sites.foldl (fun m s => m.insert s.q s) {}
    let mut seenQ : Std.HashSet Nat := {}
    for (cargs, crets, q, r, tgt, acells, rcells) in w.sites do
      if seenQ.contains q then continue
      seenQ := seenQ.insert q
      siteTotal := siteTotal + 1
      match theirSites.get? q with
      | some s =>
          let tcells := (s.args.map fun v => t.locs.getD v 0, s.rets.map fun v => t.locs.getD v 0)
          if s.r == r && s.tgt == tgt && s.args == cargs && s.rets == crets && tcells == (acells, rcells) then
            siteAgree := siteAgree + 1
          else
            siteDiffs := siteDiffs.push s!"{name}: site q={q}: table r={s.r} tgt={s.tgt} args={s.args} rets={s.rets} cells={tcells}; back end r={r} tgt={tgt} args={cargs} rets={crets} cells={(acells, rcells)}"
      | none => siteDiffs := siteDiffs.push s!"{name}: site q={q} (args {cargs}) not in the table"
    for s in t.sites do
      if !seenQ.contains s.q then
        siteTotal := siteTotal + 1
        siteDiffs := siteDiffs.push s!"{name}: table site q={s.q} r={s.r} not found by the back end"
    -- table jumps
    let theirArms := t.arms.toList
    for x in w.arms.toList.eraseDups do
      armTotal := armTotal + 1
      if theirArms.contains x then armAgree := armAgree + 1
      else armDiffs := armDiffs.push s!"{name}: back end table jump {x}, table {theirArms}"
    for x in theirArms do
      if !w.arms.contains x then
        armTotal := armTotal + 1
        armDiffs := armDiffs.push s!"{name}: table's table jump {x} not found by the back end"
    -- chains
    for (p, x, y, b, ts) in w.chains do
      chainTotal := chainTotal + 1
      match t.chains.find? (·.1 == p) with
      | some (_, x', y', b', ts') =>
          if x == x' && y == y' && b == b' && ts == ts' then chainAgree := chainAgree + 1
          else chainDiffs := chainDiffs.push s!"{name}: chain at {p}: back end ({x}, {y}, {b}, {ts.length} targets), table ({x'}, {y'}, {b'}, {ts'.length} targets), targets equal {ts == ts'}"
      | none => chainDiffs := chainDiffs.push s!"{name}: back end chain at {p} not in the table"
    for (p, _) in t.chains do
      if !w.chains.any (·.1 == p) then
        chainTotal := chainTotal + 1
        chainDiffs := chainDiffs.push s!"{name}: table chain at {p} not found by the back end"
    -- temporaries and runs
    let atoms := atomsOf tf.core.body
    let ourTmps := atoms.flatMap fun
      | .rangeCheck _ _ t1 t2 _ => [t1, t2]
      | .touch tv _ => [tv]
      | _ => []
    for (v, i) in ourTmps.zipIdx do
      tmpTotal := tmpTotal + 1
      let mine := (v.idx, (cellOfV pf v.idx).getD 0)
      if t.tmps[i]? == some mine then tmpAgree := tmpAgree + 1
      else tmpDiffs := tmpDiffs.push s!"{name}: temporary {i}: back end {mine}, table {t.tmps[i]?}"
    if t.tmps.size != ourTmps.length then tmpDiffs := tmpDiffs.push s!"{name}: {ourTmps.length} temporaries, table {t.tmps.size}"
    let ourRuns := (atoms.flatMap fun
      | .frameAddr _ run => run
      | _ => []).eraseDups
    for (v, i) in ourRuns.zipIdx do
      runTotal := runTotal + 1
      let mine := (v.idx, (cellOfV pf v.idx).getD 0)
      if t.runs[i]? == some mine then runAgree := runAgree + 1
      else runDiffs := runDiffs.push s!"{name}: run value {i}: back end {mine}, table {t.runs[i]?}"
    if t.runs.size != ourRuns.length then runDiffs := runDiffs.push s!"{name}: {ourRuns.length} run values, table {t.runs.size}"
    -- shared cells
    let ourSh := ((valueCells.toList.filter fun (n, vs) => 2 ≤ n && 2 ≤ vs.length).map (·.1)).mergeSort
    -- a cell shared in one table only because a value whose places differ, (2), is there
    let diffAt (c : Nat) : Bool := t.locs.zipIdx.any fun (cc, v) =>
      cellOfV pf v != some cc && (cc == c || cellOfV pf v == some c)
    if ourSh != t.sh then
      let only := ourSh.filter (!t.sh.contains ·) ++ t.sh.filter (!ourSh.contains ·)
      shCls := bump shCls (if only.all diffAt then "a value of (2) at the cell" else "unclassified")
    if ourSh == t.sh then shAgree := shAgree + 1
    else shDiffs := shDiffs.push s!"{name}: back end {ourSh.length} shared cells, table {t.sh.length}; only back end {ourSh.filter (!t.sh.contains ·)}, only table {t.sh.filter (!ourSh.contains ·)}"
    -- (4) counts
    if w.best.toList == t.pmax then pmaxAgree := pmaxAgree + 1
    else pmaxDiffs := pmaxDiffs.push s!"{name}: back end {w.best.toList}, table {t.pmax}"
    let theirArmCosts := LeanVM.Guest.Data.cplArms.getD j []
    for (x, cs) in w.armCosts do
      armCostTotal := armCostTotal + 1
      match theirArmCosts.find? (·.1 == x) with
      | some (_, cs') =>
          if cs == cs' then armCostAgree := armCostAgree + 1
          else
            let nd := ((cs.zip cs').filter fun (p, q) => p != q).length
            let ex := ((cs.zip cs').zipIdx.filter fun ((p, q), _) => p != q).take 3
            armCostDiffs := armCostDiffs.push s!"{name}: match on {x}: {nd} of {cs.length} arms differ (table {cs'.length}); first {ex.map fun ((p, q), k) => s!"arm {k}: back end {p}, table {q}"}"
      | none => armCostDiffs := armCostDiffs.push s!"{name}: match on {x} counted apart by the back end, not in Data.cplArms"
    for (x, _) in theirArmCosts do
      if !w.armCosts.any (·.1 == x) then
        armCostTotal := armCostTotal + 1
        armCostDiffs := armCostDiffs.push s!"{name}: Data.cplArms's match on {x} not found"
    -- (4') the completeness statements' own definitions, `Complete.pmaxP` and `Complete.armsP`
    let kd := t.key == "main_loop2"
    let ourPmax := LeanVM.Guest.Backend.Complete.ofCnt (LeanVM.Guest.Backend.Complete.pmaxP kd pf)
    if ourPmax == t.pmax then pmaxPAgree := pmaxPAgree + 1
    else pmaxPDiffs := pmaxPDiffs.push s!"{name}: pmaxP {ourPmax}, table {t.pmax}"
    let ourArms := LeanVM.Guest.Backend.Complete.armsP kd tf pf
    if ourArms == theirArmCosts then armsPAgree := armsPAgree + 1
    else armsPDiffs := armsPDiffs.push s!"{name}: armsP {ourArms.length} stages, table {theirArmCosts.length}"
    let keys := ourArms.map (·.1)
    if keys.eraseDups.length != keys.length then
      armsPDiffs := armsPDiffs.push s!"{name}: armsP has two stages on one selector"
    if LeanVM.Guest.Backend.Complete.alL pf.fn.body tf.core.body then alignedN := alignedN + 1
    else alignedDiffs := alignedDiffs.push name
  -- (1) the literals
  let mut pinOk := 0
  let mut pinDiffs : Array String := #[]
  for (n, v, wh) in T.pinned do
    let fss := (n.splitOn "+").map fun f => (pls.find? (·.fn.name == f)).map (·.fn.frameSize)
    if fss.all Option.isSome then
      let ours := (fss.filterMap id).sum
      if ours == v then pinOk := pinOk + 1 else pinDiffs := pinDiffs.push s!"{n} = {v} at {wh}: back end {ours}"
    else pinDiffs := pinDiffs.push s!"{n} at {wh}: no such function"
  -- (6) the jump table
  let mut jtAgree := 0
  let mut jtDiffs : Array String := #[]
  for (k, i) in slots.zipIdx do
    match slotPc k, T.jt.get? (base + i) with
    | some e, some e' => if e == e' then jtAgree := jtAgree + 1 else jtDiffs := jtDiffs.push s!"slot {base + i}: back end {e}, jtTrie {e'}"
    | some e, none => jtDiffs := jtDiffs.push s!"slot {base + i}: back end {e}, not in jtTrie"
    | none, some e' => jtDiffs := jtDiffs.push s!"slot {base + i}: back end fills none, jtTrie {e'}"
    | none, none => jtDiffs := jtDiffs.push s!"slot {base + i}: filled by neither"
  for (s, _) in T.jt.toList do
    if s < base || s ≥ base + slots.size then jtDiffs := jtDiffs.push s!"jtTrie slot {s} outside the back end's table"
  -- the report
  let n := pls.length
  o := o.say s!"functions: {n} (tables {T.fns.size}); jump table base {base}, {slots.size} slots; program size {size}"
  o := o.say ""
  o := o.say s!"(1) frame sizes: {fsAgree} of {n} agree with Data.frameSizes and the bundles' fs (main: placed frame + {slots.size} slots); literals in proofs: {pinOk} of {T.pinned.size}"
  for d in fsDiff ++ pinDiffs do o := o.say s!"  differs: {d}"
  o := o.say s!"(2) value cells: {cellsAgree} of {cellsTotal} agree; {cellDiffs.size} differ in {cellFns.size} functions"
  let resid : Std.HashMap (String × Nat) String := T.residual.foldl (fun m (f, v, k) => m.insert (f, v) k) {}
  let mut byKind : Std.HashMap String Nat := {}
  for (f, v, ours, cc) in cellDiffs do
    let k := s!"{(ours.splitOn " ").headD ""}/{resid.getD (f, v) "unlisted"}/{diffKind.getD (f, v) "?"}"
    byKind := byKind.insert k (byKind.getD k 0 + 1)
    o := o.note s!"cell {f} value {v}: back end {ours}, certificate {cc}, residual {resid.getD (f, v) "-"}"
  for (k, c) in byKind.toList.mergeSort (fun a b => a.1 ≤ b.1) do o := o.say s!"  {k}: {c}"
  o := o.say s!"  residual entries (B2/Residual.lean): {T.residual.size}"
  o := o.say s!"(3) plumbing: fixed cells {statAgree} of {statTotal} table entries agree, {statDiffs.size} differences, {statFns} of {n} functions identical"
  o := o.say s!"    call sites {siteAgree} of {siteTotal}; table jumps {armAgree} of {armTotal}; chains {chainAgree} of {chainTotal}; temporaries {tmpAgree} of {tmpTotal}; frame runs {runAgree} of {runTotal}; shared-cell lists {shAgree} of {n}"
  for (k, c) in statCls.toList do o := o.say s!"  fixed-cell differences, {c}: {k}"
  for (k, c) in shCls.toList do o := o.say s!"  shared-cell list differences, {c}: {k}"
  for (ds, k) in [(statDiffs, "fixed"), (siteDiffs, "site"), (armDiffs, "arm"), (chainDiffs, "chain"), (tmpDiffs, "tmp"), (runDiffs, "run"), (shDiffs, "sh")] do
    for d in (if detail then ds else ds.extract 0 12) do o := o.say s!"  {k}: {d}"
    if !detail && ds.size > 12 then o := o.say s!"  {k}: … {ds.size - 12} more"
  o := o.say s!"(4) counts: pmax {pmaxAgree} of {n} agree; separately counted arms {armCostAgree} of {armCostTotal} matches agree"
  for d in (if detail then pmaxDiffs else pmaxDiffs.extract 0 12) ++ armCostDiffs do o := o.say s!"  differs: {d}"
  if !detail && pmaxDiffs.size > 12 then o := o.say s!"  … {pmaxDiffs.size - 12} more pmax differences"
  o := o.say s!"(4') Complete.pmaxP {pmaxPAgree} of {n} functions equal Plumb.pmax; Complete.armsP {armsPAgree} of {n} equal Data.cplArms"
  for d in (if detail then pmaxPDiffs else pmaxPDiffs.extract 0 12) ++ (if detail then armsPDiffs else armsPDiffs.extract 0 12) do o := o.say s!"  differs: {d}"
  o := o.say s!"(4'') Complete.Aligned (alL): {alignedN} of {n} functions"
  for d in alignedDiffs.extract 0 12 do o := o.say s!"  not aligned: {d}"
  o := o.say s!"(5) path walk: cells written in two arms of one match: {armSharedTotal} in {armSharedFns} functions"
  for (k, c) in stats.toList.mergeSort (fun a b => a.1 ≤ b.1) do o := o.say s!"  {k}: {c}"
  let mut fk : Std.HashMap String (Array Finding) := {}
  for f in finds do fk := fk.insert f.kind ((fk.getD f.kind #[]).push f)
  for (k, fs) in fk.toList.mergeSort (fun a b => a.1 ≤ b.1) do
    let fns := (fs.map (·.fn)).toList.eraseDups
    o := o.say s!"  findings {k}: {fs.size} in {fns.length} functions"
    for f in (if detail then fs else fs.extract 0 20) do o := o.say s!"    {f.fn} @{f.pc}: {f.what}"
    if !detail && fs.size > 20 then o := o.say s!"    … {fs.size - 20} more"
  o := o.say s!"(6) jump table: {jtAgree} of {slots.size} slots agree with Data.jtTrie ({T.jt.size} entries); {jtDiffs.size} differences"
  for d in jtDiffs.extract 0 12 do o := o.say s!"  differs: {d}"
  if selftest then
    o := o.say "self-test: faults injected, detected / tried"
    for (k, (n, d)) in selfRes.toList.mergeSort (fun a b => a.1 ≤ b.1) do o := o.say s!"  {k}: {d} / {n}"
    for m in selfMiss do o := o.say s!"  not detected: {m}"
  for l in o.lines do IO.println l
  if detail then
    for l in o.detail do IO.println l
  return 0
