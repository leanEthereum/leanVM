/-
  LeanVM.Compiler.Joined

  The values of a function's trace that share a cell with a value they are copied from, into, or
  asserted equal to: their allocations marked `Kind.joined` and moved to the statement that first
  names them.
-/

module

public import LeanVM.Compiler.Trace
public import LeanVM.Core.Renumber
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Values joined to the cells of their copies

A `copy d s` (and an `assert a == b`) costs a `MUL` because its two values have cells of their
own. When one of them, the mover, is named only from one statement `F` on, by statements of the
block of `F` and blocks inside it, and the statements of that block from `F` to the copy are all
atoms, the mover needs no cell of its own: placed right before `F`, it takes the cell of the other
value (its partner) if that one is placed already, and the copy, its two values in one cell,
emits nothing. `markJoined` rewrites the trace so that placement does this:

* **run splitting**: a `Kind.cell` run is cut into the segments some statement needs in
  consecutive cells (a KECCAK's tail, cap and output runs, an `addr` run, a hint's destination);
  a run under a windows hint (`at` folded into its destination), or with a need across runs,
  stays whole;
* **merges**: a segment (or one value placement takes from a pool: a `const`, `add`, `load`, or a
  `mul` of no shifted factor) whose values are all named only from `F` on in `F`'s block, each
  equated by an atom of the run of atoms from `F` with a partner placed before, in consecutive
  cells for a segment of several values, is made `Kind.joined` and moved to the end of the flush
  before `F`;
* **reservation**: a partner allocated by a later flush of that run of atoms (a `Kind.cell`
  segment, or the return area) moves to the same point, before the mover, so that it is placed
  first.

`Kind.joined` placement binds the values to the partners' cells only where an atom among the
next statements, reached through atoms only, equates each with a value placed in that cell, the
cells consecutive, and otherwise takes the next free cells: the trace is advice, and no proof of
the back end depends on the pass. Soundness holds for every trace (a copy or an `assert ==` is
dropped only when its two values are one cell), and completeness is the per-function checks
(`scopedB`), evaluated on the program as traced: a moved allocation still comes before every
statement naming its values, in a block around them.
-/

namespace LeanVM.Compiler

open LeanVM.Core

@[expose] public section

namespace Joined

/-- What the pass reads of a statement: its block, its position there, the index of its `emit`
in the trace, and the atom it is. -/
structure SInfo where
  blk : Nat
  idx : Nat
  emit : Nat := 0
  /-- The index of the first event of the flush before it. -/
  start : Nat := 0
  atom : Option Atom
  deriving Inhabited

/-- The walk of a core function with its trace, in placement's order. -/
structure WSt where
  /-- The next event. -/
  pos : Nat := 0
  /-- The trace and the body part nowhere. -/
  ok : Bool := true
  /-- The statements, numbered in placement's order (a branch or a `match` before its blocks). -/
  stmts : Array SInfo := #[]
  /-- The block around each block; block `0` is the body. -/
  parent : Array Nat := #[0]
  /-- The statements of each block, in order. -/
  blkStmts : Array (Array Nat) := #[#[]]
  /-- The statements naming each value, in order. -/
  names : Std.HashMap V (Array Nat) := {}

abbrev W := StateM WSt

/-- The values a statement names itself, its blocks apart. -/
def ownVals : Stmt → List V
  | .atom a => a.vals
  | .ite c _ _ => [c]
  | .match_ x _ => [x]
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: args ++ rets
  | .ret vs => vs

/-- An event a flush passes. -/
def isFlushEv : Event → Bool
  | .alloc .. | .use _ | .shift .. | .chain | .note _ => true
  | _ => false

/-- Pass the events of a flush, at most `fuel`. -/
def flushW (evs : Array Event) : Nat → W Unit
  | 0 => pure ()
  | fuel + 1 => do
    let st ← get
    match evs[st.pos]? with
    | some e =>
      if isFlushEv e then
        set { st with pos := st.pos + 1 }
        flushW evs fuel
      else pure ()
    | none => pure ()

/-- Pass the event `p` accepts, which the walk must be at; its index. -/
def expectW (evs : Array Event) (p : Event → Bool) : W Nat := do
  let st ← get
  match evs[st.pos]? with
  | some e =>
    if p e then
      set { st with pos := st.pos + 1 }
      return st.pos
    else
      set { st with ok := false }
      return st.pos
  | none =>
    set { st with ok := false }
    return st.pos

/-- Whether the walk is at an `enter`. -/
def atEnter (evs : Array Event) : W Bool := do
  match evs[(← get).pos]? with
  | some .enter => return true
  | _ => return false

/-- A statement of block `b` begins: its number. -/
def newStmt (b : Nat) (s : Stmt) : W Nat := modifyGet fun st =>
  let sid := st.stmts.size
  let idx := (st.blkStmts[b]?.map (·.size)).getD 0
  let atom := match s with
    | .atom a => some a
    | _ => none
  let names := (ownVals s).foldl (fun m v => m.insert v ((m.getD v #[]).push sid)) st.names
  let stmts := st.stmts.push { blk := b, idx, start := st.pos, atom }
  let blkStmts := st.blkStmts.modify b (·.push sid)
  (sid, { st with stmts, blkStmts, names })

/-- A block inside block `b` begins: its number. -/
def newBlock (b : Nat) : W Nat := modifyGet fun st =>
  (st.parent.size, { st with parent := st.parent.push b, blkStmts := st.blkStmts.push #[] })

/-- The `emit` of statement `sid` is event `e`. -/
def setEmit (sid e : Nat) : W Unit :=
  modify fun st => { st with stmts := st.stmts.modify sid ({ · with emit := e }) }

def isEmit : Event → Bool
  | .emit => true
  | _ => false

def isEnter : Event → Bool
  | .enter => true
  | _ => false

def isLeave : Event → Bool
  | .leave => true
  | _ => false

/-- A block inside block `b`, from its `enter` to its `leave`, its statements walked by `body`. -/
def walkInner (evs : Array Event) (b : Nat) (body : Nat → W Unit) : W Unit := do
  discard <| expectW evs isEnter
  let nb ← newBlock b
  body nb
  flushW evs evs.size
  discard <| expectW evs isLeave

mutual
/-- The statements of block `b`. -/
def walkBlock (evs : Array Event) (b : Nat) : List Stmt → W Unit
  | [] => pure ()
  | s :: rest => do
    walkStmt evs b s
    walkBlock evs b rest

/-- A statement of block `b`: the flush before it, its blocks, its `emit`. -/
def walkStmt (evs : Array Event) (b : Nat) : Stmt → W Unit
  | .ite c z nz => do
    let sid ← newStmt b (.ite c [] [])
    flushW evs evs.size
    walkInner evs b fun nb => walkBlock evs nb z
    if ← atEnter evs then walkInner evs b fun nb => walkBlock evs nb nz
    setEmit sid (← expectW evs isEmit)
  | .match_ x arms => do
    let sid ← newStmt b (.match_ x [])
    flushW evs evs.size
    walkArms evs b arms
    setEmit sid (← expectW evs isEmit)
  | s => do
    let sid ← newStmt b s
    flushW evs evs.size
    setEmit sid (← expectW evs isEmit)

/-- The arms of a `match` in block `b`. -/
def walkArms (evs : Array Event) (b : Nat) : List (List Stmt) → W Unit
  | [] => pure ()
  | arm :: more => do
    walkInner evs b fun nb => walkBlock evs nb arm
    walkArms evs b more
end

/-- The walk of a function's body with its trace. -/
def walkFn (f : Fn) (evs : Array Event) : WSt :=
  let m : W Unit := do
    walkBlock evs 0 f.body
    flushW evs evs.size
  let ((), st) := m.run {}
  if st.pos != evs.size then { st with ok := false } else st

/-- Whether block `b` is block `outer` or a block inside it. -/
def within (parent : Array Nat) (outer : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, b => b == outer || (b != 0 && within parent outer fuel (parent.getD b 0))

/-! ## Runs -/

/-- The runs of values a statement needs in consecutive cells, and the values whose whole run it
needs (a windows hint writes from before its first value). -/
def needRuns : Atom → List (List V) × List V
  | .keccak ins outs _ _ => ([(ins.drop 4).take 4, (ins.drop 9).take 4, outs], [])
  | .frameAddr _ run => ([run], [])
  | .hint h =>
    match h with
    | .witness _ (.stack cs) | .bits _ _ _ (.stack cs) | .bitsExp _ _ (.stack cs)
    | .digitsExp _ _ _ _ _ _ (.stack cs) | .log2Ceil (.stack cs) _ _ _ => ([cs], [])
    | .windowsExp _ _ _ _ (.stack cs) => ([], cs)
    | .limbs _ dst => ([dst], [])
    | _ => ([], [])
  | _ => ([], [])

/-- Where a value is made: the event and its position in it. -/
abbrev AllocMap := Std.HashMap V (Nat × Nat)

/-- The values each allocation makes and where. -/
def allocMap (evs : Array Event) : AllocMap := Id.run do
  let mut m : AllocMap := {}
  for i in [0:evs.size] do
    if let some (.alloc vs _) := evs[i]? then
      for (v, p) in vs.zipIdx do
        m := m.insert v (i, p)
  return m

/-- For each `Kind.cell` allocation of two values or more, the positions after which a segment
may end, or none if the run stays whole. -/
def cuts (evs : Array Event) (am : AllocMap) (atoms : List Atom) : Std.HashMap Nat (Array Bool) :=
  Id.run do
    -- `true` at `p`: the values at `p` and `p + 1` may lie apart.
    let mut cut : Std.HashMap Nat (Array Bool) := {}
    for i in [0:evs.size] do
      if let some (.alloc vs .cell) := evs[i]? then
        if 2 ≤ vs.length then cut := cut.insert i (Array.replicate (vs.length - 1) true)
    let mut rigid : Std.HashSet Nat := {}
    for a in atoms do
      let (need, whole) := needRuns a
      for r in need do
        for (x, y) in r.zip r.tail do
          match am[x]?, am[y]? with
          | some (i, p), some (j, q) =>
            if i == j && q == p + 1 then
              cut := cut.modify i (·.set! p false)
            else
              rigid := (rigid.insert i).insert j
          | some (i, _), none => rigid := rigid.insert i
          | none, some (j, _) => rigid := rigid.insert j
          | none, none => pure ()
      for v in whole do
        if let some (i, _) := am[v]? then rigid := rigid.insert i
    for i in rigid do
      cut := cut.erase i
    return cut

/-- The segments of an allocation: `(start, length)`. -/
def segments (n : Nat) (cut : Option (Array Bool)) : List (Nat × Nat) :=
  match cut with
  | none => [(0, n)]
  | some c => Id.run do
    let mut out : Array (Nat × Nat) := #[]
    let mut start := 0
    for p in [0:n] do
      if p + 1 == n || c.getD p false then
        out := out.push (start, p + 1 - start)
        start := p + 1
    return out.toList

/-! ## The plan -/

/-- Where a value's cell is, as far as the pass predicts it: the parameters' cells, an
allocation that keeps its place (its values' cells stay consecutive but for segments moved out,
and partners are never moved), or a moved segment (an allocation and the start of the segment in
it); with the offset in it, and `loose` for a value a pool may place anywhere. -/
inductive Grp where
  | param
  | ev (i : Nat)
  | seg (i start : Nat)
  deriving BEq, Hashable, Inhabited

/-- When an allocation is placed, in the order placement meets it: an event of the trace at its
index, or one moved before the `emit` of a statement, in the order the pass moved it. -/
abbrev Key := Nat × Nat

def Key.lt (a b : Key) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- The pass's state. -/
structure PSt where
  /-- The allocations moved: the segment, to the `emit` of which event, in which order, and its
  kind there. -/
  moved : Std.HashMap (Nat × Nat) (Nat × Nat × Kind) := {}
  /-- The values that may not move later. -/
  fixed : Std.HashSet V := {}
  seq : Nat := 1
  deriving Inhabited

/-- The options of the pass. -/
structure Opts where
  /-- An `assert ==` is an anchor too. -/
  aeq : Bool := true
  /-- A partner made later in the run of atoms is made first. -/
  reserve : Bool := true

/-- What the pass reads of the function, once. -/
structure Info where
  evs : Array Event
  w : WSt
  am : AllocMap
  cut : Std.HashMap Nat (Array Bool)
  params : Std.HashMap V Nat
  /-- The values a pooled `mul` may make shifted, and `addr` pointers. -/
  shifty : Std.HashSet V
  /-- For each event, the index of the first `emit` from it on. -/
  nextEmit : Array Nat

namespace Info

/-- The segment of a value: its allocation, start, length, and offset in it, with the
allocation's kind. -/
def segOf (I : Info) (v : V) : Option (Nat × Nat × Nat × Nat × Kind) := do
  let (i, p) ← I.am[v]?
  let .alloc vs k ← I.evs[i]? | none
  let segs := if k == .cell then segments vs.length I.cut[i]? else [(0, vs.length)]
  let (s, n) ← segs.find? fun (s, n) => s ≤ p && p < s + n
  return (i, s, n, p - s, k)

/-- The values of a segment. -/
def segVals (I : Info) (i s n : Nat) : List V :=
  match I.evs[i]? with
  | some (.alloc vs _) => (vs.drop s).take n
  | _ => []

end Info

/-- When the segment `(i, s)` is placed under the plan; a value a pool places, by its statement. -/
def keyOf (I : Info) (P : PSt) (i s : Nat) (k : Kind) : Key :=
  match P.moved[(i, s)]? with
  | some (e, q, _) => (2 * e + 1, q)
  | none => if k == .pooled then (2 * I.nextEmit.getD i 0 + 3, 0) else (2 * i + 2, 0)

/-- Where a value's cell is predicted, and when it is placed: none for a value placed in no
cell (an `addr` pointer, a value no allocation makes); `loose` for a value a pool may place in
any cell. -/
def predict (I : Info) (P : PSt) (v : V) : Option (Grp × Nat × Key × Bool) :=
  match I.params[v]? with
  | some k => some (.param, k, (0, 0), false)
  | none => do
    let (i, s, _, off, k) ← I.segOf v
    let (_, p) ← I.am[v]?
    let key := keyOf I P i s k
    match k with
    | .addr | .unnamed => none
    | _ =>
      if P.moved.contains (i, s) then some (.seg i s, off, key, false)
      else if k == .pooled then some (.ev i, p, key, true)
      else some (.ev i, p, key, false)

/-- Whether a value placement takes from a pool may be made in a cell given instead: the result
of a `const`, an `add`, a `load`, or a `mul` with no shifted factor, made by statement `a`. -/
def convertible (I : Info) (v : V) : Atom → Bool
  | .const d _ | .add d _ _ | .load d _ _ => d == v
  | .mul d a b => d == v && !I.shifty.contains a && !I.shifty.contains b
  | _ => false

/-- Try to join the segment of `m`, linked to `u` by the atom of statement `aid`: the new plan. -/
def tryJoin (o : Opts) (I : Info) (P : PSt) (aid : Nat) (m : V) : Option PSt := do
  let A ← I.w.stmts[aid]?
  let (i, s, n, _, k) ← I.segOf m
  if !(k == .cell || k == .pooled) || P.moved.contains (i, s) then none
  let S := I.segVals i s n
  if S.isEmpty || S.any (fun v => P.fixed.contains v || I.params.contains v)
  then none
  -- The statements naming the segment: all in `A`'s block or inside it, the first in it.
  let nm := S.flatMap fun v => ((I.w.names[v]?).getD #[]).toList
  let fid ← nm.min?
  let F ← I.w.stmts[fid]?
  let B := A.blk
  let fuel := I.w.parent.size + 1
  if F.blk != B || A.idx < F.idx then none
  if !nm.all fun sid => (I.w.stmts[sid]?).any fun x => within I.w.parent B fuel x.blk then none
  if k == .pooled then
    let some fa := F.atom | none
    if n != 1 || !convertible I m fa then none
  -- The run of atoms from `F`.
  let blk := (I.w.blkStmts[B]?).getD #[]
  let win := ((blk.toList.drop F.idx).takeWhile fun sid =>
    (I.w.stmts[sid]?).any (·.atom.isSome)).filterMap fun sid =>
      (I.w.stmts[sid]?).bind fun x => x.atom.map (sid, ·)
  if !win.any (·.1 == aid) then none
  let F' ← I.evs[F.emit]?
  if !(F' matches .emit) then none
  -- Each value's partner: the first atom of the run equating it with a value placed before, or
  -- one reserved.
  let mut P := P
  let mut parts : Array (Grp × Nat × Bool) := #[]
  let mut us : Array V := #[]
  for v in S do
    let mut found : Option (Grp × Nat × Bool) := none
    for (aid', a) in win do
      if found.isNone then
        if let some u := eqPartner v a then
          if !S.contains u then
            if let some (g, off, key, loose) := predict I P u then
              if Key.lt key (2 * F.start + 2, 0) then
                found := some (g, off, loose)
                us := us.push u
              else if o.reserve then
                -- A partner made in the flush of a later atom of the run, up to this one: its
                -- segment moves before the mover.
                if let some (j, t, len, off', kind) := I.segOf u then
                  let R := I.segVals j t len
                  let upTo := (I.w.stmts[aid']?).any (j < ·.emit)
                  if (kind == .cell || kind == .ret) && !P.moved.contains (j, t) &&
                      F.start ≤ j && upTo && !R.any (fun r => P.fixed.contains r) then
                    let moved := P.moved.insert (j, t) (F.start, P.seq, kind)
                    P := { P with moved, seq := P.seq + 1, fixed := R.foldl (·.insert ·) P.fixed }
                    found := some (.seg j t, off', false)
                    us := us.push u
    match found with
    | some p => parts := parts.push p
    | none => none
  -- Consecutive partners for a run of several values.
  if 2 ≤ S.length then
    let some (g0, o0, _) := parts[0]? | none
    if !(parts.toList.zipIdx.all fun ((g, off, loose), q) => g == g0 && off == o0 + q && !loose)
    then none
  let fixed := (S ++ us.toList).foldl (·.insert ·) P.fixed
  some { P with moved := P.moved.insert (i, s) (F.start, P.seq, .joined), seq := P.seq + 1, fixed }

/-- The partners of a statement's anchors: the two values of a copy, or of an `assert ==`. -/
def anchor (o : Opts) : Atom → Option (V × V)
  | .copy d s => if d == s then none else some (d, s)
  | .assertEq a b => if o.aeq && a != b then some (a, b) else none
  | _ => none

/-- The plan of a function: the segments moved, in the order of the anchors. -/
def plan (o : Opts) (f : Fn) (evs : Array Event) : Option (Info × PSt) := do
  let w := walkFn f evs
  if !w.ok then none
  let am := allocMap evs
  let atoms := w.stmts.toList.filterMap (·.atom)
  let cut := cuts evs am atoms
  let params := f.params.zipIdx.foldl (fun m (v, k) => m.insert v k) ({} : Std.HashMap V Nat)
  -- `addr` pointers, and the products of them a pool keeps shifted.
  let mut shifty : Std.HashSet V := {}
  for e in evs do
    if let .alloc vs .addr := e then shifty := vs.foldl (·.insert ·) shifty
  for a in atoms do
    if let .mul d x y := a then
      if shifty.contains x || shifty.contains y then shifty := shifty.insert d
  let nextEmit := Id.run do
    let mut a := Array.replicate evs.size evs.size
    let mut nxt := evs.size
    for q in [0:evs.size] do
      let i := evs.size - 1 - q
      if evs[i]? matches some .emit then nxt := i
      a := a.set! i nxt
    return a
  let I : Info := { evs, w, am, cut, params, shifty, nextEmit }
  let mut P : PSt := {}
  for aid in [0:w.stmts.size] do
    if let some a := (w.stmts[aid]?).bind (·.atom) then
      if let some (x, y) := anchor o a then
        match tryJoin o I P aid x with
        | some P' =>
          P := { P' with fixed := P'.fixed.insert y }
        | none =>
          match tryJoin o I P aid y with
          | some P' => P := { P' with fixed := P'.fixed.insert x }
          | none => pure ()
  return (I, P)

/-- What replaces each event of the trace under the plan. -/
def parts (I : Info) (P : PSt) : List (List Event) := Id.run do
  -- The allocations moved to the start of each statement's flush, in order.
  let mut before : Std.HashMap Nat (Array (Nat × Event)) := {}
  for ((i, s), (e, q, kind)) in P.moved.toList do
    if let some (.alloc vs k) := I.evs[i]? then
      let n := if k == .cell then
          ((segments vs.length I.cut[i]?).find? (·.1 == s)).map (·.2) |>.getD 0
        else vs.length
      before := before.insert e (((before[e]?).getD #[]).push (q, .alloc ((vs.drop s).take n) kind))
  let mut out : Array (List Event) := #[]
  for i in [0:I.evs.size] do
    let mv := (((before[i]?).getD #[]).qsort (fun a b => a.1 < b.1)).toList.map (·.2)
    match I.evs[i]? with
    | some (.alloc vs k) =>
      let segs := if k == .cell then segments vs.length I.cut[i]? else [(0, vs.length)]
      if segs.any fun (s, _) => P.moved.contains (i, s) then
        out := out.push (mv ++ segs.filterMap fun (s, n) =>
          if P.moved.contains (i, s) then none else some (.alloc ((vs.drop s).take n) k))
      else out := out.push (mv ++ [.alloc vs k])
    | some e => out := out.push (mv ++ [e])
    | none => pure ()
  return out.toList

end Joined

open Joined in
/-- The events replacing each event of a function's trace under `markJoined`. -/
def markJoinedParts (f : Fn) (trace : Array Event) (o : Opts := {}) : List (List Event) :=
  match plan o f trace with
  | some (I, P) => parts I P
  | none => trace.toList.map ([·])

/-- A function's trace with its copies' and `assert ==`s' movers made `Kind.joined` at the
statement first naming them, their partners made first where needed. -/
def markJoined (f : Fn) (trace : Array Event) : Array Event :=
  (markJoinedParts f trace).flatten.toArray

/-- The source lines of a function's statements, `(n, line)` with `n` the events of the trace
before the statement, moved to the positions of `markJoined f trace`. -/
def markJoinedLines (f : Fn) (trace : Array Event) (lines : Array (Nat × Nat)) :
    Array (Nat × Nat) :=
  let (pos, n) := (markJoinedParts f trace).foldl (init := (#[], 0)) fun (pos, n) p =>
    (pos.push n, n + p.length)
  let pos := pos.push n
  lines.map fun (k, line) => (pos.getD k k, line)

end
end LeanVM.Compiler
