/-
  LeanVM.Compiler.Cut

  A function's piece in parts: its walk cut between top-level statements and between the arms of
  a `match`, the walk's state at each cut carried as data, and its code checked chunk by chunk.
-/

module

public import LeanVM.Compiler.Piece
public import LeanVM.Compiler.Sound.Fills

/-!
# Cut pieces

A function too large for one piece is checked in parts (`Sound/Cut.lean` glues them into its
`pieceOk`):

* its walk from the start to top-level statement `k₁` (`placeHead`), from `kᵢ` over the next
  statements (`placeBlockN`), and from the last cut to the end (`placeTail`), each an equation
  between the walk from one state and the next state, the states written out as data;
* a `match` statement in parts: the walk before its arms (`matchPre`, which gives the `MatchHead`),
  its arms a run at a time (`armsRunN`, which gives their blocks and the largest cell they reach),
  and the walk after them (`matchPost`); this is how the stages of a chain of `match`es, each a
  top-level statement, are placed one by one;
* `fnPreOk`: the checks `placeFn` makes besides the walk, on the last state;
* `cutHeadOk`: `pieceOk`'s comparisons but the code's, on the placed function of the last state, its
  jump table slots and size read off its statements (`blockFills`, `blockSize`), not emitted;
* `cutChunkOk`: chunk `c` of its resolved code is the compiled function's, the code read off its
  statements by position from the chunk's first instruction (`blockOpsFrom`: the statements, stages
  and arms before it skipped by their sizes, their instructions never made).

The states are `state_lit` definitions (`StateLit.lean`): each map written out as a trie sharing
the previous state's, so no check evaluates the walk that led to its state.
-/

namespace LeanVM.Compiler

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The first `n` statements of a block, each placed with the statements after it in the block. -/
def placeBlockN : List Stmt → Nat → P Unit
  | [], _ => pure ()
  | _ :: _, 0 => pure ()
  | s :: rest, n + 1 => do
      placeStmt s rest
      endStmt
      placeBlockN rest n

/-- A function's parameters in its argument cells. -/
def placeParams (tf : TracedFn) : P Unit :=
  tf.core.params.zipIdx.forM fun (v, k) => bindTo v (.cell (2 + k))

/-- A function's walk to its top-level statement `k`. -/
def placeHead (tf : TracedFn) (k : Nat) : P Unit := do
  placeParams tf
  placeBlockN tf.core.body k

/-- A function's walk from its top-level statement `k` to its end. -/
def placeTail (tf : TracedFn) (k : Nat) : P Unit := do
  placeBlock (tf.core.body.drop k)
  flush []
  if !(← get).rest.isEmpty then failP "the trace goes on past the function"

/-! ## A `match` in parts -/

/-- What a `match`'s walk computes before its arms (`placeMatch`): its selector's cell, its join,
its table, the hints and entry of the chain statement it begins (none for a later stage), how its
arms leave, the cell they start from, the pooled `1` and the frame pointer's cell. -/
structure MatchHead where
  lx : Cell
  join : Cell
  first : Nat
  head : Option (List LHint × Cell)
  exit : ArmExit
  base : Cell
  one : Cell
  sfp : Cell

/-- `placeMatch`'s walk before its arms. -/
def matchHeadOf (x : V) (n : Nat) (rest : List Stmt) (entered : Option (Nat × Cell))
    (chained : Bool) : P MatchHead := do
  let (lx, nextSel, sfp, one) ← matchCells x rest chained
  let (join, first, head) ← match entered with
    | some (first, join) => pure (join, first, none)
    | none => do
        let join ← fresh
        let hints ← takeHints
        let first ← allocTable n
        let entry ← fresh
        pure (join, first, some (hints, entry))
  let exit ← match nextSel with
    | some (x', n') => do pure (ArmExit.next x' (← allocTable n') one sfp)
    | none => pure (ArmExit.join join one sfp)
  let base := (← get).next
  pure ⟨lx, join, first, head, exit, base, one, sfp⟩

/-- `placeMatch`'s walk after its arms, which gave `blocks`. -/
def matchTail (mc : MatchHead) (blocks : List (List PStmt)) : P Unit := do
  expect isEmit "a match"
  match mc.head with
  | some (hints, entry) => push (.chain hints mc.join mc.lx entry mc.one mc.sfp [mc.first] [blocks])
  | none =>
      let st ← get
      match st.out.back? with
      | some (.chain h j x e o s firsts stages) =>
          let node := PStmt.chain h j x e o s (firsts ++ [mc.first]) (stages ++ [blocks])
          set { st with out := st.out.pop.push node }
      | _ => failP "a chained match follows no match"
  match mc.exit with
  | .next _ nf _ _ => modify fun s => { s with chainIn := some (nf, mc.join) }
  | .join .. => pure ()

/-- A `match` statement's walk before its arms (`placeStmt`). -/
def matchPre (x : V) (n : Nat) (rest : List Stmt) : P MatchHead := do
  flush []
  let st ← get
  set { st with chainIn := none, chain := false }
  matchHeadOf x n rest st.chainIn st.chain

/-- One arm `j` of `n` of a `match` (`placeArms`): its block with how it leaves, and the cell past
it. -/
def armStep (arm : List Stmt) (j n : Nat) (base : Cell) (exit : ArmExit) :
    P (List PStmt × Cell) := do
  modify fun s => { s with next := base }
  let blk ← inBlock (placeBlock arm)
  let leave ← match exit with
    | .next x first one sfp => do
        let e ← fresh
        pure [PStmt.op [] (.slot x first e), .op [] (.jump one e sfp)]
    | .join join one sfp =>
        pure (if j + 1 != n then [PStmt.op [] (.jump one join sfp)] else [])
  let top := (← get).next
  pure (blk ++ leave, top)

/-- The arms of a `match` from arm `j` of `n`, each from the cell `base`: their blocks, and the
largest of `base` and the cells past each. -/
def armsRun : List (List Stmt) → Nat → Nat → Cell → ArmExit → P (List (List PStmt) × Cell)
  | [], _, _, base, _ => pure ([], base)
  | arm :: more, j, n, base, exit => do
      let (blk, top) ← armStep arm j n base exit
      let (blocks, t) ← armsRun more (j + 1) n base exit
      pure (blk :: blocks, max t top)

/-- The first `m` arms of `armsRun`. -/
def armsRunN : List (List Stmt) → Nat → Nat → Cell → ArmExit → Nat → P (List (List PStmt) × Cell)
  | [], _, _, base, _, _ => pure ([], base)
  | _ :: _, _, _, base, _, 0 => pure ([], base)
  | arm :: more, j, n, base, exit, m + 1 => do
      let (blk, top) ← armStep arm j n base exit
      let (blocks, t) ← armsRunN more (j + 1) n base exit m
      pure (blk :: blocks, max t top)

/-- A `match` statement's walk after its arms, which gave `blocks` and reached the cell `top`, with
the statement's end (`endStmt`). -/
def matchPost (mc : MatchHead) (blocks : List (List PStmt)) (top : Cell) : P Unit := do
  modify fun s => { s with next := top }
  matchTail mc blocks
  endStmt

/-- The selector of a `match` statement. -/
def selOf : Stmt → V
  | .match_ x _ => x
  | _ => default

/-- The arms of a `match` statement. -/
def armsOf : Stmt → List (List Stmt)
  | .match_ _ arms => arms
  | _ => []

/-- Whether statement `i` of the block is a `match`. -/
def isMatchAt (body : List Stmt) (i : Nat) : Bool :=
  match body.drop i with
  | .match_ _ _ :: _ => true
  | _ => false

/-! ## States written as data -/

/-- The trace of `tf` from its event `k`: a state's `rest`, which `state_lit` writes in the trace's
own parts. -/
def traceRest (tf : TracedFn) (k : Nat) : List Event := tf.trace.toList.drop k

/-- The context of a function whose trace has `N` events: its length written out, so that a check
from a cut reads no trace's length. -/
theorem ctxOf_fuel {loops : Loops} {sigs : SMap (Nat × Nat)} {tf : TracedFn} {N : Nat}
    (h : tf.trace.size = N) : ctxOf loops sigs tf = { ctxOf loops sigs tf with fuel := N } := by
  rw [← h]
  rfl

/-! ## Maps written as additions -/

/-- The entries `l` added to a map, in order. -/
def KMap.insertAll {κ α : Type} [DecidableEq κ] [Keyed κ] (m : KMap κ α) (l : List (κ × α)) :
    KMap κ α :=
  l.foldl (fun m x => m.insert x.1 x.2) m

/-- The entries `l` added to a map, in order. -/
def PMap.insertAll {α : Type} (m : PMap α) (l : List ((Nat × Nat) × α)) : PMap α :=
  l.foldl (fun m x => m.insert x.1 x.2) m

/-- The entries `l` added to a map, in order. -/
def NMap.insertAll {α : Type} (m : NMap α) (l : List (Nat × α)) : NMap α :=
  l.foldl (fun m x => m.insert x.1 x.2) m

/-! ## The checks on the last state -/

/-- The placed function and the jump tables a function's walk ending in `st` gives. -/
def placedOf (tf : TracedFn) (st : St) : Placed × Tables :=
  (⟨{ name := tf.core.name, body := st.out.toList, frameSize := st.next }, st.locs⟩, st.tables)

/-- The checks `placeFn` makes of a function besides its walk, the walk ending in `st`. -/
def fnPreOk (loops : Loops) (tf : TracedFn) (st : St) : Bool :=
  !((loops[tf.core.name]?).any (·.registered) && (sigOf tf).2 != 0) &&
    (match tf.core.body.getLast? with
      | some (.ret _) => true
      | _ => false) &&
    decide (st.next < 2 ^ 64)

/-! ## A function's code from an instruction on -/

mutual
/-- `(stmtOps s pos).drop k`: a chain statement's stages, arms and statements before instruction `k`
skipped by their sizes, their instructions never made. -/
def stmtOpsFrom : PStmt → Nat → Nat → List LOp
  | .chain _ join x entry one sfp firsts stages, pos, k =>
      if k < 3 then
        ([LOp.set join (.local (pos + 3 + stagesSize stages)), LOp.slot x (firsts.headD 0) entry,
          LOp.jump one entry sfp]).drop k ++ stagesOps stages (pos + 3)
      else stagesOpsFrom stages (pos + 3) (k - 3)
  | s, pos, k => (stmtOps s pos).drop k

/-- `(blockOps b pos).drop k`, the statements before instruction `k` skipped by their sizes. -/
def blockOpsFrom : List PStmt → Nat → Nat → List LOp
  | [], _, _ => []
  | s :: ss, pos, k =>
      if stmtSize s ≤ k then blockOpsFrom ss (pos + stmtSize s) (k - stmtSize s)
      else stmtOpsFrom s pos k ++ blockOps ss (pos + stmtSize s)

/-- `(armsOps as pos).drop k`, the arms before instruction `k` skipped by their sizes. -/
def armsOpsFrom : List (List PStmt) → Nat → Nat → List LOp
  | [], _, _ => []
  | a :: as, pos, k =>
      if blockSize a ≤ k then armsOpsFrom as (pos + blockSize a) (k - blockSize a)
      else blockOpsFrom a pos k ++ armsOps as (pos + blockSize a)

/-- `(stagesOps ss pos).drop k`, the stages before instruction `k` skipped by their sizes. -/
def stagesOpsFrom : List (List (List PStmt)) → Nat → Nat → List LOp
  | [], _, _ => []
  | s :: ss, pos, k =>
      if armsSize s ≤ k then stagesOpsFrom ss (pos + armsSize s) (k - armsSize s)
      else armsOpsFrom s pos k ++ stagesOps ss (pos + armsSize s)
end

/-- `pieceOk`'s comparisons of the placed function `pf` and the tables `t'` but the code's, and the
number of chunks; the slots and the size read off the placed statements. -/
def cutHeadOk (t : Tables) (tf : TracedFn) (o : FnOut) (pc0 : Nat) (cf : CompiledFunction)
    (pf : Placed) (t' : Tables) : Bool :=
  t'.len == o.len && t'.shared.length == o.shared.length + t.shared.length &&
    decide (t'.shared.take o.shared.length = o.shared) &&
    allPairs fillIs (blockFills pf.fn.name pf.fn.body 0) o.fills &&
    pf.fn.frameSize == o.frame && blockSize pf.fn.body == o.size && decide (cf.name = tf.core.name) &&
    cf.entryPc == pc0 && cf.instructionCount == o.size &&
    cf.chunks.length == (o.size + chunkSize - 1) / chunkSize

/-- Chunk `c` of the placed function `pf`'s code, resolved at the layout `l` from `pc0` with frame
size `frame`, is the compiled function's: the code read off the statements by position. -/
def cutChunkOk (l : Layout) (pc0 frame : Nat) (cf : CompiledFunction) (pf : Placed) (c : Nat) :
    Bool :=
  decide (((blockOpsFrom pf.fn.body 0 (c * chunkSize)).take chunkSize).map
    (resolveOp l pc0 frame) = cf.chunks.getD c [])

/-- `cutHeadOk` and `fnPreOk` for function `j` of `p`, as `pieceAt` reads it, its walk ending in
`st`. -/
def cutHeadAt (loops : Loops) (p : List TracedFn) (os : List FnOut) (cfs : List CompiledFunction)
    (j : Nat) (st : St) : Bool :=
  let n := (tablesEnd os).len
  let tf := p.getD j default
  fnPreOk loops tf st &&
    cutHeadOk (tablesAt os j) tf (os.getD j default) (n + ((os.take j).map (·.size)).sum)
      (cfs.getD j noFunction) (placedOf tf st).1 (placedOf tf st).2

/-- `cutChunkOk` for function `j` of `p`, as `pieceAt` reads it, its walk ending in `st`. -/
def cutChunkAt (l : Layout) (p : List TracedFn) (os : List FnOut) (cfs : List CompiledFunction)
    (j : Nat) (st : St) (c : Nat) : Bool :=
  let n := (tablesEnd os).len
  cutChunkOk l (n + ((os.take j).map (·.size)).sum) ((framesOf n os).getD j 0) (cfs.getD j noFunction)
    (placedOf (p.getD j default) st).1 c

end
end LeanVM.Compiler
