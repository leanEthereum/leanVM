/-
  LeanVM.Guest.Backend.Cut

  A function's piece in parts: its walk cut between top-level statements, the walk's state at
  each cut carried as data, and its code checked chunk by chunk.
-/

module

public import LeanVM.Guest.Backend.Piece

/-!
# Cut pieces

A function too large for one piece is checked in parts (`Sound/Cut.lean` glues them into its
`pieceOk`):

* its walk from the start to top-level statement `k₁` (`placeHead`), from `kᵢ` over the next
  statements (`placeBlockN`), and from the last cut to the end (`placeTail`), each an equation
  between the walk from one state and the next state, the states written out as data;
* `fnPreOk`: the checks `placeFn` makes besides the walk, on the last state;
* `cutHeadOk`: `pieceOk`'s comparisons but the code's, on the placed function of the last state;
* `cutChunkOk`: chunk `c` of its resolved code is the compiled function's.

A state's maps are written as the one before them with the entries added (`KMap.insertAll`,
`PMap.insertAll`, `NMap.insertAll`), its statements as the ones before them with the new ones
(`Rev.appendList`), so the data of all the cuts of a function is about one walk's.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Guest.Core

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

/-- `pieceOk`'s comparisons of the placed function `pf` and the tables `t'` but the code's, and the
number of chunks. -/
def cutHeadOk (t : Tables) (tf : TracedFn) (o : FnOut) (pc0 : Nat) (cf : CompiledFunction)
    (pf : Placed) (t' : Tables) : Bool :=
  let e := emitFn pf.fn
  t'.len == o.len && t'.shared.length == o.shared.length + t.shared.length &&
    decide (t'.shared.take o.shared.length = o.shared) && allPairs fillIs e.2.toList o.fills &&
    pf.fn.frameSize == o.frame && e.1.code.size == o.size && decide (cf.name = tf.core.name) &&
    cf.entryPc == pc0 && cf.instructionCount == o.size &&
    cf.chunks.length == (o.size + chunkSize - 1) / chunkSize

/-- Chunk `c` of the placed function `pf`'s code, resolved at the layout `l` from `pc0` with frame
size `frame`, is the compiled function's. -/
def cutChunkOk (l : Layout) (pc0 frame : Nat) (cf : CompiledFunction) (pf : Placed) (c : Nat) :
    Bool :=
  decide (((resolvedFn l pc0 { (emitFn pf.fn).1 with frameSize := frame }).drop (c * chunkSize)).take
    chunkSize = cf.chunks.getD c [])

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
end LeanVM.Guest.Backend
