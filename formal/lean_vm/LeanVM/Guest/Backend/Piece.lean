/-
  LeanVM.Guest.Backend.Piece

  The check of one function's placement, emission and assembly against the statement's bytecode,
  which the kernel evaluates function by function on the guest (`Backend/Guest/Piece/`).
-/

module

public import LeanVM.Guest.Backend.Assemble
public import LeanVM.Guest.Backend.Place

/-!
# A function's piece

`pieceOk loops sigs l t tf o pc0 frame cf` places the traced function `tf` from the jump tables `t`,
emits it, and checks what that gives against `o` and the compiled function `cf`:

* the jump tables after it are `t.after o`: `o.len` slots, and the shared tables `o.shared` made
  before `t`'s (only the new ones are compared: placement only adds to the front, `placeFn_tables`);
* the jump table slots it fills are `o.fills`, as `(slot, instruction)` of its own code;
* its frame size and code size are `o.frame` and `o.size`;
* `cf` is it, at entry `pc0`: its name, entry, length, and its code resolved at the layout `l`
  with frame size `frame` (`main`'s frame holds the jump tables too) and cut in chunks.

`Sound/Piece.lean` proves what a success says (`pieceOk_spec`) and composes the pieces of a
program into `lowerProgram`'s result and the assembled functions.
-/

namespace LeanVM.Guest.Backend

@[expose] public section

/-- What placement and emission give of one function, as the guest's data records it. -/
structure FnOut where
  /-- The jump tables' length after it. -/
  len : Nat
  /-- The shared tables it made, the last first. -/
  shared : List (List String × Nat)
  /-- The jump table slots it fills: slot, and the index of the instruction in its code. -/
  fills : List (Nat × Nat)
  /-- Its frame size. -/
  frame : Nat
  /-- Its number of instructions. -/
  size : Nat
  deriving Inhabited

/-- The jump tables after a function that gives `o`. -/
def Tables.after (t : Tables) (o : FnOut) : Tables := ⟨o.len, o.shared ++ t.shared⟩

/-- A jump table slot filled with instruction `i` of the function. -/
def fillIs : Fill → Nat × Nat → Bool
  | (s, .at _ i), (s', i') => s == s' && i == i'
  | _, _ => false

/-- Two lists, element by element. -/
def allPairs {α β : Type} (r : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => r a b && allPairs r as bs
  | _, _ => false

/-- A lowered function as the layout reads it: name, number of instructions, frame size. -/
def infoOf (f : Lowered) : String × Nat × Nat := (f.name, f.code.size, f.frameSize)

/-- The layout of functions given by `infoOf`, with no table of powers (`Layout.pow` computes
them): `layout`'s, but for its table (`layout_eq_info`). -/
def layoutInfo (info : List (String × Nat × Nat)) (tablesBase : Nat) : Layout :=
  let (entry, frame, total) := info.foldl (init := (({} : SMap Nat), ({} : SMap Nat), 0))
    fun (entry, frame, pc) (n, size, fs) => (entry.insert n pc, frame.insert n fs, pc + size)
  { entry, frame, tablesBase, sentinel := nextPow2 (total + 1) - 1, gpow := #[] }

/-- `__jump_tables`, `main`'s frame from `base` (`withTables`). -/
def jtOf (base : Nat) (slots : Array KVal) : Lowered :=
  ⟨"__jump_tables", slots.zipIdx.map fun (k, j) => (⟨.set (base + j) k, []⟩ : LInstr),
    base + slots.size⟩

/-- The jump table slots a function gives `o` fills, as `lowerProgram` lists them. -/
def fillsOfOut (tf : TracedFn) (o : FnOut) : List Fill :=
  o.fills.map fun x => (x.1, KVal.at tf.core.name x.2)

/-- **A function's piece**, its placement also passing the test `extra` on the placed locations:
placed from `t` and emitted, the function gives `o`, and resolved at the layout `l` from `pc0` with
frame size `frame` it is `cf`. -/
def pieceOkWith (extra : VMap Loc → Bool) (loops : Loops) (sigs : SMap (Nat × Nat)) (l : Layout)
    (t : Tables) (tf : TracedFn) (o : FnOut) (pc0 frame : Nat) (cf : CompiledFunction) : Bool :=
  match placeFn loops sigs t tf with
  | .error _ => false
  | .ok (pf, t') =>
      let e := emitFn pf.fn
      t'.len == o.len && t'.shared.length == o.shared.length + t.shared.length &&
        decide (t'.shared.take o.shared.length = o.shared) && allPairs fillIs e.2.toList o.fills &&
        pf.fn.frameSize == o.frame && e.1.code.size == o.size && decide (cf.name = tf.core.name) &&
        cf.entryPc == pc0 && cf.instructionCount == o.size &&
        decide (chunked (resolvedFn l pc0 { e.1 with frameSize := frame }) = cf.chunks) &&
        extra pf.locs

/-- **A function's piece**: placed from `t` and emitted, the function gives `o`, and resolved at
the layout `l` from `pc0` with frame size `frame` it is `cf`. -/
def pieceOk (loops : Loops) (sigs : SMap (Nat × Nat)) (l : Layout) (t : Tables) (tf : TracedFn)
    (o : FnOut) (pc0 frame : Nat) (cf : CompiledFunction) : Bool :=
  pieceOkWith (fun _ => true) loops sigs l t tf o pc0 frame cf

/-! ## A program's pieces -/

/-- The jump tables after the first `j` functions, from none. -/
def tablesAt (os : List FnOut) (j : Nat) : Tables := (os.take j).foldl Tables.after {}

/-- The jump tables after every function. -/
def tablesEnd (os : List FnOut) : Tables := os.foldl Tables.after {}

/-- The frame size each function is resolved with: `main`'s, the first, holds the `n` slots of the
jump tables past its own cells (`withTables`). -/
def framesOf (n : Nat) : List FnOut → List Nat
  | [] => []
  | o :: os => (o.frame + n) :: os.map (·.frame)

/-- `main`'s frame size, where the jump tables start. -/
def baseOf (os : List FnOut) : Nat := (os.head?.map (·.frame)).getD 0

/-- What the layout reads of each function, `__jump_tables` first, when the functions `p` give
`os`. -/
def infoOfOuts (p : List TracedFn) (os : List FnOut) : List (String × Nat × Nat) :=
  let n := (tablesEnd os).len
  ("__jump_tables", n, baseOf os + n) ::
    ((p.zip (framesOf n os)).zip os).map fun x => (x.1.1.core.name, x.2.size, x.1.2)

/-- The jump table slots the functions `p` fill when they give `os`. -/
def fillsOfOuts (p : List TracedFn) (os : List FnOut) : List Fill :=
  (p.zip os).flatMap fun x => fillsOfOut x.1 x.2

/-- The slots of the shared tables, as a list. -/
def entriesL (shared : List (List String × Nat)) : List (Nat × String) :=
  shared.reverse.flatMap fun (cs, first) => cs.zipIdx.map fun (c, j) => (first + j, c)

/-- The map of the jump table slots written, as `tableSlots` makes it, on lists. -/
def tableMapL (fills : List Fill) (entries : List (Nat × String)) : NMap KVal :=
  entries.foldl (fun m x => m.insert x.1 (.entry x.2))
    (fills.foldl (fun m x => m.insert x.1 x.2) {})

/-- The `len` slots of the map `m`, as `tableSlots` reads them. -/
def slotsFrom (m : NMap KVal) (len : Nat) : Array KVal :=
  ((List.range len).map fun i => (m.get? i).getD (.const 0 0)).toArray

/-- The jump tables' slots when the functions `p` give `os` (`lowerProgram`'s). -/
def slotsOfOuts (p : List TracedFn) (os : List FnOut) : Array KVal :=
  slotsFrom (tableMapL (fillsOfOuts p os) (entriesL (tablesEnd os).shared)) (tablesEnd os).len

/-- Whether the numbers are distinct, by a map of the numbers seen. -/
def natsDistinct (l : List Nat) : Bool :=
  go l {}
where
  go : List Nat → NMap Unit → Bool
    | [], _ => true
    | n :: ns, seen => !seen.contains n && go ns (seen.insert n ())

/-- The slots the functions giving `os` write: the slots their arms fill, then the slots of the
shared tables. -/
def slotKeys (os : List FnOut) : List Nat :=
  os.flatMap (fun o => o.fills.map (·.1)) ++
    (tablesEnd os).shared.reverse.flatMap fun x => (List.range x.1.length).map (x.2 + ·)

/-- **The slots are written once each**, and inside the tables: numbers only. -/
def slotsOk (os : List FnOut) : Bool :=
  let ks := slotKeys os
  natsDistinct ks && ks.all (· < (tablesEnd os).len)

/-- The checks `placeProgram` makes of the program before placing it. -/
def progChecks (p : List TracedFn) (loops : Loops) : Bool :=
  (p.map (·.core.name)).head? == some "main" && !(p.map (·.core.name)).contains "__jump_tables" &&
    namesDistinct (p.map (·.core.name)) && !(loops["main"]?).any (·.registered)

/-- No compiled function. -/
def noFunction : CompiledFunction := ⟨"", 0, 0, []⟩

/-- **The piece of function `j`** of the program `p`, which gives `os`, compiled to `cfs` (the
functions past `__jump_tables`), at the layout `l`. -/
def pieceAt (loops : Loops) (sigs : SMap (Nat × Nat)) (l : Layout) (p : List TracedFn)
    (os : List FnOut) (cfs : List CompiledFunction) (j : Nat) : Bool :=
  let n := (tablesEnd os).len
  pieceOk loops sigs l (tablesAt os j) (p.getD j default) (os.getD j default)
    (n + ((os.take j).map (·.size)).sum) ((framesOf n os).getD j 0) (cfs.getD j noFunction)

/-- `pieceAt`, its placement also passing the test `extra j` on the placed locations. -/
def pieceAtWith (extra : Nat → VMap Loc → Bool) (loops : Loops) (sigs : SMap (Nat × Nat)) (l : Layout)
    (p : List TracedFn) (os : List FnOut) (cfs : List CompiledFunction) (j : Nat) : Bool :=
  let n := (tablesEnd os).len
  pieceOkWith (extra j) loops sigs l (tablesAt os j) (p.getD j default) (os.getD j default)
    (n + ((os.take j).map (·.size)).sum) ((framesOf n os).getD j 0) (cfs.getD j noFunction)

/-- The pieces of functions `a` to `b - 1`. -/
def piecesIn (loops : Loops) (sigs : SMap (Nat × Nat)) (l : Layout) (p : List TracedFn)
    (os : List FnOut) (cfs : List CompiledFunction) (a b : Nat) : Bool :=
  (List.range' a (b - a)).all (pieceAt loops sigs l p os cfs)

/-- `piecesIn`, the placement of each function `j` also passing the test `extra j` on its placed
locations. -/
def piecesInWith (extra : Nat → VMap Loc → Bool) (loops : Loops) (sigs : SMap (Nat × Nat)) (l : Layout)
    (p : List TracedFn) (os : List FnOut) (cfs : List CompiledFunction) (a b : Nat) : Bool :=
  (List.range' a (b - a)).all (pieceAtWith extra loops sigs l p os cfs)

/-- The locations function `j` of `p` is placed at, from the jump tables the functions before it
leave: none if its placement fails. -/
def placedLocsAt (loops : Loops) (sigs : SMap (Nat × Nat)) (p : List TracedFn) (os : List FnOut)
    (j : Nat) : VMap Loc :=
  match placeFn loops sigs (tablesAt os j) (p.getD j default) with
  | .ok r => r.1.locs
  | .error _ => {}

/-- Chunk `k` of `__jump_tables`, `main`'s frame from `base`, resolved at the layout `l`: one `SET`
a slot. -/
def jtChunk (l : Layout) (base : Nat) (slots : Array KVal) (k : Nat) : List OffsetInstruction :=
  (((slots.toList.drop (k * chunkSize)).take chunkSize).zipIdx (k * chunkSize)).map fun x =>
    resolveOp l 0 (base + slots.size) (.set (base + x.2) x.1)

/-- The instructions of a chunk of `__jump_tables` compared at once. -/
def jtPartSize : Nat := 512

/-- The parts of a chunk. -/
def jtParts : Nat := 4

/-- Instructions `a` to `a + n - 1` of chunk `k` of `__jump_tables`. -/
def jtPart (l : Layout) (base : Nat) (slots : Array KVal) (k a n : Nat) : List OffsetInstruction :=
  (((slots.toList.drop (k * chunkSize + a)).take n).zipIdx (k * chunkSize + a)).map fun x =>
    resolveOp l 0 (base + slots.size) (.set (base + x.2) x.1)

/-- Part `q` of chunk `k` of `__jump_tables` is the compiled function's. -/
def jtPartOk (l : Layout) (base : Nat) (slots : Array KVal) (cf : CompiledFunction) (k q : Nat) :
    Bool :=
  decide (jtPart l base slots k (q * jtPartSize) jtPartSize =
    ((cf.chunks.getD k []).drop (q * jtPartSize)).take jtPartSize)

/-- Whether a compiled function is `__jump_tables` of `slots` at pc `0` but for its code. -/
def jtHead (slots : Array KVal) (cf : CompiledFunction) : Bool :=
  cf.name == "__jump_tables" && cf.entryPc == 0 && cf.instructionCount == slots.size &&
    cf.chunks.length == (slots.size + chunkSize - 1) / chunkSize &&
    cf.chunks.all (·.length ≤ chunkSize)



end
end LeanVM.Guest.Backend
