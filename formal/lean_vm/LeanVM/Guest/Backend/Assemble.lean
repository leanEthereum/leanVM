/-
  LeanVM.Guest.Backend.Assemble

  Assembly: the functions' labelled code and the jump tables to one program, every immediate and
  hint resolved (`compile` and `resolve`, `crates/lean_compiler/src/lib.rs`).
-/

module

public import LeanVM.Guest.Backend.Emit
public import LeanVM.Guest.Word
public import Std.Data.HashMap

/-!
# Assembly

The jump tables sit in `main`'s frame past its own cells, and `__jump_tables`, at pc `0`, writes
every slot with one `SET` before falling through into `main`. The functions follow in the
order they were lowered. The bytecode is padded to the next power of two past its length, whose
last slot is the halting pc.

`resolve` then makes each instruction an `OffsetInstruction`: a `SET` of a pc becomes the limbs
of `g^pc`, a loop frame's copy an offset past the frame, a table read a `DEREF` at the tables'
base; and each hint its runtime form, the callee's frame size known.

Invariant (stated, not proved here): a function's entry is the sum of the lengths before it
(`Layout.Consecutive`), which is what `LeanVM.Guest.consecutive` asks of `Statement/Data/`.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The limbs of `g^0, …, g^(n-1)`, by repeated multiplication. -/
def gpowTable (n : Nat) : Array Nat :=
  go n 1 (Array.emptyWithCapacity n)
where
  go : Nat → K → Array Nat → Array Nat
    | 0, _, acc => acc
    | k + 1, x, acc => go k (x * g) (acc.push x.toBitVec.toNat)

/-- `gpowTable` holds the powers of `g`: the table is `gpowK` computed once. -/
def GpowTableSpec : Prop :=
  ∀ (n k : Nat), k < n → (gpowTable n)[k]? = some (gpowK k).toBitVec.toNat

/-- The layout of a program: each function's entry and frame size, the tables' base in `main`'s
frame, the halting pc. -/
structure Layout where
  entry : Std.HashMap String Nat
  frame : Std.HashMap String Nat
  tablesBase : Nat
  sentinel : Nat
  /-- The limbs of the powers of `g` below the padded size. -/
  gpow : Array Nat

/-- `g^k`'s limb. -/
def Layout.pow (l : Layout) (k : Nat) : Nat :=
  match l.gpow[k]? with
  | some x => x
  | none => (gpowK k).toBitVec.toNat

/-- The smallest power of two that is at least `n`. -/
def nextPow2 (n : Nat) : Nat :=
  go n 1
where
  go : Nat → Nat → Nat
    | 0, p => p
    | fuel + 1, p => if n ≤ p then p else go fuel (2 * p)

/-- A `SET` immediate's limbs (`resolve_kval`). -/
def resolveK (l : Layout) (pc0 frameSize : Nat) : KVal → Nat × Nat
  | .frameSize => (l.pow frameSize, 0)
  | .const c0 c1 => (c0, c1)
  | .entry f => (l.pow (l.entry.getD f 0), 0)
  | .endSentinel => (l.pow l.sentinel, 0)
  | .local i => (l.pow (pc0 + i), 0)
  | .at f i => (l.pow (l.entry.getD f 0 + i), 0)

/-- An instruction of a function at `pc0` with frame `frameSize` (`resolve`). -/
def resolveOp (l : Layout) (pc0 frameSize : Nat) : LOp → OffsetInstruction
  | .mulNextFrame a b c => .mul a b (frameSize + c)
  | .set o k => let (c0, c1) := resolveK l pc0 frameSize k; .set o c0 c1
  | .xor a b c => .xor a b c
  | .mul a b c => .mul a b c
  | .deref o1 o2 o3 mode => .deref o1 o2 o3 mode
  | .jump oc od of => .jump oc od of
  | .slot x first dst => .deref x (l.tablesBase + first) dst .cell
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
      .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells

/-- A hint of a function with frame `frameSize`, the callees' frames known (`compile`). -/
def resolveHint (l : Layout) (frameSize : Nat) : LHint → RHint
  | .nextFrameAddress => .frameAddress frameSize
  | .allocLoopFrames ptr callee count tail =>
      let size := l.frame.getD callee 0
      match count with
      | .constant n => .alloc ptr (size * (n - 1) + tail)
      | .bound cell start =>
          .allocFrames ptr size cell (gpowK (2 ^ 64 - 1 - start)).toBitVec.toNat tail
  | .allocFrame ptr callee => .alloc ptr (l.frame.getD callee 0)
  | .allocFrameMax ptr callees => .alloc ptr (callees.foldl (fun m c => max m (l.frame.getD c 0)) 0)
  | .resolved h => h

/-- The functions with `__jump_tables` before them: `main`'s frame grows by the slots, and one
`SET` a slot writes the tables there (`compile`). -/
def withTables (fns : List Lowered) (slots : Array KVal) : List Lowered × Nat :=
  match fns with
  | [] => ([], 0)
  | main :: rest =>
      let base := main.frameSize
      if slots.isEmpty then (main :: rest, base)
      else
        let frame := base + slots.size
        let code := slots.zipIdx.map fun (k, j) => (⟨.set (base + j) k, []⟩ : LInstr)
        (⟨"__jump_tables", code, frame⟩ :: { main with frameSize := frame } :: rest, base)

/-- The layout of the functions `fns`, `main`'s frame holding the tables from `tablesBase`. -/
def layout (fns : List Lowered) (tablesBase : Nat) : Layout × Nat :=
  let (entry, frame, total) := fns.foldl (init := (({} : Std.HashMap String Nat),
      ({} : Std.HashMap String Nat), 0)) fun (entry, frame, pc) f =>
    (entry.insert f.name pc, frame.insert f.name f.frameSize, pc + f.code.size)
  let size := nextPow2 (total + 1)
  ({ entry, frame, tablesBase, sentinel := size - 1, gpow := gpowTable size }, size)

/-- Every function's entry is the end of the one before it. -/
def Layout.Consecutive (l : Layout) (fns : List Lowered) : Prop :=
  ∀ (pre : List Lowered) (f : Lowered) (post : List Lowered), fns = pre ++ f :: post →
    l.entry[f.name]? = some (pre.foldl (fun n g => n + g.code.size) 0)

/-- The program of the functions `fns` (`__jump_tables` among them) at the layout `l`, padded to
`size` slots. -/
def assembleAt (l : Layout) (size : Nat) (fns : List Lowered) : Assembled :=
  let (code, hints, ranges) := fns.foldl (init := (#[], #[], #[])) fun (code, hints, ranges) f =>
    let start := code.size
    let pc0 := l.entry.getD f.name start
    let (code, hints) := f.code.foldl (init := (code, hints)) fun (code, hints) ins =>
      let hints := if ins.hints.isEmpty then hints
        else hints.push (code.size, ins.hints.map (resolveHint l f.frameSize))
      (code.push (resolveOp l pc0 f.frameSize ins.op), hints)
    (code, hints, ranges.push (f.name, start, f.code.size))
  { size, code, hints, mainFrame := l.frame.getD "main" 0, fns := ranges }

/-- Assemble the functions' labelled code, `main` first, with the jump tables' slots. -/
def assemble (fns : List Lowered) (slots : Array KVal) : Assembled :=
  let (fns, tablesBase) := withTables fns slots
  let (l, size) := layout fns tablesBase
  assembleAt l size fns

/-- A function's code in chunks of `chunkSize` instructions, the last shorter, as
`CompiledFunction.chunks` holds it. -/
def chunked (code : List OffsetInstruction) : List (List OffsetInstruction) :=
  go (code.length / chunkSize + 1) code
where
  go : Nat → List OffsetInstruction → List (List OffsetInstruction)
    | 0, _ => []
    | fuel + 1, l => if l.isEmpty then [] else l.take chunkSize :: go fuel (l.drop chunkSize)

/-- The assembled functions as the statement holds a program's (`Statement/Data/`): the program is
`LeanVM.Guest.assemble a.toFunctions logSize` with `2 ^ logSize = a.size`. -/
def Assembled.toFunctions (a : Assembled) : List CompiledFunction :=
  a.fns.toList.map fun (name, entry, len) =>
    ⟨name, entry, len, chunked (a.code.extract entry (entry + len)).toList⟩

/-- The jump tables' slots, from the fills of the functions' `match`es and the shared tables of
the dispatched calls. -/
def tableSlots (len : Nat) (fills : Array Fill) (shared : Array (Nat × String)) : Array KVal :=
  let slots := Array.replicate len (KVal.const 0 0)
  let slots := fills.foldl (init := slots) fun s (i, k) => s.setIfInBounds i k
  shared.foldl (init := slots) fun s (i, c) => s.setIfInBounds i (.entry c)

end
end LeanVM.Guest.Backend
