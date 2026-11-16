/-
  LeanVM.Guest.Backend.Invariants

  What each pass of the back end is meant to maintain, as checks a compiled run evaluates and as
  the statements a correctness proof starts from.
-/

module

public import LeanVM.Guest.Backend.Compile

/-!
# Invariants of the back end

Nothing here is proved. Each `Bool` check is evaluated on a compiled program by
`lake exe guest-backend check` and by the tests (`LeanVMTests.Guest.Backend`), and each `Prop`
states for every program what the check finds of one.

* **Emission** (`sizesAgree`, `EmitBlockSize`): a function's code has the length `blockSize`
  gives its placed body, which is what makes every `KVal.local` the index of the instruction
  meant; and every local target, table slot and entry names an instruction that exists
  (`targetsExist`).
* **Frames** (`withinFrame`): every cell an instruction or a hint names is below its function's
  frame size, a loop frame's copy below the next frame's.
* **Jump tables** (`tablesFilled`): every slot is filled once, by an arm or by a callee's entry.
* **Assembly** (`laidOut`, `Layout.Consecutive`): the functions lie one after another from pc
  `0`, as `LeanVM.Guest.consecutive` asks of `Statement/Data/`, and the code fits the padded size
  with the halting slot left.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Semantics

@[expose] public section

/-- The frame cells an instruction names; the last of a `mulNextFrame` is in the next frame. -/
def LOp.cells : LOp → List Cell
  | .mulNextFrame a b c => [a, b, c]
  | .set o _ => [o]
  | .xor a b c => [a, b, c]
  | .mul a b c => [a, b, c]
  | .deref o1 _ o3 mode => if mode = .cell then [o1, o3] else [o1]
  | .jump oc od of => [oc, od, of]
  | .slot x _ dst => [x, dst]
  | .keccak m0 m1 m2 m3 tail b8 cap out _ _ outCells =>
      [m0, m1, m2, m3, tail + 3, b8, cap + 3, out + outCells.cellCount - 1]

def BitsDest.cells (n : Nat) : BitsDest → List Cell
  | .stack base => [base + n - 1]
  | .heap ptr => [ptr]

/-- The frame cells a hint names. -/
def RHint.cells : RHint → List Cell
  | .frameAddress _ => []
  | .allocFrames ptr _ bound _ _ => [ptr, bound]
  | .alloc ptr _ => [ptr]
  | .allocDyn ptr size => [ptr, size]
  | .witnessStack _ base len => [base + len - 1]
  | .witnessHeap _ ptr _ _ => [ptr]
  | .log2Ceil bits dst nbits _ => dst :: bits.cells nbits
  | .bitDecompose value bits nbits => value :: bits.cells nbits
  | .bitDecomposeExp value bits nbits => value :: bits.cells nbits
  | .digitDecomposeExp value dst _ ndigits _ _ startCell => value :: (startCell.toList ++ dst.cells ndigits)
  | .windowsExp value dest skip _ _ count => value :: dest.cells (skip + count)
  | .fieldLimbs value base len => [value, base + len - 1]
  | .inverse value dst => [value, dst]

def LHint.cells : LHint → List Cell
  | .nextFrameAddress => []
  | .allocLoopFrames ptr _ count _ =>
      match count with
      | .constant _ => [ptr]
      | .bound cell _ => [ptr, cell]
  | .allocFrame ptr _ => [ptr]
  | .allocFrameMax ptr _ => [ptr]
  | .resolved h => h.cells

/-- Every cell the function's instructions and hints name is in its frame. -/
def Lowered.withinFrame (f : Lowered) : Bool :=
  f.code.all fun ins =>
    ins.op.cells.all (· < f.frameSize) && ins.hints.all fun h => h.cells.all (· < f.frameSize)

/-- A function's code is as long as `blockSize` says. -/
def sizesAgree (p : PFn) : Bool := (emitFn p).1.code.size == blockSize p.body

/-- Every local jump target of the function is one of its instructions. -/
def Lowered.targetsExist (f : Lowered) : Bool :=
  f.code.all fun ins =>
    match ins.op with
    | .set _ (.local i) => i < f.code.size
    | _ => true

/-- Every slot of the jump tables is filled once, and names an instruction that exists. -/
def tablesFilled (fns : List Lowered) (len : Nat) (fills : Array Fill) (shared : Array (Nat × String)) :
    Bool :=
  let sizes : Std.HashMap String Nat := fns.foldl (init := {}) fun m f => m.insert f.name f.code.size
  let counts := (fills.map (·.1) ++ shared.map (·.1)).foldl (init := Array.replicate len 0)
    fun c i => c.modify i (· + 1)
  fills.size + shared.size == len && counts.all (· == 1) &&
    (fills.all fun (_, k) =>
      match k with
      | .at f i => (sizes[f]?).any (i < ·)
      | _ => false) &&
    shared.all fun (_, f) => sizes.contains f

/-- The assembled functions lie one after another from pc `0`, and leave the halting slot. -/
def Assembled.laidOut (a : Assembled) : Bool :=
  let stop := a.fns.foldl (init := some 0) fun pc (_, entry, len) =>
    pc.bind fun pc => if entry == pc then some (pc + len) else none
  stop == some a.code.size && a.code.size < a.size

/-- The checks of a program's back end run, each with its name. -/
def invariants (p : List TracedFn) : Except String (List (String × Bool)) := do
  let (placed, tables) ← placeProgram p
  let pfns := placed.map (·.fn)
  let lowered := pfns.map fun pf => (emitFn pf).1
  let fills := pfns.foldl (init := #[]) fun fills pf => fills ++ (emitFn pf).2
  let a := assemble lowered (tableSlots tables.len fills tables.entries)
  let (withTabs, _) := withTables lowered (tableSlots tables.len fills tables.entries)
  return [
    ("a function's code has its placed body's size", pfns.all sizesAgree),
    ("every local jump target exists", lowered.all Lowered.targetsExist),
    ("every cell is in its frame", withTabs.all Lowered.withinFrame),
    ("every jump table slot is filled once", tablesFilled lowered tables.len fills tables.entries),
    ("the functions are laid out one after another", a.laidOut)]

/-- Every compiled program passes every check. -/
def InvariantsHold : Prop :=
  ∀ (p : List TracedFn) (checks : List (String × Bool)), invariants p = .ok checks →
    ∀ c ∈ checks, c.2 = true

end
end LeanVM.Guest.Backend
