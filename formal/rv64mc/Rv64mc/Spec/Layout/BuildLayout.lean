/-
  Rv64mc.Spec.Layout.BuildLayout

  The contract of `verifier::layout::build_layout(bytecode, log_memory, table_rows) -> Result<Layout, VerifierError>`:
  the result's slot (`sret`) in `a0`, the borrowed `Bytecode` at `a1`, `log_memory` in `a2`, the announced rows as a
  slice in `a3`, `a4`. Where `Model.buildLayoutRust` (on the bytecode's length) fails, the result is `Err`; where it
  gives `l`, the result is `Ok(l)` laid out at `sret` (`BuiltLayoutAt`): the fields the bus reads (`Bus.LayoutAt`,
  borrowing the bytecode at `a1`) and the ones `walk` reads besides (placements, stack size, heights, the Keccak
  shape), every buffer allocated before the return (`LiveVecAt`).

  `Gen/Layouts.lean` does not print `Result<Layout, VerifierError>`: read off the code, it is niche-encoded in the
  first word (`Layout.tables`' capacity), `Err` being the word `2^64 - 1` there (`errNiche`), and `Ok` the `Layout`
  itself at `sret`.
-/

import Rv64mc.Spec.Bus.Repr

namespace Rv64mc.Spec.Layout.BuildLayout

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript

/-- `Err`'s niche value in the first word of `Result<Layout, VerifierError>` (read off the code). -/
def errNiche : Word := 0xffffffffffffffff#64

/-- **The `Layout` `l` at `a`, borrowing `bc`**: what the bus reads, and the placements, the stack's log size, the
    tables' log heights and the Keccak shape. -/
structure BuiltLayoutAt (env : Env) (m : MachineState) (a : Word) (l : Model.LayoutRust) (bc : Model.BytecodeRust) :
    Prop where
  bus : Bus.LayoutAt env m a l bc
  placements : LiveVecAt env Layouts.OptionPlacement.byteSize
    (ArrayAt Layouts.OptionPlacement.byteSize OptPlacementAt) m (a + BitVec.ofNat 64 Layouts.Layout.placements)
    l.placements
  stackLog : m.getMem (a + BitVec.ofNat 64 Layouts.Layout.stack_log) = BitVec.ofNat 64 l.stackLog
  heights : LiveVecAt env 8 UsizesAt m (a + BitVec.ofNat 64 Layouts.Layout.table_log_heights) l.tableLogHeights
  keccakLogSteps : m.getMem (a + BitVec.ofNat 64 (Layouts.Layout.keccak + Layouts.KeccakShape.log_steps)) =
    BitVec.ofNat 64 l.keccak.logSteps
  keccakDepth : m.getMem (a + BitVec.ofNat 64 (Layouts.Layout.keccak + Layouts.KeccakShape.depth)) =
    BitVec.ofNat 64 l.keccak.depth

/-- **The `Result<Layout, VerifierError>` at `a`**: `Err` where the Model fails, else `Ok(l)`. -/
def ResultLayoutAt (env : Env) (m : MachineState) (a : Word) (bc : Model.BytecodeRust) : Option Model.LayoutRust → Prop
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.Layout.tables) = errNiche
  | some l => BuiltLayoutAt env m a l bc

/-- The result's slot is the caller's and apart from the bytecode; the bytecode and the rows are live. -/
def Pre (env : Env) (bc : Model.BytecodeRust) (rows : List (BitVec 64)) (regs : Reg → Word) (m : MachineState) :
    Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Layout.byteSize ∧
    env.Owned m (regs .x2) (regs .x11) Layouts.Bytecode.byteSize ∧ Walk.BytecodeAt env m (regs .x11) bc ∧
    Apart (regs .x10) Layouts.Layout.byteSize (regs .x11) Layouts.Bytecode.byteSize ∧
    SliceArgs WordsAt m (regs .x13) (regs .x14) rows ∧ env.Live m (regs .x13) (8 * rows.length)

def Post (env : Env) (bc : Model.BytecodeRust) (rows : List (BitVec 64)) (regs : Reg → Word) (_m : MachineState)
    (_r' : Reg → Word) (m' : MachineState) : Prop :=
  ResultLayoutAt env m' (regs .x10) bc (Model.buildLayoutRust bc.len (regs .x12) rows)

/-- What it writes besides its stack and allocations: the result's slot. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Layout.byteSize b

/-- **The contract of `build_layout`**, function `i` of `p` with `need` bytes of stack, for every bytecode and
    every list of announced rows. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ bc rows, Holds env p i need (Pre env bc rows) (Post env bc rows) Out

end Rv64mc.Spec.Layout.BuildLayout
