import Rv64Verifier.Proofs.Layout.ContractsBuild

/-!
# Contracts of `keccak_cell_lanes` and of `flushes_keccak`'s limb closure

As `Contracts.lean`. An `Option<usize>` is two doublewords, the tag (`0` or `1`) and the value.
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror

/-- The `Option<usize>` at `a` is `o`. -/
def OptAt (s : MachineState) (a : Word) : Option ℕ → Prop
  | none => s.getMem a = 0
  | some v => s.getMem a = 1 ∧ s.getMem (a + 8) = BitVec.ofNat 64 v

/-! ## `keccak_cell_lanes`, at `0x80004d10` -/

/-- Its 448-byte frame, and `memcpy`'s stack below it. -/
@[rv_addr] def cellLanesStack : Nat := 448 + memcpyStack

/-- `a0` = where the 13 pairs go (416 bytes), `a1` = `odd`. -/
structure CellLanesPre (s : MachineState) : Prop where
  stack : RtStack s cellLanesStack
  out : Mapped (s.getReg .x10) 416
  outAligned : (s.getReg .x10).toNat % 8 = 0
  outStack : Apart (s.getReg .x10) 416 (stackLo s cellLanesStack) cellLanesStack
  odd : s.getReg .x11 = 0 ∨ s.getReg .x11 = 1

/-- Cell `i`'s pair at `out + 32 i`; memory changes only there and on the stack. -/
structure CellLanesPost (s t : MachineState) : Prop where
  cells : ∀ i < keccakCellsRust,
    OptAt t (s.getReg .x10 + BitVec.ofNat 64 (32 * i)) (keccakCellLanesAt (s.getReg .x11 = 1) i).1 ∧
    OptAt t (s.getReg .x10 + BitVec.ofNat 64 (32 * i + 16)) (keccakCellLanesAt (s.getReg .x11 = 1) i).2
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 416 ∨
    Within a (stackLo s cellLanesStack) cellLanesStack

def CellLanesSpec : Prop := FunSpec Image.code 0x80004d10 CellLanesPre CellLanesPost

/-! ## `flushes_keccak`'s `limb` closure, at `0x80004de4`

`|e, o| layout_limb(lane(e), lane(o), flag, missing)`, with `lane(x) = x.map(|x| lanes + x)`; the
closure's environment holds `&&&lanes`, `&flag` and `&missing`. -/

/-- Its 208-byte frame, and `col`'s and `prod`'s stack below it (deeper than `add_scaled`'s and
`term`'s). -/
@[rv_addr] def limbStack : Nat := 208 + colStack

/-- An `Option<usize>` from its tag and value. -/
def optOf (tag val : Word) : Option ℕ := if tag = 0 then none else some val.toNat

/-- `lane(x)`: `lanes + x`, as the code adds. -/
def laneOf (lanes tag val : Word) : Option ℕ := if tag = 0 then none else some (lanes + val).toNat

/-- `lanes`, `&flag` and `&missing`, through the environment at `a1`. -/
@[rv_addr] def limbLanes (s : MachineState) : Word :=
  s.getMem (s.getMem (s.getMem (s.getReg .x11)))
@[rv_addr] def limbFlagPtr (s : MachineState) : Word := s.getMem (s.getReg .x11 + 8)
@[rv_addr] def limbMissing (s : MachineState) : Word := s.getMem (s.getReg .x11 + 16)

/-- `a0` = where the `Form` goes, `a1` = the environment, `a2`/`a3` = `e`, `a4`/`a5` = `o`. The
environment and what it points to are read before any write but the saved registers. -/
structure LimbPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s limbStack
  out : ValidMemRange (s.getReg .x10) 3
  outFree : Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s limbStack) limbStack
  env : ValidMemRange (s.getReg .x11) 3
  envStack : Apart (s.getReg .x11) 24 (stackLo s limbStack) limbStack
  lanes1 : ValidMemRange (s.getMem (s.getReg .x11)) 1
  lanes1Stack : Apart (s.getMem (s.getReg .x11)) 8 (stackLo s limbStack) limbStack
  lanes2 : ValidMemRange (s.getMem (s.getMem (s.getReg .x11))) 1
  lanes2Stack : Apart (s.getMem (s.getMem (s.getReg .x11))) 8 (stackLo s limbStack) limbStack
  flag : ValidMemRange (limbFlagPtr s) 1
  flagStack : Apart (limbFlagPtr s) 8 (stackLo s limbStack) limbStack
  missing : ValidMemRange (limbMissing s) 2
  missingStack : Apart (limbMissing s) 16 (stackLo s limbStack) limbStack
  evenTag : s.getReg .x12 = 0 ∨ s.getReg .x12 = 1
  oddTag : s.getReg .x14 = 0 ∨ s.getReg .x14 = 1
  rodata : RodataOk s

/-- `layout_limb(lane(e), lane(o), flag, missing)`. -/
def LimbSpec : Prop := FunSpec Image.code 0x80004de4 LimbPre fun s t ↦
  NewForm s t (s.getReg .x10) limbStack ∧
    formOf t (s.getReg .x10) = layoutLimbRust (laneOf (limbLanes s) (s.getReg .x12) (s.getReg .x13))
      (laneOf (limbLanes s) (s.getReg .x14) (s.getReg .x15)) (s.getMem (limbFlagPtr s)).toNat
      (optOf (s.getMem (limbMissing s)) (s.getMem (limbMissing s + 8)))

end Rv64Verifier.Layout
