import Rv64Verifier.Proofs.Walk.AtDeref

/-!
# `walk`: `tables()` at JUMP's first call and at the tables' copy

`AtJump`: the DEREF `Table` finished at `sp + 2144` (`L5`), JUMP's empty `Flushes` at `sp + 1728`, at
the call `prod(13, 6, 0)` into `sp + 2240` (`0x80005138`, returning to `0x800029b0`). `AtR9`: all six
tables finished in their frame slots (`L6`), at the first `memcpy` into the tables' buffer
(`0x800126e4`, returning to `0x80002dbc`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4

/-- The DEREF and JUMP `Table`s. -/
def derefT : LayoutMirror.TableRust := ⟨3, List.replicate 15 0, LayoutMirror.flushesDerefRust⟩
def jumpT : LayoutMirror.TableRust := ⟨4, List.replicate 14 0, LayoutMirror.flushesJumpRust⟩

theorem tablesRust_three : LayoutMirror.tablesRust[3]? = some derefT := rfl
theorem tablesRust_four : LayoutMirror.tablesRust[4]? = some jumpT := rfl

/-- The finished tables after DEREF's, and after JUMP's. -/
abbrev L5 (s : MachineState) : List (Word × LayoutMirror.TableRust) :=
  L4 s setT ++ [(s.getReg .x2 - 512, derefT)]
abbrev L6 (s : MachineState) : List (Word × LayoutMirror.TableRust) :=
  L5 s ++ [(s.getReg .x2 - 928, jumpT)]

/-- At JUMP's `prod(13, 6, 0)` call (`0x80005138`, returning to `0x800029b0`). -/
structure AtJump (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (Bb : Word) : Prop where
  pc : u.pc = 0x80005138
  m : M8 OI s u A k R Q B Bb (heapNext u) (L5 s)
  empty : EmptyAt u (s.getReg .x2 - 928)
  x10 : u.getReg .x10 = s.getReg .x2 - 416
  x11 : u.getReg .x11 = 13
  x12 : u.getReg .x12 = 6
  x13 : u.getReg .x13 = 0
  x1 : u.getReg .x1 = 0x800029b0
  x19 : u.getReg .x19 = 1
  x21 : u.getReg .x21 = 6
  x22 : u.getReg .x22 = 2
  x23 : u.getReg .x23 = s.getReg .x2 - 512
  x27 : u.getReg .x27 = 6

/-- At the first `memcpy(Bb, sp + 1024, 72)` (`0x800126e4`, returning to `0x80002dbc`). -/
structure AtR9 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (Bb : Word) : Prop where
  pc : u.pc = 0x800126e4
  m : M8 OI s u A k R Q B Bb (heapNext u) (L6 s)
  x10 : u.getReg .x10 = Bb
  x11 : u.getReg .x11 = s.getReg .x2 - 1632
  x12 : u.getReg .x12 = 72
  x1 : u.getReg .x1 = 0x80002dbc
  x8 : u.getReg .x8 = 5
  x9 : u.getReg .x9 = 8
  x18 : u.getReg .x18 = Bb
  x19 : u.getReg .x19 = 1
  x20 : u.getReg .x20 = s.getReg .x2 - 512
  x21 : u.getReg .x21 = 6
  x22 : u.getReg .x22 = 2
  x27 : u.getReg .x27 = 6

end Rv64Verifier.Proofs.Walk
