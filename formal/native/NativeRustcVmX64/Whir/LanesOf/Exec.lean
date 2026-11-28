module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.LanesOf
public meta import NativeRustcVmX64.Code.Vm.LanesOf
public meta import NativeRustcVmX64.Whir.Common
public meta import NativeRustcVmX64.Field.Frame
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `lanes_of`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Transcript.frameEnv m0 _ 8`): RBX's slot, pushed by `b0`, and the return
address. From the entry (`entryS`) the blocks before a loop run in the entry's environment: a later
level `b0`, `b1` (`None` `b11`), `b2` (no pair `b10`), `b3`, then one pair (`b4`, on to `b15`) or
the pairs' loop (`b12`); level `0` `b0`, `b5` (`None` `b11`), `b6` (no lane `b16`), `b7`. Each
loop turn runs in its own environment, the frame and the bytes it reads and writes:
- `headA` (`b8`, `b9`): region 1 the row's word `len - 1 - i` at RSI + R8, region 2 lane `i` at
  RCX;
- `headB` (`b13`): region 1 the row's pairs `2j`, `2j + 1` at RSI + R10 - 24, region 2 their lanes
  at RCX + R10 - 24;
- `tailS` (`b15`): region 1 the row's pair `e` at RSI + 16 RDI, region 2 its lane;
- `midS0` (`b14`, `b10`): the frame only.
-/

namespace NativeRustcVmX64.Whir.LanesOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LanesOf NativeRustcVmX64.Field
open NativeRustcVmX64.Transcript (Slots ProOk MidOk EpiOk)

@[expose] public section

/-- At the entry: the frame, RSP above RBX's slot. -/
abbrev entryS : SState := frameS 8
/-- After the prologue `b0`. -/
def s0 : SState := after b0 entryS
/-- A later level: after `b1`, `b2`, `b3`. -/
def s1 : SState := after b1 s0
def s2 : SState := after b2 s1
def s3 : SState := after b3 s2
/-- Level `0`: after `b5`, `b6`. -/
def s5 : SState := after b5 s0
def s6 : SState := after b6 s5

/-- The frame only, RSP at RBX's slot. -/
def midS0 : SState := init [16] [(.rsp, .ptr 0 0)]
/-- Level `0`'s loop: the row's word at RSI + R8, the lane at RCX. -/
def headA : SState := init [16, 8, 16] [(.rsp, .ptr 0 0)] [] []
  [(.bin .add .W64 (.reg .rsi) (.reg .r8), 1, 0), (.reg .rcx, 2, 0)]
/-- The pairs' loop: two pairs at RSI + R10 - 24, their lanes at RCX + R10 - 24. -/
def headB : SState := init [16, 32, 32] [(.rsp, .ptr 0 0)] [] []
  [(.bin .add .W64 (.reg .rsi) (.reg .r10), 1, 24), (.bin .add .W64 (.reg .rcx) (.reg .r10), 2, 24)]
/-- The last pair: at RSI + 16 RDI, its lane at RCX + 16 RDI. -/
def tailS : SState := init [16, 16, 16] [(.rsp, .ptr 0 0)] [] []
  [(.bin .add .W64 (.reg .rsi) (.bin .shl .W64 (.reg .rdi) (.lit 4)), 1, 0),
    (.bin .add .W64 (.reg .rcx) (.bin .shl .W64 (.reg .rdi) (.lit 4)), 2, 0)]

/-- RBX's slot. -/
def slots : Slots := [(0, .rbx)]

/-- The writes of a block, all in region `r`, below `n`. -/
def writesBelow (S : SState) (r n : Nat) : Bool := S.mem.all fun w ↦ w.r == r && decide (w.off + w.n ≤ n)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 s0
sym_block run_b11p := exec b11 s1
sym_block run_b2 := exec b2 s1
sym_block run_b10z := exec b10 s2
sym_block run_b3 := exec b3 s2
sym_block run_b4 := exec b4 s3
sym_block run_b12 := exec b12 s3
sym_block run_b5 := exec b5 s0
sym_block run_b11r := exec b11 s5
sym_block run_b6 := exec b6 s5
sym_block run_b16 := exec b16 s6
sym_block run_b7 := exec b7 s6
sym_block run_b8 := exec b8 headA
sym_block run_b9 := exec b9 (after b8 headA)
sym_block run_b13 := exec b13 headB
sym_block run_b14 := exec b14 midS0
sym_block run_b10 := exec b10 midS0
sym_block run_b15 := exec b15 tailS

/-! ## The prologue's chains: RBX in its slot -/

public theorem pro_b4 : ProOk 8 0 slots (after b4 s3) = true ∧ writesBelow (after b4 s3) 0 8 = true :=
  by decide +kernel
public theorem pro_b12 : ProOk 8 0 slots (after b12 s3) = true ∧
    writesBelow (after b12 s3) 0 8 = true := by decide +kernel
public theorem pro_b7 : ProOk 8 0 slots (after b7 s6) = true ∧ writesBelow (after b7 s6) 0 8 = true :=
  by decide +kernel

/-! ## Returns from the entry's environment -/

public theorem epi_b11p : EpiOk 8 [] (after b11 s1) = true ∧ writesBelow (after b11 s1) 0 8 = true :=
  by decide +kernel
public theorem epi_b11r : EpiOk 8 [] (after b11 s5) = true ∧ writesBelow (after b11 s5) 0 8 = true :=
  by decide +kernel
public theorem epi_b10z : EpiOk 8 [] (after b10 s2) = true ∧ writesBelow (after b10 s2) 0 8 = true :=
  by decide +kernel
public theorem epi_b16 : EpiOk 8 [] (after b16 s6) = true ∧ writesBelow (after b16 s6) 0 8 = true :=
  by decide +kernel

/-! ## The loops and the returns from a frame -/

public theorem mid_b8 : MidOk 8 0 slots (after b8 headA) = true ∧
    writesBelow (after b8 headA) 2 16 = true := by decide +kernel
public theorem mid_b9 : MidOk 8 0 slots (after b9 (after b8 headA)) = true ∧
    writesBelow (after b9 (after b8 headA)) 2 16 = true := by decide +kernel
public theorem mid_b13 : MidOk 8 0 slots (after b13 headB) = true ∧
    writesBelow (after b13 headB) 2 32 = true := by decide +kernel
/-! ## The lanes written -/

public theorem lane_b8 : (∀ t < 8, findWrite 2 (0 + t) (after b8 headA).mem = some (.load 1 0 8, t)) ∧
    (∀ t < 8, findWrite 2 (0 + 8 + t) (after b8 headA).mem = some (.lit 0, t)) := by decide +kernel
public theorem lane_b9 :
    (∀ t < 8, findWrite 2 (0 + t) (after b9 (after b8 headA)).mem = some (.load 1 0 8, t)) ∧
    (∀ t < 8, findWrite 2 (0 + 8 + t) (after b9 (after b8 headA)).mem = some (.lit 0, t)) := by
  decide +kernel
public theorem lane_b13 :
    (∀ t < 8, findWrite 2 (0 + t) (after b13 headB).mem = some (.load 1 0 8, t)) ∧
    (∀ t < 8, findWrite 2 (0 + 8 + t) (after b13 headB).mem = some (.load 1 8 8, t)) ∧
    (∀ t < 8, findWrite 2 (16 + t) (after b13 headB).mem = some (.load 1 16 8, t)) ∧
    (∀ t < 8, findWrite 2 (16 + 8 + t) (after b13 headB).mem = some (.load 1 24 8, t)) := by
  decide +kernel
public theorem lane_b15 :
    (∀ t < 8, findWrite 2 (0 + t) (after b15 tailS).mem = some (.load 1 0 8, t)) ∧
    (∀ t < 8, findWrite 2 (0 + 8 + t) (after b15 tailS).mem = some (.load 1 8 8, t)) := by
  decide +kernel

public theorem mid_b14 : MidOk 8 0 slots (after b14 midS0) = true ∧ (after b14 midS0).mem = [] := by
  decide +kernel
public theorem epi_b10 : EpiOk 8 slots (after b10 midS0) = true ∧ (after b10 midS0).mem = [] := by
  decide +kernel
public theorem epi_b15 : EpiOk 8 slots (after b15 tailS) = true ∧
    writesBelow (after b15 tailS) 2 16 = true := by decide +kernel

end NativeRustcVmX64.Whir.LanesOf
