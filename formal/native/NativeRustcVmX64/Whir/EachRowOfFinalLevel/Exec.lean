module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel
public meta import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel
public meta import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Frame
public meta import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Frame

/-!
# `each_row` with `final_level`'s closure: its blocks, run by the symbolic executor (x86-64)

Region 0 is the 1936 bytes below the entry's RSP (the call slot, the 1880-byte frame, the six
pushes), the return address and the 24 bytes of stack arguments (`stackBelow m0 1936`, 1968
bytes); the body's RSP is its offset `8`. `entryS` at the entry; `frameS` the frame alone, RSP at
`8`; `rowsS` at `b3`, the `Rows` (R14) region 1; `headS` at `b6`, query `j` (RBP) region 1 (in
both region 0 without the arguments, which the inputs need not be apart from); `zS` an iteration
of the lanes' clearing (`b7`): region 0 the 104 bytes at `RSP + RAX`.
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EachRowOfFinalLevel

@[expose] public section

/-- The entry. -/
def entryS : SState := init [1968] [(.rsp, .ptr 0 1936)]
/-- The frame alone, RSP at offset `8`. -/
def frameS : SState := init [1968] [(.rsp, .ptr 0 8)]
/-- At `b3`: the `Rows` (R14). -/
def rowsS : SState := init [1944, 32] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]
/-- At `b6`: query `j` (RBP). -/
def headS : SState := init [1944, 8] [(.rsp, .ptr 0 8), (.rbp, .ptr 1 0)]
/-- The bytes `b7` clears: `RSP + RAX` and the 104 bytes from it (the 64 from `40`). -/
def zS : SState := init [104] [] [] [] [(.bin .add .W64 (.reg .rsp) (.reg .rax), 0, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (EachRow.gotFrameS 1936 24 "memcpy")
sym_block run_b2 := exec b2 (after b1 (EachRow.gotFrameS 1936 24 "memcpy"))
sym_block run_b3 := exec b3 rowsS
sym_block run_b4 := exec b4 frameS
sym_block run_b5 := exec b5 frameS
sym_block run_b6 := exec b6 headS
sym_block run_b7 := exec b7 zS
sym_block run_b8 := exec b8 frameS
sym_block run_b9 := exec b9 frameS
sym_block run_b10 := exec b10 frameS
sym_block run_b11 := exec b11 frameS
sym_block run_b12 := exec b12 frameS
sym_block run_b13 := exec b13 frameS
sym_block run_b14 := exec b14 frameS
sym_block run_b15 := exec b15 (after b14 frameS)
sym_block run_b16 := exec b16 (after b15 (after b14 frameS))
sym_block run_b17 := exec b17 (after b16 (after b15 (after b14 frameS)))
sym_block run_b18 := exec b18 frameS
sym_block run_b19 := exec b19 frameS
sym_block run_b20 := exec b20 frameS

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
