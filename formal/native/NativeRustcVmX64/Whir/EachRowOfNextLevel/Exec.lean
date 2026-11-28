module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel
public meta import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel
public meta import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Frame
public meta import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Frame

/-!
# `each_row` with `next_level`'s closure: its blocks, run by the symbolic executor (x86-64)

Region 0 is the 1984 bytes below the entry's RSP (the call slot, the 1928-byte frame, the six
pushes), the return address and the 16 bytes of stack arguments (`stackBelow m0 1984`, 2008
bytes); the body's RSP is its offset `8`. `entryS` at the entry; `frameS` the frame alone. The
states with an input region keep region 0 without the arguments (1992 bytes; the inputs need not
be apart from them): `rowsS` at `b3`, the `Rows` (R12); `argS` in `b4` after its first two
instructions, the closure (RAX, the stack argument `1`); `headS` at `b10`, query `j` (R15); `muS`
at `b17`, `μ` (the word at offset `64`); `qwS` at `b6`, query weight `j` (16 bytes at the word at
offset `8` plus `16 j`, RBX `j`) and the batched value (R14); `batS` the batched value (R14).
`zS` an iteration of the lanes' clearing (`b11`, the 64 bytes at `RSP + RAX + 88`); `whatS` at
`b18`, the `What`s (RCX) indexed by `μ` (RAX, below 31).
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EachRowOfNextLevel

@[expose] public section

/-- The entry. -/
def entryS : SState := init [2008] [(.rsp, .ptr 0 1984)]
/-- The frame alone, RSP at offset `8`. -/
def frameS : SState := init [2008] [(.rsp, .ptr 0 8)]
/-- At `b3`: the `Rows` (R12). -/
def rowsS : SState := init [1992, 32] [(.rsp, .ptr 0 8), (.r12, .ptr 1 0)]
/-- `b4` after its load of the closure's address (RAX), the closure region 1. -/
def argS : SState := init [1992, 48] [(.rsp, .ptr 0 8), (.rax, .ptr 1 0)]
/-- At `b10`: query `j` (R15). -/
def headS : SState := init [1992, 8] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]
/-- The 64 bytes `b11` clears: `RSP + RAX + 88`. -/
def zS : SState := init [64] [] [] [] [(.bin .add .W64 (.reg .rsp) (.reg .rax), 0, -88)]
/-- At `b17`: `μ`, at the word at offset `64`. -/
def muS : SState := init [1992, 8] [(.rsp, .ptr 0 8)] [] [] [(.load 0 64 8, 1, 0)]
/-- At `b18`: the `What`s (RCX), `μ` (RAX) below 31. -/
def whatS : SState := init [2008] [(.rsp, .ptr 0 8), (.rcx, .ptr 0 1184)] [] [(.reg .rax, 31)]
/-- Query weight `j`'s address: the weights' address plus `16 j`. -/
def qwAddr : Sym := .bin .add .W64 (.load 0 8 8) (.bin .shl .W64 (.reg .rbx) (.lit 4))
/-- At `b6`: query weight `j`, the batched value (R14). -/
def qwS : SState := init [1992, 16, 16] [(.rsp, .ptr 0 8), (.r14, .ptr 2 0)] [] [] [(qwAddr, 1, 0)]
/-- The batched value (R14). -/
def batS : SState := init [1992, 16] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (EachRow.gotFrameS 1984 16 "memcpy")
sym_block run_b2 := exec b2 (after b1 (EachRow.gotFrameS 1984 16 "memcpy"))
sym_block run_b3 := exec b3 rowsS
sym_block run_b4a := exec (b4.take 2) frameS
sym_block run_b4b := exec (b4.drop 2) argS
sym_block run_b9 := exec b9 frameS
sym_block run_b10 := exec b10 headS
sym_block run_b11 := exec b11 zS
sym_block run_b12 := exec b12 frameS
sym_block run_b13 := exec b13 frameS
sym_block run_b14 := exec b14 frameS
sym_block run_b15 := exec b15 frameS
sym_block run_b16 := exec b16 frameS
sym_block run_b17 := exec b17 muS
sym_block run_b18 := exec b18 whatS
sym_block run_b19 := exec b19 frameS
sym_block run_b20 := exec b20 frameS
sym_block run_b21 := exec b21 frameS
sym_block run_b22 := exec b22 frameS
sym_block run_b23 := exec b23 batS
sym_block run_b24 := exec b24 (after b23 batS)
sym_block run_b7z := exec b7 (after b24 (after b23 batS))
sym_block run_b6 := exec b6 qwS
sym_block run_b7 := exec b7 (after b6 qwS)
sym_block run_b8 := exec b8 batS
sym_block run_b27 := exec b27 frameS
sym_block run_b26 := exec b26 frameS

end NativeRustcVmX64.Whir.EachRowOfNextLevel
