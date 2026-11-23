module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel
public meta import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel
public meta import NativeRustcVmArm.Whir.Common

/-!
# `each_row` with `final_level`'s closure: its blocks, run by the symbolic executor

Region 0 is always the 1952-byte frame below SP. `entryS` at the entry; `tableS` after
`subspace_table` (X19 its output, at 552 in the frame); `rowsS` after `memcpy`, with the `Rows`
(X22); `argS` at `b4`, with the folded scalars' count (the word at the entry's SP); `frameS` the frame alone;
`headS` at `b6`, with query `j` (`qAddr`, X23 plus 8 times X25).
-/

namespace NativeRustcVmArm.Whir.EachRowOfFinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.EachRowOfFinalLevel

@[expose] public section

/-- The entry. -/
def entryS : SState := init [(1952, true)] (.ptr 0 1952)
/-- After `subspace_table`. -/
def tableS : SState := init [(1952, true)] (.ptr 0 0) [(.X19, .ptr 0 552)]
/-- After `memcpy`. -/
def rowsS : SState := init [(1952, true), (32, false)] (.ptr 0 0) [(.X22, .ptr 1 0)]
/-- At `b4`, with the word at the entry's SP. -/
def argS : SState :=
  init [(1952, true), (8, false)] (.ptr 0 0) [(.X26, .ptr 0 56)] [] [] [(.ptr 0 1952, 1, 0)]
/-- Query `j`'s address. -/
def qAddr : Sym := .bin .add .W64 (.reg .X23) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X25))
/-- At `b6`. -/
def headS : SState := init [(1952, true), (8, false)] (.ptr 0 0) [] [] [] [(qAddr, 1, 0)]
/-- The frame alone. -/
def frameS : SState := init [(1952, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 tableS
sym_block run_b2 := exec b2 (after b1 tableS)
sym_block run_b3 := exec b3 rowsS
sym_block run_b4 := exec b4 argS
sym_block run_b5 := exec b5 frameS
sym_block run_b6 := exec b6 headS
sym_block run_b7 := exec b7 frameS
sym_block run_b8 := exec b8 frameS
sym_block run_b9 := exec b9 (after b8 frameS)
sym_block run_b10 := exec b10 frameS
sym_block run_b11 := exec b11 frameS
sym_block run_b12 := exec b12 frameS
sym_block run_b13 := exec b13 (after b12 frameS)
sym_block run_b14 := exec b14 (after b13 (after b12 frameS))
sym_block run_b15 := exec b15 (after b14 (after b13 (after b12 frameS)))
sym_block run_b16 := exec b16 frameS
sym_block run_b17 := exec b17 frameS
sym_block run_b18t := exec b18 (after b16 frameS)
sym_block run_b18f := exec b18 (after b17 frameS)

end NativeRustcVmArm.Whir.EachRowOfFinalLevel
