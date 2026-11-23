module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.EachRowOfNextLevel
public meta import NativeRustcVmArm.Code.Vm.EachRowOfNextLevel
public meta import NativeRustcVmArm.Whir.Common

/-!
# `each_row` with `next_level`'s closure: its blocks, run by the symbolic executor

Region 0 is always the 2000-byte frame below SP. `entryS` at the entry; `tableS` after
`subspace_table` (X19 its output, at 600); `rowsS` at `b3`, with the `Rows` (X21); `envS` at `b4`,
with the closure (X25); `frameS` the frame alone; `queryS` at `b9`, with query `j` (`qAddr`, the
queries' address at 88 plus 8 times X24); `muS` at `b14`, with `μ`'s word (its address at 48);
`whatS` at `b15`, `What` `μ` at an index below `31`; `weightS` at `b5`, with query weight `j`
(X23 − 8); `batchS` at `b6`, `b7`, with the batched value (X20).
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.EachRowOfNextLevel

@[expose] public section

/-- The entry. -/
def entryS : SState := init [(2000, true)] (.ptr 0 2000)
/-- After `subspace_table`. -/
def tableS : SState := init [(2000, true)] (.ptr 0 0) [(.X19, .ptr 0 600)]
/-- At `b3`. -/
def rowsS : SState := init [(2000, true), (32, false)] (.ptr 0 0) [(.X21, .ptr 1 0)]
/-- At `b4`. -/
def envS : SState := init [(2000, true), (48, false)] (.ptr 0 0) [(.X25, .ptr 1 0), (.X26, .ptr 0 104)]
/-- The frame alone. -/
def frameS : SState := init [(2000, true)] (.ptr 0 0)
/-- Query `j`'s address. -/
def qAddr : Sym := .bin .add .W64 (.load 0 88 8) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X24))
/-- At `b9`. -/
def queryS : SState := init [(2000, true), (8, false)] (.ptr 0 0) [] [] [] [(qAddr, 1, 0)]
/-- At `b14`. -/
def muS : SState := init [(2000, true), (8, false)] (.ptr 0 0) [] [] [] [(.load 0 48 8, 1, 0)]
/-- At `b15`. -/
def whatS : SState := init [(2000, true)] (.ptr 0 0) [(.X3, .ptr 0 1632)] [] [(.reg .X8, 31)]
/-- At `b5`. -/
def weightS : SState := init [(2000, true), (16, false)] (.ptr 0 0) [] [] [] [(.reg .X23, 1, 8)]
/-- At `b6`, `b7`. -/
def batchS : SState := init [(2000, true), (16, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 tableS
sym_block run_b2 := exec b2 (after b1 tableS)
sym_block run_b3 := exec b3 rowsS
sym_block run_b4 := exec b4 envS
sym_block run_b8 := exec b8 frameS
sym_block run_b9 := exec b9 queryS
sym_block run_b10 := exec b10 frameS
sym_block run_b11 := exec b11 frameS
sym_block run_b12 := exec b12 (after b11 frameS)
sym_block run_b13 := exec b13 frameS
sym_block run_b14 := exec b14 muS
sym_block run_b15 := exec b15 whatS
sym_block run_b16 := exec b16 frameS
sym_block run_b17 := exec b17 frameS
sym_block run_b18 := exec b18 (after b17 frameS)
sym_block run_b19 := exec b19 frameS
sym_block run_b20 := exec b20 frameS
sym_block run_b5 := exec b5 weightS
sym_block run_b21 := exec b21 frameS
sym_block run_b6 := exec b6 batchS
sym_block run_b7 := exec b7 batchS
sym_block run_b22 := exec b22 frameS
sym_block run_b23 := exec b23 frameS
sym_block run_b24f := exec b24 (after b22 frameS)
sym_block run_b24t := exec b24 (after b23 frameS)

end NativeRustcVmArm.Whir.EachRowOfNextLevel
