module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.TableSumcheck
public meta import NativeRustcVmArm.Code.Vm.TableSumcheck

/-!
# `table_sumcheck`'s blocks, run by the symbolic executor

Region 0 the 720-byte frame (the 624 bytes below the 96-byte save area): the stack arguments of
`table_terms` (`0`), the challenges (`24`, thirty slots), the sumcheck's `Option<EW>` and then the
weights (`504`), `table_terms`' `Option<EW>` (`600`), the saved registers (`624` on).

- `entryS` at the entry (`b0`: the prologue, the challenges zeroed, `n_rounds`): region 1 the six
  heights (X1).
- `sF` in the frame (`b1`: `bl sumcheck`; `b2`: its result; `b3`, `b4`: the reverse's start;
  `b7`: `bl table_terms`; `b8`, `b9`: the final comparison; `b10`, `b11`: the exits).
- `revS` (`b5`, a swap of the reverse): regions 0 and 1 the elements at X9 and X10.
- `busS` (`b6`: `bl table_weights`): region 1 the bus's result (X19).
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableSumcheck

@[expose] public section

/-- At the entry: the frame (region 0) below SP, the heights (region 1) at X1. -/
def entryS : SState := init [(720, true), (48, false)] (.ptr 0 720) [(.X1, .ptr 1 0)]
/-- In the frame, SP at its base. -/
def sF : SState := init [(720, true)] (.ptr 0 0)
/-- A swap: the elements at X9 (region 0) and X10 (region 1). -/
def revS : SState := init [(16, false), (16, false)] .sp [(.X9, .ptr 0 0), (.X10, .ptr 1 0)]
/-- In the frame, the bus's result (region 1) at X19. -/
def busS : SState := init [(720, true), (107768, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 sF
sym_block run_b2 := exec b2 sF
sym_block run_b3 := exec b3 sF
sym_block run_b4 := exec b4 sF
sym_block run_b5 := exec b5 revS
sym_block run_b6 := exec b6 busS
sym_block run_b7 := exec b7 sF
sym_block run_b8 := exec b8 sF
sym_block run_b9 := exec b9 sF
sym_block run_b10 := exec b10 sF
sym_block run_b11 := exec b11 sF

end NativeRustcVmArm.Tables.TableSumcheck
