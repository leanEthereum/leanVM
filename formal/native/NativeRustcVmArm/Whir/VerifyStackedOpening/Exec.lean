module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening
public meta import NativeRustcVmArm.Code.Vm.VerifyStackedOpening
public meta import NativeRustcVmArm.Whir.Common

/-!
# `verify_stacked_opening`'s blocks, run by the symbolic executor

Each run starts where a block follows a call or a branch, from a literal state naming the regions
it touches: the 512-byte frame below SP (region 0 where present), the claims' count word
(`entryS`), the layout with an index bound on three times a column (`placeS`), a column claim
(`claimS`), a scale (`scaleS`), the scales' count word (`scS`), the ring switch's target
(`ringS`), the out-of-domain claim (`oodS`), the layout's head (`ladS`), the stack argument and the
`WhirW`'s head (`whirS`); `init [] .sp` for the blocks of registers only.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyStackedOpening

@[expose] public section

/-- Three times register `r`: a column's placement word index. -/
def t3 (r : XReg) : Sym := .bin .add .W64 (.reg r) (.un (.shift .LSL 1) .W64 (.reg r))

/-- The entry: the frame, the claims' count word at X5. -/
def entryS : SState := init [(512, true), (8, false)] (.ptr 0 512) [(.X5, .ptr 1 0)]
/-- Registers only. -/
def regS : SState := init [] .sp
/-- `b2`: the layout at X9 − 120, a column below `158` in X12. -/
def placeS : SState := init [(3912, false)] .sp [(.X9, .ptr 0 120)] [] [(t3 .X12, 472)]
/-- `b23`: the layout at X20 − 120, a column below `158` in X8. -/
def place2S : SState := init [(3912, false)] .sp [(.X20, .ptr 0 120)] [] [(t3 .X8, 472)]
/-- `b3`: the claim at X10. -/
def claimS : SState := init [(608, false)] .sp [(.X10, .ptr 0 0)]
/-- `b19`, `b22`: the claim at X28. -/
def claim2S : SState := init [(608, false)] .sp [(.X28, .ptr 0 0)]
/-- The frame alone. -/
def frameS : SState := init [(512, true)] (.ptr 0 0)
/-- `b11`, `b12`: the frame, the scales' count word at X26. -/
def scS : SState := init [(512, true), (8, false)] (.ptr 0 0) [(.X26, .ptr 1 0)]
/-- `b13`: the scale at X23. -/
def scaleS : SState := init [(16, false)] .sp [(.X23, .ptr 0 0)]
/-- `b18`, `b27`: the scale at X19. -/
def scale2S : SState := init [(16, false)] .sp [(.X19, .ptr 0 0)]
/-- `b15`: the frame, the ring switch's target at X24. -/
def ringS : SState := init [(512, true), (16, false)] (.ptr 0 0) [(.X24, .ptr 1 0)]
/-- `b29`: the frame, the out-of-domain claim at the frame's word 40. -/
def oodS : SState := init [(512, true), (504, false)] (.ptr 0 0) [] [] [] [(.load 0 40 8, 1, 0)]
/-- `b30`: the frame, the layout's head at X22. -/
def ladS : SState := init [(512, true), (24, false)] (.ptr 0 0) [(.X22, .ptr 1 0)]
/-- `b34`: the frame, the stack argument, the `WhirW`'s head at the stack argument. -/
def whirS : SState :=
  init [(512, true), (8, false), (512, false)] (.ptr 0 0) [] [] []
    [(.ptr 0 512, 1, 0), (.load 1 0 8, 2, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 regS
sym_block run_b2 := exec b2 placeS
sym_block run_b3 := exec b3 claimS
sym_block run_b4 := exec b4 regS
sym_block run_b5 := exec b5 regS
sym_block run_b6 := exec b6 frameS
sym_block run_b7 := exec b7 regS
sym_block run_b8 := exec b8 frameS
sym_block run_b9 := exec b9 frameS
sym_block run_b10 := exec b10 regS
sym_block run_b11 := exec b11 scS
sym_block run_b12 := exec b12 scS
sym_block run_b13 := exec b13 scaleS
sym_block run_b14 := exec b14 regS
sym_block run_b15 := exec b15 ringS
sym_block run_b16 := exec b16 regS
sym_block run_b17 := exec b17 regS
sym_block run_b18 := exec b18 scale2S
sym_block run_b19 := exec b19 claim2S
sym_block run_b20 := exec b20 regS
sym_block run_b21 := exec b21 regS
sym_block run_b22 := exec b22 claim2S
sym_block run_b23 := exec b23 place2S
sym_block run_b24 := exec b24 regS
sym_block run_b25 := exec b25 regS
sym_block run_b26 := exec b26 regS
sym_block run_b27 := exec b27 scale2S
sym_block run_b28 := exec b28 regS
sym_block run_b29 := exec b29 oodS
sym_block run_b30 := exec b30 ladS
sym_block run_b31 := exec b31 frameS
sym_block run_b32 := exec b32 frameS
sym_block run_b33 := exec b33 frameS
sym_block run_b34 := exec b34 whirS
sym_block run_b35 := exec b35 regS
sym_block run_b36 := exec b36 regS
sym_block run_b37 := exec b37 frameS

end NativeRustcVmArm.Whir.VerifyStackedOpening
