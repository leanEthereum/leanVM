module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.BusLayout
public meta import NativeRustcVmArm.Code.Vm.BusLayout

/-!
# `bus_layout`'s blocks, run by the symbolic executor

Region 0 is the 1840-byte frame: the sizes at `8` (54 words), the offsets at `440` (54 words), the
`BusLayoutW` under construction at `872`, the saved registers from `1760`. `b0` saves them and
clears the sizes (`memset`); `b2`-`b4` copy the framework sizes (region 1 the framework sizes at
X25); the loop `b7`, `b6` (`b7`: region 0 the block at X23) writes each block's height
(`sL`: the byte offset X8 is `8 · var 0`, the heights region 1; every owner is a table's, so
`b8` is never reached); `b9` clears the offsets; `b10`
calls `stack_offsets`; `b12` clears the layout; the loop `b13`-`b18` pushes each placement
(`sP`, `sF16`, `sT`); `b20` copies the layout out (`memcpy`), `b21` sets the tag (region 1 the
output's tag at X19), `b22` returns.
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout

@[expose] public section

/-- At the entry: the frame below SP. -/
def s0 : SState := init [(1840, true)] (.ptr 0 1840)
/-- In the frame. -/
def sF : SState := init [(1840, true)] (.ptr 0 0)
/-- Registers only. -/
def sR : SState := init []
/-- The framework sizes (`n` bytes) at X25. -/
def sW (n : Nat) : SState := init [(1840, true), (n, false)] (.ptr 0 0) [(.X25, .ptr 1 0)]
/-- The block at X23. -/
def sB : SState := init [(16, false)] .sp [(.X23, .ptr 0 0)]
/-- A block's height into the sizes: the byte offset X8 is `8 · var 0`, the heights at X9. -/
def sL : SState :=
  init [(1840, true), (48, false)] (.ptr 0 0)
    [(.X26, .ptr 0 8), (.X9, .ptr 1 0), (.X8, .un (.shift .LSL 3) .W64 (.var 0))] []
    [(.var 0, 54), (.reg .X10, 6)]
/-- The sizes and offsets read at X8. -/
def sP : SState :=
  init [(1840, true)] (.ptr 0 0) [(.X23, .ptr 0 8), (.X22, .ptr 0 440)] [] [(.reg .X8, 54)]
/-- A framework placement pushed at X9. -/
def sF16 : SState := init [(1840, true)] (.ptr 0 0) [(.X10, .ptr 0 888)] [] [(.reg .X9, 3)]
/-- A table placement pushed at the tables' count X14. -/
def sT : SState := init [(1840, true)] (.ptr 0 0) [(.X11, .ptr 0 944)] [] [(.reg .X14, 51)]
/-- The output's tag at X19. -/
def sO : SState := init [(1840, true), (8, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 s0
sym_block run_b1 := exec b1 sF
sym_block run_b2 := exec b2 (sW 8)
sym_block run_b3 := exec b3 (sW 16)
sym_block run_b4 := exec b4 (sW 24)
sym_block run_b5 := exec b5 sR
sym_block run_b6 := exec b6 sL
sym_block run_b7 := exec b7 sB
sym_block run_b9 := exec b9 sF
sym_block run_b10 := exec b10 sF
sym_block run_b11 := exec b11 sR
sym_block run_b12 := exec b12 sF
sym_block run_b13 := exec b13 sR
sym_block run_b14 := exec b14 sP
sym_block run_b15 := exec b15 sR
sym_block run_b16 := exec b16 sF16
sym_block run_b17 := exec b17 sF
sym_block run_b18 := exec b18 sT
sym_block run_b20 := exec b20 sF
sym_block run_b21 := exec b21 sO
sym_block run_b22 := exec b22 sF

end NativeRustcVmArm.Bus.BusLayout
