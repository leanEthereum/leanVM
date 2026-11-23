module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.GlueLevel
public meta import NativeRustcVmArm.Code.Vm.GlueLevel
public meta import NativeRustcVmArm.Whir.Common

/-!
# `glue_level`'s blocks, run by the symbolic executor

Each run starts where a block follows a call (or at the entry), from a literal state naming the
regions it touches: the 112-byte frame below SP, the six argument words at the entry's SP, the
state's head (its claim, `α`s and the glued claims' count), and a glued claim (the first at
`512 + 6064 · len`, the second `6064` bytes on).
-/

namespace NativeRustcVmArm.Whir.GlueLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GlueLevel

@[expose] public section

/-- The entry: the frame (region 0, 112 bytes below SP), the stack arguments (region 1, 48
bytes at SP), the state's head (region 2, 512 bytes at X0). -/
def entryS : SState :=
  init [(112, true), (48, false), (512, false)] (.ptr 0 112) [(.X0, .ptr 2 0)] []
    [] [(.ptr 0 144, 1, 32), (.ptr 0 152, 1, 40)]

/-- Registers only. -/
def regS : SState := init []

/-- The first glued claim's address: `512 + 6064 · len` from the state. -/
def g1Sym : Sym := .bin .add .W64 (.bin .mul .W64 (.load 0 504 8) (.lit 6064)) (.ptr 0 512)

/-- Blocks 3 and 4: the state's head (region 0) at X19, the first glued claim (region 1). -/
def headS : SState :=
  init [(512, false), (6064, false)] .sp [(.X19, .ptr 0 0)] [] [] [(g1Sym, 1, 0)]

/-- The second glued claim's address. -/
def g2Sym : Sym :=
  .bin .add .W64 (.bin .mul .W64 (.bin .add .W64 (.load 2 504 8) (.lit 1)) (.lit 6064))
    (.ptr 2 512)

/-- Blocks 5 to 7: the frame (region 0), the stack arguments (region 1), the state's head
(region 2) at X19, the second glued claim (region 3). -/
def secondS : SState :=
  init [(112, true), (48, false), (512, false), (6064, false)] (.ptr 0 0)
    [(.X19, .ptr 2 0), (.X28, .ptr 2 512)] [] [] [(.ptr 0 112, 1, 0), (.ptr 0 120, 1, 8), (g2Sym, 3, 0)]

/-- Blocks 8 and 9: the frame, the stack arguments, the second glued claim (region 2) at X21. -/
def weightsS : SState :=
  init [(112, true), (48, false), (6064, false)] (.ptr 0 0) [(.X21, .ptr 2 0)] [] []
    [(.ptr 0 128, 1, 16), (.ptr 0 136, 1, 24)]

/-- Blocks 10, 11, 13: the frame (region 0), the state's head (region 1) at X19. -/
def exitS : SState := init [(112, true), (512, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 regS
sym_block run_b2 := exec b2 regS
sym_block run_b3 := exec b3 headS
sym_block run_b4 := exec b4 (after b3 headS)
sym_block run_b5 := exec b5 secondS
sym_block run_b6 := exec b6 (after b5 secondS)
sym_block run_b7 := exec b7 (after b6 (after b5 secondS))
sym_block run_b8 := exec b8 weightsS
sym_block run_b9 := exec b9 (after b8 weightsS)
sym_block run_b10 := exec b10 exitS
sym_block run_b11 := exec b11 (after b10 exitS)
sym_block run_b13 := exec b13 (after b11 (after b10 exitS))

end NativeRustcVmArm.Whir.GlueLevel
