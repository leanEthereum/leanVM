module

public import NativeRustcX64.LayerRead.Inv
meta import NativeRustcX64.LayerRead.Inv
meta import NativeRustcX64.Code.Xmss.LayerRead

/-! # Symbolic execution of the sixteen authentication-path reads -/

namespace NativeRustcX64.Xmss.LayerRead

open NativeRustcX64.Sym

set_option Elab.async false

@[expose] public def stP0 : SState :=
  (init [1944, 16, 1200, 8]
    [(.rsp, .ptr 0 8), (.r14, .ptr 1 0), (.r13, .ptr 2 912), (.r15, .ptr 2 944)] [] []
    [(.gotSlot "memcpy", 3, 0)]).withKnownBytes 3 0 8 (.label "memcpy")

sym_block b6_execP := exec b6 stP0

/-- After block 6. -/
@[expose] public def stP1 : SState := ((exec b6 stP0).getD (stP0, .fall)).1

sym_block b7_execP := exec b7 stP1

/-- After block 7. -/
@[expose] public def stP2 : SState := ((exec b7 stP1).getD (stP1, .fall)).1

sym_block b8_execP := exec b8 stP2

/-- After block 8. -/
@[expose] public def stP3 : SState := ((exec b8 stP2).getD (stP2, .fall)).1

sym_block b9_execP := exec b9 stP3

/-- After block 9. -/
@[expose] public def stP4 : SState := ((exec b9 stP3).getD (stP3, .fall)).1

sym_block b10_execP := exec b10 stP4

/-- After block 10. -/
@[expose] public def stP5 : SState := ((exec b10 stP4).getD (stP4, .fall)).1

sym_block b11_execP := exec b11 stP5

/-- After block 11. -/
@[expose] public def stP6 : SState := ((exec b11 stP5).getD (stP5, .fall)).1

sym_block b12_execP := exec b12 stP6

/-- After block 12. -/
@[expose] public def stP7 : SState := ((exec b12 stP6).getD (stP6, .fall)).1

sym_block b13_execP := exec b13 stP7

/-- After block 13. -/
@[expose] public def stP8 : SState := ((exec b13 stP7).getD (stP7, .fall)).1

sym_block b14_execP := exec b14 stP8

/-- After block 14. -/
@[expose] public def stP9 : SState := ((exec b14 stP8).getD (stP8, .fall)).1

sym_block b15_execP := exec b15 stP9

/-- After block 15. -/
@[expose] public def stP10 : SState := ((exec b15 stP9).getD (stP9, .fall)).1

sym_block b16_execP := exec b16 stP10

/-- After block 16. -/
@[expose] public def stP11 : SState := ((exec b16 stP10).getD (stP10, .fall)).1

sym_block b17_execP := exec b17 stP11

/-- After block 17. -/
@[expose] public def stP12 : SState := ((exec b17 stP11).getD (stP11, .fall)).1

sym_block b18_execP := exec b18 stP12

/-- After block 18. -/
@[expose] public def stP13 : SState := ((exec b18 stP12).getD (stP12, .fall)).1

sym_block b19_execP := exec b19 stP13

/-- After block 19. -/
@[expose] public def stP14 : SState := ((exec b19 stP13).getD (stP13, .fall)).1

sym_block b20_execP := exec b20 stP14

/-- After block 20. -/
@[expose] public def stP15 : SState := ((exec b20 stP14).getD (stP14, .fall)).1

sym_block b21_execP := exec b21 stP15

/-- After block 21. -/
@[expose] public def stP16 : SState := ((exec b21 stP15).getD (stP15, .fall)).1

sym_block b22_execP := exec b22 stP16

/-- After block 22. -/
@[expose] public def stP17 : SState := ((exec b22 stP16).getD (stP16, .fall)).1

public theorem stP17_regs : stP17.reg .rdi = some (.load 0 24 8) ∧
    stP17.reg .rsi = some (.ptr 0 32) ∧ stP17.reg .rdx = some (.lit 256) ∧
    stP17.reg .rsp = some (.ptr 0 0) ∧ stP17.reg .r14 = some (.load 0 24 8) ∧
    stP17.reg .rbx = some (.label "memcpy") := by decide +kernel

public theorem stP17_path : ∀ t < 256,
    findWrite 0 (32 + t) stP17.mem = some (.load 2 (944 + 8 * (t / 8)) 8, t % 8) := by
  decide +kernel

public theorem stP17_cursor : ∀ t < 8,
    findWrite 1 (0 + t) stP17.mem = some (.ptr 2 1200, t) := by decide +kernel
public theorem stP17_length : ∀ t < 8,
    findWrite 1 (8 + t) stP17.mem =
      some (.bin .add .W64 (.lit (2 ^ 64 - 288))
        (.bin .add .W64 (.lit (2 ^ 64 - 16)) (.reg .rbx)), t) := by decide +kernel

public theorem stP17_writes : writesBelow stP17 [(0, 288), (1, 16)] = true := by decide +kernel
public theorem stP17_input : firstOverlap 0 16 8 stP17.mem = none := by decide +kernel
public theorem stP17_output : firstOverlap 0 24 8 stP17.mem = none := by decide +kernel
public theorem stP17_chain : firstOverlap 0 960 928 stP17.mem = none := by decide +kernel
public theorem stP17_save : ∀ j < 6, firstOverlap 0 (1888 + 8 * j) 8 stP17.mem = none := by
  decide +kernel
public theorem stP17_retAddr : ∀ t < 8, findWrite 0 (0 + t) stP17.mem = some (.retAddr, t) := by
  decide +kernel

end NativeRustcX64.Xmss.LayerRead
