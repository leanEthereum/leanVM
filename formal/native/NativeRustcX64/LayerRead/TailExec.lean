module

public import NativeRustcX64.LayerRead.Inv
meta import NativeRustcX64.LayerRead.Inv
meta import NativeRustcX64.Code.Xmss.LayerRead

/-! # Symbolic output stores and restoration of all six saved registers -/

namespace NativeRustcX64.Xmss.LayerRead

open NativeRustcX64.Sym

set_option Elab.async false

@[expose] public def stT0 : SState :=
  init [1944, 1200, 1200] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0), (.rbx, .label "memcpy")]
    [] [] [(.load 0 16 8, 2, 0)]
sym_block b23_execT := exec b23 stT0
@[expose] public def stT1 : SState := ((exec b23 stT0).getD (stT0, .fall)).1

public theorem stT1_facts : stT1.reg .rdi = some (.ptr 1 256) ∧
    stT1.reg .rsi = some (.ptr 0 960) ∧ stT1.reg .rdx = some (.lit 928) ∧
    stT1.reg .rsp = some (.ptr 0 0) ∧
    writesBelow stT1 [(0, 8), (1, 1200)] = true ∧ firstOverlap 0 960 928 stT1.mem = none ∧
    (∀ j < 6, firstOverlap 0 (1888 + 8 * j) 8 stT1.mem = none) ∧
    firstOverlap 1 0 256 stT1.mem = none := by decide +kernel
public theorem stT1_rand : ∀ t < 16,
    findWrite 1 (1184 + t) stT1.mem = some (.load 2 (8 * (t / 8)) 8, t % 8) := by decide +kernel

@[expose] public def stE0 : SState := init [1944] [(.rsp, .ptr 0 8)]
sym_block b24_execE := exec b24 stE0
@[expose] public def stE1 : SState := ((exec b24 stE0).getD (stE0, .fall)).1
public theorem stE1_facts : stE1.mem = [] ∧ stE1.reg .rsp = some (.ptr 0 1944) ∧
    (∀ j < 6, stE1.reg (saveRegs.getD j .rax) = some (.load 0 (1888 + 8 * j) 8)) := by
  decide +kernel

end NativeRustcX64.Xmss.LayerRead
