module

public import NativeRustcVmX64.Field.Parts
public meta import NativeRustcVmX64.Field.Parts
public import NativeRustcVmX64.Field.RustSym
public import NativeRustcVmX64.Field.Frame
public meta import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.EWMul
public meta import NativeRustcVmX64.Code.Vm.EWMul

/-!
# `EW::mul`'s block, run by the symbolic executor in parts (x86-64)

`EW::mul` (`x` in RDI, RSI, `y` in RDX, RCX) is one straight-line block (`b0`), run from
`frameS 144` (its 6 pushes and 96-byte frame below RSP) in eleven parts, each but the last ending
where rustc has computed a bit reversal or a product of reversed words, which becomes a variable
of the environment: `0`, `1` the reversed `x0`, `y0`, `2` their product, `3` its reversal; `4`,
`5` the reversed `x1`, `y1`, `6` their product; `7`, `8` the reversed `x0 ^ x1`, `y0 ^ y1`, `9`
their product. The slices retain rustc's base-less scaled `lea`s in the reversals and reductions.
Each variable is checked against its definition (`c1` to `c10`), the results against `ewMulS`,
Karatsuba over the carry-less products (`c11`, `c12`).
-/

namespace NativeRustcVmX64.Field.EWMul

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.EWMul

@[expose] public section

/-- `EW::mul` of the argument registers over the variables, Karatsuba as `field.rs`. -/
def ewMulS : Sym × Sym :=
  let p0l := clmulLowS (.reg .rdi) (.reg .rdx)
  let p0h := shrS (.var 3) 1
  let p1l := clmulLowS (.reg .rsi) (.reg .rcx)
  let p1h := shrS (revS (.var 6)) 1
  let ml := clmulLowS (xorS (.reg .rdi) (.reg .rsi)) (xorS (.reg .rdx) (.reg .rcx))
  let mh := shrS (revS (.var 9)) 1
  let ml' := xorS (xorS ml p0l) p1l
  let mh' := xorS (xorS mh p0h) p1h
  let sl := shlS p1l 1
  let sh := orS (shlS p1h 1) (shrS p1l 63)
  (reduceS (xorS p0l p1l) (xorS p0h p1h), reduceS (xorS ml' sl) (xorS mh' sh))

end

set_option Elab.async false

sym_part r1 := exec (slice b0 0 125) (frameS 144)
sym_part r2 := exec (slice b0 125 16) (r1.out.setReg .r11 (some (.var 0)))
sym_part r3 := exec (slice b0 141 66) (r2.out.setReg .rdx (some (.var 1)))
sym_part r4 := exec (slice b0 207 20) (r3.out.setReg .rax (some (.var 2)))
sym_part r5 := exec (slice b0 227 95) (r4.out.setReg .rax (some (.var 3)))
sym_part r6 := exec (slice b0 322 18) (r5.out.setReg .rsi (some (.var 4)))
sym_part r7 := exec (slice b0 340 68) (r6.out.setReg .rax (some (.var 5)))
sym_part r8 := exec (slice b0 408 107) (r7.out.setReg .rcx (some (.var 6)))
sym_part r9 := exec (slice b0 515 16) (r8.out.setReg .r11 (some (.var 7)))
sym_part r10 := exec (slice b0 531 67) (r9.out.setReg .r10 (some (.var 8)))
sym_part r11 := exec (slice b0 598 81) (r10.out.setReg .r8 (some (.var 9)))

public theorem c1 : (r1.out.reg .r11).map (fun v ↦ Lin.checkRev 64 v (.reg .rdi)) = some true := by
  decide +kernel

public theorem c2 : (r2.out.reg .rdx).map (fun v ↦ Lin.checkRev 64 v (.reg .rdx)) = some true := by
  decide +kernel

public theorem c3 : (r3.out.reg .rax).map
    (fun v ↦ Lin.check 64 v (clmulLowS (.var 0) (.var 1))) = some true := by
  decide +kernel

public theorem c4 : (r4.out.reg .rax).map (fun v ↦ Lin.checkRev 64 v (.var 2)) = some true := by
  decide +kernel

public theorem c5 : (r5.out.reg .rsi).map (fun v ↦ Lin.checkRev 64 v (.reg .rsi)) = some true := by
  decide +kernel

public theorem c6 : (r6.out.reg .rax).map (fun v ↦ Lin.checkRev 64 v (.reg .rcx)) = some true := by
  decide +kernel

public theorem c7 : (r7.out.reg .rcx).map
    (fun v ↦ Lin.check 64 v (clmulLowS (.var 4) (.var 5))) = some true := by
  decide +kernel

public theorem c8 : (r8.out.reg .r11).map
    (fun v ↦ Lin.checkRev 64 v (xorS (.reg .rdi) (.reg .rsi))) = some true := by
  decide +kernel

public theorem c9 : (r9.out.reg .r10).map
    (fun v ↦ Lin.checkRev 64 v (xorS (.reg .rdx) (.reg .rcx))) = some true := by
  decide +kernel

public theorem c10 : (r10.out.reg .r8).map
    (fun v ↦ Lin.check 64 v (clmulLowS (.var 7) (.var 8))) = some true := by
  decide +kernel

public theorem c11 : (r11.out.reg .rax).map (fun v ↦ Lin.check 64 v ewMulS.1) = some true := by
  decide +kernel

public theorem c12 : (r11.out.reg .rdx).map (fun v ↦ Lin.check 64 v ewMulS.2) = some true := by
  decide +kernel

public theorem exits : r1.exit = .fall ∧ r2.exit = .fall ∧ r3.exit = .fall ∧ r4.exit = .fall ∧
    r5.exit = .fall ∧ r6.exit = .fall ∧ r7.exit = .fall ∧ r8.exit = .fall ∧ r9.exit = .fall ∧
    r10.exit = .fall ∧ r11.exit = .ret (.load 0 144 8) := by
  decide +kernel

public theorem lens : (slice b0 0 125).length = 125 ∧ (slice b0 125 16).length = 16 ∧
    (slice b0 141 66).length = 66 ∧ (slice b0 207 20).length = 20 ∧
    (slice b0 227 95).length = 95 ∧ (slice b0 322 18).length = 18 ∧
    (slice b0 340 68).length = 68 ∧ (slice b0 408 107).length = 107 ∧
    (slice b0 515 16).length = 16 ∧ (slice b0 531 67).length = 67 ∧ 598 ≤ b0.length := by
  decide +kernel

public theorem r11_rsp : r11.out.reg .rsp = some (.ptr 0 ((144 + 8 : Nat) : Int)) := by
  decide +kernel

public theorem r11_keeps : keeps (frameS 144) r11.out = true := by decide +kernel

public theorem r11_mem : ∀ w ∈ r11.out.mem, w.r = 0 ∧ w.off + w.n ≤ 144 := by decide +kernel

end NativeRustcVmX64.Field.EWMul
