module

public import NativeRustcVmArm.Field.Norm

/-!
# `field.rs`'s products as symbolic values

`Field.clmulLow`, `clmul`, `reduce` and `ewMul` (`NativeRustcVm.Field.Rust`) built as symbolic
values of their arguments (`clmulLowS`, …), each evaluating to the transcription of the
arguments' values (`eval_clmulLowS`, …), for `Lin.check` to compare with rustc's.
-/

namespace NativeRustcVmArm.Field

open NativeRustcArm NativeRustcArm.Sym

@[expose] public section

def andS (a : Sym) (n : Nat) : Sym := .bin .and .W64 a (.lit n)
def xorS (a b : Sym) : Sym := .bin .eor .W64 a b
def orS (a b : Sym) : Sym := .bin .orr .W64 a b
def mulS (a b : Sym) : Sym := .bin .mul .W64 a b
def shlS (a : Sym) (k : Nat) : Sym := .un (.shift .LSL k) .W64 a
def shrS (a : Sym) (k : Nat) : Sym := .un (.shift .LSR k) .W64 a
def revS (a : Sym) : Sym := .un .rbit .W64 a

/-- `clmulLow`. -/
def clmulLowS (a b : Sym) : Sym :=
  let x0 := andS a 0x1111111111111111
  let x1 := andS a 0x2222222222222222
  let x2 := andS a 0x4444444444444444
  let x3 := andS a 0x8888888888888888
  let y0 := andS b 0x1111111111111111
  let y1 := andS b 0x2222222222222222
  let y2 := andS b 0x4444444444444444
  let y3 := andS b 0x8888888888888888
  let z0 := xorS (xorS (xorS (mulS x0 y0) (mulS x1 y3)) (mulS x2 y2)) (mulS x3 y1)
  let z1 := xorS (xorS (xorS (mulS x0 y1) (mulS x1 y0)) (mulS x2 y3)) (mulS x3 y2)
  let z2 := xorS (xorS (xorS (mulS x0 y2) (mulS x1 y1)) (mulS x2 y0)) (mulS x3 y3)
  let z3 := xorS (xorS (xorS (mulS x0 y3) (mulS x1 y2)) (mulS x2 y1)) (mulS x3 y0)
  orS (orS (orS (andS z0 0x1111111111111111) (andS z1 0x2222222222222222))
    (andS z2 0x4444444444444444)) (andS z3 0x8888888888888888)

/-- `clmul`. -/
def clmulS (a b : Sym) : Sym × Sym := (clmulLowS a b, shrS (revS (clmulLowS (revS a) (revS b))) 1)

/-- `reduce`. -/
def reduceS (lo hi : Sym) : Sym :=
  let spill := xorS (xorS (shrS hi 63) (shrS hi 61)) (shrS hi 60)
  let v := xorS hi spill
  xorS (xorS (xorS (xorS lo v) (shlS v 1)) (shlS v 3)) (shlS v 4)

/-- `ewMul`. -/
def ewMulS (a0 a1 b0 b1 : Sym) : Sym × Sym :=
  let p0 := clmulS a0 b0
  let p1 := clmulS a1 b1
  let m := clmulS (xorS a0 a1) (xorS b0 b1)
  let ml := xorS (xorS m.1 p0.1) p1.1
  let mh := xorS (xorS m.2 p0.2) p1.2
  let sl := shlS p1.1 1
  let sh := orS (shlS p1.2 1) (shrS p1.1 63)
  (reduceS (xorS p0.1 p1.1) (xorS p0.2 p1.2), reduceS (xorS ml sl) (xorS mh sh))

variable [Labels] (env : Env)

theorem eval_clmulLowS (a b : Sym) :
    (clmulLowS a b).eval env = NativeRustcVm.Field.clmulLow (a.eval env) (b.eval env) := by
  simp only [clmulLowS, andS, xorS, orS, mulS, Sym.eval, and_apply, eor_apply, orr_apply,
    mul_apply, NativeRustcVm.Field.clmulLow]

theorem eval_clmulS_fst (a b : Sym) :
    (clmulS a b).1.eval env = (NativeRustcVm.Field.clmul (a.eval env) (b.eval env)).1 := by
  simp only [clmulS, eval_clmulLowS, NativeRustcVm.Field.clmul]

theorem eval_clmulS_snd (a b : Sym) :
    (clmulS a b).2.eval env = (NativeRustcVm.Field.clmul (a.eval env) (b.eval env)).2 := by
  simp only [clmulS, shrS, revS, Sym.eval, eval_clmulLowS, rbit_apply, lsr_apply,
    NativeRustcVm.Field.clmul]

theorem eval_reduceS (lo hi : Sym) :
    (reduceS lo hi).eval env = NativeRustcVm.Field.reduce (lo.eval env) (hi.eval env) := by
  simp only [reduceS, xorS, shlS, shrS, Sym.eval, eor_apply, lsl_apply, lsr_apply,
    NativeRustcVm.Field.reduce]

theorem eval_ewMulS (a0 a1 b0 b1 : Sym) :
    ((ewMulS a0 a1 b0 b1).1.eval env, (ewMulS a0 a1 b0 b1).2.eval env) =
      NativeRustcVm.Field.ewMul (a0.eval env) (a1.eval env) (b0.eval env) (b1.eval env) := by
  simp only [ewMulS, NativeRustcVm.Field.ewMul, eval_reduceS, xorS, orS, shlS, shrS, Sym.eval,
    eor_apply, orr_apply, lsl_apply, lsr_apply, eval_clmulS_fst, eval_clmulS_snd]

end

end NativeRustcVmArm.Field
