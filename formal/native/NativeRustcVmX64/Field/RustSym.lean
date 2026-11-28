module

public import NativeRustcVmX64.Field.LinSound
public import NativeRustcVm.Field.Rust

/-!
# `field.rs`'s products as symbolic values (x86-64)

`Field.clmulLow` and `reduce` (`NativeRustcVm.Field.Rust`) built as symbolic values of their
arguments (`clmulLowS`, `reduceS`), and a bit reversal as x86 code computes one (`revS`), each
evaluating to the transcription of the arguments' values (`eval_clmulLowS`, `eval_reduceS`,
`eval_revS`), for `Lin.check` to compare with rustc's.
-/

namespace NativeRustcVmX64.Field

open NativeRustcX64 NativeRustcX64.Sym Lin

@[expose] public section

def andS (a : Sym) (n : Nat) : Sym := .bin .and .W64 a (.lit n)
def xorS (a b : Sym) : Sym := .bin .xor .W64 a b
def orS (a b : Sym) : Sym := .bin .or .W64 a b
def mulS (a b : Sym) : Sym := .bin .mul .W64 a b
def shlS (a : Sym) (k : Nat) : Sym := .bin .shl .W64 a (.lit k)
def shrS (a : Sym) (k : Nat) : Sym := .bin .shr .W64 a (.lit k)

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

/-- A bit reversal, as x86 code computes one: `bswap`, then the nibbles, pairs and bits of each
byte swapped. -/
def revS (a : Sym) : Sym :=
  let x := Sym.un .bswap .W64 a
  let y := orS (shlS (andS x 0x0F0F0F0F0F0F0F0F) 4) (andS (shrS x 4) 0x0F0F0F0F0F0F0F0F)
  let z := orS (shlS (andS y 0x3333333333333333) 2) (andS (shrS y 2) 0x3333333333333333)
  orS (shlS (andS z 0x5555555555555555) 1) (andS (shrS z 1) 0x5555555555555555)

/-- `reduce`. -/
def reduceS (lo hi : Sym) : Sym :=
  let spill := xorS (xorS (shrS hi 63) (shrS hi 61)) (shrS hi 60)
  let v := xorS hi spill
  xorS (xorS (xorS (xorS lo v) (shlS v 1)) (shlS v 3)) (shlS v 4)

end

public section

/-- `revS` reverses: checked on a variable. -/
theorem checkRev_revS : Lin.checkRev 64 (revS (.var 0)) (.var 0) = true := by decide +kernel

variable [Labels] (env : Env)

theorem eval_revS (a : Sym) : (revS a).eval env = (a.eval env).reverse :=
  Lin.eval_eq_of_checkRev checkRev_revS { env with vars := fun _ ↦ a.eval env }

theorem eval_clmulLowS (a b : Sym) :
    (clmulLowS a b).eval env = NativeRustcVm.Field.clmulLow (a.eval env) (b.eval env) := by
  simp only [clmulLowS, andS, xorS, orS, mulS, Sym.eval, and_apply, xor_apply, or_apply,
    mul_apply, NativeRustcVm.Field.clmulLow]

theorem eval_shlS (a : Sym) {k : Nat} (hk : k < 64) : (shlS a k).eval env = a.eval env <<< k :=
  shl_apply _ hk

theorem eval_shrS (a : Sym) {k : Nat} (hk : k < 64) : (shrS a k).eval env = a.eval env >>> k :=
  shr_apply _ hk

theorem eval_reduceS (lo hi : Sym) :
    (reduceS lo hi).eval env = NativeRustcVm.Field.reduce (lo.eval env) (hi.eval env) := by
  simp only [reduceS, xorS, Sym.eval, xor_apply, eval_shlS env _ (show 1 < 64 by decide),
    eval_shlS env _ (show 3 < 64 by decide), eval_shlS env _ (show 4 < 64 by decide),
    eval_shrS env _ (show 63 < 64 by decide), eval_shrS env _ (show 61 < 64 by decide),
    eval_shrS env _ (show 60 < 64 by decide), NativeRustcVm.Field.reduce]

end

end NativeRustcVmX64.Field
