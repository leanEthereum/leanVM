module

/-!
# `field.rs`, transcribed

The word arithmetic of `rustc/vm/src/field.rs` on `BitVec 64`, line by line, as the symbolic
executor meets it (`&&&`, `*`, `^^^`, `|||`, shifts, `BitVec.reverse` for `rbit`): the carry-less
product by integer multiplication of the four classes of bit positions mod 4 (`clmulLow`), its
high word by bit reversal (`clmul`), the reduction by `x^64 = x^4 + x^3 + x + 1` (`reduce`), the
product in `K` (`kmul`), in `E` by Karatsuba (`ewMul`), the power (`kpow`, `kpowLoop`), the
Itoh-Tsujii inverse (`sq`, `kinv`), and `bit_length`'s halving loop as rustc unrolls it
(`bitLengthStep`, `bitLength`), with its uses `log2_ceil`, `grinding_bits`, `log2_strict`.

Each is the model's (`NativeVm.Model`): `kmul_eq` (`NativeRustcVm.Field.Clmul`), `ewMul_eq`
(`…EW`), `kpow_eq`, `kinv_eq` (`…Pow`), `bitLength_eq`, `log2Ceil_eq`, `grindingBits_eq`,
`log2Strict_eq` (`…BitLength`).
-/

namespace NativeRustcVm.Field

@[expose] public section

/-- `clmul_low`: the low 64 bits of the carry-less product of `a` and `b`. -/
def clmulLow (a b : BitVec 64) : BitVec 64 :=
  let x0 := a &&& 0x1111111111111111#64
  let x1 := a &&& 0x2222222222222222#64
  let x2 := a &&& 0x4444444444444444#64
  let x3 := a &&& 0x8888888888888888#64
  let y0 := b &&& 0x1111111111111111#64
  let y1 := b &&& 0x2222222222222222#64
  let y2 := b &&& 0x4444444444444444#64
  let y3 := b &&& 0x8888888888888888#64
  let z0 := x0 * y0 ^^^ x1 * y3 ^^^ x2 * y2 ^^^ x3 * y1
  let z1 := x0 * y1 ^^^ x1 * y0 ^^^ x2 * y3 ^^^ x3 * y2
  let z2 := x0 * y2 ^^^ x1 * y1 ^^^ x2 * y0 ^^^ x3 * y3
  let z3 := x0 * y3 ^^^ x1 * y2 ^^^ x2 * y1 ^^^ x3 * y0
  z0 &&& 0x1111111111111111#64 ||| z1 &&& 0x2222222222222222#64 |||
    z2 &&& 0x4444444444444444#64 ||| z3 &&& 0x8888888888888888#64

/-- `clmul`: the carry-less product's low and high words. -/
def clmul (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let low := clmulLow a b
  let high := (clmulLow a.reverse b.reverse).reverse >>> 1
  (low, high)

/-- `reduce`: the 128-bit `hi·x^64 + lo` modulo `x^64 + x^4 + x^3 + x + 1`. -/
def reduce (lo hi : BitVec 64) : BitVec 64 :=
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

/-- `kmul`: the product in `K`. -/
def kmul (a b : BitVec 64) : BitVec 64 :=
  let p := clmul a b
  reduce p.1 p.2

/-- `ksquare`. -/
def ksquare (a : BitVec 64) : BitVec 64 := kmul a a

/-- `EW::mul`: the product in `E` (`y² = x·y + 1`), Karatsuba over the carry-less products;
`self = (a0, a1)`, `b = (b0, b1)`, the result's limbs `(c0, c1)`. -/
def ewMul (a0 a1 b0 b1 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p0 := clmul a0 b0
  let p1 := clmul a1 b1
  let m := clmul (a0 ^^^ a1) (b0 ^^^ b1)
  let ml := m.1 ^^^ p0.1 ^^^ p1.1
  let mh := m.2 ^^^ p0.2 ^^^ p1.2
  let sl := p1.1 <<< 1
  let sh := (p1.2 <<< 1) ||| (p1.1 >>> 63)
  (reduce (p0.1 ^^^ p1.1) (p0.2 ^^^ p1.2), reduce (ml ^^^ sl) (mh ^^^ sh))

/-- `kpow`'s loop: `while n != 0 { if n & 1 == 1 { acc = kmul(acc, base) } base = kmul(base,
base); n >>= 1 }`, then `acc`. -/
def kpowLoop (base acc n : BitVec 64) : BitVec 64 :=
  if _h : n = 0 then acc
  else kpowLoop (kmul base base) (if n &&& 1#64 = 1#64 then kmul acc base else acc) (n >>> 1)
termination_by n.toNat
decreasing_by
  have : n.toNat ≠ 0 := fun h0 ↦ _h (BitVec.eq_of_toNat_eq (by simpa using h0))
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  omega

/-- `kpow`: `a^n` in `K`, square-and-multiply from the low bit. -/
def kpow (a n : BitVec 64) : BitVec 64 := kpowLoop a 1#64 n

/-- `kinv`'s `sq`: `n` squarings, `while i < n { v = ksquare(v); i += 1 }`. -/
def sq (v : BitVec 64) : Nat → BitVec 64
  | 0 => v
  | n + 1 => sq (ksquare v) n

/-- `kinv`: `a^(2^64 - 2)` by Itoh-Tsujii, `t_k = a^(2^k - 1)`. -/
def kinv (a : BitVec 64) : BitVec 64 :=
  let t1 := a
  let t2 := kmul (sq t1 1) t1
  let t3 := kmul (sq t2 1) t1
  let t6 := kmul (sq t3 3) t3
  let t12 := kmul (sq t6 6) t6
  let t24 := kmul (sq t12 12) t12
  let t48 := kmul (sq t24 24) t24
  let t60 := kmul (sq t48 12) t12
  let t63 := kmul (sq t60 3) t3
  sq t63 1

/-- One step of `bit_length`'s loop at shift `s`, on `(n, v)`: `if v >> s != 0 { n += s; v >>= s }`. -/
def bitLengthStep (s : Nat) (p : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  if p.2 >>> s ≠ 0 then (p.1 + BitVec.ofNat 64 s, p.2 >>> s) else p

/-- `bit_length`: the loop over `s = 32, 16, 8, 4, 2, 1` (unrolled by rustc), then
`n + (v != 0) as usize`. -/
def bitLength (v : BitVec 64) : BitVec 64 :=
  let p := bitLengthStep 1 (bitLengthStep 2 (bitLengthStep 4 (bitLengthStep 8
    (bitLengthStep 16 (bitLengthStep 32 (0#64, v))))))
  p.1 + if p.2 ≠ 0 then 1#64 else 0#64

/-- `u64::saturating_sub`. -/
def satSub (a b : BitVec 64) : BitVec 64 := if b ≤ a then a - b else 0#64

/-- `log2_ceil` (`layout.rs`): `bit_length(value.saturating_sub(1))`. -/
def log2Ceil (value : BitVec 64) : BitVec 64 := bitLength (satSub value 1#64)

/-- `grinding_bits` (`transcript.rs`): `bit_length(numerator.saturating_sub(1)).saturating_sub(3)`
(the `u32` is below `65`, kept in a word). -/
def grindingBits (numerator : BitVec 64) : BitVec 64 :=
  satSub (bitLength (satSub numerator 1#64)) 3#64

/-- `log2_strict` (`layout.rs`). -/
def log2Strict (value : BitVec 64) : Option (BitVec 64) :=
  if value ≠ 0 ∧ value &&& (value - 1#64) = 0 then some (bitLength value - 1#64) else none

end

end NativeRustcVm.Field
