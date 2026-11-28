module

public import Statement.Field

/-!
# Verifier arithmetic (`crates/verifier/src/field.rs`, `crates/verifier/src/multilinear.rs`)

A function that transcribes a Rust function has its name in `lowerCamelCase` and computes the same
value on the inputs the verifier gives it; the products and sums are taken in the Rust's order
where it is visible (`foldl` from `1` or `0`), although `E` is a field and neither the order nor
the grouping changes a value. The Rust's `E::new(n, 0)` for an integer `n < 2^64` is
`eOfNat n`: the natural-number cast of `E` is the characteristic-two one (`(2 : E) = 0`) and is
never used for a wire integer. A `K` value that the Rust lifts into `E` (`E::from`,
`field.rs`) is `ofK`.

**Preconditions the Rust checks and the verifier always meets.** `multilinear_eval` rejects a
table not of `2^|point|` entries, and `eq_eval` and `dot` assert equal lengths. At every call site
of the verifier the lengths agree by construction (the table sizes are `2^k` for the `k`
coordinates the caller passes), so these functions are total here: an excess entry is ignored, as
`zip` ignores it.
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics

/-- The integer value of a `K` word (the Rust's `K.0`). -/
def kToNat (a : K) : ℕ := a.toBitVec.toNat

/-- The two limbs of `e` as one 128-bit integer, limb `0` lowest: the bits `sample_queries`
reads (`whir.rs`). -/
def eToNat (e : E) : ℕ :=
  kToNat (e.limb 0) + 2 ^ 64 * kToNat (e.limb 1)

/-- `gpow(index) = GEN.pow(index)` (`layout.rs`): `Parameters.addressOfIndex index`, the
same power in `K`, in limb `0`. -/
def gpow (index : ℕ) : E := gen ^ index

/-- `E::sum(values)`: the sum from `ZERO`, left to right (`field.rs`). -/
def sumE (values : List E) : E := values.foldl (· + ·) 0

/-- The product from `ONE`, left to right (`product`, `crates/verifier/src/link.rs`). -/
def prodE (values : List E) : E := values.foldl (· * ·) 1

/-- `acc, acc·base, acc·base², …`, `count` terms. -/
def powersFrom (acc base : E) : ℕ → List E
  | 0 => []
  | count + 1 => acc :: powersFrom (acc * base) base count

/-- `powers(base, count)`: `1, base, base², …`, `count` terms (`field.rs`). -/
def powers (base : E) (count : ℕ) : List E := powersFrom 1 base count

/-- `eq_kernel(point)`: the `2^|point|` equality weights, the first coordinate the lowest bit
(`multilinear.rs`). -/
def eqKernel (point : List E) : List E :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) [1]

/-- One fold of `multilinear_eval`: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairs (r : E) : List E → List E
  | a :: b :: rest => (a * (1 + r) + b * r) :: foldPairs r rest
  | _ => []

/-- `multilinear_eval(mle, point)`: the multilinear extension of the table at the point, the
first coordinate folding adjacent entries (`multilinear.rs`). A table of the wrong size,
which the Rust rejects, never reaches it (see the section note); `0` for an empty result. -/
def multilinearEval (mle point : List E) : E :=
  (point.foldl (fun cur r ↦ foldPairs r cur) mle).headD 0

/-- The bit length of a natural number, `0` at `0`. -/
def bitLength (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

/-- `log2_ceil(value)`: the bit length of `value - 1`, saturating (`multilinear.rs`); `0`
at `value = 0`, the height of a table with no row. -/
def log2Ceil (value : ℕ) : ℕ := bitLength (value - 1)

/-- `log2_strict(value)`: the exponent of a power of two, `none` otherwise
(`multilinear.rs`). -/
def log2Strict (value : ℕ) : Option ℕ :=
  if 0 < value ∧ value &&& (value - 1) = 0 then some (bitLength value - 1) else none

/-- `eq_eval(left, right) = Π (1 + x + y)` (`multilinear.rs`). -/
def eqEval (left right : List E) : E :=
  (List.zipWith (fun x z ↦ 1 + x + z) left right).foldl (· * ·) 1

/-- `dot(left, right) = Σ x·y` (`multilinear.rs`). -/
def dot (left right : List E) : E :=
  (List.zipWith (· * ·) left right).foldl (· + ·) 0

/-- `padding_weight(point, n)`: `pad_n(point)`, the multilinear extension of `[z ≥ n]` for
`n ≤ 2^|point|`, unrolled from the low bit (`multilinear.rs`; `doc/leanvm`, Lemma
`lem:suffix`). -/
def paddingWeight (point : List E) (n : ℕ) : E :=
  (1 + eOfNat ((n >>> point.length) % 2)) *
    point.zipIdx.foldl (fun pad (r, k) ↦
      let b := eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) 1

/-- `index_mle(point)`: the multilinear extension of `[1, g, g², …]` at an LSB-first point,
`Π (1 + r_i·(1 + g^(2^i)))` (`multilinear.rs`). -/
def indexMleFrom (generatorPower : E) : List E → E → E
  | [], acc => acc
  | r :: rs, acc => indexMleFrom (generatorPower ^ 2) rs (acc * (1 + r * (1 + generatorPower)))

/-- `index_mle(point)` (`multilinear.rs`). -/
def indexMle (point : List E) : E := indexMleFrom gen point 1

/-- `poly_eval(coefficients, point)`: Horner's rule over the coefficients, constant first
(`multilinear.rs`). -/
def polyEval (coefficients : List E) (point : E) : E :=
  coefficients.foldr (fun c acc ↦ acc * point + c) 0

/-- `selector_point(selector, length)`: the low `length` bits of `selector` as `0/1` elements,
lowest first (`multilinear.rs`). -/
def selectorPoint (selector length : ℕ) : List E :=
  (List.range length).map fun bit ↦ eOfNat ((selector >>> bit) % 2)

end LeanVM.Protocol.Verifier

end
