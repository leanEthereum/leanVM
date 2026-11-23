module

public import Statement.Field

/-!
# The model's field arithmetic

`K` and `E` on machine words, as the native code computes them: a `K` element is its lane
(`K.ofLane`, `K.lane`), an `E` element its two limb lanes (`EW`, `EW.toE`). `kmul` is CompPoly's
word-level loop (`BF64.mulShift`, which `BF64.mul_eq_mulShift` proves to be the product), `mulX`
the product by `g = x`, `kpow` square-and-multiply, `kinv` the power `2^64 - 2` (`0 ↦ 0`, as `K`'s
inverse). `E`'s sum is the limbs' `xor`, its product folds `y² = x·y + 1`.

`EW`'s boolean equality is lawful at the model boundary, independently of field equivalence.

The next wave proves each operation is its field operation through `EW.toE`
(`(a * b).toE = a.toE * b.toE`, `K.ofLane (kmul a b) = K.ofLane a * K.ofLane b`).
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters

/-! ## `K` on lanes -/

/-- `t · x` in `K`: shift left, and fold the bit shifted out by `x^64 = x^4 + x^3 + x + 1`. -/
def mulX (t : UInt64) : UInt64 := (t <<< 1) ^^^ (((0 : UInt64) - (t >>> 63)) &&& 0x1B)

/-- The product in `K`, CompPoly's loop over the bits of `a` (`BF64.mulShift`). -/
def kmul (a b : UInt64) : UInt64 := BF64.mulShift a 0 b 0 0

/-- The loop of `kpow`: `acc · base^n`, `fuel` bounding the bits of `n`. -/
def kpowAux : (fuel : Nat) → (base acc : UInt64) → (n : Nat) → UInt64
  | 0, _, acc, _ => acc
  | fuel + 1, base, acc, n =>
    if n = 0 then acc
    else kpowAux fuel (kmul base base) (if n % 2 = 1 then kmul acc base else acc) (n / 2)

/-- `a^n` in `K`, by square-and-multiply from the low bit. -/
def kpow (a : UInt64) (n : Nat) : UInt64 := kpowAux (n.log2 + 1) a 1 n

/-- `a⁻¹` in `K` as `a^(2^64 - 2)`, `0` at `0`. -/
def kinv (a : UInt64) : UInt64 := kpow a (2 ^ 64 - 2)

/-- `g^n` as a lane. -/
def gpowK (n : Nat) : UInt64 := kpow 2 n

/-! ## `E` on pairs of lanes -/

/-- An `E` element as its two limb lanes, limb `0` first. -/
structure EW where
  c0 : UInt64
  c1 : UInt64
  deriving Inhabited, BEq, DecidableEq, Repr

instance : LawfulBEq EW where
  eq_of_beq {a b} h := by
    rcases a with ⟨a0, a1⟩
    rcases b with ⟨b0, b1⟩
    simp_all [BEq.beq, instBEqEW.beq]
  rfl {a} := by
    rcases a with ⟨a0, a1⟩
    simp [BEq.beq, instBEqEW.beq]

namespace EW

/-- The element the lanes encode. -/
def toE (x : EW) : E := E.ofLimbs (K.ofLane x.c0) (K.ofLane x.c1)

/-- The lanes of an element. -/
def ofE (x : E) : EW := ⟨(x.limb 0).lane, (x.limb 1).lane⟩

/-- A `K` lane in limb `0`. -/
def ofK (a : UInt64) : EW := ⟨a, 0⟩

/-- `E::new(n, 0)`: the word `n` in limb `0` (`eOfNat`). -/
def ofNat (n : Nat) : EW := ⟨n.toUInt64, 0⟩

instance : OfNat EW 0 := ⟨⟨0, 0⟩⟩
instance : OfNat EW 1 := ⟨⟨1, 0⟩⟩

/-- The sum: the limbs' `xor`. -/
def add (a b : EW) : EW := ⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1⟩

/-- The product, `y² = x·y + 1`. -/
def mul (a b : EW) : EW :=
  let c2 := kmul a.c1 b.c1
  ⟨kmul a.c0 b.c0 ^^^ c2, kmul a.c0 b.c1 ^^^ kmul a.c1 b.c0 ^^^ mulX c2⟩

instance : Add EW := ⟨add⟩
instance : Mul EW := ⟨mul⟩

/-- The product by a `K` lane, limb by limb. -/
def scale (k : UInt64) (x : EW) : EW := ⟨kmul k x.c0, kmul k x.c1⟩

/-- `x^(2^k)`: `k` squarings. -/
def sqIter : Nat → EW → EW
  | 0, x => x
  | k + 1, x => sqIter k (x * x)

end EW

/-- `GEN`, `g` in limb `0`. -/
def gen : EW := ⟨2, 0⟩

/-- `gpow(index)`: `g^index` in limb `0`. -/
def gpow (index : Nat) : EW := EW.ofK (gpowK index)

/-! ## Arrays of `E` (`multilinear.rs`, `field.rs`)

Each is the function of the same name in `Statement/LeanVmVerifier.lean` on arrays, in its loop
order. -/

/-- `sumE`. -/
def sumE (values : Array EW) : EW := values.foldl (· + ·) 0

/-- `prodE`. -/
def prodE (values : Array EW) : EW := values.foldl (· * ·) 1

/-- `powers`: `1, base, base², …`, `count` terms. -/
def powers (base : EW) (count : Nat) : Array EW :=
  ((List.range count).foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * base))
    (#[], 1)).1

/-- `eqKernel`: the `2^|point|` equality weights, the first coordinate the lowest bit. -/
def eqKernel (point : Array EW) : Array EW :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) #[1]

/-- `foldPairs`: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairs (r : EW) (cur : Array EW) : Array EW :=
  (Array.range (cur.size / 2)).map fun i ↦ cur[2 * i]! * (1 + r) + cur[2 * i + 1]! * r

/-- `multilinearEval`. -/
def multilinearEval (mle point : Array EW) : EW :=
  (point.foldl (fun cur r ↦ foldPairs r cur) mle).getD 0 0

/-- `eqEval`: `Π (1 + x + y)` over the common length. -/
def eqEval (left right : Array EW) : EW :=
  (Array.zipWith (fun x z ↦ 1 + x + z) left right).foldl (· * ·) 1

/-- `dot`: `Σ x·y` over the common length. -/
def dot (left right : Array EW) : EW :=
  (Array.zipWith (· * ·) left right).foldl (· + ·) 0

/-- `paddingWeight`: the multilinear extension of `[z ≥ n]`, from the low bit. -/
def paddingWeight (point : Array EW) (n : Nat) : EW :=
  (1 + EW.ofNat ((n >>> point.size) % 2)) *
    (point.zipIdx.foldl (fun pad (r, k) ↦
      let b := EW.ofNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) 1)

/-- The loop of `indexMle`. -/
def indexMleFrom (generatorPower : EW) (point : Array EW) : EW :=
  (point.foldl (fun (acc : EW × EW) r ↦ (acc.1 * (1 + r * (1 + acc.2)), acc.2 * acc.2))
    (1, generatorPower)).1

/-- `indexMle`: `Π (1 + r_i·(1 + g^(2^i)))`. -/
def indexMle (point : Array EW) : EW := indexMleFrom gen point

/-- `polyEval`: Horner's rule, constant first. -/
def polyEval (coefficients : Array EW) (point : EW) : EW :=
  coefficients.foldr (fun c acc ↦ acc * point + c) 0

/-- `selectorPoint`: the low `length` bits of `selector`, lowest first. -/
def selectorPoint (selector length : Nat) : Array EW :=
  (Array.range length).map fun bit ↦ EW.ofNat ((selector >>> bit) % 2)

end NativeVm.Model
