module

public import Statement.Keccak
public import CompPoly.Fields.Binary.BF64
public import CompPoly.Fields.Extension
public import Statement.Fast.FieldWords
public import Statement.Fast.QuadExt
public import Statement.Fast.Keccak
public import Statement.Lemmas.FieldModulus

/-!
# The fields

`K = GF(2^64)`, `E = GF(2^128)` and the generator `g` of leanVM (specification §2,
`doc/leanvm/body/02-vm-specification.tex`), on CompPoly's computable carriers:

```text
K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)      CompPoly's BF64
E = K[y]/(y^2 + x·y + 1)                     CompPoly's extension framework, `eParams`
g = x                                        a generator of K^× (order 2^64 - 1)
```

`K` wraps a `BitVec 64` whose bit `i` is the coefficient of `x^i`; `E` is a `Vector K 2` whose
limb `i` is the coefficient of `y^i`. Natural-number casts follow characteristic two
(`2 : K = 0`); wire words go through `K.ofBits`. Then the field encodings of Keccak
(`crates/verifier/src/field.rs` and `hash.rs`): a lane as a `K` word, a
`K` word as bytes, and a digest as two `E` elements.

`E`'s field instance needs its modulus irreducible (`ePoly_irreducible`), proved in
`Statement/Lemmas/FieldModulus.lean`.
-/

@[expose] public section

namespace LeanVM.Parameters

open CompPoly.Extension Polynomial

/-- `K = GF(2^64)`, CompPoly's `BF64`. -/
abbrev K : Type := BF64

/-- Decode a polynomial-basis word, reducing its integer representation modulo `2^64`.
This is a wire encoding, distinct from the characteristic-two natural-number cast. -/
def K.ofBits (n : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 n)

/-- Decide equality through bit coordinates, keeping kernel comparisons of computed words
free of the dependent transport introduced by the upstream derived instance. -/
instance instDecidableEqK : DecidableEq K := fun a b ↦
  decidable_of_iff (a.toBitVec = b.toBitVec) BF64.toBitVec_injective.eq_iff

/-- `g = x`, the word `0x2` (`crates/primitives/src/field/gf2_64.rs`, `F64::G = F64(2)`;
`crates/verifier/src/field.rs`, `GEN = E::new(2, 0)`). Its order `2^64 - 1` is proved
(`orderOf_g`), not assumed. -/
def g : K := K.ofBits 0x2

/-! ## `E`'s modulus -/

/-- The modulus `y^2 + x·y + 1` of `E` over `K`. -/
noncomputable def ePoly : Polynomial K := X ^ 2 + C g * X + 1

/-- Parameters of `K[y]/(y^2 + x·y + 1)`: degree two, the lower coefficients `(1, x)`. -/
def eParams : ExtensionParams K where
  d := 2
  two_le := le_rfl
  lower := #v[1, g]
  q := 2 ^ 64

instance : Fact (Nat.card K = eParams.q) := ⟨BF64.nat_card_bf64⟩

/-- The parameters' defining polynomial is `y^2 + x·y + 1`. -/
theorem eParams_poly : eParams.poly = ePoly := by
  have h0 : eParams.lowerCoeff ⟨0, by decide⟩ = 1 := rfl
  have h1 : eParams.lowerCoeff ⟨1, by decide⟩ = g := rfl
  rw [ExtensionParams.poly, ePoly]
  show X ^ 2 + (∑ i : Fin 2, C (eParams.lowerCoeff i) * X ^ (i : ℕ)) = X ^ 2 + C g * X + 1
  rw [Fin.sum_univ_two, show eParams.lowerCoeff (0 : Fin 2) = 1 from h0,
    show eParams.lowerCoeff (1 : Fin 2) = g from h1]
  simp only [map_one, pow_zero, Fin.val_zero, Fin.val_one, pow_one, one_mul]
  ring

/-- `y^2 + x·y + 1` is irreducible over `K`. -/
theorem ePoly_irreducible : Irreducible ePoly := FieldModulus.irreducible

instance : Fact (Irreducible eParams.poly) := ⟨eParams_poly ▸ ePoly_irreducible⟩

/-! ## `E` and its limbs -/

/-- `E = K[y]/(y^2 + x·y + 1)`. -/
abbrev E : Type := Ext eParams

/-- The embedding `K ↪ E` as the `y^0` limb; it is `algebraMap K E` by `rfl`. -/
abbrev ofK (a : K) : E := Ext.ofBase a

/-- Limb `i` of a word: the coefficient of `y^i`. -/
abbrev E.limb (x : E) (i : Fin 2) : K := Ext.coeff x i

/-- The word `c0 + c1·y`. -/
def E.ofLimbs (c0 c1 : K) : E := Ext.ofVector #v[c0, c1]

/-- A word lies in `K`: its `y` limb is zero. -/
def IsInK (x : E) : Prop := x.limb 1 = 0

instance : DecidablePred IsInK :=
  fun x ↦ inferInstanceAs (Decidable (x.limb 1 = 0))

/-- Exponent addressing: index `i` is the address `g ^ i`. -/
abbrev addressOfIndex (i : ℕ) : K := g ^ i

/-- A `K` word from a 64-bit lane: bit `i` of the lane is the coefficient of `x^i`. -/
def K.ofLane (w : UInt64) : K := BF64.ofBitVec w.toBitVec

/-- The 64-bit lane of a `K` word (`K`'s word, `field.rs`). -/
def K.lane (a : K) : UInt64 := ⟨a.toBitVec⟩

end LeanVM.Parameters

namespace LeanVM.Protocol.KeccakHash

open LeanVM.Parameters LeanVM.Semantics

/-- The eight little-endian bytes of a `K` word (`K::to_bytes`, `field.rs`). -/
def _root_.LeanVM.Parameters.K.toBytes (a : K) : List UInt8 := wordBytes a.lane

/-- The 16 bytes of an `E` word: its two limbs' bytes, `y^0` first. -/
def _root_.LeanVM.Parameters.E.toBytes (x : E) : List UInt8 :=
  K.toBytes (x.limb 0) ++ K.toBytes (x.limb 1)

/-- A digest as the two field elements a transcript carries it in, its 128-bit halves
`E(w0, w1)`, `E(w2, w3)` (`Digest::halves`, `hash.rs`). -/
def digestHalves (digest : Digest) : E × E :=
  (E.ofLimbs (K.ofLane digest[0]) (K.ofLane digest[1]),
    E.ofLimbs (K.ofLane digest[2]) (K.ofLane digest[3]))

/-- The digest two field elements encode (`Digest::from_halves`, `hash.rs`). -/
def digestFromHalves (halves : E × E) : Digest :=
  #v[(halves.1.limb 0).lane, (halves.1.limb 1).lane, (halves.2.limb 0).lane,
    (halves.2.limb 1).lane]

end LeanVM.Protocol.KeccakHash

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

/-- `E::new(n, 0)`: the 64-bit word `n` in limb `0` (`field.rs`). -/
def eOfNat (n : ℕ) : E := ofK (K.ofBits n)

/-- `GEN = E::new(2, 0)`, the generator `x` whose powers index the bytecode and the memory
(`field.rs`): `g` in limb `0`. -/
def gen : E := eOfNat 2

end LeanVM.Protocol.Verifier

end
