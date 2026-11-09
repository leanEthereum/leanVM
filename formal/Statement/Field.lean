module

public import Statement.Keccak
public import CompPoly.Fields.Binary.BF64
public import CompPoly.Fields.Extension
public import Statement.Fast.FieldWords
public import Statement.Fast.CubicExt
public import Statement.Fast.Keccak

/-!
# The fields

`K = GF(2^64)`, `E = GF(2^192)` and the generator `g` of leanVM (specification §2,
`doc/leanvm/body/02-vm-specification.tex:6-12`), on CompPoly's computable carriers:

```text
K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)      CompPoly's BF64
E = K[y]/(y^3 + y + 1)                       CompPoly's BF64.Ext3
g = x                                        a generator of K^× (order 2^64 - 1)
```

`K` wraps a `BitVec 64` whose bit `i` is the coefficient of `x^i`; `E` is a `Vector K 3` whose
limb `i` is the coefficient of `y^i`. Natural-number casts follow characteristic two
(`2 : K = 0`); wire words go through `K.ofBits`. Then the field encodings of Keccak
(`crates/verifier/src/field.rs` and `hash.rs`, read at `../leanvm-rev`): a lane as a `K` word, a
`K` word as bytes, and a digest as two `E` elements.
-/

@[expose] public section

namespace LeanVM.Parameters

open CompPoly.Extension

/-- `K = GF(2^64)`, CompPoly's `BF64`. -/
abbrev K : Type := BF64

/-- Decode a polynomial-basis word, reducing its integer representation modulo `2^64`.
This is a wire encoding, distinct from the characteristic-two natural-number cast. -/
def K.ofBits (n : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 n)

/-- Decide equality through bit coordinates, keeping kernel comparisons of computed words
free of the dependent transport introduced by the upstream derived instance. -/
instance instDecidableEqK : DecidableEq K := fun a b ↦
  decidable_of_iff (a.toBitVec = b.toBitVec) BF64.toBitVec_injective.eq_iff

/-- `E = K[y]/(y^3 + y + 1)`, CompPoly's `BF64.Ext3`. -/
abbrev E : Type := BF64.Ext3

/-- The embedding `K ↪ E` as the `y^0` limb; it is `algebraMap K E` by `rfl`. -/
abbrev ofK (a : K) : E := Ext.ofBase a

/-- Limb `i` of a word: the coefficient of `y^i`. -/
abbrev E.limb (x : E) (i : Fin 3) : K := Ext.coeff x i

/-- The word `c0 + c1·y + c2·y²`. -/
def E.ofLimbs (c0 c1 c2 : K) : E := Ext.ofVector #v[c0, c1, c2]

/-- A word lies in `K`: its `y` and `y²` limbs are zero. -/
def IsInK (x : E) : Prop := x.limb 1 = 0 ∧ x.limb 2 = 0

/-- A canonical 128-bit word: its `y²` limb is zero. -/
def IsCanonical128 (x : E) : Prop := x.limb 2 = 0

instance : DecidablePred IsInK :=
  fun x ↦ inferInstanceAs (Decidable (x.limb 1 = 0 ∧ x.limb 2 = 0))

instance : DecidablePred IsCanonical128 :=
  fun x ↦ inferInstanceAs (Decidable (x.limb 2 = 0))

/-- `g = x`, the word `0x2` (`crates/primitives/src/field/gf2_64.rs:26`, `F64::G = F64(2)`;
`crates/verifier/src/field.rs:114`, `GEN = E::new(2, 0, 0)`). Its order `2^64 - 1` is proved
(`orderOf_g`), not assumed. -/
def g : K := K.ofBits 0x2

/-- Exponent addressing: index `i` is the address `g ^ i`. -/
abbrev addressOfIndex (i : ℕ) : K := g ^ i

/-- A `K` word from a 64-bit lane: bit `i` of the lane is the coefficient of `x^i`. -/
def K.ofLane (w : UInt64) : K := BF64.ofBitVec w.toBitVec

/-- The 64-bit lane of a `K` word (`K`'s word, `field.rs:56`). -/
def K.lane (a : K) : UInt64 := ⟨a.toBitVec⟩

end LeanVM.Parameters

namespace LeanVM.Protocol.KeccakHash

open LeanVM.Parameters LeanVM.Semantics

/-- The eight little-endian bytes of a `K` word (`K::to_bytes`, `field.rs:60-62`). -/
def _root_.LeanVM.Parameters.K.toBytes (a : K) : List UInt8 := wordBytes a.lane

/-- The 24 bytes of an `E` word: its three limbs' bytes, `y^0` first. -/
def _root_.LeanVM.Parameters.E.toBytes (x : E) : List UInt8 :=
  K.toBytes (x.limb 0) ++ K.toBytes (x.limb 1) ++ K.toBytes (x.limb 2)

/-- A digest as the two field elements a transcript carries it in, its 128-bit halves
`E(w0, w1)`, `E(w2, w3)` (`Digest::halves`, `hash.rs:110-113`). -/
def digestHalves (digest : Digest) : E × E :=
  (E.ofLimbs (K.ofLane digest[0]) (K.ofLane digest[1]) 0,
    E.ofLimbs (K.ofLane digest[2]) (K.ofLane digest[3]) 0)

/-- The digest two field elements encode, or `none` if either has a nonzero top limb
(`Digest::from_halves`, `hash.rs:115-127`). -/
def digestFromHalves (halves : E × E) : Option Digest :=
  if IsCanonical128 halves.1 ∧ IsCanonical128 halves.2 then
    some #v[(halves.1.limb 0).lane, (halves.1.limb 1).lane, (halves.2.limb 0).lane,
      (halves.2.limb 1).lane]
  else none

end LeanVM.Protocol.KeccakHash

/-! ### The duplex sponge

The Fiat-Shamir sponge of the leanVM verifier and of LeanDA's membership challenges, the Rust's
(`crates/verifier/src/transcript.rs:17-75`, `Sponge`; the prover's `crates/fiat_shamir/src/lib.rs`):
a duplex over a permutation `π` of the Keccak state (deployed: Keccak-f[1600]) in overwrite mode,
the rate lanes `0..16`, the capacity lanes `16..25`, and up to four absorbed scalars waiting, each
with a tag, `1` for a scalar the prover sent (`DS_OBSERVE`) and `4` for a proof-of-work nonce
(`DS_POW_NONCE`). A permutation writes waiting scalar `i` over lanes `4i..4i+4` (its three limbs,
then its tag), zeroes the rest of the rate, keeps the capacity, and empties the queue; absorbing a
fifth scalar permutes the four waiting first. The sponge starts at `π` of the IV's and the public
input's words, the other lanes zero (`Sponge::new`, `transcript.rs:34-46`). -/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics

/-- `DS_OBSERVE`: the tag of a scalar the prover sent (`transcript.rs:17`). -/
def dsObserve : ℕ := 1

/-- `DS_POW_NONCE`: the tag of a proof-of-work nonce (`transcript.rs:18`). -/
def dsPowNonce : ℕ := 4

/-- `RATE_SCALARS`: the scalars that wait to be absorbed, four lanes each
(`transcript.rs:19-20`). -/
def rateScalars : ℕ := 4

/-- The duplex sponge: the Keccak state, and the scalars waiting to be absorbed (at most
`rateScalars`), each with its tag (`Sponge`'s `state` and `pending`, `transcript.rs:26-30`). -/
structure Sponge where
  /-- The Keccak state the last permutation left. -/
  state : KeccakState
  /-- The scalars waiting to be absorbed, each with its tag, in order. -/
  pending : List (E × ℕ)

/-- The rate lanes of the waiting scalars: each its three limbs, then its tag
(`transcript.rs:51-53`). -/
def pendingLanes (pending : List (E × ℕ)) : List UInt64 :=
  pending.flatMap fun (x, tag) ↦ [(x.limb 0).lane, (x.limb 1).lane, (x.limb 2).lane, tag.toUInt64]

/-- The input of a permutation: the waiting scalars' lanes, zeros up to lane `16`, then the
capacity, lanes `16..25` of the state (`Sponge::duplex`, `transcript.rs:49-53`). -/
def duplexInput (sponge : Sponge) : KeccakState :=
  Vector.ofFn fun i ↦
    if i.val < 16 then (pendingLanes sponge.pending).getD i 0 else Keccak.lane sponge.state i

/-- The challenge squeezed into a state: its first three lanes (`Sponge::sample`,
`transcript.rs:73`). -/
def challengeOf (state : KeccakState) : E :=
  E.ofLimbs (K.ofLane (Keccak.lane state 0)) (K.ofLane (Keccak.lane state 1))
    (K.ofLane (Keccak.lane state 2))

/-- The initial state's input: the IV's four words, the public input's four words, then zeros
(`Sponge::new`, `transcript.rs:35-37`). -/
def seedInput (iv publicInput : Digest) : KeccakState :=
  Vector.ofFn fun i ↦
    if h : i.val < 4 then iv[i.val] else if h' : i.val < 8 then publicInput[i.val - 4] else 0

section Duplex

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- A permutation: the waiting scalars over the rate, the capacity kept, then `π`; the queue
empties (`Sponge::duplex`, `transcript.rs:48-57`). -/
def duplex (sponge : Sponge) : m Sponge := do
  let state ← π (duplexInput sponge)
  pure ⟨state, []⟩

/-- Absorb a scalar with a tag: a full queue is permuted first (`Sponge::absorb`,
`transcript.rs:59-65`). -/
def absorb (sponge : Sponge) (x : E) (tag : ℕ) : m Sponge := do
  let sponge ← if sponge.pending.length = rateScalars then duplex π sponge else pure sponge
  pure { sponge with pending := sponge.pending ++ [(x, tag)] }

/-- Squeeze a challenge: a permutation, then the new state's first three lanes (`Sponge::sample`,
`transcript.rs:71-74`). -/
def squeeze (sponge : Sponge) : m (E × Sponge) := do
  let sponge ← duplex π sponge
  pure (challengeOf sponge.state, sponge)

end Duplex

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

/-- `E::new(n, 0, 0)`: the 64-bit word `n` in limb `0` (`field.rs:117-119`). -/
def eOfNat (n : ℕ) : E := ofK (K.ofBits n)

/-- `GEN = E::new(2, 0, 0)`, the generator `x` whose powers index the bytecode and the memory
(`field.rs:114`): `g` in limb `0`. -/
def gen : E := eOfNat 2

end LeanVM.Protocol.Verifier

end
