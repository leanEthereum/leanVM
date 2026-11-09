/-
  LeanVM.Protocol.KeccakAbsorb

  Keccak-256 over Keccak-f[1600] without the monad: the absorption of a block and of a byte
  string as pure functions, and `keccak256` through them.
-/

module

public import Statement.Fast.Keccak

/-!
# Keccak-256 without the monad

`Statement/RandomPermutation.lean` defines Keccak-256 once, over any permutation in any monad
(`keccak256With`), and the deployed `keccak256` as it over Keccak-f[1600] in `Id`. The proofs
about the deployed hash work with the pure absorption: `absorbBlock` (XOR a block's `17` lanes
into the rate, then Keccak-f[1600]) and `absorb` (whole blocks, then the padded last one), with
`keccak256_eq_absorb`.
-/

namespace LeanVM.Protocol.KeccakHash

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- Absorb one block of `136` bytes with Keccak-f[1600]: XOR its `17` lanes into the rate, then
permute (`absorbBlockWith` without the monad). -/
def absorbBlock (state : KeccakState) (block : List UInt8) : KeccakState :=
  keccakF1600 (Vector.ofFn fun i ↦
    if i.val < 17 then Keccak.lane state i ^^^ littleEndianLane block i else Keccak.lane state i)

/-- Absorb `data` into `state` with Keccak-f[1600]: `blocks` whole blocks of `136` bytes, then the
padded last block (`absorbWith` without the monad). -/
def absorb : (blocks : ℕ) → KeccakState → List UInt8 → KeccakState
  | 0, state, data => absorbBlock state (padBlock data)
  | blocks + 1, state, data => absorb blocks (absorbBlock state (data.take rate)) (data.drop rate)

/-- `absorbWith` over Keccak-f[1600] in `Id` is `absorb`. -/
theorem absorbWith_keccakF : ∀ (blocks : ℕ) (state : KeccakState) (data : List UInt8),
    absorbWith (m := Id) (fun s ↦ pure (keccakF1600 s)) blocks state data = absorb blocks state data
  | 0, _, _ => rfl
  | blocks + 1, _, _ => absorbWith_keccakF blocks _ _

/-- **The deployed Keccak-256 through the pure absorption.** -/
theorem keccak256_eq_absorb (data : List UInt8) :
    keccak256 data =
      let state := absorb (data.length / rate) (Vector.replicate 25 0) data
      #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3] := by
  rw [keccak256, LeanVM.Fast.Keccak.keccak256With_id, absorbWith_keccakF]
  rfl

end

end LeanVM.Protocol.KeccakHash
