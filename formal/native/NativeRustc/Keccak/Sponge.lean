module

public import NativeRustc.Bytes

/-!
# The Keccak sponge on bytes

The Keccak state as `crates/keccak256/src/lib.rs` holds it, `[u64; 25]`: 200 bytes, lane `i`
little-endian at bytes `8 i` to `8 i + 7` (`stateBytes`, read back by `stateOf`). On these bytes:
`keccak_f` (`keccakF`, `keccakF_stateBytes`: Keccak-f[1600] of the lanes), the XOR of a block's 17
lanes into the rate (`xorBlock`), `absorb` (`absorb`, `absorb_stateBytes`) and `digest_of`
(`digestOf`). The sponge state after the whole blocks of an input (`sponge`, by `absorbBlocks`):
Keccak-256 of the input is the padded last block absorbed into it (`absorbWith_eq`,
`digestOf_absorb_sponge`).
-/

@[expose] public section

namespace NativeRustc.Keccak

open LeanVM.Semantics LeanVM.Protocol.KeccakHash Native.Keccak Native.Keccak.Proof

/-! ## The state's bytes -/

/-- The 200 bytes of a state: its 25 lanes, little-endian. -/
def stateBytes (A : KeccakState) : List UInt8 := wordsBytes A.toList

/-- The state the first 200 bytes hold. -/
def stateOf (b : List UInt8) : KeccakState := Vector.ofFn fun i ↦ littleEndianLane b i

theorem length_stateBytes (A : KeccakState) : (stateBytes A).length = 200 := by
  rw [stateBytes, length_wordsBytes]; simp

/-- **The state of a state's bytes is the state.** -/
theorem stateOf_stateBytes (A : KeccakState) : stateOf (stateBytes A) = A := by
  apply Vector.ext
  intro i hi
  rw [stateOf, Vector.getElem_ofFn, stateBytes, littleEndianLane_wordsBytes]
  simp [List.getD_eq_getElem?_getD, hi]

theorem lane_stateOf (b : List UInt8) {i : Nat} (hi : i < 25) :
    Keccak.lane (stateOf b) i = littleEndianLane b i := by
  rw [stateOf, lane_ofFn _ hi]

/-! ## `keccak_f`, `absorb`, `digest_of` -/

/-- **`keccak_f`** on the state's 200 bytes: Keccak-f[1600] of its lanes. -/
def keccakF (st : List UInt8) : List UInt8 := stateBytes (keccakF1600 (stateOf st))

theorem keccakF_stateBytes (A : KeccakState) : keccakF (stateBytes A) = stateBytes (keccakF1600 A) := by
  rw [keccakF, stateOf_stateBytes]

/-- The block's 17 lanes XORed into the rate (`absorb`'s loop, with `block_of`). -/
def xorBlock (st block : List UInt8) : List UInt8 :=
  stateBytes (xorRate (stateOf st) (littleEndianLane block))

/-- `absorb`: XOR the block into the rate, then `keccak_f`. -/
def absorb (st block : List UInt8) : List UInt8 := keccakF (xorBlock st block)

/-- `digest_of`: the first four lanes' 32 bytes. -/
def digestOf (st : List UInt8) : List UInt8 := st.take 32

/-! ## The sponge -/

/-- Absorbing one block into a state. -/
def absorbBlock (A : KeccakState) (block : List UInt8) : KeccakState :=
  keccakF1600 (xorRate A (littleEndianLane block))

/-- **`absorb` on bytes is `absorbBlock`.** -/
theorem absorb_stateBytes (A : KeccakState) (block : List UInt8) :
    absorb (stateBytes A) block = stateBytes (absorbBlock A block) := by
  rw [absorb, xorBlock, stateOf_stateBytes, keccakF_stateBytes, absorbBlock]

/-- Absorbing the first `n` whole blocks of `data`. -/
def absorbBlocks : Nat → KeccakState → List UInt8 → KeccakState
  | 0, A, _ => A
  | n + 1, A, data => absorbBlocks n (absorbBlock A (data.take 136)) (data.drop 136)

/-- The sponge's state after the whole blocks of `absorbed`, from the zero state. -/
def sponge (absorbed : List UInt8) : KeccakState :=
  absorbBlocks (absorbed.length / 136) (Vector.replicate 25 0) absorbed

/-- The last of `n + 1` blocks. -/
theorem absorbBlocks_succ : ∀ (n : Nat) (A : KeccakState) (data : List UInt8),
    absorbBlocks (n + 1) A data =
      absorbBlock (absorbBlocks n A data) ((data.drop (136 * n)).take 136)
  | 0, A, data => by simp only [absorbBlocks, Nat.mul_zero, List.drop_zero]
  | n + 1, A, data => by
    have h : data.drop (136 * (n + 1)) = (data.drop 136).drop (136 * n) := by
      rw [List.drop_drop, show 136 + 136 * n = 136 * (n + 1) by omega]
    rw [absorbBlocks, absorbBlocks_succ n, h]
    rfl

/-- The first `n` blocks do not depend on what follows them. -/
theorem absorbBlocks_append : ∀ (n : Nat) (A : KeccakState) (data rest : List UInt8),
    136 * n ≤ data.length → absorbBlocks n A (data ++ rest) = absorbBlocks n A data
  | 0, _, _, _, _ => rfl
  | n + 1, A, data, rest, h => by
    rw [absorbBlocks, absorbBlocks, List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega)]
    exact absorbBlocks_append n _ _ _ (by simp; omega)

/-- **The sponge of Keccak-256**: absorbing `n` whole blocks then the padded rest is
`absorbBlock` of the padded rest into `absorbBlocks`. -/
theorem absorbWith_eq : ∀ (n : Nat) (A : KeccakState) (data : List UInt8),
    absorbWith perm n A data = absorbBlock (absorbBlocks n A data) (padBlock (data.drop (136 * n)))
  | 0, A, data => by simp only [absorbWith_zero, absorbBlocks, Nat.mul_zero, List.drop_zero, absorbBlock]
  | n + 1, A, data => by
    have h : data.drop (136 * (n + 1)) = (data.drop 136).drop (136 * n) := by
      rw [List.drop_drop, show 136 + 136 * n = 136 * (n + 1) by omega]
    rw [absorbWith_succ, absorbWith_eq n, h]
    rfl

/-- The first `n` words' bytes. -/
theorem take_stateBytes (A : KeccakState) (n : Nat) :
    (stateBytes A).take (8 * n) = wordsBytes (A.toList.take n) :=
  take_wordsBytes _ _

/-- **`digest_of` after the padded last block is Keccak-256's digest.** -/
theorem digestOf_absorb_sponge (data : List UInt8) :
    digestOf (stateBytes (absorbBlock (sponge data)
        (padBlock (data.drop (136 * (data.length / 136)))))) =
      digestBytes (keccak256 data) := by
  have hlane : ∀ (v : KeccakState) {k : Nat} (hk : k < 25), Keccak.lane v k = v[k] := fun v k hk ↦ by
    simp [Keccak.lane, Array.getD_eq_getD_getElem?, hk]
  rw [digestOf, show (32 : Nat) = 8 * 4 from rfl, take_stateBytes]
  show wordsBytes _ = wordsBytes (keccak256 data).toList
  refine congrArg wordsBytes (List.ext_getElem (by simp) fun k h1 h2 ↦ ?_)
  have hk : k < 4 := by simpa using h2
  rw [List.getElem_take, Vector.getElem_toList, Vector.getElem_toList, keccak256_lane _ hk,
    absorbWith_eq, hlane _ (by omega)]
  rfl

end NativeRustc.Keccak
