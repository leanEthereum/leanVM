module

public import NativeRustcArm.Sym
public import NativeRustcArm.Spec.Keccak
public import NativeRustc.Keccak.Permute

/-!
# `keccak_f`'s words in memory

A 64-bit word at an address (`WordAt`: its eight `byteOf`s, as the executor's writes leave them),
read back by an environment load (`load_of_wordAt`). A word whose bytes the environment holds as
a `UInt64`'s little-endian bytes is that `UInt64` (`load_eq_of_bytes`): the state's lanes, as
`stateOf` reads them (`load_lane`), and the round constants (`load_rc`). The state's 200 bytes
from its 25 lanes' words (`bytesAt_stateBytes`).
-/

namespace NativeRustcArm.KeccakF

open NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics LeanVM.Parameters
  LeanVM.Protocol.KeccakHash Native.Keccak Native.Keccak.Proof

@[expose] public section

/-- The 8 bytes from `a` hold `w`, little-endian. -/
def WordAt (d : DataMem) (a w : BitVec 64) : Prop := BytesAt d a ((List.range 8).map (byteOf w))

end

public section

/-- Byte `k` of a word's bit vector is its byte `k`. -/
theorem byteOf_toBitVec (w : UInt64) {k : Nat} (hk : k < 8) :
    byteOf w.toBitVec k = (w >>> (8 * k).toUInt64).toUInt8 := by
  apply UInt8.toNat_inj.mp
  rw [byteOf, UInt8.toNat_ofNat', UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, UInt64.toNat_toBitVec]
  congr 3
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

variable {env : Env}

/-- **A word at a region's offset** is what the environment loads there. -/
theorem load_of_wordAt {r off : Nat} {w : BitVec 64}
    (h : WordAt env.mem0 (env.base r + BitVec.ofNat 64 off) w) : env.load r off 8 = w := by
  rw [Env.load_of_bytesAt (by simp) h]
  have := ofBytes_byteOf w 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  rw [this, Nat.mod_eq_of_lt w.isLt, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A load of 8 bytes, as a `UInt64`, is the little-endian word of its bytes. -/
theorem ofBitVec_load {r off : Nat} :
    UInt64.ofBitVec (env.load r off 8) =
      laneOf fun k => (env.mem0.get? (env.base r + BitVec.ofNat 64 (off + k))).getD 0 := by
  rw [← laneOf_word (UInt64.ofBitVec (env.load r off 8))]
  apply laneOf_congr
  intro k hk
  rw [← byteOf_toBitVec _ hk, UInt64.toBitVec_ofBitVec, byteOf_load hk (by omega)]

/-- **A load of a `UInt64`'s little-endian bytes** is the `UInt64`. -/
theorem load_eq_of_bytes {r off : Nat} {w : UInt64}
    (h : ∀ k < 8, (env.mem0.get? (env.base r + BitVec.ofNat 64 (off + k))).getD 0 =
      (w >>> (8 * k).toUInt64).toUInt8) : env.load r off 8 = w.toBitVec := by
  have hw : UInt64.ofBitVec (env.load r off 8) = w := by
    rw [ofBitVec_load, ← laneOf_word w]
    exact laneOf_congr h
  rw [← hw]

/-- **Lane `j` of the state** `stateOf` reads from the 200 bytes at region `r`'s base is what the
environment loads at `8 j`. -/
theorem load_lane {r : Nat} {j : Nat} (hj : j < 25) :
    env.load r (8 * j) 8 =
      (Keccak.lane (stateOf (bytesOf env.mem0 (env.base r) 200)) j).toBitVec := by
  have hw : UInt64.ofBitVec (env.load r (8 * j) 8) =
      Keccak.lane (stateOf (bytesOf env.mem0 (env.base r) 200)) j := by
    rw [ofBitVec_load, lane_stateOf _ hj, littleEndianLane_eq]
    apply laneOf_congr
    intro k hk
    rw [bytesOf, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  rw [← hw]

/-- `load_lane` at an offset given as a literal. -/
theorem load_lane' {r off j : Nat} (hoff : off = 8 * j) (hj : j < 25) :
    env.load r off 8 =
      (Keccak.lane (stateOf (bytesOf env.mem0 (env.base r) 200)) j).toBitVec := by
  subst hoff
  exact load_lane hj

theorem getElem_eq_getD' (l : List UInt8) {p : Nat} (h : p < l.length) : l[p] = l.getD p 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_toList (A : KeccakState) (j : Nat) : A.toList.getD j 0 = Keccak.lane A j := by
  simp [Keccak.lane, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

/-- **Round constant `i`** is what the environment loads at `8 i` from the table at region `r`. -/
theorem load_rc {r i : Nat} (hb : BytesAt env.mem0 (env.base r) rcBytes) (hi : i < 24) :
    env.load r (8 * i) 8 = (keccakRC.getD i 0).toBitVec := by
  have hlen : rcBytes.length = 192 := by
    rw [show rcBytes = wordsBytes keccakRC from rfl, length_wordsBytes]
    rfl
  apply load_eq_of_bytes
  intro k hk
  rw [hb (8 * i + k) (by omega), Option.getD_some, getElem_eq_getD', show rcBytes = wordsBytes keccakRC from rfl,
    getD_wordsBytes, show (8 * i + k) / 8 = i by omega, show (8 * i + k) % 8 = k by omega]

/-- **The state's bytes** from its lanes' words. -/
theorem bytesAt_stateBytes {d : DataMem} {a : BitVec 64} {A : KeccakState}
    (h : ∀ j < 25, WordAt d (a + BitVec.ofNat 64 (8 * j)) (Keccak.lane A j).toBitVec) :
    BytesAt d a (stateBytes A) := by
  intro p hp
  rw [length_stateBytes] at hp
  have := h (p / 8) (by omega) (p % 8) (by simp; omega)
  rw [addr_add, show 8 * (p / 8) + p % 8 = p by omega] at this
  rw [this, List.getElem_map, List.getElem_range, byteOf_toBitVec _ (by omega),
    getElem_eq_getD' (stateBytes A), stateBytes, getD_wordsBytes, getD_toList]

end

end NativeRustcArm.KeccakF
