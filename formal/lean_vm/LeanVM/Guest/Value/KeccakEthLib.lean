module

public import Statement.LeanXmss
public import EthLib.Cryptography.Proofs.Hash.Keccak.Lanes

/-!
# leanVM's Keccak-256 is EthLib's

leanVM's sponge on bytes (`keccak256With`) over a permutation `π` of its state is EthLib's
(`EthLib.Cryptography.Hash.Keccak.keccak256With`) over `π` carried to EthLib's layout of the state,
the same `32` bytes, in any lawful monad (`keccak256With_eq_ethLib`). So leanXMSS's hash, EthLib's
sponge on lanes over `π` (`LeanXmss.xmssHash`), is leanVM's Keccak-256 of the lanes' bytes
(`xmssHash_eq_keccak256With`), and over Keccak-f[1600] the guest's (`xmssHash_keccakF1600`). This
is the one place where the two definitions of Keccak-256 meet.
-/

@[expose] public section

namespace LeanVM.Guest.KeccakEthLib

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanXmss (stateToEthLib stateOfEthLib xmssHash)

open EthLib.Cryptography.Hash.Keccak (Internal.laneAt Internal.absorbBlock Internal.absorbBlocks
  Internal.blockLane pad)

/-- A lane read from a byte string that a list holds is leanVM's little-endian lane. -/
theorem laneAt_mk (l : List UInt8) (i : ℕ) :
    Internal.laneAt ⟨l.toArray⟩ (8 * i) = littleEndianLane l i := by
  have e : ∀ k, EthLib.Base.byteAtOrZero (ByteArray.mk l.toArray) k = l.getD k 0 := fun k ↦ by
    rw [EthLib.Base.byteAtOrZero_eq_getD]; simp
  simp only [Internal.laneAt, littleEndianLane, e, List.range_succ, List.range_zero,
    List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, UInt64.zero_or]
  simp

/-- Absorbing a block into EthLib's state is leanVM's XOR of its lanes into the rate. -/
theorem stateOfEthLib_absorbBlock (s : KeccakState) (read : ℕ → UInt64) (start : ℕ)
    (block : List UInt8) (h : ∀ i < 17, read (start + 8 * i) = littleEndianLane block i) :
    stateOfEthLib (Internal.absorbBlock 136 (stateToEthLib s) read start) =
      Vector.ofFn fun i : Fin 25 ↦
        if i.val < 17 then Keccak.lane s i ^^^ littleEndianLane block i else Keccak.lane s i := by
  have key : ∀ i : ℕ, Internal.blockLane 136 read start i =
      if i < 17 then littleEndianLane block i else 0 := by
    intro i
    unfold Internal.blockLane
    by_cases hi : i < 17
    · simp only [hi, show 8 * i + 8 ≤ 136 by omega, ite_true]
      exact h i hi
    · simp only [hi, show ¬ 8 * i + 8 ≤ 136 by omega, ite_false]
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [stateOfEthLib, Internal.absorbBlock, stateToEthLib, Keccak.lane, key]

/-- A byte of the padded last block, by position. -/
theorem getD_padBlock (r : List UInt8) (h : r.length < 136) (j : ℕ) (hj : j < 136) :
    (padBlock r).getD j 0 =
      ((if j < r.length then r.getD j 0 else 0) ^^^ (if r.length = j then 0x01 else 0)) ^^^
        (if 135 = j then 0x80 else 0) := by
  simp only [padBlock, rate, padFirst, padLast, List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases h1 : j < r.length
  · simp [List.getElem?_append_left h1, h1, show r.length ≠ j by omega,
      show 135 ≠ j by omega]
  · rw [List.getElem?_append_right (by omega)]
    simp only [List.getElem?_replicate, show j - r.length < 136 - r.length by omega, ite_true]
    by_cases h2 : r.length = j <;> by_cases h3 : 135 = j <;> simp [h1, h2, h3]

/-- The bytes of the padded last block are those of EthLib's padded message. -/
theorem getD_padBlock_eq_pad (data : List UInt8) (j : ℕ) (hj : j < 136) :
    (padBlock (data.drop (136 * (data.length / 136)))).getD j 0 =
      EthLib.Base.byteAtOrZero (pad 136 ⟨data.toArray⟩) (136 * (data.length / 136) + j) := by
  set r := data.drop (136 * (data.length / 136)) with hr
  have hrl : r.length = data.length % 136 := by rw [hr, List.length_drop]; omega
  have hlt : r.length < 136 := by omega
  rw [getD_padBlock r hlt j hj]
  have hd : r.getD j 0 = data.getD (136 * (data.length / 136) + j) 0 := by
    simp [hr, List.getD_eq_getElem?_getD]
  by_cases h1 : j < r.length
  · rw [EthLib.Cryptography.Hash.Keccak.byteAtOrZero_pad_of_lt _ (by simp; omega),
      EthLib.Base.byteAtOrZero_eq_getD]
    simp only [h1, ite_true, show r.length ≠ j by omega, show 135 ≠ j by omega, ite_false,
      UInt8.xor_zero]
    simpa [List.getD_eq_getElem?_getD, h1] using hd
  · rw [EthLib.Cryptography.Hash.Keccak.byteAtOrZero_pad_of_le _ (by simp; omega)]
    simp only [ByteArray.size, List.size_toArray, EthLib.Cryptography.Hash.Keccak.paddingByte]
    have e : 136 * (data.length / 136) + j - data.length = j - r.length := by omega
    have e2 : 136 - data.length % 136 = 136 - r.length := by omega
    have c1 : (j - r.length = 0) = (r.length = j) := propext (by omega)
    have c2 : (j - r.length + 1 = 136 - r.length) = (135 = j) := propext (by omega)
    have hlt' : j - r.length < 136 - r.length := by omega
    have hg : r.getD j 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show r.length ≤ j by omega)]
    rw [e, e2]
    simp only [h1, hlt', hg, c1, c2, ite_true, ite_false, UInt8.zero_xor]
    by_cases h2 : r.length = j <;> by_cases h3 : 135 = j <;> simp [h2, h3]

/-- The digest's bytes are those of the first four lanes of EthLib's state. -/
theorem digest_toBytes_eq (st : KeccakState) :
    Digest.toBytes #v[Keccak.lane st 0, Keccak.lane st 1, Keccak.lane st 2, Keccak.lane st 3] =
      EthLib.Cryptography.Hash.Keccak.Internal.squeeze256 (stateToEthLib st) := by
  apply Vector.ext
  intro j hj
  interval_cases j <;>
    simp [Digest.toBytes, KeccakHash.digestBytes, KeccakHash.wordBytes,
      EthLib.Cryptography.Hash.Keccak.Internal.squeeze256,
      EthLib.Cryptography.Hash.Keccak.Internal.squeezeLanes256,
      EthLib.Cryptography.Hash.Keccak.Lanes4.bytes, stateToEthLib, Keccak.lane, List.range_succ]

/-- A whole block of the message reads the same lanes from leanVM's block and from `P`. -/
theorem leLane_take_drop (data : List UInt8) (k : ℕ) (hk : 136 * k + 136 ≤ data.length)
    (i : ℕ) (hi : i < 17) :
    littleEndianLane ((data.drop (136 * k)).take 136) i =
      Internal.laneAt (pad 136 ⟨data.toArray⟩) (136 * k + 8 * i) := by
  rw [← laneAt_mk]
  refine EthLib.Cryptography.Hash.Keccak.laneAt_congr fun t ht ↦ ?_
  rw [EthLib.Cryptography.Hash.Keccak.byteAtOrZero_pad_of_lt _ (by simp; omega),
    EthLib.Base.byteAtOrZero_eq_getD, EthLib.Base.byteAtOrZero_eq_getD]
  simp [List.getElem?_drop, show 8 * i + t < 136
    by omega, show 136 * k + (8 * i + t) = 136 * k + 8 * i + t by omega]

/-- The padded last block reads the same lanes as `P`. -/
theorem leLane_padBlock (data : List UInt8) (i : ℕ) (hi : i < 17) :
    littleEndianLane (padBlock (data.drop (136 * (data.length / 136)))) i =
      Internal.laneAt (pad 136 ⟨data.toArray⟩) (136 * (data.length / 136) + 8 * i) := by
  rw [← laneAt_mk]
  refine EthLib.Cryptography.Hash.Keccak.laneAt_congr fun t ht ↦ ?_
  rw [EthLib.Base.byteAtOrZero_eq_getD, show 136 * (data.length / 136) + 8 * i + t =
    136 * (data.length / 136) + (8 * i + t) by omega, ← getD_padBlock_eq_pad _ _ (by omega)]
  simp

/-- leanVM's absorbing, block by block, is EthLib's, from block `k` of the padded message. -/
theorem absorbWith_eq_absorbBlocks {m : Type → Type} [Monad m] [LawfulMonad m]
    (π : KeccakState → m KeccakState) (data : List UInt8) (n : ℕ) :
    ∀ (k : ℕ), k + n = data.length / 136 → ∀ s : KeccakState,
      stateToEthLib <$> absorbWith π n s (data.drop (136 * k)) =
        Internal.absorbBlocks (fun S ↦ stateToEthLib <$> π (stateOfEthLib S)) 136
          (Internal.laneAt (pad 136 ⟨data.toArray⟩)) (n + 1) (136 * k) (stateToEthLib s) := by
  induction n with
  | zero =>
    intro k hk s
    obtain rfl : k = data.length / 136 := by omega
    simp only [absorbWith, absorbBlockWith, Internal.absorbBlocks, bind_pure]
    rw [stateOfEthLib_absorbBlock s _ _ (padBlock (data.drop (136 * (data.length / 136))))
        (fun i hi ↦ (leLane_padBlock data i hi).symm)]
  | succ n ih =>
    intro k hk s
    have hk' : 136 * k + 136 ≤ data.length := by omega
    rw [absorbWith, Internal.absorbBlocks, map_bind, bind_map_left,
      show (data.drop (136 * k)).take rate = (data.drop (136 * k)).take 136 from rfl]
    rw [absorbBlockWith, stateOfEthLib_absorbBlock s _ _ ((data.drop (136 * k)).take 136)
      (fun i hi ↦ (leLane_take_drop data k hk' i hi).symm)]
    refine bind_congr fun t ↦ ?_
    have := ih (k + 1) (by omega) t
    rw [show 136 * (k + 1) = 136 * k + 136 by ring, ← List.drop_drop] at this
    exact this

/-- **leanVM's Keccak-256 over `π` is EthLib's**, over `π` carried to EthLib's layout. -/
theorem keccak256With_eq_ethLib {m : Type → Type} [Monad m] [LawfulMonad m]
    (π : KeccakState → m KeccakState) (data : List UInt8) :
    Digest.toBytes <$> keccak256With π data =
      EthLib.Cryptography.Hash.Keccak.keccak256With
        (fun s ↦ stateToEthLib <$> π (stateOfEthLib s)) ⟨data.toArray⟩ := by
  have h := absorbWith_eq_absorbBlocks π data (data.length / 136) 0 (by omega)
    (Vector.replicate 25 0)
  rw [EthLib.Cryptography.Hash.Keccak.keccak256With_eq_squeeze256,
    EthLib.Cryptography.Hash.Keccak.spongeAbsorb_eq, EthLib.Cryptography.Hash.Keccak.blockCount,
    show (⟨data.toArray⟩ : ByteArray).size = data.length by simp [ByteArray.size], keccak256With]
  simp only [show EthLib.Cryptography.Hash.Keccak.RATE_256 = 136 from rfl,
    show KeccakHash.rate = 136 from rfl]
  rw [List.drop_zero, Nat.mul_zero] at h
  rw [← show stateToEthLib (Vector.replicate 25 0) = EthLib.Cryptography.Hash.Keccak.State.zero
    from rfl, ← h]
  simp only [bind_pure_comp, Functor.map_map]
  exact congrArg (· <$> _) (funext digest_toBytes_eq)

/-- leanXMSS's hash over `π` is leanVM's Keccak-256 over `π` of the lanes' bytes. -/
theorem xmssHash_eq_keccak256With {m : Type → Type} [Monad m] [LawfulMonad m]
    (π : KeccakState → m KeccakState) (lanes : Array UInt64) :
    EthLib.Cryptography.Hash.Keccak.Lanes4.bytes <$> xmssHash π lanes =
      Digest.toBytes <$> keccak256With π (EthLib.Cryptography.Hash.Keccak.lanesBytes lanes) := by
  exact (EthLib.Cryptography.Hash.Keccak.keccak256LanesWith_lanesBytes _ lanes).trans
    (keccak256With_eq_ethLib π _).symm

/-- **leanXMSS's hash over Keccak-f[1600] is the guest's Keccak-256** of the lanes' bytes. -/
theorem xmssHash_keccakF1600 (lanes : Array UInt64) :
    (Id.run (xmssHash (m := Id) keccakF1600 lanes)).bytes =
      (keccak256 (EthLib.Cryptography.Hash.Keccak.lanesBytes lanes)).toBytes := by
  exact xmssHash_eq_keccak256With (m := Id) keccakF1600 lanes

end LeanVM.Guest.KeccakEthLib

end
