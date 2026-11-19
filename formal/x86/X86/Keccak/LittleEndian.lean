module

public import X86.Keccak.Lanes
public import Statement.HashSignatures

/-!
# Little-endian numbers as words

A number's little-endian bytes are the bytes of its 64-bit words, low first
(`littleEndianBytes_eq_wordsBytes`), and the little-endian number of a word's bytes is the word
(`foldr_wordBytes`), of a digest's bytes the sum of its words (`foldr_digestBytes`). `X86.Bytes`
states these for digests, messages and the hash `H`.
-/

@[expose] public section

namespace X86.Keccak.Proof

open LeanVM.Protocol LeanVM.Protocol.KeccakHash HashSig

theorem getElem_eq_getD (l : List UInt8) {p : Nat} (h : p < l.length) : l[p] = l.getD p 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Byte `r` of word `q` of a number is its byte `8 q + r`. -/
theorem byte_of_word (x q r : Nat) (hr : r < 8) :
    (x / 2 ^ (64 * q) % 2 ^ 64) >>> (8 * r) % 2 ^ 8 = x >>> (8 * (8 * q + r)) % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.shiftRight_eq_div_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · simp [hj, show j + 8 * r < 64 by omega,
      show j + 8 * r + 64 * q = j + 8 * (8 * q + r) by ring]
  · simp [hj]

/-- **A number's little-endian bytes are its words' bytes**, the words `x / 2^(64 q) % 2^64`. -/
theorem littleEndianBytes_eq_wordsBytes (n : Nat) (x : BitVec (8 * n)) (ws : List UInt64)
    (hlen : 8 * ws.length = n)
    (hw : ∀ q < ws.length, (ws.getD q 0).toNat = x.toNat / 2 ^ (64 * q) % 2 ^ 64) :
    littleEndianBytes n x = wordsBytes ws := by
  apply List.ext_getElem (by simp [littleEndianBytes, length_wordsBytes, hlen])
  intro p h1 h2
  have hp : p < n := by simpa [littleEndianBytes] using h1
  have h8 : (8 * (p % 8)).toUInt64.toNat % 64 = 8 * (p % 8) := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [getElem_eq_getD _ h2, getD_wordsBytes]
  simp only [littleEndianBytes, List.getElem_ofFn]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, UInt64.toNat_toUInt8,
    UInt64.toNat_shiftRight, hw _ (by omega), h8, byte_of_word _ _ _ (Nat.mod_lt _ (by omega)),
    show 8 * (p / 8) + p % 8 = p by omega]

/-- The little-endian number of bytes `f 0, …, f (m - 1)` of `n`, then `acc`. -/
theorem foldr_bytes (m : Nat) : ∀ (n acc : Nat) (f : Nat → UInt8),
    (∀ k < m, (f k).toNat = n / 256 ^ k % 256) →
    ((List.range m).map f).foldr (fun b acc ↦ b.toNat + 256 * acc) acc =
      n % 256 ^ m + 256 ^ m * acc := by
  induction m with
  | zero => intro n acc f _; simp [Nat.mod_one]
  | succ m ih =>
    intro n acc f hf
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons,
      ih (n / 256) acc (f ∘ Nat.succ) fun k hk ↦ by
        simp only [Function.comp, hf (k + 1) (by omega), pow_succ', Nat.div_div_eq_div_mul],
      hf 0 (by omega), pow_succ', Nat.mod_mul]
    simp only [pow_zero, Nat.div_one]
    ring

/-- **The little-endian number of a word's bytes is the word.** -/
theorem foldr_wordBytes (w : UInt64) (acc : Nat) :
    (wordBytes w).foldr (fun b acc ↦ b.toNat + 256 * acc) acc = w.toNat + 2 ^ 64 * acc := by
  rw [wordBytes, foldr_bytes 8 w.toNat acc _ fun k hk ↦ ?_]
  · rw [Nat.mod_eq_of_lt (by have := w.toNat_lt; norm_num at this ⊢; omega)]
    norm_num
  · have h8 : (8 * k).toUInt64.toNat % 64 = 8 * k := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      omega
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h8, Nat.shiftRight_eq_div_pow, pow_mul]
    norm_num

/-- **The little-endian number of a digest's bytes** is the sum of its words. -/
theorem foldr_digestBytes (D : LeanVM.Protocol.Digest) :
    (digestBytes D).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      ∑ i : Fin 4, D[i].toNat * 2 ^ (64 * i.val) := by
  obtain ⟨⟨l⟩, hl⟩ := D
  match l, hl with
  | [a, b, c, d], _ =>
    simp only [digestBytes, Vector.toList_mk, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.foldr_append, foldr_wordBytes, Fin.sum_univ_four]
    simp
    ring

/-- The low 128 bits of the little-endian number of a digest's words are its first two words. -/
theorem truncateHash_sum (D : LeanVM.Protocol.Digest) :
    truncateHash (BitVec.ofNat 256 (∑ i : Fin 4, D[i].toNat * 2 ^ (64 * i.val))) =
      BitVec.ofNat 128 (D[0].toNat + 2 ^ 64 * D[1].toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [Fin.sum_univ_four]
  have h0 := D[0].toNat_lt
  have h1 := D[1].toNat_lt
  have h2 := D[2].toNat_lt
  have h3 := D[3].toNat_lt
  show (BitVec.extractLsb' 0 128 (BitVec.ofNat 256 (D[0].toNat * 2 ^ (64 * 0) +
    D[1].toNat * 2 ^ (64 * 1) + D[2].toNat * 2 ^ (64 * 2) + D[3].toNat * 2 ^ (64 * 3)))).toNat =
    (BitVec.ofNat 128 (D[0].toNat + 2 ^ 64 * D[1].toNat)).toNat
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  generalize D[0].toNat = a at *
  generalize D[1].toNat = b at *
  generalize D[2].toNat = c at *
  generalize D[3].toNat = d at *
  simp only [Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.mul_one]
  omega

end X86.Keccak.Proof
