module

public import Common.Transfer2

@[expose] public section

/-!
# Keccak-256 in the random-permutation model

The abstract results instantiated at Keccak-256 (`Common.Sponge`): states of 200 bytes, a
capacity of 64 bytes (`|C| = 2^512`), the Keccak padding and the all-zero initial state. A
distinguisher making at most `q` calls to Keccak-f[1600] in all (its own forward and inverse
calls, and the sponge's, one per 136-byte block of every padded message it hashes) tells
Keccak-256 over a random permutation from a random oracle with the simulator with advantage at
most `q² / 2^509` (`keccak256_indifferentiable`); the same bound moves ROM games to the RPM
(`keccak256_transfer`).

With direct permutation calls in a duplex (leanVM's Fiat–Shamir transcript), the non-final
blocks are those whose last byte (byte 135, the top byte of lane 16) has its top bit clear
(`keccakNF`): the padding's last byte is `0x80` or `0x81` (`not_keccakNF_of_pad`), while a
duplexing that overwrites lanes `0..16` and keeps lanes `16..25` absorbs a block whose lane 16
is zero (`keccakNF_blockTo`). The two-oracle transfer then costs `q² / 2^508`
(`keccak256_transfer2`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace Common

/-- There are 256 bytes. -/
theorem card_uInt8 : Fintype.card UInt8 = 256 := by
  rw [← FinEnum.card_eq_fintypeCard]; rfl

/-- There are `256 ^ n` byte vectors of length `n`. -/
theorem card_vector_uInt8 (n : ℕ) : Fintype.card (Vector UInt8 n) = 256 ^ n := by
  rw [instFintypeVector, Fintype.ofEquiv_card, Fintype.card_fun, card_uInt8, Fintype.card_fin]

/-- The Keccak capacity has `2^512` values. -/
theorem card_kCap : Fintype.card KCap = 2 ^ 512 := by
  rw [card_vector_uInt8, show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul]

/-- The Keccak state has `2^1600` values. -/
theorem card_kState : Fintype.card KState = 2 ^ 1600 := by
  simp only [KState, SpState, Fintype.card_prod, DigestBytes, KRest, KCap, card_vector_uInt8]
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add,
    ← pow_add]

/-- **The Keccak-256 bound**: `q² / 2^1600 + (q (2q + 1) + q (q + 1)) / 2^512 ≤ q² / 2^509`. -/
theorem keccak_indiffBound_le (q : ℕ) :
    indiffBound (Fintype.card KState) (Fintype.card KCap) q ≤ (q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
  rw [indiffBound, card_kState, card_kCap]
  have hq : q ≤ q ^ 2 := by nlinarith
  have hN : ((2 ^ 512 : ℕ) : ℝ≥0∞) = 2 ^ 509 * 8 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, show (8 : ℝ≥0∞) = 2 ^ 3 by norm_num, ← pow_add]
  have hNS : ((2 ^ 512 : ℕ) : ℝ≥0∞) ≤ ((2 ^ 1600 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hN0 : ((2 ^ 512 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  calc (q : ℝ≥0∞) * (q / ((2 ^ 1600 : ℕ) : ℝ≥0∞)) +
        ((q * (2 * q + 1) + q * (q + 1) : ℕ) : ℝ≥0∞) / ((2 ^ 512 : ℕ) : ℝ≥0∞)
      ≤ ((q ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ 512 : ℕ) : ℝ≥0∞) +
        ((q * (2 * q + 1) + q * (q + 1) : ℕ) : ℝ≥0∞) / ((2 ^ 512 : ℕ) : ℝ≥0∞) := by
        gcongr
        rw [mul_div_assoc', ← Nat.cast_mul, ← pow_two]
        exact ENNReal.div_le_div_left hNS _
    _ = ((q ^ 2 + (q * (2 * q + 1) + q * (q + 1)) : ℕ) : ℝ≥0∞) / ((2 ^ 512 : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_add (q ^ 2), ENNReal.add_div]
    _ ≤ ((8 * q ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ 512 : ℕ) : ℝ≥0∞) := by
        gcongr
        nlinarith
    _ = (q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
        rw [hN, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm (2 ^ 509 : ℝ≥0∞),
          ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- **Keccak-256 is indifferentiable from a random oracle** in the random-permutation model:
a distinguisher of cost `q` (`queryCost`) has advantage at most `q² / 2^509`. -/
theorem keccak256_indifferentiable {α : Type} (D : OracleComp (dSpec (List UInt8) DigestBytes KState) α)
    (q : ℕ) (hD : QueryCostAtMost D (queryCost (Dg := DigestBytes) keccakPadding) q) (p : α → Prop) :
    Pr{let a ← realGame keccakPadding KState.zero D}[p a] ≤
        Pr{let a ← idealGame keccakPadding KState.zero D}[p a] + (q ^ 2 : ℝ≥0∞) / 2 ^ 509 ∧
      Pr{let a ← idealGame keccakPadding KState.zero D}[p a] ≤
        Pr{let a ← realGame keccakPadding KState.zero D}[p a] + (q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
  obtain ⟨h1, h2⟩ := indifferentiability keccakPadding KState.zero D q hD p
  exact ⟨h1.trans (by gcongr; exact keccak_indiffBound_le q),
    h2.trans (by gcongr; exact keccak_indiffBound_le q)⟩

/-- **The ROM-to-RPM transfer for Keccak-256**: for an RPM game with honest parts hashing through
`H` and an adversary with `H`, `π` and `π⁻¹`, of cost `q` in all, every event has probabilities
in the RPM and in the ROM against `advS keccakPadding KState.zero A` within `q² / 2^509`. -/
theorem keccak256_transfer {β γ δ : Type}
    (pre : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) β)
    (A : β → OracleComp (dSpec (List UInt8) DigestBytes KState) γ)
    (post : β → γ → OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) δ) (q : ℕ)
    (hq : QueryCostAtMost (rpmGame pre A post) (queryCost (Dg := DigestBytes) keccakPadding) q)
    (p : δ → Prop) :
    Pr{let a ← realGame keccakPadding KState.zero (rpmGame pre A post)}[p a] ≤
        Pr{let a ← romRun (pre >>= fun x ↦ advS keccakPadding KState.zero (A x) >>= fun a ↦
          post x a)}[p a] + (q ^ 2 : ℝ≥0∞) / 2 ^ 509 ∧
      Pr{let a ← romRun (pre >>= fun x ↦ advS keccakPadding KState.zero (A x) >>= fun a ↦
          post x a)}[p a] ≤
        Pr{let a ← realGame keccakPadding KState.zero (rpmGame pre A post)}[p a] +
          (q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
  obtain ⟨h1, h2⟩ := transfer keccakPadding KState.zero pre A post q hq p
  exact ⟨h1.trans (by gcongr; exact keccak_indiffBound_le q),
    h2.trans (by gcongr; exact keccak_indiffBound_le q)⟩

/-! ## The two-oracle model -/

/-- A **non-final** Keccak block: its last byte (byte 135 of the state) has its top bit clear. -/
def keccakNF (B : KBlock) : Prop := B.2[103] < 0x80

instance : DecidablePred keccakNF := fun B ↦ by unfold keccakNF; infer_instance

/-- The last block of a padded message is final: its last byte is `0x80` or `0x81`. -/
theorem not_keccakNF_of_pad (m : List UInt8) (β : List KBlock) (B : KBlock)
    (h : keccakPadding.pad m = β ++ [B]) : ¬ keccakNF B := by
  have hb : blocksToBytes (keccakPad m) = keccakPadBytes m :=
    blocksToBytes_toBlocks _ (by rw [keccakPadBytes_length]; omega)
  have h1 : (keccakPadBytes m).getLast? = some B.2[103] := by
    have h' : keccakPad m = β ++ [B] := h
    rw [← hb, h']
    simp [blocksToBytes, KBlock.toBytes, List.getLast?_eq_getElem?]
  obtain ⟨l, b, hl, hb'⟩ : ∃ l b, keccakPadBytes m = l ++ [b] ∧ (b = 0x81 ∨ b = 0x80) := by
    unfold keccakPadBytes
    split_ifs
    · exact ⟨m, 0x81, rfl, Or.inl rfl⟩
    · exact ⟨m ++ [0x01] ++ List.replicate (134 - m.length % 136) 0, 0x80, rfl, Or.inr rfl⟩
  rw [hl, List.getLast?_concat, Option.some_inj] at h1
  unfold keccakNF
  rw [← h1]
  rcases hb' with rfl | rfl <;> decide

/-- A duplexing that keeps byte 135 and the capacity absorbs a non-final block. -/
theorem keccakNF_blockTo (y x : KState) (h : x.1.2[103] = y.1.2[103]) :
    keccakNF (blockTo y x) := by
  simp only [keccakNF, blockTo, rxor]
  change (Vector.zipWith (· ^^^ ·) y.1.2 x.1.2)[103] < 0x80
  rw [Vector.getElem_zipWith, h, UInt8.xor_self]
  decide

/-- **The two-oracle Keccak-256 bound**: `indiffBound2 ≤ q² / 2^508`. -/
theorem keccak_indiffBound2_le (q : ℕ) :
    indiffBound2 (Fintype.card KState) (Fintype.card KCap) q ≤ (q ^ 2 : ℝ≥0∞) / 2 ^ 508 := by
  rw [indiffBound2]
  have h2 : (q : ℝ≥0∞) * (q / (Fintype.card KCap : ℝ≥0∞)) ≤ (q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
    rw [card_kCap, mul_div_assoc', ← pow_two, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _
  calc _ ≤ (q ^ 2 : ℝ≥0∞) / 2 ^ 509 + (q ^ 2 : ℝ≥0∞) / 2 ^ 509 :=
        add_le_add (keccak_indiffBound_le q) h2
    _ = (q ^ 2 : ℝ≥0∞) / 2 ^ 508 := by
        rw [← ENNReal.add_div, ← two_mul, show (2 : ℝ≥0∞) ^ 509 = 2 * 2 ^ 508 by
          rw [← pow_succ']]
        exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

/-- **The two-oracle ROM-to-RPM transfer for Keccak-256**: for a game with an honest part
hashing through `H`, an adversary with `H`, `π` and `π⁻¹`, and an honest part hashing through
`H` and calling `F = π` in a duplex (`Duplex keccakNF`, e.g. by `keccakNF_blockTo`), of cost `q`
in all, every event has probabilities in the RPM and in the two-oracle ROM against
`advS2 keccakPadding KState.zero A` within `q² / 2^508`. -/
theorem keccak256_transfer2 {β γ δ : Type}
    (pre : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) β)
    (A : β → OracleComp (dSpec (List UInt8) DigestBytes KState) γ)
    (post : β → γ → OracleComp (unifSpec + hfSpec (List UInt8) DigestBytes KState) δ)
    (hpost : ∀ x a, Duplex KState.zero keccakNF (post x a) []) (q : ℕ)
    (hq : QueryCostAtMost (rpmGame2 pre A post) (queryCost2 (Dg := DigestBytes) keccakPadding) q)
    (p : δ → Prop) :
    Pr{let a ← realGame2 keccakPadding KState.zero (rpmGame2 pre A post)}[p a] ≤
        Pr{let a ← romRun2 (simulateQ hInF pre >>= fun x ↦
          advS2 keccakPadding KState.zero (A x) >>= fun a ↦ post x a)}[p a] +
          (q ^ 2 : ℝ≥0∞) / 2 ^ 508 ∧
      Pr{let a ← romRun2 (simulateQ hInF pre >>= fun x ↦
          advS2 keccakPadding KState.zero (A x) >>= fun a ↦ post x a)}[p a] ≤
        Pr{let a ← realGame2 keccakPadding KState.zero (rpmGame2 pre A post)}[p a] +
          (q ^ 2 : ℝ≥0∞) / 2 ^ 508 := by
  obtain ⟨h1, h2⟩ := transfer2 keccakPadding KState.zero keccakNF not_keccakNF_of_pad pre A
    post hpost q hq p
  exact ⟨h1.trans (by gcongr; exact keccak_indiffBound2_le q),
    h2.trans (by gcongr; exact keccak_indiffBound2_le q)⟩

end Common
