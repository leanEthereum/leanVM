module

public import NativeRustcVm.Field.Rust
public import NativeVm.Model.Transcript
public import Statement.Verifier.Multilinear

/-!
# `bit_length` and its uses

`bitLength v` is the bit length of `v` (`Verifier.bitLength`, `0` at `0`): each step of the halving
loop at shift `s`, the value below `2^(2s)`, keeps `n + bitLength(v') = bitLength(v)` and leaves the
value below `2^s` (`Inv.step`), so after the shifts `32, …, 1` the value is `0` or `1`
(`bitLength_eq`). Then `log2_ceil`, `grinding_bits` and `log2_strict` are the model's
(`log2Ceil_eq`, `grindingBits_eq`, `log2Strict_eq`).
-/

namespace NativeRustcVm.Field

open LeanVM.Protocol

public section

/-- A bit length is the shift plus the shifted value's, while that is nonzero. -/
theorem bitLength_div {x s : ℕ} (h : x / 2 ^ s ≠ 0) :
    Verifier.bitLength x = s + Verifier.bitLength (x / 2 ^ s) := by
  have hx : x ≠ 0 := by rintro rfl; simp at h
  have hy := Nat.log2_self_le h
  have hy2 := Nat.lt_log2_self (n := x / 2 ^ s)
  have e : x.log2 = s + (x / 2 ^ s).log2 := by
    apply Nat.le_antisymm
    · rw [← Nat.lt_succ_iff, Nat.log2_lt hx]
      calc x < 2 ^ s * (x / 2 ^ s + 1) := Nat.lt_mul_div_succ x (Nat.two_pow_pos s)
        _ ≤ 2 ^ s * 2 ^ ((x / 2 ^ s).log2 + 1) := Nat.mul_le_mul_left _ hy2
        _ = 2 ^ (s + (x / 2 ^ s).log2).succ := by rw [← pow_add]; congr 1
    · rw [Nat.le_log2 hx, pow_add]
      calc 2 ^ s * 2 ^ (x / 2 ^ s).log2 ≤ 2 ^ s * (x / 2 ^ s) := Nat.mul_le_mul_left _ hy
        _ ≤ x := Nat.mul_div_le x (2 ^ s)
  simp only [Verifier.bitLength, hx, h, ↓reduceIte, e]
  omega

/-- The state `(n, v')` of `bit_length`'s loop before the shift `s` with `B = 2s`. -/
structure Inv (v : BitVec 64) (B : ℕ) (p : BitVec 64 × BitVec 64) : Prop where
  lt : p.2.toNat < 2 ^ B
  len : p.1.toNat + Verifier.bitLength p.2.toNat = Verifier.bitLength v.toNat
  room : p.1.toNat + B ≤ 64

theorem Inv.step {v : BitVec 64} {s : ℕ} {p : BitVec 64 × BitVec 64} (h : Inv v (2 * s) p) :
    Inv v s (bitLengthStep s p) := by
  obtain ⟨n, w⟩ := p
  have hr := h.room
  have hl := h.lt
  have hsh : (w >>> s).toNat = w.toNat / 2 ^ s := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [bitLengthStep]
  split
  · next hne =>
    have hne' : w.toNat / 2 ^ s ≠ 0 := fun h0 ↦ hne (BitVec.eq_of_toNat_eq (by rw [hsh, h0]; rfl))
    have hn : (n + BitVec.ofNat 64 s).toNat = n.toNat + s := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := s), Nat.mod_eq_of_lt]
      · have : n.toNat + s ≤ 64 := by simp only at hr; omega
        exact lt_of_le_of_lt this (by norm_num)
      · exact lt_of_le_of_lt (show s ≤ 64 by simp only at hr; omega) (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · simp only
      rw [hsh, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), ← pow_add]
      simpa [Nat.two_mul] using hl
    · have hlen := h.len
      simp only at hlen ⊢
      rw [hn, hsh, ← hlen, bitLength_div hne']
      omega
    · simp only at hr ⊢
      omega
  · next he =>
    have h0 : w.toNat / 2 ^ s = 0 := by
      rw [← hsh]
      simp only [ne_eq, Decidable.not_not] at he
      rw [he]
      rfl
    refine ⟨?_, h.len, ?_⟩
    · simp only
      by_contra hc
      have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos s)
      omega
    · simp only at hr ⊢
      omega

/-- **`bit_length` is the bit length.** -/
theorem bitLength_eq (v : BitVec 64) : (bitLength v).toNat = Verifier.bitLength v.toNat := by
  have h0 : Inv v (2 * 32) (0#64, v) := ⟨v.isLt, by simp, by simp⟩
  have h6 := (((((h0.step (s := 32)).step (s := 16)).step (s := 8)).step (s := 4)).step
    (s := 2)).step (s := 1)
  simp only [bitLength]
  generalize bitLengthStep 1 (bitLengthStep 2 (bitLengthStep 4 (bitLengthStep 8
    (bitLengthStep 16 (bitLengthStep 32 (0#64, v)))))) = p at h6 ⊢
  obtain ⟨hlt, hlen, hroom⟩ := h6
  by_cases hp : p.2 = 0
  · rw [hp] at hlen
    simp only [hp, ne_eq, not_true_eq_false, ↓reduceIte, BitVec.add_zero]
    simpa [Verifier.bitLength] using hlen
  · have h1 : p.2.toNat = 1 := by
      have : p.2.toNat ≠ 0 := fun h ↦ hp (BitVec.eq_of_toNat_eq (by simpa using h))
      simp at hlt
      omega
    rw [h1] at hlen
    simp only [hp, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]
    · simpa [Verifier.bitLength] using hlen
    · simp only [BitVec.toNat_ofNat]
      exact lt_of_le_of_lt (show p.1.toNat + 1 ≤ 64 by simp at hroom; omega) (by norm_num)

theorem toNat_satSub (a b : BitVec 64) : (satSub a b).toNat = a.toNat - b.toNat := by
  unfold satSub
  split
  · next h => exact BitVec.toNat_sub_of_le h
  · next h =>
    rw [BitVec.le_def] at h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega

/-- `log2_ceil` is the model's `log2Ceil`. -/
theorem log2Ceil_eq (v : BitVec 64) : (log2Ceil v).toNat = Verifier.log2Ceil v.toNat := by
  rw [log2Ceil, bitLength_eq, toNat_satSub]
  rfl

/-- `grinding_bits` is the model's `grindingBits`. -/
theorem grindingBits_eq (v : BitVec 64) :
    (grindingBits v).toNat = NativeVm.Model.grindingBits v.toNat := by
  have e1 : (1#64).toNat = 1 := rfl
  have e3 : (3#64).toNat = 3 := rfl
  rw [grindingBits, toNat_satSub, bitLength_eq, toNat_satSub, e1, e3]
  simp only [NativeVm.Model.grindingBits, Compile.grindingBits, Verifier.bitLength,
    Compile.securityBits]
  by_cases h : v.toNat ≤ 1
  · rw [ite_eq_left (show v.toNat - 1 = 0 by omega), ite_eq_left h]
  · rw [ite_eq_right (show ¬ v.toNat - 1 = 0 by omega), ite_eq_right h]

/-- `log2_strict` is the model's `log2Strict`. -/
theorem log2Strict_eq (v : BitVec 64) :
    (log2Strict v).map BitVec.toNat = Verifier.log2Strict v.toNat := by
  by_cases hv : v = 0
  · subst hv
    simp [log2Strict, Verifier.log2Strict]
  · have hv' : 0 < v.toNat := by
      rcases Nat.eq_zero_or_pos v.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv
      · exact h
    have hs : (v - 1#64).toNat = v.toNat - 1 :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hv')
    have hc : v &&& (v - 1#64) = 0 ↔ v.toNat &&& (v.toNat - 1) = 0 := by
      rw [← BitVec.toNat_inj, BitVec.toNat_and, hs]
      simp
    have hb : 0 < Verifier.bitLength v.toNat := by
      rw [Verifier.bitLength, ite_eq_right (by omega)]
      omega
    have hl : (bitLength v - 1#64).toNat = Verifier.bitLength v.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, bitLength_eq]; exact hb), bitLength_eq]
      simp
    simp only [log2Strict, Verifier.log2Strict, hc, hv, hv', ne_eq, not_false_eq_true, true_and]
    split_ifs <;> simp [hl]

end

end NativeRustcVm.Field
