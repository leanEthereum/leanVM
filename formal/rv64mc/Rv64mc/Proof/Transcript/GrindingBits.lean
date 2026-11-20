/-
  Rv64mc.Proof.Transcript.GrindingBits

  `grinding_bits` keeps its contract (`Spec.Transcript.GrindingBits.spec`). The code tests `numerator <= 1`
  (`small_iff`), forms `numerator - 1` on two words (`pred_split`), and counts the leading zeros of its high word,
  or of its low word plus `64`, in software (`Model.smear`, `Model.popc`: their values are
  `Model.Extra.GrindingBits`'s); the count is the bit length's complement (`bitLength_hi`), and the saturating
  `125 - clz` is `fin_eq`. Each path's goal is restated over `Model.smear`/`Model.popc` by `change`.
-/

import Rv64mc.Spec.Transcript.GrindingBits
import Rv64mc.Model.Extra.GrindingBits
import Rv64mc.Gen.Tmpl.Verifier.Transcript.GrindingBits
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.GrindingBits

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript.GrindingBits
open Rv64mc.Gen.Verifier.Transcript.GrindingBits (Link tmpl)

theorem ult_eval (a b : Word) : BinOp.ult.eval a b = if a.toNat < b.toNat then 1#64 else 0#64 := by
  simp [BinOp.eval, BitVec.ult]

/-- The saturating `125 - c` the code ends with, for every count the popcounts give. -/
theorem fin_eq {c : Nat} (hc : c ≤ 128) :
    0#64 - BinOp.ult.eval (125#64 - BitVec.ofNat 64 c) 126#64 &&& (125#64 - BitVec.ofNat 64 c) =
      BitVec.ofNat 64 (125 - c) := by
  interval_cases c <;> decide +kernel

/-- `grinding_bits` on the numerator's two words, as a number. -/
theorem grinding_eq (hi lo : Word) :
    Model.grindingBitsRust (hi ++ lo) = if hi.toNat * 2 ^ 64 + lo.toNat ≤ 1 then 0
      else LeanVM.Protocol.Verifier.bitLength (hi.toNat * 2 ^ 64 + lo.toNat - 1) - 3 := by
  have ht := BitVec.toNat_append_eq_mul_add hi lo
  have hle : hi ++ lo ≤ 1#128 ↔ hi.toNat * 2 ^ 64 + lo.toNat ≤ 1 := by
    rw [BitVec.le_def, ht]; simp
  by_cases h : hi.toNat * 2 ^ 64 + lo.toNat ≤ 1
  · simp only [Model.grindingBitsRust, hle.2 h, h, ↓reduceIte]
  · have h1 : ¬ hi ++ lo ≤ 1#128 := fun h' => h (hle.1 h')
    have hsub : ((hi ++ lo) - 1#128).toNat = hi.toNat * 2 ^ 64 + lo.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ht]; simp; omega), ht]; simp
    simp only [Model.grindingBitsRust, h1, h, ↓reduceIte, Model.sub_clz_eq_bitLength, hsub]

/-- The numerator less one, as the code computes its words. -/
theorem pred_split {hi lo : Word} (h : ¬ hi.toNat * 2 ^ 64 + lo.toNat ≤ 1) :
    (hi - BinOp.ult.eval lo 1#64).toNat * 2 ^ 64 + (lo + 18446744073709551615#64).toNat =
      hi.toNat * 2 ^ 64 + lo.toNat - 1 := by
  rw [ult_eval]
  have hlo := lo.isLt
  have e1 : (1#64 : Word).toNat = 1 := rfl
  rw [e1]
  by_cases hl : lo.toNat = 0
  · have hh : 1 ≤ hi.toNat := by
      by_contra hc; apply h; rw [hl, show hi.toNat = 0 by omega]; simp
    have hadd : (lo + 18446744073709551615#64).toNat = 2 ^ 64 - 1 := by
      rw [BitVec.toNat_add, hl]; rfl
    rw [ite_eq_left (by omega), BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e1]; exact hh), e1, hadd, hl,
      Nat.sub_mul, Nat.one_mul]
    have : 2 ^ 64 ≤ hi.toNat * 2 ^ 64 := Nat.le_mul_of_pos_left _ hh
    omega
  · have hadd : (lo + 18446744073709551615#64).toNat = lo.toNat - 1 := by
      rw [BitVec.toNat_add, show (18446744073709551615#64 : Word).toNat = 2 ^ 64 - 1 from rfl]
      rw [show lo.toNat + (2 ^ 64 - 1) = (lo.toNat - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_right (by omega), BitVec.sub_zero, hadd]
    omega

/-- The bit length of a two-word number with a nonzero high word. -/
theorem bitLength_hi {h l : Nat} (hh : h ≠ 0) (hl : l < 2 ^ 64) :
    LeanVM.Protocol.Verifier.bitLength (h * 2 ^ 64 + l) = 64 + LeanVM.Protocol.Verifier.bitLength h := by
  generalize hB : LeanVM.Protocol.Verifier.bitLength h = B
  generalize hP : (2 : Nat) ^ 64 = P at hl ⊢
  have hP1 : 0 < P := by rw [← hP]; exact Nat.two_pow_pos 64
  have hb : 0 < B := by rw [← hB]; exact Model.lt_bitLength_iff.2 (by simp; omega)
  have h1 : h < 2 ^ B := Model.bitLength_le_iff.1 (by rw [hB])
  have h2 : 2 ^ (B - 1) ≤ h := Model.lt_bitLength_iff.1 (by rw [hB]; omega)
  apply Nat.le_antisymm
  · rw [Model.bitLength_le_iff, Nat.pow_add, hP, Nat.mul_comm P]
    have : (h + 1) * P ≤ 2 ^ B * P := Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  · have : 2 ^ (B - 1) * P ≤ h * P := Nat.mul_le_mul_right _ h2
    have e : 64 + B = (64 + (B - 1)) + 1 := by omega
    rw [e, Nat.succ_le_iff, Model.lt_bitLength_iff, Nat.pow_add, hP, Nat.mul_comm P]
    omega

/-- The first test: the numerator is at most `1` exactly where the high word is `0` and the low below `2`. -/
theorem small_iff (hi lo : Word) :
    BinOp.ult.eval hi 1#64 &&& BinOp.ult.eval lo 2#64 = 0#64 ↔ ¬ hi.toNat * 2 ^ 64 + lo.toNat ≤ 1 := by
  rw [ult_eval, ult_eval, show (1#64 : Word).toNat = 1 from rfl, show (2#64 : Word).toNat = 2 from rfl]
  have : hi.toNat * 2 ^ 64 + lo.toNat ≤ 1 ↔ hi.toNat = 0 ∧ lo.toNat < 2 := by
    constructor
    · intro h
      have : hi.toNat = 0 := by
        by_contra hc; have := Nat.le_mul_of_pos_left (2 ^ 64) (Nat.pos_of_ne_zero hc); omega
      exact ⟨this, by omega⟩
    · rintro ⟨h1, h2⟩; rw [h1]; omega
  rw [this]
  by_cases h1 : hi.toNat < 1 <;> by_cases h2 : lo.toNat < 2 <;> simp [h1, h2] <;> omega

/-- **`grinding_bits` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (_hL : L.WF p)
    {need : Nat} : spec env p i need := by
  rv_auto hp
  · have hN := (small_iff _ _).1 hc_1
    have hp := pred_split hN
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.1 hc
    rw [h1, h2] at hp
    simp at hp
    omega
  · change 0#64 - BinOp.ult.eval (125#64 - Model.popc (Model.smear (regs .x11 - BinOp.ult.eval (regs .x10) 1#64) ^^^
      18446744073709551615#64)) 126#64 &&& (125#64 - Model.popc (Model.smear (regs .x11 -
      BinOp.ult.eval (regs .x10) 1#64) ^^^ 18446744073709551615#64)) = _
    have hN := (small_iff _ _).1 hc_1
    have hne : (regs .x11 - BinOp.ult.eval (regs .x10) 1#64).toNat ≠ 0 := fun h =>
      hc (BitVec.eq_of_toNat_eq (by simpa using h))
    have hB := Model.bitLength_le_64 (regs .x11 - BinOp.ult.eval (regs .x10) 1#64)
    rw [Model.smear_eq, Model.popc_eq hB, fin_eq (by omega), grinding_eq, ite_eq_right hN, ← pred_split hN,
      bitLength_hi hne (BitVec.isLt _)]
    congr 1
    omega
  · change 0#64 - BinOp.ult.eval (125#64 - (Model.popc (Model.smear (regs .x10 + 18446744073709551615#64) ^^^
      18446744073709551615#64) + 64#64)) 126#64 &&& (125#64 - (Model.popc (Model.smear (regs .x10 +
      18446744073709551615#64) ^^^ 18446744073709551615#64) + 64#64)) = _
    have hN := (small_iff _ _).1 hc_1
    have hB := Model.bitLength_le_64 (regs .x10 + 18446744073709551615#64)
    rw [Model.smear_eq, Model.popc_eq hB, ← BitVec.ofNat_add, fin_eq (by omega), grinding_eq, ite_eq_right hN,
      ← pred_split hN, hc]
    rw [show (0#64 : Word).toNat * 2 ^ 64 = 0 from rfl, Nat.zero_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [grinding_eq, ite_eq_left (Decidable.of_not_not fun h => hc ((small_iff _ _).2 h))]

end Rv64mc.Proof.Transcript.GrindingBits
