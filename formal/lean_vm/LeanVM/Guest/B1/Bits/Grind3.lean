/-
  LeanVM.Guest.B1.Bits.Grind3

  B1 for `grind_check__L3`: the low three bits of a challenge's first limb are zero.
-/

module

public import LeanVM.Guest.B1.Bits.Grind

/-!
# `grind_check__L3` (the folds' proof of work)

`grind_check(word, 3)`, as `grind_check__L17` (`Bits/Grind.lean`) with the Horner steps pinning
bits `63` down to `3`: its low three bits are zero (`grind_check3_holds`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The expansion of `grind_check__L3`. -/
def gcBody3 : List Stmt :=
  canonicalLimbsT (.n 0) 1 ++ [.atom (.hint (.bits (.n 1) 0 64 (.stack gcRun)))] ++
  ((List.range 61).map gcBlk).flatten ++
  [.atom (.const (.n 249) (word (2 ^ 3) 0 0)), .atom (.mul (.n 250) (.n 248) (.n 249)),
    .atom (.assertEq (.n 250) (.n 1)), .ret []]

theorem grind_check3_body : Fn.body Data.core1600 = gcBody3 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem find_grind_check3 : coreProgram.find? "grind_check__L3" = some Data.core1600 :=
  Program.find?_of_indexOf? (j := 1600) (by decide +kernel) rfl

/-- **Horner's rule**: after step `n`, the running value shifted to bit `63 - n` is the bits
`63 - n .. 63` at their places. -/
theorem gc_horner3 {σ : Val} : ∀ n, n < 61 → (∀ j < n + 1, GcOk σ j) →
    σ (.n (gcAcc n)) * coordBasis (63 - n) =
      ∑ i ∈ Finset.range (n + 1), σ (.n (68 - i)) * coordBasis (63 - i)
  | 0, _, _ => by rw [Finset.sum_range_one]; rfl
  | n + 1, hn, h => by
    obtain ⟨-, e69, e70, e71⟩ := h (n + 1) (by omega)
    have ih := gc_horner3 n (by omega) fun j hj => h j (by omega)
    have h2 : word 2 0 0 = coordBasis 1 := by rw [← word_coordBasis (by norm_num), pow_one]
    have hm : coordBasis 1 * coordBasis (63 - (n + 1)) = coordBasis (63 - n) := by
      rw [coordBasis_mul (by norm_num) (by omega)]; congr 1; omega
    rw [Finset.sum_range_succ, ← ih, gcAcc, e71, e70, e69, h2, add_mul, mul_assoc, hm,
      show 68 - (n + 1) = 67 - n by omega]

/-- The bits `3 .. 63`, Horner's rule finished and shifted by `X^3`. -/
theorem gc_value3 {σ : Val} (h : ∀ j < 61, GcOk σ j) :
    σ (.n 248) * coordBasis 3 =
      ∑ j ∈ Finset.range 61, σ (.n (8 + j)) * coordBasis (3 + j) := by
  have := gc_horner3 60 (by omega) h
  rw [show gcAcc 60 = 248 from rfl, show 63 - 60 = 3 from rfl] at this
  rw [this, ← Finset.sum_range_reflect]
  exact Finset.sum_congr rfl fun i hi => by
    have := Finset.mem_range.mp hi
    rw [show 68 - (61 - 1 - i) = 8 + i by omega, show 63 - (61 - 1 - i) = 3 + i by omega]

/-- The honest values of `grind_check__L3` on the word `w`, `L` its low limb's integer. -/
def gcVals3 (w : E) (k : ℕ) : E :=
  let L := kToNat (w.limb 0)
  if k = 0 then w else if k = 1 then ofK (w.limb 0) else if k = 2 then w + ofK (w.limb 0)
  else if k = 3 then word 1 0 1 else if k = 4 then ofK (w.limb 1)
  else if k < 69 then bitE (L.testBit (k - 5))
  else if k < 249 then
    (if (k - 69) % 3 = 0 then word 2 0 0
    else if (k - 69) % 3 = 1 then gcH w ((k - 69) / 3) * word 2 0 0
    else gcH w ((k - 69) / 3 + 1))
  else if k = 249 then word (2 ^ 3) 0 0 else gcH w 60 * word (2 ^ 3) 0 0

theorem gv3_bit (w : E) {k : ℕ} (h1 : 5 ≤ k) (h2 : k < 69) :
    gcVals3 w k = bitE ((kToNat (w.limb 0)).testBit (k - 5)) := by
  unfold gcVals3; split_ifs <;> first | omega | rfl

theorem gv3_c (w : E) {j : ℕ} (hj : j < 60) : gcVals3 w (69 + 3 * j) = word 2 0 0 := by
  unfold gcVals3
  split_ifs <;> first | omega | rfl

theorem gv3_m (w : E) {j : ℕ} (hj : j < 60) :
    gcVals3 w (70 + 3 * j) = gcH w j * word 2 0 0 := by
  unfold gcVals3
  split_ifs <;> first | omega | (rw [show (70 + 3 * j - 69) / 3 = j by omega])

theorem gv3_acc (w : E) {j : ℕ} (hj : j < 61) : gcVals3 w (gcAcc j) = gcH w j := by
  cases j with
  | zero => rw [show gcAcc 0 = 68 from rfl, gv3_bit w (by omega) (by omega)]; rfl
  | succ j =>
    show gcVals3 w (71 + 3 * j) = _
    unfold gcVals3
    split_ifs <;> first | omega | (rw [show (71 + 3 * j - 69) / 3 = j by omega])

/-- **`grind_check`'s core IR is its meaning.** -/
theorem grind_check3_holds : ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "grind_check__L3" args rets ↔ MeaningGrindCheck 3 args rets := by
  intro rd args rets
  rw [rel_iff_sem find_grind_check3, grind_check3_body, show Fn.params Data.core1600 = [.n 0] from rfl,
    gcBody3]
  simp only [holdsList_append, holds_canonicalLimbsT,
    holdsList_range_flatten 61 gcBlk (fun j => by cases j <;> rfl), holds_gcBlk, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  constructor
  · rintro ⟨σ, hp, ⟨hc, h1, -⟩, hbits, h249, h250, ha, hret⟩
    subst hp
    refine ⟨hret.symm, hc, ?_⟩
    have hsum := gc_value3 hbits
    have h17 : σ (.n 249) = coordBasis 3 := h249.trans (word_coordBasis (by norm_num))
    rw [← h17, ← h250, e_add_eq_zero_iff.mp ha, h1] at hsum
    have hb : ∀ m < 61, σ (.n (8 + m)) * σ (.n (8 + m)) = σ (.n (8 + m)) := by
      intro m hm
      by_cases h46 : m = 60
      · subst h46; exact (hbits 0 (by omega)).symm
      · have := hbits (59 - m + 1) (by omega)
        rw [show 8 + m = 67 - (59 - m) by omega]
        exact this.1.symm
    obtain ⟨N, hN, hx, -⟩ := bits_of_reconstruct (s := 3) hb hsum.symm
    have hm : 2 ^ 3 * N < 2 ^ 64 := by
      calc 2 ^ 3 * N < 2 ^ 3 * 2 ^ 61 := Nat.mul_lt_mul_of_pos_left hN (by positivity)
        _ = 2 ^ 64 := by norm_num
    rw [eOfNat192_of_lt hm, eOfNat] at hx
    have hl := ofK_injective hx
    show kToNat ((σ (.n 0)).limb 0) % 2 ^ 3 = 0
    rw [hl, kToNat_ofBits, Nat.mod_eq_of_lt hm, Nat.mul_mod_right]
  · intro hm
    obtain ⟨w, rfl⟩ : ∃ w, args = [w] := by
      match args, hm with
      | [a], _ => exact ⟨a, rfl⟩
    obtain ⟨rfl, hc, hlow⟩ := hm
    change kToNat (w.limb 0) % 2 ^ 3 = 0 at hlow
    let σ : Val := fun x => gcVals3 w x.idx
    have ev : ∀ k, σ (.n k) = gcVals3 w k := fun _ => rfl
    have hL : kToNat (w.limb 0) < 2 ^ 64 := by
      have := (w.limb 0).toBitVec.isLt; exact this
    set L := kToNat (w.limb 0) with hLdef
    have hLN : L = 2 ^ 3 * (L / 2 ^ 3) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow)).symm
    have hN : L / 2 ^ 3 < 2 ^ 61 := by omega
    have hblk : ∀ j < 61, GcOk σ j := fun j hj => by
      cases j with
      | zero =>
        show gcVals3 w 68 = gcVals3 w 68 * gcVals3 w 68
        rw [gv3_bit w (by omega) (by omega)]; exact (bitE_mul_self _).symm
      | succ j =>
        refine ⟨?_, by rw [ev, gv3_c w (by omega)], ?_, ?_⟩
        · rw [ev, gv3_bit w (by omega) (by omega)]; exact (bitE_mul_self _).symm
        · rw [ev, ev, ev, gv3_m w (by omega), gv3_c w (by omega), gv3_acc w (by omega)]
        · show gcVals3 w (71 + 3 * j) = gcVals3 w (70 + 3 * j) + gcVals3 w (67 - j)
          rw [gv3_m w (by omega), gv3_bit w (k := 67 - j) (by omega) (by omega),
            show (71 + 3 * j) = gcAcc (j + 1) from rfl, gv3_acc w (by omega), gcH,
            show 67 - j - 5 = 62 - j by omega]
    refine ⟨σ, rfl, ⟨by simpa [ev, gcVals3] using hc, by simp [ev, gcVals3], by simp [ev, gcVals3],
      by simp [ev, gcVals3], by simp [ev, gcVals3]⟩, hblk, by simp [ev, gcVals3], ?_, ?_, rfl⟩
    · show gcVals3 w 250 = gcVals3 w 248 * gcVals3 w 249
      rw [show (248 : ℕ) = gcAcc 60 from rfl, gv3_acc w (by omega)]
      simp [gcVals3]
    · have hv := gc_value3 hblk
      have h249 : σ (.n 249) = coordBasis 3 := by
        rw [ev, ← word_coordBasis (by norm_num)]; simp [gcVals3]
      have h250 : σ (.n 250) = σ (.n 248) * σ (.n 249) := by
        show gcVals3 w 250 = gcVals3 w 248 * gcVals3 w 249
        rw [show (248 : ℕ) = gcAcc 60 from rfl, gv3_acc w (by omega)]
        simp [gcVals3]
      rw [h250, h249, hv, e_add_eq_zero_iff]
      have hb : ∀ j ∈ Finset.range 61, σ (.n (8 + j)) * coordBasis (3 + j) =
          bitE ((L / 2 ^ 3).testBit j) * coordBasis (3 + j) := fun j hj => by
        rw [ev, gv3_bit w (by omega) (by have := Finset.mem_range.mp hj; omega),
          Nat.testBit_div_two_pow, show 8 + j - 5 = j + 3 by omega]
      rw [Finset.sum_congr rfl hb, reconstruct_bits 3 hN, ← hLN, eOfNat192_of_lt hL]
      show eOfNat L = gcVals3 w 1
      rw [show gcVals3 w 1 = ofK (w.limb 0) by simp [gcVals3], eOfNat, hLdef, ofBits_kToNat]

end
end LeanVM.Guest.B1
