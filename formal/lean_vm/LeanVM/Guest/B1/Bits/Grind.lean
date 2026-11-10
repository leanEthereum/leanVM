/-
  LeanVM.Guest.B1.Bits.Grind

  B1 for `grind_check`: the low bits of a challenge's first limb are zero.
-/

module

public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Bits.Templates

/-!
# `grind_check` (lean_ethereum.py:912-939 at 40f877dc, TRIAGE #21)

`grind_check(word, 17)` splits the word (`canonicalLimbsT (.n 0) 1`: canonical, its low limb at
`1`), hints the low limb's 64 bits into frame cells `5 .. 68`, pins bits `63` down to `17` by
booleanity, reads them by Horner's rule from the top bit by the one constant `X` (`gcBlk`, the
running value at `gcAcc`), and asserts the result times `X^17` is the low limb: its low 17 bits
are zero.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The running value after Horner step `j` (bit `63 - j`). -/
def gcAcc : ℕ → ℕ
  | 0 => 68
  | j + 1 => 71 + 3 * j

/-- Horner step `j`, bit `63 - j` at cell `68 - j`: booleanity, then (past the first) the running
value times `X`, plus the bit. -/
def gcBlk : ℕ → List Stmt
  | 0 => [.atom (.mul (.n 68) (.n 68) (.n 68))]
  | j + 1 => [.atom (.mul (.n (67 - j)) (.n (67 - j)) (.n (67 - j))),
      .atom (.const (.n (69 + 3 * j)) (word 2 0 0)),
      .atom (.mul (.n (70 + 3 * j)) (.n (gcAcc j)) (.n (69 + 3 * j))),
      .atom (.add (.n (71 + 3 * j)) (.n (70 + 3 * j)) (.n (67 - j)))]

/-- The 64 frame cells of the lane's bits. -/
def gcRun : List V := (List.range 64).map fun i => .n (5 + i)

/-- The expansion of `grind_check__L17`. -/
def gcBody : List Stmt :=
  canonicalLimbsT (.n 0) 1 ++ [.atom (.hint (.bits (.n 1) 0 64 (.stack gcRun)))] ++
  ((List.range 47).map gcBlk).flatten ++
  [.atom (.const (.n 207) (word (2 ^ 17) 0 0)), .atom (.mul (.n 208) (.n 206) (.n 207)),
    .atom (.assertEq (.n 208) (.n 1)), .ret []]

theorem grind_check_body : Fn.body Data.core424 = gcBody := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem find_grind_check : coreProgram.find? "grind_check__L17" = some Data.core424 :=
  Program.find?_of_indexOf? (j := 424) (by decide +kernel) rfl

/-- What Horner step `j` asks of a valuation. -/
def GcOk (σ : Val) : ℕ → Prop
  | 0 => σ (.n 68) = σ (.n 68) * σ (.n 68)
  | j + 1 => σ (.n (67 - j)) = σ (.n (67 - j)) * σ (.n (67 - j)) ∧
      σ (.n (69 + 3 * j)) = word 2 0 0 ∧
      σ (.n (70 + 3 * j)) = σ (.n (gcAcc j)) * σ (.n (69 + 3 * j)) ∧
      σ (.n (71 + 3 * j)) = σ (.n (70 + 3 * j)) + σ (.n (67 - j))

theorem holds_gcBlk {C : CallRel} {rd : Reader} {σ : Val} (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gcBlk j) True kret ↔ GcOk σ j := by
  cases j <;> simp only [gcBlk, GcOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

theorem word_coordBasis {i : ℕ} (h : i < 64) : word (2 ^ i) 0 0 = coordBasis i := by
  rw [word_eOfNat, coordBasis_of_lt h]

/-- Basis vectors multiply without reduction while the degree stays inside a limb. -/
theorem coordBasis_mul {i j : ℕ} (hi : i < 192) (h : i % 64 + j < 64) :
    coordBasis i * coordBasis j = coordBasis (i + j) := by
  rw [coordBasis_of_lt (show j < 64 by omega), coordBasis_mul_eOfNat hi (by
    rw [← Nat.pow_add]; exact Nat.pow_lt_pow_right (by decide) h), ← Nat.pow_add]; rfl

/-- **Horner's rule**: after step `n`, the running value shifted to bit `63 - n` is the bits
`63 - n .. 63` at their places. -/
theorem gc_horner {σ : Val} : ∀ n, n < 47 → (∀ j < n + 1, GcOk σ j) →
    σ (.n (gcAcc n)) * coordBasis (63 - n) =
      ∑ i ∈ Finset.range (n + 1), σ (.n (68 - i)) * coordBasis (63 - i)
  | 0, _, _ => by rw [Finset.sum_range_one]; rfl
  | n + 1, hn, h => by
    obtain ⟨-, e69, e70, e71⟩ := h (n + 1) (by omega)
    have ih := gc_horner n (by omega) fun j hj => h j (by omega)
    have h2 : word 2 0 0 = coordBasis 1 := by rw [← word_coordBasis (by norm_num), pow_one]
    have hm : coordBasis 1 * coordBasis (63 - (n + 1)) = coordBasis (63 - n) := by
      rw [coordBasis_mul (by norm_num) (by omega)]; congr 1; omega
    rw [Finset.sum_range_succ, ← ih, gcAcc, e71, e70, e69, h2, add_mul, mul_assoc, hm,
      show 68 - (n + 1) = 67 - n by omega]

/-- The bits `17 .. 63`, Horner's rule finished and shifted by `X^17`. -/
theorem gc_value {σ : Val} (h : ∀ j < 47, GcOk σ j) :
    σ (.n 206) * coordBasis 17 =
      ∑ j ∈ Finset.range 47, σ (.n (22 + j)) * coordBasis (17 + j) := by
  have := gc_horner 46 (by omega) h
  rw [show gcAcc 46 = 206 from rfl, show 63 - 46 = 17 from rfl] at this
  rw [this, ← Finset.sum_range_reflect]
  exact Finset.sum_congr rfl fun i hi => by
    have := Finset.mem_range.mp hi
    rw [show 68 - (47 - 1 - i) = 22 + i by omega, show 63 - (47 - 1 - i) = 17 + i by omega]

/-- Horner's honest running value: the lane's bits from `63 - j` up, `L >>> (63 - j)`. -/
def gcH (w : E) : ℕ → E
  | 0 => bitE ((kToNat (w.limb 0)).testBit 63)
  | j + 1 => gcH w j * word 2 0 0 + bitE ((kToNat (w.limb 0)).testBit (62 - j))

/-- The honest values of `grind_check__L17` on the word `w`, `L` its low limb's integer. -/
def gcVals (w : E) (k : ℕ) : E :=
  let L := kToNat (w.limb 0)
  if k = 0 then w else if k = 1 then ofK (w.limb 0) else if k = 2 then w + ofK (w.limb 0)
  else if k = 3 then word 1 0 1 else if k = 4 then ofK (w.limb 1)
  else if k < 69 then bitE (L.testBit (k - 5))
  else if k < 207 then
    (if (k - 69) % 3 = 0 then word 2 0 0
    else if (k - 69) % 3 = 1 then gcH w ((k - 69) / 3) * word 2 0 0
    else gcH w ((k - 69) / 3 + 1))
  else if k = 207 then word (2 ^ 17) 0 0 else gcH w 46 * word (2 ^ 17) 0 0

theorem gv_bit (w : E) {k : ℕ} (h1 : 5 ≤ k) (h2 : k < 69) :
    gcVals w k = bitE ((kToNat (w.limb 0)).testBit (k - 5)) := by
  unfold gcVals; split_ifs <;> first | omega | rfl

theorem gv_c (w : E) {j : ℕ} (hj : j < 46) : gcVals w (69 + 3 * j) = word 2 0 0 := by
  unfold gcVals
  split_ifs <;> first | omega | rfl

theorem gv_m (w : E) {j : ℕ} (hj : j < 46) :
    gcVals w (70 + 3 * j) = gcH w j * word 2 0 0 := by
  unfold gcVals
  split_ifs <;> first | omega | (rw [show (70 + 3 * j - 69) / 3 = j by omega])

theorem gv_acc (w : E) {j : ℕ} (hj : j < 47) : gcVals w (gcAcc j) = gcH w j := by
  cases j with
  | zero => rw [show gcAcc 0 = 68 from rfl, gv_bit w (by omega) (by omega)]; rfl
  | succ j =>
    show gcVals w (71 + 3 * j) = _
    unfold gcVals
    split_ifs <;> first | omega | (rw [show (71 + 3 * j - 69) / 3 = j by omega])

/-- **`grind_check`'s core IR is its meaning.** -/
theorem grind_check_holds : grind_check_Spec := by
  intro rd args rets
  rw [rel_iff_sem find_grind_check, grind_check_body, show Fn.params Data.core424 = [.n 0] from rfl,
    gcBody]
  simp only [holdsList_append, holds_canonicalLimbsT,
    holdsList_range_flatten 47 gcBlk (fun j => by cases j <;> rfl), holds_gcBlk, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  constructor
  · rintro ⟨σ, hp, ⟨hc, h1, -⟩, hbits, h207, h208, ha, hret⟩
    subst hp
    refine ⟨hret.symm, hc, ?_⟩
    have hsum := gc_value hbits
    have h17 : σ (.n 207) = coordBasis 17 := h207.trans (word_coordBasis (by norm_num))
    rw [← h17, ← h208, e_add_eq_zero_iff.mp ha, h1] at hsum
    have hb : ∀ m < 47, σ (.n (22 + m)) * σ (.n (22 + m)) = σ (.n (22 + m)) := by
      intro m hm
      by_cases h46 : m = 46
      · subst h46; exact (hbits 0 (by omega)).symm
      · have := hbits (45 - m + 1) (by omega)
        rw [show 22 + m = 67 - (45 - m) by omega]
        exact this.1.symm
    obtain ⟨N, hN, hx, -⟩ := bits_of_reconstruct (s := 17) hb hsum.symm
    have hm : 2 ^ 17 * N < 2 ^ 64 := by
      calc 2 ^ 17 * N < 2 ^ 17 * 2 ^ 47 := Nat.mul_lt_mul_of_pos_left hN (by positivity)
        _ = 2 ^ 64 := by norm_num
    rw [eOfNat192_of_lt hm, eOfNat] at hx
    have hl := ofK_injective hx
    show kToNat ((σ (.n 0)).limb 0) % 2 ^ 17 = 0
    rw [hl, kToNat_ofBits, Nat.mod_eq_of_lt hm, Nat.mul_mod_right]
  · intro hm
    obtain ⟨w, rfl⟩ : ∃ w, args = [w] := by
      match args, hm with
      | [a], _ => exact ⟨a, rfl⟩
    obtain ⟨rfl, hc, hlow⟩ := hm
    change kToNat (w.limb 0) % 2 ^ 17 = 0 at hlow
    let σ : Val := fun x => gcVals w x.idx
    have ev : ∀ k, σ (.n k) = gcVals w k := fun _ => rfl
    have hL : kToNat (w.limb 0) < 2 ^ 64 := by
      have := (w.limb 0).toBitVec.isLt; exact this
    set L := kToNat (w.limb 0) with hLdef
    have hLN : L = 2 ^ 17 * (L / 2 ^ 17) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow)).symm
    have hN : L / 2 ^ 17 < 2 ^ 47 := by omega
    have hblk : ∀ j < 47, GcOk σ j := fun j hj => by
      cases j with
      | zero =>
        show gcVals w 68 = gcVals w 68 * gcVals w 68
        rw [gv_bit w (by omega) (by omega)]; exact (bitE_mul_self _).symm
      | succ j =>
        refine ⟨?_, by rw [ev, gv_c w (by omega)], ?_, ?_⟩
        · rw [ev, gv_bit w (by omega) (by omega)]; exact (bitE_mul_self _).symm
        · rw [ev, ev, ev, gv_m w (by omega), gv_c w (by omega), gv_acc w (by omega)]
        · show gcVals w (71 + 3 * j) = gcVals w (70 + 3 * j) + gcVals w (67 - j)
          rw [gv_m w (by omega), gv_bit w (k := 67 - j) (by omega) (by omega),
            show (71 + 3 * j) = gcAcc (j + 1) from rfl, gv_acc w (by omega), gcH,
            show 67 - j - 5 = 62 - j by omega]
    refine ⟨σ, rfl, ⟨by simpa [ev, gcVals] using hc, by simp [ev, gcVals], by simp [ev, gcVals],
      by simp [ev, gcVals], by simp [ev, gcVals]⟩, hblk, by simp [ev, gcVals], ?_, ?_, rfl⟩
    · show gcVals w 208 = gcVals w 206 * gcVals w 207
      rw [show (206 : ℕ) = gcAcc 46 from rfl, gv_acc w (by omega)]
      simp [gcVals]
    · have hv := gc_value hblk
      have h207 : σ (.n 207) = coordBasis 17 := by
        rw [ev, ← word_coordBasis (by norm_num)]; simp [gcVals]
      have h208 : σ (.n 208) = σ (.n 206) * σ (.n 207) := by
        show gcVals w 208 = gcVals w 206 * gcVals w 207
        rw [show (206 : ℕ) = gcAcc 46 from rfl, gv_acc w (by omega)]
        simp [gcVals]
      rw [h208, h207, hv, e_add_eq_zero_iff]
      have hb : ∀ j ∈ Finset.range 47, σ (.n (22 + j)) * coordBasis (17 + j) =
          bitE ((L / 2 ^ 17).testBit j) * coordBasis (17 + j) := fun j hj => by
        rw [ev, gv_bit w (by omega) (by have := Finset.mem_range.mp hj; omega),
          Nat.testBit_div_two_pow, show 22 + j - 5 = j + 17 by omega]
      rw [Finset.sum_congr rfl hb, reconstruct_bits 17 hN, ← hLN, eOfNat192_of_lt hL]
      show eOfNat L = gcVals w 1
      rw [show gcVals w 1 = ofK (w.limb 0) by simp [gcVals], eOfNat, hLdef, ofBits_kToNat]

end
end LeanVM.Guest.B1
