/-
  LeanVM.Guest.B1.Tables.VtPlVals

  `verify_tables`' placed form: the padding weights' and the selectors' values, the hints' sizes
  and pointers.
-/

module

public import LeanVM.Guest.B1.Tables.VtPlDec

/-!
# Values on a valuation of the body

The padding weights' selectors, row counts and results (`vt_pad_vals`), a selector's frame's
words (`vt_sel_facts2`), and the hints' sizes: constants, `g^34` for the selectors' bits, and the
sum-check's `4(n + 1)`, `n + 1`, `n + 1` (`vtSzSrc`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

section
variable {rd : Reader} {σ : Val}

/-- A selector's frame's words. -/
theorem vt_sel_facts2 (h : VtHolds rd σ) {i : ℕ} (hi : i < 65) :
    σ (.n (selVal.getD i 0 + 10)) = σ (.n 5) * σ (.n (selVal.getD i 0)) ∧
      σ (.n (selVal.getD i 0 + 11)) = word 17179869184 0 0 ∧
      σ (.n (selVal.getD i 0 + 14)) = σ (.n (selVal.getD i 0 + 12)) * σ (.n (selVal.getD i 0)) ∧
      σ (.n (selVal.getD i 0 + 20)) = 1 + σ (.n (selVal.getD i 0 + 5)) ∧
      σ (.n (selVal.getD i 0 + 21)) = 1 := by
  obtain ⟨kr, hb⟩ := h.slice _ _ (sel_blocks i hi)
  simp only [selT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and, word_one,
    List.map_cons, List.map_nil] at hb
  obtain ⟨-, -, -, -, -, -, m10, c11, -, m14, -, -, -, -, c19, a20, c21, -, -, -, -, -, -, -, -⟩ := hb
  exact ⟨m10, c11, m14, by rw [a20, c19], c21⟩

/-- **The padding weights**: table `t`'s selector `g^τ`, row count and results. -/
theorem vt_pad_vals (h : VtHolds rd σ) {rowsN : List ℕ} {point : List E} {logMem dims rows z : ℕ}
    (hrl : rowsN.length = 6) (hτ29 : ∀ m ∈ rowsN, log2Ceil m < 29)
    (hτμ : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length)
    (h7 : σ (.n 7) = ofK (Parameters.gpow dims)) (h8 : σ (.n 8) = ofK (Parameters.gpow rows))
    (h5 : σ (.n 5) = ofK (Parameters.gpow z))
    (hd : ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun m ↦ gen ^ log2Ceil m))
    (hr : ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat))
    (hz : ReadsAt rd (ofK (Parameters.gpow z)) point) {t : ℕ} (ht : t < 6) :
    σ (.n (1733 + 14 * t)) = gen ^ log2Ceil (rowsN.getD t 0) ∧
      σ (.n (1733 + 14 * t + 5)) = eOfNat (rowsN.getD t 0) ∧
      [σ (.n (1733 + 14 * t + 6)), σ (.n (1733 + 14 * t + 7)), σ (.n (1733 + 14 * t + 8))] =
        [paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0),
          pwLead (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0),
          pwRest (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0)] := by
  obtain ⟨k, hb⟩ := h.slice _ _ (vt_pad_blocks t ht)
  simp only [vtPad, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and, word_one,
    word_zero, List.map_cons, List.map_nil] at hb
  obtain ⟨l0, -, -, l5, ⟨j, hj, hjx, hrel⟩, -⟩ := hb
  have hτ := hτ29 (rowsN.getD t 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hdt : LoadHolds rd (ofK (Parameters.gpow dims)) (t + 1) (gen ^ log2Ceil (rowsN.getD t 0)) := by
    have := hd (t + 1) (by simp; omega)
    simp only [List.getElem_cons_succ, List.getElem_map] at this
    rwa [List.getD_eq_getElem _ _ (by omega)]
  have hrt : LoadHolds rd (ofK (Parameters.gpow rows)) t (eOfNat (rowsN.getD t 0)) := by
    have := hr t (by simp; omega)
    simp only [List.getElem_map] at this
    rwa [List.getD_eq_getElem _ _ (by omega)]
  rw [h7] at l0
  rw [h8] at l5
  have ev := loadHolds_unique l0 hdt
  have e5 := loadHolds_unique l5 hrt
  have hj29 : j < 29 := by simpa [pwNames] using hj
  have hjτ : j = log2Ceil (rowsN.getD t 0) := by
    rw [ev, gen_pow_eq_ofK] at hjx
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega)
      (by simp only [Set.mem_Iio]; omega) (ofK_injective hjx)).symm
  subst hjτ
  obtain ⟨n', zs, hn', hrows, hzl, hzs, hret⟩ := pw_dispatch _ hj hrel
  rw [e5] at hrows
  have hle := le_two_pow_log2Ceil (rowsN.getD t 0)
  have hpow : 2 ^ log2Ceil (rowsN.getD t 0) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hn := eOfNat_inj (by omega) (by omega) hrows
  rw [h5] at hzs
  have hzs' : zs = point.take (log2Ceil (rowsN.getD t 0)) := by
    apply List.ext_getElem (by simpa [hzl] using hτμ t ht)
    intro k h1 h2
    have hk : k < point.length := by simp at h2; omega
    rw [List.getElem_take]
    exact loadHolds_unique (hzs k h1) (hz k hk)
  refine ⟨ev, e5, ?_⟩
  rw [hret, hzs', ← hn]

end

end
end LeanVM.Guest.B1.VerifySub
