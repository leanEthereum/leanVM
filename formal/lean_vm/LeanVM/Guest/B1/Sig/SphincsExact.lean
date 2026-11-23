/-
  LeanVM.Guest.B1.Sig.SphincsExact

  `verify_sig_lean_sphincs`'s bit hints are exact on a valuation whose bit run holds the bits of `H_msg`'s cells
  (`SBits`), so its node is exact there (`sNode_exact`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFieldsComplete
public import LeanVM.Guest.Exact.SphincsPinned

/-!
# `verify_sig_lean_sphincs`, exact

The digest's number `digestNatOf x0 x1 y` holds `x0`'s bits from `0`, `x1`'s from `128`, the low sixteen of `y`'s from
`256`. `SBits.exact`: on a valuation satisfying `SBits`, each of the three bit hints (`sBitsAtoms`) writes the
executor's bits of its cell. `sNode_exact`: every event of a holding path of the body is then exact, its other computed
hints being none (`sPinned`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

theorem digestNatOf_eq (x0 x1 y : E) :
    digestNatOf x0 x1 y = 2 ^ 128 * (2 ^ 128 * (cellNat y % 2 ^ 16) + cellNat x1) + cellNat x0 := by
  unfold digestNatOf; ring

theorem testBit_digestNatOf_lo (x0 x1 y : E) {j : ℕ} (hj : j < 128) :
    (digestNatOf x0 x1 y).testBit j = (cellNat x0).testBit j := by
  rw [digestNatOf_eq, Nat.testBit_two_pow_mul_add _ (cellNat_lt x0)]
  simp [hj]

theorem testBit_digestNatOf_mid (x0 x1 y : E) {j : ℕ} (hj : j < 128) :
    (digestNatOf x0 x1 y).testBit (128 + j) = (cellNat x1).testBit j := by
  rw [digestNatOf_eq, Nat.testBit_two_pow_mul_add _ (cellNat_lt x0)]
  simp only [show ¬128 + j < 128 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [Nat.testBit_two_pow_mul_add _ (cellNat_lt x1)]
  simp [hj]

theorem testBit_digestNatOf_hi (x0 x1 y : E) {j : ℕ} (hj : j < 16) :
    (digestNatOf x0 x1 y).testBit (256 + j) = (cellNat y).testBit j := by
  rw [digestNatOf_eq, Nat.testBit_two_pow_mul_add _ (cellNat_lt x0)]
  simp only [show ¬256 + j < 128 by omega, ↓reduceIte, show 256 + j - 128 = 128 + j by omega]
  rw [Nat.testBit_two_pow_mul_add _ (cellNat_lt x1)]
  simp only [show ¬128 + j < 128 by omega, ↓reduceIte, Nat.add_sub_cancel_left, Nat.testBit_mod_two_pow]
  simp [hj]

/-- A run of bits read from the bit run. -/
theorem bits_run_eq {σ : Val} {o n : ℕ} {x : E} (h : ∀ j < n, σ (.n (o + j)) = bitE ((cellNat x).testBit j)) :
    ((List.range n).map fun k => V.n (o + k)).map σ = (List.range n).map fun j => LeanVM.Prover.Exec.bitWord
      ((LeanVM.Prover.Exec.wordNat x).testBit (0 + j)) := by
  rw [List.map_map]
  exact List.map_congr_left fun j hj => by rw [Function.comp_apply, h j (List.mem_range.mp hj), Nat.zero_add]; rfl

/-- **On a valuation satisfying `SBits`, the bit hints are exact.** -/
theorem SBits.exact {σ : Val} (h : SBits σ) (rd : Reader) : ∀ a ∈ sBitsAtoms, a.Exact rd σ := by
  intro a ha
  simp only [sBitsAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact bits_run_eq fun j hj => by
      rw [h j (by omega), testBit_digestNatOf_lo _ _ _ hj]; rfl
  · exact bits_run_eq fun j hj => by
      rw [show 156 + j = 28 + (128 + j) by omega, h _ (by omega), testBit_digestNatOf_mid _ _ _ hj]; rfl
  · exact bits_run_eq fun j hj => by
      rw [show 284 + j = 28 + (256 + j) by omega, h _ (by omega), testBit_digestNatOf_hi _ _ _ hj]; rfl

/-- **A holding path of `verify_sig_lean_sphincs` on a valuation satisfying `SBits` is exact.** -/
theorem sNode_exact {rd : Reader} {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ (Fn.«verify_sig_lean_sphincs».core).body = .ret es vs) (hes : ∀ e ∈ es, e.Holds rd σ)
    (h : SBits σ) : ∀ e ∈ es, e.Exact rd σ :=
  exact_of_sites sPinned hw hes fun a ha _ => h.exact rd a ha

end
end LeanVM.Guest.B1.Sig
