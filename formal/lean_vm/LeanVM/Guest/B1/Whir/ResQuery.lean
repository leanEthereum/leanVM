/-
  LeanVM.Guest.B1.Whir.ResQuery

  The template's inline `residual_query` computes `residualProd` on the vanishing values.
-/

module

public import LeanVM.Guest.B1.Whir.Flat
public import LeanVM.Guest.B1.Opening.Residual

/-!
# `residual_query` inline (G:1419-1427)

`osResQuery pos bd row vo n k` multiplies `d_t + chain_t` over `t < n`, the row's words `d_t`
at `bd·g^(row + t)`, the chain from the position by `chain ← chain·(chain + VALS[vo + t])`
(`osVals vo n`, the words of `LIG_VANISH_VALS`): `osResQuery_val`, B1-a's `residualProd`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The vanishing values `VALS[vo + t]`, `t < n`, as words. -/
def osVals (vo n : ℕ) : List E := (List.range n).map fun t ↦ word (vanishVal (vo + t)) 0 0

theorem osVals_getD {vo n t : ℕ} (h : t < n) :
    (osVals vo n).getD t 0 = word (vanishVal (vo + t)) 0 0 := by
  simp [osVals, List.getD_eq_getElem?_getD, h]

/-- The blocks after the first factor. -/
theorem osResQ_val {pos bd row vo L : ℕ} {D : ℕ → E} : ∀ (n t pe k : ℕ), 1 ≤ t → t + n ≤ L →
    σ (.n (if t = 1 then pos else k - 4)) = residualChain (osVals vo L) (σ (.n pos)) (t - 1) →
    σ (.n pe) = residualProd (osVals vo L) (σ (.n pos)) D t →
    (∀ s, t ≤ s → s < t + n → LoadHolds rd (σ (.n bd)) (row + s) (D s)) →
    AllOk C rd σ (osResQ pos bd row vo n t pe k).1 →
    σ (.n (osResQ pos bd row vo n t pe k).2.1) = residualProd (osVals vo L) (σ (.n pos)) D (t + n)
  | 0, t, pe, k, _, _, _, hpe, _, _ => by simpa [osResQ] using hpe
  | n + 1, t, pe, k, ht, hL, hch, hpe, hD, hok => by
    simp only [osResQ] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨hA, hR⟩ := hok
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hA
    obtain ⟨c0, c1, c2, l3, a4, m5⟩ := hA
    have hc : σ (.n (k + 2)) = residualChain (osVals vo L) (σ (.n pos)) t := by
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [c2, c1, c0, hch, residualChain, osVals_getD (by omega)]
      rw [show vo + (t' + 1) - 1 = vo + t' by omega, Nat.add_sub_cancel]
    have hd : σ (.n (k + 3)) = D t := loadHolds_unique l3 (hD t le_rfl (by omega))
    have hp : σ (.n (k + 5)) = residualProd (osVals vo L) (σ (.n pos)) D (t + 1) := by
      rw [m5, a4, hd, hc, hpe, residualProd]
    have := osResQ_val n (t + 1) (k + 5) (k + 6) (by omega) (by omega)
      (by
        have h1 : (t + 1 = 1) = False := eq_false (by omega)
        simp only [h1, ↓reduceIte, Nat.add_sub_cancel, show k + 6 - 4 = k + 2 by omega]
        exact hc)
      hp (fun s h1 h2 ↦ hD s (by omega) (by omega)) hR
    rw [this, show t + 1 + n = t + (n + 1) by ring]

/-- **The inline `residual_query`** over `n ≥ 1` coordinates: `Π_{t<n} (d_t + chain_t)`. -/
theorem osResQuery_val {pos bd row vo n k : ℕ} (hn : 1 ≤ n) {D : ℕ → E}
    (hD : ∀ s < n, LoadHolds rd (σ (.n bd)) (row + s) (D s))
    (hok : AllOk C rd σ (osResQuery pos bd row vo n k).1) :
    σ (.n (osResQuery pos bd row vo n k).2.1) = residualProd (osVals vo n) (σ (.n pos)) D n := by
  simp only [osResQuery] at hok ⊢
  rw [allOk_append] at hok
  obtain ⟨hA, hR⟩ := hok
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hA
  obtain ⟨l0, a1⟩ := hA
  have hd0 : σ (.n k) = D 0 := loadHolds_unique l0 (by simpa using hD 0 (by omega))
  have := osResQ_val (rd := rd) (L := n) (D := D) (n - 1) 1 (k + 1) (k + 2) le_rfl (by omega)
    (by simp [residualChain]) (by rw [a1, hd0]; simp [residualProd, residualChain])
    (fun s h1 h2 ↦ hD s (by omega)) hR
  rw [this, show 1 + (n - 1) = n by omega]

end
end LeanVM.Guest.B1.Whir
