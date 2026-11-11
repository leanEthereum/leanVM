/-
  LeanVM.Guest.B1.KeccakGkr.LayerWeight0

  A later claim's weight at the local point in `keccak_layer` (G:2818-2821): `keccak_shifts_eq`
  then `keccak_form`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerProof
public import LeanVM.Guest.B1.KeccakGkr.ShiftsT
public import LeanVM.Guest.B1.KeccakGkr.FormT

/-!
# A later claim's weight

`weightOk_zero`: the shifts of the claim's local point against the new one (`shiftsT_holds`),
then `keccak_form` on the claim's lanes (`formAll_holds`), is the claim's weights `laterWeights`
against the new local point's equality weights (`later_dot`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

theorem formVal_congr {F F' L S S' : ℕ → E} (hF : ∀ l < 25, F l = F' l)
    (hS : ∀ l < 25, S (kRho l) = S' (kRho l) ∧ S ((kRho l + 1) % 64) = S' ((kRho l + 1) % 64)) :
    formVal F L S = formVal F' L S' := by
  unfold formVal colS colN
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun l hl ↦ ?_)
    (Finset.sum_congr rfl fun x hx ↦ ?_)
  · have := Finset.mem_range.1 hl
    rw [hF l this, (hS l this).1]
  · have := Finset.mem_range.1 hx
    refine congrArg₂ (· * ·) (Finset.sum_congr rfl fun y hy ↦ ?_)
      (congrArg₂ (· + ·) (Finset.sum_congr rfl fun y hy ↦ ?_) (Finset.sum_congr rfl fun y hy ↦ ?_))
    · have := Finset.mem_range.1 hy
      rw [hF _ (by omega)]
    · have := Finset.mem_range.1 hy
      rw [(hS _ (by omega)).1]
    · have := Finset.mem_range.1 hy
      rw [(hS _ (by omega)).2]

theorem rho_used : ∀ l < 25, kRho l ∈ shiftUsed ∧ (kRho l + 1) % 64 ∈ shiftUsed := by decide

/-- **A later claim's weight section** (G:2824-2827). -/
theorem weightOk_zero (o : ℕ) : WeightOk 0 o := by
  intro C rd σ c y locPt next kret hcr hlocL hloc hf h
  obtain ⟨-, -, -, -, -, -, lp, lanes, hlp, hlen, hlanes, lc, sl, loc, hlc, hlocL', hlocR, -, -, hw⟩ :=
    hcr
  simp only [weightT, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, holdsList_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds] at h
  obtain ⟨l3, l4, h⟩ := h
  rw [show keccakLocalBits = 11 from rfl] at hlocL'
  rw [← loadHolds_unique l3 hlp] at hlanes
  rw [← loadHolds_unique l4 hlc] at hlocR
  obtain ⟨hld, hsh, h⟩ := shiftsT_holds h
  obtain ⟨hv, hn⟩ := formAll_holds hlanes hlen h
  refine ⟨?_, hn⟩
  have ha : ((List.range 6).map fun t ↦ σ (.n (o + 1192 + 11 * t))) = loc.take 6 := by
    apply List.ext_getElem (by simp [hlocL'])
    intro t h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_take]
    exact loadHolds_unique (hld t h1).1 (hlocR t (by omega))
  have hb : ((List.range 6).map fun t ↦ σ (.n (o + 1192 + 11 * t + 1))) = locPt.take 6 := by
    apply List.ext_getElem (by simp [hlocL])
    intro t h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_take]
    exact loadHolds_unique (hld t h1).2 (hloc t (by omega))
  rw [ha, hb] at hsh
  simp only [weightVal, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
  rw [hv, hw, later_dot locPt (loc.take 6) lanes hlocL
    (by simp [hlocL'])]
  refine formVal_congr (fun l hl ↦ hf l hl) (fun l hl ↦ ⟨?_, ?_⟩)
  · exact hsh _ (rho_used l hl).1
  · exact hsh _ (rho_used l hl).2

end
end LeanVM.Guest.B1.VerifySub
