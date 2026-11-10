/-
  LeanVM.Guest.B1.Whir.CFinCall

  The finish's residual loop calls at the values the honest run gives them.
-/

module

public import LeanVM.Guest.B1.Whir.CFinM
public import LeanVM.Guest.B1.Place.OsCallV

/-!
# The finish's loop calls, honestly

`osResCall_vals`: at the finish after `open_stacked`'s levels and closing rounds, each non-final
level's residual loop call (`osResCall`) reads, under the valuation `osFinishA_completeC` leaves,
the guard, the bounds, the query positions, `basis_d`, the scaled high parts, the chains' buffer
and `λ⁻¹`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **The residual loop calls' values.** -/
theorem osResCall_vals {c : OsCfg} {σ σ' : Val} {li RC : ℕ → E} {BD : E}
    (h : FinCallV c (osTail c (osLvsEnd c)).2.1 (osTail c (osLvsEnd c)).2.2 σ σ' li RC BD) :
    ∀ l < c.yrLevel, (osResCall c l).1.map σ' = some (1 + gen ^ ((finLv c l).queries / resBatch)) ∧
      (osResCall c l).2.2.1.map σ' = [1, gen ^ ((finLv c l).queries / resBatch), σ (.n osQpos), BD,
        σ (.n osHs), RC l, li l] := by
  intro l hl
  obtain ⟨hbd, hq, hh, hv⟩ := h
  obtain ⟨e0, e2, e7, e8, e9⟩ := hv l hl
  have hk : osResK c l = finResK c (osTail c (osLvsEnd c)).2.1 (osTail c (osLvsEnd c)).2.2 l := rfl
  have hb : (osResBase c).2.1 = finBdV c (osTail c (osLvsEnd c)).2.1 (osTail c (osLvsEnd c)).2.2 := rfl
  refine ⟨?_, ?_⟩
  · show some (σ' (.n (osResK c l + 7))) = _
    rw [hk, e7]
  · show [σ' (.n (osResK c l + 8)), σ' (.n (osResK c l + 9)), σ' (.n osQpos), σ' (.n (osResBase c).2.1),
      σ' (.n osHs), σ' (.n (osResK c l + 2)), σ' (.n (osResK c l))] = _
    rw [hk, hb, e8, e9, hq, hbd, hh, e2, e0]

end
end LeanVM.Guest.B1.Whir
