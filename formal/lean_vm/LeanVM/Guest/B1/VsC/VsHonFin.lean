/-
  LeanVM.Guest.B1.VsC.VsHonFin

  `VsHonPartsEx alW` from `VsHonPartsIn`.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonEcIn
public import LeanVM.Guest.B1.VsC.Os.LeftEnd

/-!
# `VsHonPartsEx alW`

**`VsHonPartsIn`**: what the pinned calls do not give, each at the honest context `x.honCtx N ec bp bp1` with `N` from
`natOpen`: `D3.Ok`'s remaining facts (`VsD3Left`). The pinned calls are vshp-ec's `ecPart` on `honCtx_ecIn`.
**`vsHonPartsEx_of_in : VsHonPartsIn → VsHonPartsEx alW`**, **`vsWindows_alW_of_in`**; `VsHonDone.lean` discharges
`VsHonPartsIn`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Guest.Memory (alW)

@[expose] public section

/-- **What the assembly takes beyond the pinned calls** (`VsCtx.honCtx_d3Left`). -/
structure VsHonPartsIn : Prop where
  d3 : ∀ (x : VsCtx) (N : NatOpen) (ec : ℕ → ℕ) (bp bp1 : ℕ), x.al = alW → x.Ok → N.Ok x.seed x.c →
    VsEcFacts (x.honCtx N ec bp bp1) N bp bp1 → VsD3Left (x.honCtx N ec bp bp1) N bp bp1

/-- **The pinned calls at the honest context**: vshp-ec's `ecPart` on `EcIn` (`honCtx_ecIn`). -/
theorem VsCtx.honCtx_ec {x : VsCtx} (hal : x.al = alW) (hok : x.Ok) {N : NatOpen} (hN : N.Ok x.seed x.c) :
    ∃ ec bp bp1, VsEcFacts (x.honCtx N ec bp bp1) N bp bp1 := by
  have hok' : ({ x.withBw N with ex := [] } : VsCtx).Ok := ⟨hok.child, hok.ht, hok.ho, hok.hfc, hok.pre, hok.hcur⟩
  obtain ⟨ec, bp, bp1, h⟩ := VsCtx.ecPart { x.withBw N with ex := [] } (hal ▸ openStackedEndA_17) hok' hN
    (x.honRetR N) N.op N.kp N.kw (fun ec bp bp1 => VsCtx.honCtx_ecIn (ec := ec) (bp := bp) (bp1 := bp1) hok hN)
  exact ⟨ec, bp, bp1, VsEcFacts.ofEc h⟩

/-- **`VsHonPartsEx alW`** from `VsHonPartsIn`. -/
theorem vsHonPartsEx_of_in (h : VsHonPartsIn) : VsHonPartsEx alW := fun x hal hok => by
  obtain ⟨N, hN⟩ := natOpen hok.child
  obtain ⟨ec, bp, bp1, hE⟩ := VsCtx.honCtx_ec hal hok hN
  exact ⟨ec, x.honBw N, [], x.honRetR N bp bp1, VsCtx.honParts_honCtx hok hN hE
    (VsCtx.honD3_ok hok hN hE (h.d3 x N ec bp bp1 hal hok hN hE))⟩

/-- **`verify_sub`'s windows at `alW`** from `VsHonPartsIn`. -/
theorem vsWindows_alW_of_in (h : VsHonPartsIn) : VsWindowsFromCallees alW 17 :=
  vsWindows_alW_of_parts (vsHonPartsEx_of_in h)

end
end LeanVM.Guest.B1.VsC
