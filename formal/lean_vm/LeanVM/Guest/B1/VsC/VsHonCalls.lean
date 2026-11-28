/-
  LeanVM.Guest.B1.VsC.VsHonCalls

  The pinned non-leaf calls at an honest context: each callee's completeness, with its end bound.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonEnds
public import LeanVM.Guest.B1.VsC.VsOrcPh46
public import LeanVM.Guest.B1.VsC.CalleesU

/-!
# The pinned calls, chosen

`VsHonEx` chooses the callees' ends `x.ec` from their completeness statements. Each lemma here gives one pinned
call at its frame, with the end bound `EcSteps` asks, from `VsCalleesEndU` at `B2C.fs` (`vsCalleesEndU_b2c`):
**`VsCtx.cs_of`** (`certify_stack` at `x.fpc`, `Ret1.cs`, `EcSteps.s4`), **`VsCtx.sp_of`** (`squeeze_packed` at
`x.fpsp`, `Ret1.sp`, `EcSteps.s6`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

namespace VsCtx

variable (x : VsCtx)

/-- The front's callees' cursor is past the buffers. -/
theorem le_frontEnd : x.cur + (vsAllocSz x.p).sum ≤ x.frontEnd B2C.fs x.al := by
  unfold VsCtx.frontEnd
  split_ifs
  · exact le_trans le_frontKc (le_trans le_leafEnd le_leafEnd)
  · exact le_trans le_frontKc le_leafEnd

/-- `certify_stack`'s frame is past the buffers. -/
theorem le_fpc : x.cur + (vsAllocSz x.p).sum ≤ x.fpc := by
  refine le_trans x.le_frontEnd ?_
  unfold VsCtx.fpc; exact le_trans le_leafEnd (le_allocBase _ _)

variable {x}

/-- **`certify_stack`'s pinned call** at its frame `x.fpc`, its end within `2^20` of its frame's end. -/
theorem cs_of (hU : VsCalleesEndU B2C.fs x.al B2C.cert 17) (hok : x.Ok) :
    ∃ e, CsCall B2C.fs x.al B2C.cert 17 x.lay x.qt (x.base 20) x.fpc e ∧
      e ≤ x.fpc + B2C.fs "certify_stack" + 2 ^ 20 := by
  obtain ⟨layout, r, hann, hS, hN⟩ := frontNum_of_child hok.child
  have hlay : x.lay = layout := by simp [VsCtx.lay, hann]
  have hfpc := x.le_fpc
  have hsum := x.allocSz_sum
  have b20 : x.base 20 = x.cur + (824 + 256 * x.p) + 6 := vsBaseF_20 _ _
  have hwt : winTabAt + 2 ^ winTabBits = 2226 := rfl
  have hnt : nTables = 6 := rfl
  have e4 : expTabLen = 2226 := expTabLen_eq
  have hqt := hok.ht
  have hfc := hok.hfc
  rw [hlay]
  obtain ⟨e, hb, hc⟩ := hU.certify_stack guestBytecode layout.logMemory layout.tableRows layout x.qt (x.base 20) x.fpc
    (announced_build hann) hS.stack_le (by rw [hwt]; omega) (by rw [hnt]; omega)
  exact ⟨e, hc, hb⟩

/-- **`squeeze_packed`'s pinned call** at its frame `x.fpsp` (past `certify_stack`'s end `x.ec 4`), on the opening
message's capacity, writing `.n 10`'s words from `1`; its end within `2^21` of its frame's end. -/
theorem sp_of (hU : VsCalleesEndU B2C.fs x.al B2C.cert 17) (hok : x.Ok) (h4 : x.cur + (vsAllocSz x.p).sum ≤ x.ec 4) :
    ∃ e, SpCall B2C.fs x.al B2C.cert 17 (x.w 575) (x.w 576) (x.w 577) (x.w 578) (x.w 579) (ptrAt (x.base 4 + 1)) x.pk
      x.fpsp e ∧ e ≤ x.fpsp + B2C.fs "squeeze_packed" + 2 ^ 21 := by
  obtain ⟨layout, r, hann, hS, hN⟩ := frontNum_of_child hok.child
  have hlay : x.lay = layout := by simp [VsCtx.lay, hann]
  have hn24 : hMax x.lay ≤ 24 := by
    rw [hlay]; obtain ⟨t, ht, e⟩ := hN.hn; rw [← e]; exact hN.h24 t ht
  have hw19 : 19 ≤ widthOf x.lay := by rw [hlay]; exact hN.hw19
  have hw24 : widthOf x.lay ≤ 24 := by rw [hlay]; exact hN.hw24
  obtain ⟨hp64, -⟩ := vsPk hn24 hw19 hw24
  have hpk19 : 8 * x.pk ≤ 152 := by
    have := chal_fits hn24 hw19 hw24
    have h153 : guest_const% LINK_CHAL_CAP = 153 := rfl
    rw [h153] at this
    unfold VsCtx.pk; omega
  have hsum := x.allocSz_sum
  have b4 : x.base 4 = x.cur + 190 := VsCtx.base_4
  have hfp : x.ec 4 ≤ x.fpsp := by
    unfold VsCtx.fpsp; exact le_trans (le_trans le_leafEnd le_leafEnd) (le_allocBase _ _)
  obtain ⟨e, hb, hc⟩ := hU.squeeze_packed (x.w 575) (x.w 576) (x.w 577) (x.w 578) (x.w 579) (ptrAt (x.base 4 + 1))
    x.pk x.fpsp hp64 (by
      intro q hq t ht
      simp only [List.mem_singleton] at hq
      subst hq
      dsimp only at ht
      rw [Link.pkSqueeze_length] at ht
      exact ⟨x.base 4 + 1 + t, by omega, B1.Main.addr_ofK _ _⟩)
  exact ⟨e, hc, hb⟩

end VsCtx

end
end LeanVM.Guest.B1.VsC
