module

public import NativeRustcVm.Whir.Basis
public import NativeRustcVm.Tables.Same

/-!
# The basis over bytes that stayed the same

`BasisWAt.of_same`: the `BasisW` at `p` and the areas it names still hold `b` in a memory whose
bytes over the `BasisW` and over each area are the same.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeVm.Model NativeRustcVm NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr
open NativeRustcVm.Transcript (off)

public section

variable {d d' : Mem 64}

theorem ringWAt_of_same {p : BitVec 64} {target : EW} {cs : Array EW} (h : RingWAt d p target cs)
    (hs : Same d d' p ringWBytes) : RingWAt d' p target cs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨EWAt.of_same h1 hs (by decide), h2,
    Tables.EWsAt.of_same h3 (hs.sub (o := 16) (k := 16 * coeffCount) (by decide)) ?_⟩
  rw [Array.length_toList, h2]

theorem keccakOutAt_of_same {p : BitVec 64} {point slices : Array EW}
    (h : KeccakOutAt d p point slices) (hs : Same d d' p outBytes) :
    KeccakOutAt d' p point slices := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨BufEWAt.of_same h1 hs (by decide), h2,
    Tables.EWsAt.of_same h3 (hs.sub (o := slicesOff) (k := 16 * 64) (by decide)) ?_⟩
  rw [Array.length_toList, h2]

theorem eqClaimAt_of_same {p : BitVec 64} {z : Array EW} {v : EW} (h : EqClaimAt d p z v)
    (hs : Same d d' p eqClaimBytes) : EqClaimAt d' p z v :=
  ⟨BufEWAt.of_same h.1 hs (by decide),
    EWAt.of_same h.2 (hs.sub (o := 488) (k := 16) (by decide)) le_rfl⟩

/-- **The basis** over bytes that stayed the same. -/
theorem basisWAt_of_same {p : BitVec 64} {ba : BasisAddrs} {b : BasisW} (h : BasisWAt d p ba b)
    (hp : Same d d' p basisBytes) (hr : ∀ r ∈ ba.regions, Same d d' r.addr r.size) :
    BasisWAt d' p ba b := by
  have h0 := hr ⟨ba.scales, 16 * ba.count⟩ (by simp [BasisAddrs.regions])
  have h1 := hr ⟨ba.layout, layoutBytes⟩ (by simp [BasisAddrs.regions])
  have h2 := hr ⟨ba.ring, ringWBytes⟩ (by simp [BasisAddrs.regions])
  have h3 := hr ⟨ba.keccak, outBytes⟩ (by simp [BasisAddrs.regions])
  have h4 := hr ⟨ba.claims, claimsBytes⟩ (by simp [BasisAddrs.regions])
  have h5 := hr ⟨ba.ood, eqClaimBytes⟩ (by simp [BasisAddrs.regions])
  obtain ⟨hlt, hw, hsz, hsc, ⟨L, t, cs, pt, sl, ccs, z, v, hL, hLa, hR, hK, hC, hE, heq⟩⟩ := h
  refine ⟨hlt, Tables.WordsAt.of_same hw hp (by simp [basisBytes]), hsz,
    Tables.EWsAt.of_same hsc h0 (by simp [hsz]),
    ⟨L, t, cs, pt, sl, ccs, z, v, hL, Tables.LayoutWAt.of_same hLa h1, ringWAt_of_same hR h2,
      keccakOutAt_of_same hK h3, Tables.ClaimsWAt.of_same hC h4, eqClaimAt_of_same hE h5, heq⟩⟩

end

end NativeRustcVmArm.Whir.WhirLevels
