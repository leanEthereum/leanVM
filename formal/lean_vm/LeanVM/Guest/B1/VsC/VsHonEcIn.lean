/-
  LeanVM.Guest.B1.VsC.VsHonEcIn

  vshp-ec's `EcIn` at the honest context, for every `ec`, `bp`, `bp1`.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonD3
public import LeanVM.Guest.B1.VsC.VsHonEcPf

/-!
# `EcIn` at the honest context

**`VsCtx.honCtx_ecIn`**: `EcIn (x.honCtx N ec bp bp1) N N.op N.kp N.kw` from `x.Ok` and `N.Ok x.seed x.c`, the guest's
values at the pinned calls' arguments the native ones; **`VsCtx.honCtx_hchd`**; **`VsEcFacts.ofEc`**.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link LeanVM.Guest.B1.Stack
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VerifySub (qkeccakVarsCap keccakTauMin keccakTauMax)

@[expose] public section

attribute [local semireducible] VsCtx.lay

/-- vshp-ec's facts are `VsEcFacts` at the native Keccak claim. -/
theorem VsEcFacts.ofEc {y : VsCtx} {N : NatOpen} {bp bp1 : ℕ} (h : VsCtx.EcFacts y N N.op N.kp N.kw bp bp1) :
    VsEcFacts y N bp bp1 :=
  ⟨h.cs, h.sp, h.lk, h.e12, h.hlt, h.hvk, h.hrt, h.hos, h.hbp, h.hbp1, h.steps⟩

namespace VsCtx

section
variable {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ} (hok : x.Ok) (hN : N.Ok x.seed x.c)

local notation "Y" => VsCtx.honCtx x N ec bp bp1

include hok hN in
/-- The link's chunk count fits `.n 10`'s words past the challenges. -/
theorem honCtx_hchd : 89 + (Y).nS + (Y).wdS + N.L.chunks.d ≤ 153 := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨h19, h24, hn, -⟩ := ctx_nums x hok
  have hc := chal_fits hn h19 h24
  have h153 : guest_const% LINK_CHAL_CAP = 153 := rfl
  have h88 : guest_const% LINK_FIXED = 88 := rfl
  rw [h153, packedChallenges_eq, h88] at hc
  have hd : chunkCount x.wdS = N.L.chunks.d := by
    unfold chunkCount
    rw [show x.wdS = linkWidth x.lay from rfl, hL.chunks]
    rfl
  have := (packed_vanish (88 + x.nS + x.wdS + chunkCount x.wdS)).1
  show 89 + x.nS + x.wdS + N.L.chunks.d ≤ 153
  omega

include hok hN in
/-- **`EcIn` at the honest context.** -/
theorem honCtx_ecIn : EcIn Y N N.op N.kp N.kw := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨hbits, hR0, hq6, hwd⟩ := honCtx_link0 hok hN
  obtain ⟨hs1, hs2⟩ := honCtx_stream hok hN
  obtain ⟨h19, h24, -⟩ := ctx_nums x hok
  have hokY : (Y).Ok := honCtx_ok hok
  have hq0 : linkQVars (Y).lay ≠ 0 := by rw [show linkQVars (Y).lay = 6 from hq6]; decide
  have hrl : (Y).lay.tableRows.length = 6 := by
    rw [VsCtx.lay_nat (x := Y) hN, hN.shape.rows_length]; rfl
  have htab := tab_ctx (x := Y) hN
  have hlb := lb_ctx (x := Y) hN
  have hbw := honCtx_hbw (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have hfs := honCtx_fs1 (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have hood := honCtx_hood (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have hb1 := honCtx_bw1 (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have hrd18 := VsCtx.reads18 (x := Y) hokY hbw
  obtain ⟨hr2, r767, r1071, r1287⟩ :=
    ret_of_honRet (honCtx_honRet (x := x) (N := N) (ec := ec) (bp := bp) (bp1 := bp1))
  obtain ⟨hout, hks, hpend, hopl, hkpl, hτ0, hτ1, hrun⟩ := honCtx_kec (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have hb15 : ((Y).bw.getD 15 []).take 64 = N.ks := by
    show N.ks.take 64 = N.ks
    exact List.take_of_length_le (by omega)
  obtain ⟨hrun', -, -, hptl⟩ := VsCtx.kec_bufs (x := Y) (bm := x.natBm N.L) hb15 rfl hopl hkpl hrun
  obtain ⟨e573, ecap, hpk⟩ := VsCtx.front_nat (x := Y) hw htab hL.chunks hbits hfs hood
  obtain ⟨-, h4⟩ := VsCtx.bw4_nat (x := Y) hb1 e573 ecap hpk
  have hcl := VsCtx.clI_nat (x := Y) hL htab hlb hrl h24 hb1 h4
  have hcapI : (Link.chainLast ⟨[], 0, 0⟩ ((Y).natLI N.L)).cap.length = 5 := natChain_last_cap (by omega) _ _ _
  have ha : (Y).args.length = 6 := rfl
  refine {
    hbw := hbw
    cap1 := ecap
    g1 := ?_
    g3 := VsCtx.g3_of hfs
    gcl := ?_
    g2 := VsCtx.g2_of (x := Y) hw hbits (by omega) hL.lenI honCtx_hret rfl hrd18 r767
    g773 := ?_
    sec := honCtx_sec hok hN
    w1077 := VsCtx.w1077_nat (x := Y) honCtx_hret hcl (by omega) hR0 hq0 r1071
    hpm := fun j hj => honCtx_w (by interval_cases j <;> decide)
      (fun σ => (show 1288 + j = 1287 + (j + 1) by omega) ▸ r1287 (j + 1) (by omega) σ)
    w1076 := honCtx_w1076 hok hN
    hbmIn := ⟨by show x.base 18 ≤ x.natBm N.L; simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]; omega, by
      show x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p; omega⟩
    hchw := by omega
    hchd := honCtx_hchd hok hN
    hid := VsCtx.hid_nat (x := Y) (D := honD3 Y N bp bp1 []) honCtx_hret hb1 hfs hood hw hL htab hlb hrl h19 h24 hR0
      rfl rfl r1071 hL.chunks rfl (honCtx_sec hok hN)
    hτ0 := hτ0
    hτ1 := hτ1
    hcar := VsCtx.hcar_nat (x := Y) honCtx_hret hbits hq0 hw rfl hL.lenM r1287
    hrun := hrun'
    hpend := hpend
    hopl := hopl
    hptl := hptl
    hs64 := rsW_length _ _ _
    hc16 := by rw [List.length_append, honRingF_length, honRingG_length]; rfl }
  · rw [honCtx_r680l, ecap, hpk]
    rfl
  · have e1 : (Y).w 752 = _ := vsW_retC ha honCtx_hret (i := 752) (by decide) hr2.r752
    have e2 : (Y).w 753 = _ := vsW_retC ha honCtx_hret (i := 753) (by decide) hr2.r753
    rw [e1, e2]
    rfl
  · have e : (Y).w (767 + 6) = _ := vsW_retC ha honCtx_hret (i := 767 + 6) (by decide) (r767 6 (by norm_num))
    exact e.trans (cells_getD_6 hcapI)

end

end VsCtx

end
end LeanVM.Guest.B1.VsC
