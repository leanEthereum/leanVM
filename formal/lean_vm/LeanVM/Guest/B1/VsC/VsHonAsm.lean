/-
  LeanVM.Guest.B1.VsC.VsHonAsm

  `VsHonPartsEx alW`, assembled from the honest choices and the parts still taken as hypotheses.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonCore
public import LeanVM.Guest.B1.VsC.VsHonAlW
public import LeanVM.Guest.B1.VsC.VsHpRing

/-!
# `VsHonPartsEx alW`, assembled

The honest choices `x.honCtx N ec bp bp1` (`VsHonBw.lean`) at `N` from `natOpen`. **`VsEcFacts y N bp bp1`**: the
pinned calls at the ends `ec` (vshp-ec's part). **`VsCtx.honParts_honCtx`**: `HonParts` at the honest context from
`VsEcFacts` and `D3`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link LeanVM.Guest.B1.Stack
open LeanVM.Guest.B1.Link (pkSqueeze pkSqueeze_length)
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VerifySub (qkeccakVarsCap keccakTauMin keccakTauMax)

@[expose] public section

attribute [local semireducible] VsCtx.lay

/-- **The pinned calls at the honest context** `y` (vshp-ec's part): `certify_stack`, `squeeze_packed`, the link's
two, `Ph12`'s cursor, `link_terminal`, `verify_keccak`, `ring_switch_target` (native form), `open_stacked` (at
`openCallEnd_nat`'s data, with `bp`, `bp1`), the ends' steps. -/
structure VsEcFacts (y : VsCtx) (N : NatOpen) (bp bp1 : ℕ) : Prop where
  cs : CsCall B2C.fs y.al B2C.cert 17 y.lay y.qt (y.base 20) y.fpc (y.ec 4)
  sp : SpCall B2C.fs y.al B2C.cert 17 (y.w 575) (y.w 576) (y.w 577) (y.w 578) (y.w 579) (ptrAt (y.base 4 + 1)) y.pk
    y.fpsp (y.ec 6)
  lk : y.LkCalls (y.natLk2 N.L)
  e12 : y.ec 12 = ph11End B2C.fs y.al y.nS y.h0S (y.ec 9)
  hlt : LtCall B2C.fs y.al B2C.cert 17 y.wdS y.σ0 (y.w 1077) (y.base 6) (y.natBm N.L) (y.base 13)
    (y.base 4 + 89 + y.nS + y.wdS) ((y.bw.getD 6 []).take N.L.chunks.width) (y.sw (y.natBm N.L) 80 64)
    (y.cells19.map Prod.snd) (((y.bw.getD 4 []).drop (89 + y.nS + y.wdS)).take N.L.chunks.d)
    (allocBase (y.al (Link.ltNames.getD (y.wdS - 19) "")) (tpKc B2C.fs y.al y.hgS 5 (y.ec 12))) (y.ec 13)
  hvk : VkCall B2C.fs y.al B2C.cert 17 y.w (y.base 9) (y.base 14) (y.base 15) y.qt (y.hgS 5) (y.bw.getD 9 [])
    (y.sw (y.natBm N.L) 55 25) (y.sw (y.natBm N.L) 144 N.xs.length) N.op N.kp ((y.bw.getD 15 []).take 64) N.kw N.s'
    (allocBase (y.al "verify_keccak") (y.ec 13)) (y.ec 14)
  hrt : RtCall B2C.fs y.al B2C.cert 17 y.a1 (rsW N.ks N.L.msg (ringRho N.S)) (ringF N.S ++ ringG N.S)
    (allocBase (y.al "ring_switch_target") (y.ec 14)) (y.ec 15)
  hos : CallAtA B2C.fs y.al B2C.cert 17 (openName N.layout.stackLog)
      (rateSel N.r :: ringCap N.S ++ [N.target y.seed y.c, y.c.proof.stream.getD 8 0, y.c.proof.stream.getD 9 0,
        ptrAt (y.natBm N.L + 144 + N.xs.length + 1), ptrAt (y.qt + 178)])
      (osRets N.wE bp bp1 (y.natBm N.L + 144 + N.xs.length + 1 + N.ws.length)) (fun i => y.R i ∨ y.OwnB i)
      (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
      (fun rd => ReadsAt rd (ptrAt bp) (N.wE.point ++ List.replicate (pointCap - N.layout.stackLog) 0) ∧
        ReadsAt rd (ptrAt bp1) (N.wE.point.map (1 + ·) ++ List.replicate (pointCap - N.layout.stackLog) 1))
      (fun rd => ReadsAt rd (ptrAt (y.natBm N.L + 144 + N.xs.length + 1)) N.ws ∧ WinTabs rd (ptrAt (y.qt + 178)))
      (fun rd t => SameStreams (t.pops coreProgram rd)
          (Prover.merkleHints true (Prover.childQueries guestBytecode y.seed y.c) y.c.proof.openings) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs (openName N.layout.stackLog)) (allocBase (y.al (openName N.layout.stackLog)) (y.ec 15))
      (allocBase (y.al (openName N.layout.stackLog)) (y.ec 15) + B2C.fs (openName N.layout.stackLog)) (y.ec 16)
  hbp : bp + pointCap ≤ y.ec 16
  hbp1 : bp1 + pointCap ≤ y.ec 16
  steps : y.EcSteps 36 N.layout.stackLog

namespace VsCtx

section
variable {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ} (hok : x.Ok) (hN : N.Ok x.seed x.c)

local notation "Y" => VsCtx.honCtx x N ec bp bp1

include hok hN in
/-- **`Bw3.hlow` at the honest context.** -/
theorem honCtx_hlow : (((Y).σ0 (.n 2931)).limb 0).lane.toNat % 2 ^ 13 = 0 := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨hbits, -⟩ := honCtx_link0 hok hN
  obtain ⟨-, -, hpend, -⟩ := honCtx_kec (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have hrd := VsCtx.nonce_reads (x := Y) hbits hw rfl hL.lenM hN.hrest
    (VsCtx.reads18 (x := Y) (honCtx_ok hok) (honCtx_hbw hok hN))
  exact VsCtx.hlow_nat honCtx_hret honCtx_rvk hpend hrd hN.hpow

include hok hN in
/-- **The ring switch's buffers and the cycles' bits at the honest context** (vshp-ring's lemmas): `Bw3.b2`, `b21`,
`b22`, `D3.Ok.b23`. -/
theorem honCtx_ring : (∃ n, n < 2 ^ 24 ∧ (Y).σ0 (.n 240) = ofK (g ^ n) ∧
      (Y).bw.getD 2 [] = (List.range 24).map fun j => LeanVM.Prover.Exec.bitWord (n.testBit j)) ∧
    (Y).bw.getD 21 [] = mcW (Y).σ0 ∧ (Y).bw.getD 22 [] = mcRc (Y).σ0 ∧
    (Y).bw.getD 23 [] = rsW ((Y).bw.getD 15 []) ((Y).sw ((Y).natBm N.L) 0 144) ((Y).σ0 (.n 3026)) := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨hbits, -⟩ := honCtx_link0 hok hN
  obtain ⟨-, -, hpend, -⟩ := honCtx_kec (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have hrd := VsCtx.nonce_reads (x := Y) hbits hw rfl hL.lenM hN.hrest
    (VsCtx.reads18 (x := Y) (honCtx_ok hok) (honCtx_hbw hok hN))
  have hmsg : (Y).sw (x.natBm N.L) 0 144 = N.L.msg := VsCtx.msg_nat (x := Y) hbits hw rfl hL.lenM
  obtain ⟨b21, b22, b23⟩ := VsCtx.ringBufs_nat (x := Y) rfl honCtx_hret honCtx_rvk hpend hrd rfl rfl
    (by rw [hmsg]; rfl)
  exact ⟨VsCtx.b2_honest (honCtx_ok hok) honCtx_hret honCtx_ret1F rfl, b21, b22, b23⟩

include hok hN in
theorem honCtx_hpt : x.c.freshClaim.point = ((Y).bw.getD 6 []).take 19 := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  have h19 : 19 ≤ x.wdS := (ctx_nums x hok).1
  have hp := hL.point
  rw [lb_ctx hN] at hp
  exact freshPoint_of_bw6 rfl (by rw [natR_length hL]; exact h19) hp

end

/-- **`HonParts` at the honest context**, from the pinned calls, the ring's facts and `D3`. -/
theorem honParts_honCtx {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ} (hok : x.Ok) (hN : N.Ok x.seed x.c)
    (hE : VsEcFacts (x.honCtx N ec bp bp1) N bp bp1)
    (hD : ∃ D : D3, D.Ok (x.honCtx N ec bp bp1)) : (x.honCtx N ec bp bp1).HonParts := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨hR2, hR21, hR22, -⟩ := honCtx_ring (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  exact {
    ok := honCtx_ok hok
    hbw := honCtx_hbw hok hN
    hex := by intro q hq; exact absurd hq (List.not_mem_nil)
    hret := honCtx_hret
    retFs := honCtx_retFs
    bwFs := honCtx_bwFs
    bw1 := honCtx_bw1 hok hN
    ret1 := ⟨honCtx_ret1F, honCtx_r484, honCtx_r485, honCtx_r486, honCtx_r487, honCtx_r680l, hE.cs, hE.sp⟩
    ret3 := honCtx_ret3
    num6 := honCtx_num6 hok hN
    link := ⟨N.L, N.link, N.rest, hw, hL, honCtx_bwNat, honCtx_honRet, hE.lk⟩
    e12 := hE.e12
    hpt := honCtx_hpt (x := x) (N := N) (ec := ec) (bp := bp) (bp1 := bp1) hok hN
    b8 := rfl
    b0 := rfl
    b3 := rfl
    b2 := hR2
    b21 := hR21
    b22 := hR22
    hlow := honCtx_hlow (x := x) (N := N) (ec := ec) (bp := bp) (bp1 := bp1) hok hN
    d3 := hD
    steps := ⟨_, hE.steps⟩ }

end VsCtx

end
end LeanVM.Guest.B1.VsC
