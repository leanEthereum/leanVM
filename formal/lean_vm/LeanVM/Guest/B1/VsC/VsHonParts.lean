/-
  LeanVM.Guest.B1.VsC.VsHonParts

  `Hon` from the honest choices' own facts: the derived fields assembled.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonEnds
public import LeanVM.Guest.B1.VsC.VsAvoid
public import LeanVM.Guest.B1.VsC.VsNatLk

/-!
# `Hon` from its parts

`Hon` has fields the helpers derive from others: `fs1` (vsnat3's `fsChecks1`, from the returns `RetFs` and the
buffers `BwFs`), `bw2` and `ret2` (vsnat2's `bw2Ret2_honest`, from the native link `L`, the buffers `BwNat`, the
returns `honRet` and the link's pinned calls), `fresh` (vsavoid's `fresh_of`, from `Num6`, the link's `Lk2` and
`D3`), `hend` (`hend_of_steps`, from the pinned ends' steps). **`VsCtx.HonParts x`** is `Hon` with those
replaced by their inputs; **`VsCtx.hon_of_parts : x.HonParts → x.Hon`**.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Guest.B1.Link

@[expose] public section

namespace VsCtx

variable (x : VsCtx)

/-- **The native link's choices**: `natLink_of`'s `L` at the context's layout, the buffers `BwNat`, the returns
agreeing with `honRet`, the link's two non-leaf calls at the pinned ends. -/
def LinkParts : Prop :=
  ∃ (L : LinkNat) (link : LinkEnd) (rest : List E), x.c.proof.stream.drop 12 = L.words x.lay ++ rest ∧
    L.Ok x.lay x.nF x.c.freshClaim link ∧ BwNat x L ∧ (∀ i v, honRet x L i = some v → ∀ σ, x.ret i σ = v) ∧
    x.LkCalls (x.natLk2 L)

/-- **`Hon`'s inputs**: `Hon` with `fresh`, `fs1`, `bw2`, `ret2` and `hend` replaced by what derives them. -/
structure HonParts : Prop where
  ok : x.Ok
  hbw : x.bw.map List.length = vsAllocSz x.p
  hex : ∀ q ∈ x.ex, x.cur + (vsAllocSz x.p).sum ≤ q.1 ∧ q.1 < 2 ^ 63
  hret : CausalRule x.ret
  retFs : x.RetFs
  bwFs : x.BwFs
  bw1 : x.Bw1
  ret1 : x.Ret1
  ret3 : x.Ret3
  num6 : x.Num6
  link : x.LinkParts
  e12 : x.ec 12 = ph11End B2C.fs x.al x.nS x.h0S (x.ec 9)
  hpt : x.c.freshClaim.point = (x.bw.getD 6 []).take 19
  b8 : x.bw.getD 8 [] = x.c.freshClaim.values
  b0 : x.bw.getD 0 [] = x.lay.tableLogHeights.map Prover.count
  b3 : x.bw.getD 3 [] = vsLinkShape x.lay
  b2 : ∃ n, n < 2 ^ 24 ∧ x.σ0 (.n 240) = ofK (g ^ n) ∧
    x.bw.getD 2 [] = (List.range 24).map fun j => LeanVM.Prover.Exec.bitWord (n.testBit j)
  b21 : x.bw.getD 21 [] = mcW x.σ0
  b22 : x.bw.getD 22 [] = mcRc x.σ0
  hlow : ((x.σ0 (.n 2931)).limb 0).lane.toNat % 2 ^ 13 = 0
  d3 : ∃ D : D3, D.Ok x
  steps : ∃ sl, x.EcSteps 36 sl

/-- **`Hon` from its parts.** -/
theorem hon_of_parts (h : x.HonParts) : x.Hon := by
  obtain ⟨L, link, rest, hw, hL, hB, hR, hcalls⟩ := h.link
  have fs1 := VsCtx.fsChecks1 ⟨h.ok, h.hbw, h.hret⟩ h.bw1.front.b18 h.retFs h.bwFs
  obtain ⟨bw2, ret2⟩ := VsCtx.bw2Ret2_honest h.ok h.hbw h.hret fs1 h.bw1 h.ret1 hw hL hB hR hcalls h.e12
  obtain ⟨D, hD⟩ := h.d3
  obtain ⟨L2, hL2⟩ := bw2.lk
  have fr := VsCtx.fresh_of h.ok h.hret h.num6 hL2 hD
  obtain ⟨sl, hs⟩ := h.steps
  obtain ⟨_, _, _, _, hN⟩ := frontNum_of_child h.ok.child
  exact ⟨h.ok, h.hbw, h.hex, h.hret, fr, fs1, h.bw1, bw2,
    ⟨fr, h.hpt, h.b8, h.b0, h.b3, h.b2, h.b21, h.b22, h.hlow, ⟨D, hD⟩⟩, h.ret1, ret2, h.ret3,
    VsCtx.hend_of_steps (x := x) (by norm_num) hN.hp hs⟩

end VsCtx

end
end LeanVM.Guest.B1.VsC
