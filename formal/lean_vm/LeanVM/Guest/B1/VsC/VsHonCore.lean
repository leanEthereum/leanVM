/-
  LeanVM.Guest.B1.VsC.VsHonCore

  The honest context's facts that name no pinned call.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonBwF
public import LeanVM.Guest.B1.VsC.VsNum6B
public import LeanVM.Guest.B1.VsC.VsAvoid
public import LeanVM.Guest.B1.VsC.VsNatIr

/-!
# The honest context's call-free facts

At `x.honCtx N ec bp bp1`, for every `ec`, `bp`, `bp1`, from `x.Ok` and `N.Ok x.seed x.c`: the native link's facts
at the context, the buffers' sizes, `VsFsChecks1`, `Bw1`, `Ret1F`, `Num6`, `BwNat`, the bridge `hood`, `Ret1.r680`.
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

namespace VsCtx

section
variable {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ} (hok : x.Ok) (hN : N.Ok x.seed x.c)

local notation "Y" => VsCtx.honCtx x N ec bp bp1

theorem honCtx_ok (h : x.Ok) : (Y).Ok := ⟨h.child, h.ht, h.ho, h.hfc, h.pre, h.hcur⟩

include hN in
/-- The native run's link at the context's layout and sponge. -/
theorem natL_ctx : x.c.proof.stream.drop 12 = N.L.words x.lay ++ N.rest ∧
    N.L.Ok x.lay x.nF x.c.freshClaim N.link := by
  rw [VsCtx.lay_nat hN, VsCtx.nF_nat hN]
  exact ⟨hN.hw, hN.hL⟩

include hN in
theorem tab_ctx : x.lay.tables = tables := by rw [VsCtx.lay_nat hN]; exact announced_tables hN.hann

include hN in
theorem lb_ctx : x.lay.logBytecode = 19 := by
  rw [VsCtx.lay_nat hN]
  exact Nat.pow_right_injective (le_refl 2) (hN.shape.logBytecode_eq.symm.trans guest_logBytecode)

theorem honCtx_bwNat : BwNat Y N.L := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem honCtx_r1287 : ∀ j < 6, ∀ σ, (Y).ret (1287 + j) σ = ((Y).natPm N.L).getD j 0 :=
  (ret_of_honRet honCtx_honRet).2.2.2

theorem honCtx_h9 : ((Y).bw.getD 9 []).take (Y).nS = N.L.chi (Y).lay (Y).nF :=
  padTo_take natChi_length

include hok hN in
/-- **`kec_nat` at the honest context**, with the output claim `N.op`, `N.kw`. -/
theorem honCtx_kec : N.outs = [⟨qkeccak, N.op, N.kw⟩] ∧ N.ks.length = 64 ∧ N.s'.pend.length = rateScalars ∧
    N.op.length ≤ qkeccakVarsCap ∧ N.kp.length ≤ qkeccakVarsCap ∧ keccakTauMin ≤ (Y).hgS 5 ∧
    (Y).hgS 5 ≤ keccakTauMax ∧
    RunsTo (verifyKeccak ((Y).hgS 5) (((Y).bw.getD 9 []).take ((Y).hgS 5)) ((Y).sw ((Y).natBm N.L) 55 25))
      ⟨[(Y).w 1288, (Y).w 1289, (Y).w 1290, (Y).w 1291, (Y).w 1292], []⟩ ((Y).sw ((Y).natBm N.L) 144 N.xs.length)
      ([⟨qkeccak, N.op, N.kw⟩], N.kp, N.ks) N.s' := by
  obtain ⟨layout, r, hann, -, hFN⟩ := frontNum_of_child hok.child
  have e := hN.hann
  rw [hann] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨op, kw, hout, h1, h2, h3, h4, h5, h6, h7⟩ := VsCtx.kec_nat (x := Y) (L := N.L) honCtx_hret hN.hann hFN
    hN.hw hN.hL hN.hln hN.hrest hN.hrun rfl honCtx_r1287 honCtx_h9
  have eo : N.op = op := by unfold NatOpen.op; rw [hout]; rfl
  have ek : N.kw = kw := by unfold NatOpen.kw; rw [hout]; rfl
  rw [eo, ek]
  exact ⟨hout, h1, h2, h3, h4, h5, h6, h7⟩

theorem honRingChs_length (S : KeccakState) : (ringChs S).length = 18 := by
  simp [ringChs, Link.pkSqueeze_length]

theorem honRingF_length (S : KeccakState) : (ringF S).length = 8 := by
  simp [ringF, honRingChs_length, ringMapWidth]

theorem honRingG_length (S : KeccakState) : (ringG S).length = 8 := by
  simp [ringG, honRingChs_length, ringMapWidth]

include hok hN in
/-- **The honest buffers' sizes.** -/
theorem honCtx_hbw : (Y).bw.map List.length = vsAllocSz (Y).p := by
  obtain ⟨h19, h24, hn, hhg, hps, -⟩ := ctx_nums x hok
  obtain ⟨hw, hL⟩ := natL_ctx hN
  have htab := tab_ctx hN
  obtain ⟨-, hks, -, hop, hkp, -⟩ := honCtx_kec (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have h4 := honB4_length x hok
  obtain ⟨l5, l6, l7, l9, l10, l11, l12⟩ := BwNat.lengths (x := Y) honCtx_bwNat hL htab h24 hn
    (by show 54 ≤ x.honB4.length; omega)
  have l0 : (x.lay.tableLogHeights.map Prover.count).length = 6 := by
    rw [List.length_map]; exact lay_heights_length hN
  have l1 : ((List.range 6).flatMap (fun t => padTo 26 (tsBitsW (x.rows t) (x.hg t)))).length = 156 := by
    have hf : ∀ t ∈ List.range 6, (padTo 26 (tsBitsW (x.rows t) (x.hg t))).length = 26 := fun t ht =>
      padTo_length (by rw [tsBitsW_length]; have := hhg t (List.mem_range.mp ht); omega)
    rw [List.length_flatMap, List.map_congr_left hf]
    rfl
  have l8 : x.c.freshClaim.values.length = 36 := by rw [hL.values]; rfl
  have l14 : (padTo qkeccakVarsCap N.op ++ padTo qkeccakVarsCap N.kp).length = 78 := by
    rw [List.length_append, padTo_length hop, padTo_length hkp]; rfl
  have l16 : (padTo 30 (natOodZ x.seed x.c x.lay.stackLog)).length = 30 := by
    refine padTo_length ?_
    have h30 := hN.sl30
    rw [← VsCtx.lay_nat hN] at h30
    simp only [natOodZ, List.length_cons, honSqN_length]
    omega
  have l21 : (ringF N.S ++ ringG N.S).length = 16 := by
    rw [List.length_append, honRingF_length, honRingG_length]
  have l22 : (ringCoefficients (ringF N.S) (ringG N.S)).length = 64 :=
    ringCoefficients_length _ _ (honRingF_length _) (honRingG_length _)
  show [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _].map List.length = _
  simp only [List.map_cons, List.map_nil]
  rw [l0, l1, h4, l8, l14, hks, l16, hps, l21, l22, rsW_length]
  have l5' : (eqLevels (ph7Rs x.honB4) 4).length = 30 := l5
  have l6' : (padTo 24 (N.L.r x.lay x.nF)).length = 24 := l6
  have l7' : (padTo 25 ((List.range (x.wdS + 1)).map (Link.belowE (N.L.r x.lay x.nF)))).length = 25 := l7
  have l9' : (padTo 24 (N.L.chi x.lay x.nF)).length = 24 := l9
  have l10' : (N.L.qPoint x.lay x.nF).length = 6 := l10
  have l11' : (eqLevels ((N.L.qPoint x.lay x.nF).take 6) 6).length = 126 := l11
  have l12' : (padTo 25 ((List.range (x.nS + 1)).map (Link.belowE (N.L.chi x.lay x.nF)))).length = 25 := l12
  rw [l5', l6', l7', l9', l10', l11', l12']
  simp [cbL, vsLinkShape, rowsW, heightsW, vsAllocSz, vsSz0]
  rfl

include hok hN in
theorem honCtx_honB : (Y).HonB := ⟨honCtx_ok hok, honCtx_hbw hok hN, honCtx_hret⟩

include hok hN in
theorem honCtx_fs1 : VsFsChecks1 Y :=
  VsCtx.fsChecks1 (honCtx_honB hok hN) rfl honCtx_retFs honCtx_bwFs

include hok hN in
theorem honCtx_hood : [(Y).σ0 (.n 507), (Y).σ0 (.n 508), (Y).σ0 (.n 509), (Y).σ0 (.n 510), (Y).σ0 (.n 511)] =
    capOf (natOodS x.seed x.c) :=
  VsCtx.hood_of (honCtx_ok hok) (honCtx_hbw hok hN) honCtx_hret rfl

include hok hN in
theorem honCtx_bw1F : (Y).Bw1F := by
  obtain ⟨-, -, -, hhg, -⟩ := ctx_nums x hok
  refine ⟨(honCtx_b0 hN).symm, fun t ht k hk => ?_, rfl, honCtx_b3, rfl, rfl, rfl⟩
  have hf : ∀ t' < 6, (padTo 26 (tsBitsW (x.rows t') (x.hg t'))).length = 26 := fun t' ht' =>
    padTo_length (by rw [tsBitsW_length]; have := hhg t' ht'; omega)
  have hk' : k < (tsBitsW (x.rows t) (x.hg t)).length := hk
  have hk26 : k < 26 := by
    have := hhg t ht
    rw [tsBitsW_length] at hk'
    omega
  show ((List.range 6).flatMap (fun t => padTo 26 (tsBitsW (x.rows t) (x.hg t))))[26 * t + k]? = _
  rw [flatMap_range_getElem? 6 hf t k ht hk26]
  exact padTo_getElem? hk'

include hok hN in
theorem honCtx_bw1 : (Y).Bw1 := by
  refine ⟨honCtx_bw1F hok hN, ?_, fun k hk => ?_⟩
  · show (x.honB4)[0]? = some ((Y).w (573 + 0))
    rw [honCtx_w573 0 (by omega)]
    unfold honB4
    rw [padTo_getElem? (by simp)]
    rfl
  · rw [honCtx_w575, show (Y).pk = x.pk from rfl, pkSqueeze_length] at hk
    rw [honCtx_w575]
    show (x.honB4)[k + 1]? = _
    unfold honB4
    rw [padTo_getElem? (by simp [pkSqueeze_length]; omega)]
    rfl

theorem honCtx_r680l : [(Y).w 680, (Y).w 681, (Y).w 682, (Y).w 683, (Y).w 684] =
    (pkSqueeze (Y).pk [(Y).w 575, (Y).w 576, (Y).w 577, (Y).w 578, (Y).w 579]).2 := by
  rw [honCtx_w575, honCtx_w680 0 (by omega), honCtx_w680 1 (by omega), honCtx_w680 2 (by omega),
    honCtx_w680 3 (by omega), honCtx_w680 4 (by omega)]
  have hl := Link.pkSqueeze_cap_length x.pk [x.omN.getD 2 0, x.omN.getD 3 0, x.omN.getD 4 0, x.omN.getD 5 0,
    x.omN.getD 6 0] rfl
  exact (list5 hl).symm

include hok hN in
theorem honCtx_num6 : (Y).Num6 :=
  VsCtx.num6_of (honCtx_ok hok) (honCtx_hbw hok hN) (by simp [honCtx]) honCtx_hret (honCtx_bw1F hok hN) honCtx_ret1F
    honCtx_r484

include hok hN in
/-- The link grind's bits are nonzero, the link's rows and pointer variables too. -/
theorem honCtx_link0 : N.L.bits x.lay ≠ 0 ∧ linkRows x.lay ≠ 0 ∧ linkQVars x.lay = 6 ∧
    N.L.chunks.width = x.wdS := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨h19, -⟩ := ctx_nums x hok
  obtain ⟨layout, r, hann, -, hFN⟩ := frontNum_of_child hok.child
  have hl : x.lay = layout := VsCtx.lay_of hann
  have hwd : N.L.chunks.width = x.wdS := VerifySub.chunks_width hL.chunks
  refine ⟨grindingBits_ne (le_max_of_le_right (by omega)), ?_, VerifySub.linkQVars_tables (tab_ctx hN), hwd⟩
  have h5 : 9 ≤ layout.tableLogHeights.getD 5 0 := hFN.h9
  have h55 : layout.tableLogHeights.getD 5 0 ≤ hMax layout := hFN.hht 5 (by norm_num)
  show hMax x.lay ≠ 0
  rw [hl]; omega

include hok hN in
/-- **The stream's layout past the link**: the packed message's cursor, the Keccak reduction's words, the ring
grind's nonce and the opening's words end at the stream's end, inside its `256 p` words. -/
theorem honCtx_stream : x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length = x.base 18 + x.c.proof.stream.length ∧
    x.c.proof.stream.length ≤ 256 * x.p := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨-, -, -, -, hps, -⟩ := ctx_nums x hok
  obtain ⟨hbits, -⟩ := honCtx_link0 hok hN
  have e := congrArg List.length hw
  rw [hN.hrest] at e
  simp [LinkNat.words, grindWords, hbits] at e
  have hm := hL.lenM
  have hp : x.c.proof.stream.length ≤ (padStream x.c.proof.stream).length := by simp [padStream]
  refine ⟨?_, by omega⟩
  simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]
  omega

include hok hN in
/-- **`AvoidHyp` at the honest context**, from the native run alone (no pinned call). -/
theorem honCtx_avoidHyp : (Y).AvoidHyp := by
  have h6 := honCtx_num6 (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  obtain ⟨layout, r, hann, -, hFN⟩ := frontNum_of_child hok.child
  have hl : x.lay = layout := VsCtx.lay_of hann
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨hbits, hR0, hq6, hwd⟩ := honCtx_link0 hok hN
  obtain ⟨hs1, hs2⟩ := honCtx_stream hok hN
  obtain ⟨-, r767, r1071, -⟩ := ret_of_honRet (honCtx_honRet (x := x) (N := N) (ec := ec) (bp := bp) (bp1 := bp1))
  have h19 : 19 ≤ x.wdS := (ctx_nums x hok).1
  have hb18 : (Y).base 18 = x.base 18 := rfl
  refine ⟨hok.ht, hok.hfc, hok.hcur, hFN.hp1, hFN.hp, honCtx_hret, ⟨x.wdS, ?_, ?_, h6.n409⟩, ⟨x.mS, ?_, h6.n101⟩,
    fun t ht => ?_, fun i hi => ?_⟩
  · omega
  · exact (by simp only [VsCtx.wdS, hl]; exact hFN.hw24)
  · have := hFN.hmw; have := hFN.hw24; simp only [VsCtx.mS, hl]; omega
  · rcases Nat.eq_zero_or_pos t with rfl | h0
    · refine ⟨x.h0S, ?_, h6.n115⟩
      simp only [VsCtx.h0S, hl]; exact hFN.h24 0 (by norm_num)
    · refine ⟨x.hgS t, ?_, h6.sel t h0 ht⟩
      simp only [VsCtx.hgS, hl]; exact hFN.h24 t (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    have hwdY : N.L.chunks.width = (Y).wdS := hwd
    have h19Y : 19 ≤ (Y).wdS := h19
    have hq6Y : linkQVars (Y).lay = 6 := hq6
    have hR0Y : linkRows (Y).lay ≠ 0 := hR0
    rcases hi with rfl | rfl | rfl
    · show ∃ a, (Y).w 772 = ptrAt a ∧ x.base 18 ≤ a ∧ a ≤ x.base 18 + 256 * x.p
      refine ⟨x.natB772 N.L, ?_, by simp only [VsCtx.natB772, VsCtx.sI]; omega, by
        simp only [VsCtx.natBm] at hs1; simp only [VsCtx.natB772, VsCtx.sI] at hs1 ⊢; omega⟩
      have hne1 : (Y).natLI N.L ≠ [] := natChain_ne (by omega) _ _
      have hcapI : (Link.chainLast ⟨[], 0, 0⟩ ((Y).natLI N.L)).cap.length = 5 := natChain_last_cap (by omega) _ _ _
      rw [honCtx_w (by decide) (r767 5 (by norm_num)), cells_getD_5 hcapI,
        chainLast_ne hne1 _ ⟨N.L.cap2 (Y).lay (Y).nF, ptrAt (Y).sI, (Y).clI⟩, VsCtx.natLI, LinkNat.chainI, natChain_cur,
        ← hL.lenI, ptrAt_add]
      rfl
    · show ∃ a, (Y).w 1076 = ptrAt a ∧ x.base 18 ≤ a ∧ a ≤ x.base 18 + 256 * x.p
      refine ⟨x.natBm N.L, ?_, by simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]; omega, by omega⟩
      have hne3 : (Y).natLC N.L ≠ [] := natChain_ne (by omega) _ _
      have hcapC : (Link.chainLast ⟨[], 0, 0⟩ ((Y).natLC N.L)).cap.length = 5 := natChain_last_cap (by omega) _ _ _
      rw [honCtx_w (by decide) (r1071 5 (by norm_num)), cells_getD_5 hcapC]
      exact VsCtx.natLC_cur (x := Y) hL hR0Y (by omega)
    · show ∃ a, (Y).w 2920 = ptrAt a ∧ x.base 18 ≤ a ∧ a ≤ x.base 18 + 256 * x.p
      refine ⟨x.natBm N.L + 144 + N.xs.length, ?_, by simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]; omega,
        by omega⟩
      have hc5 : (capOf N.s'.perm).length = 5 := rfl
      rw [honCtx_w (by decide) (honCtx_rvk 5 (by norm_num)), vkRets, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hc5]), hc5]
      simp [ptrAt_mul_pow]

include hok hN in
/-- **`Hon.fresh` at the honest context.** -/
theorem honCtx_fresh : VsFresh (Y).rd1 (Y).rd0 (Y).w (Y).args :=
  VsCtx.fresh_of_avoid (vsAvoid_of_hyp (honCtx_avoidHyp hok hN))

end

end VsCtx

end
end LeanVM.Guest.B1.VsC
