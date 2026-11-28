/-
  LeanVM.Guest.B1.VsC.VsHonD3L

  `VsD3Left` at the honest context: the facts of `D3.Ok` the pinned calls do not give.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonD3
public import LeanVM.Guest.B1.VsC.VsHonEcIn
public import LeanVM.Guest.B1.VsC.VkPA
public import LeanVM.Guest.B1.VsC.Os.LeftOs
public import LeanVM.Guest.B1.VerifySub.PhLinkEnd

/-!
# `VsD3Left` at the honest context

At `x.honCtx N ec bp bp1`, from `x.Ok`, `N.Ok x.seed x.c` and the pinned calls `VsEcFacts`:

* **`VsCtx.honCtx_h489`**: `.n 489` is `g^(stackLog - 16)` (`certify_stack`'s return over `g^16`);
* **`VsCtx.honCtx_hPo`**: the opening's words in the stream's buffer, the window tables from `Pre`;
* the native lengths: **`NatOpen.Ok.wE_point_length`** (the opening's point has `stackLog` coordinates, from
  `HonRun.finPt`), **`VsCtx.honCtx_kLen`** (the Keccak claim's two points have `τ + 6`, from `VkData`);
* **`VsCtx.honCtx_stk`**: the stack terminal's arrays (`hcarr`, `hfc`, `hcc`) and context `StackCtxAt` (`hPc`);
* **`VsCtx.honCtx_d3Left`**: `VsD3Left` at the honest context.
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

/-! ## The native lengths -/

/-- **The opening's point has `stackLog` coordinates.** -/
theorem NatOpen.Ok.wE_point_length {N : NatOpen} {seed : Digest} {c : Child} (hN : N.Ok seed c) :
    N.wE.point.length = N.layout.stackLog := by
  have h16 := hN.sl16
  have h30 := hN.sl30
  have e : N.layout.stackLog = minOpenLog + (N.layout.stackLog - minOpenLog) := by
    have : minOpenLog = 16 := rfl
    omega
  have hrun := hN.hos
  have hq := hN.hq
  rw [e] at hrun hq
  obtain ⟨S, cfg, Ls, -, hR⟩ := osHonRun_of_open (by show N.layout.stackLog - 16 ≤ 14; omega)
    hN.shape.rate_ge hN.shape.rate_le (carries_capOf (Link.pkPerm (capOf (Link.pkPerm (capOf N.S))))) hrun hq
  obtain ⟨hGl, hTl, hpt, hmu, hla, -⟩ := hR.finPt
  rw [hpt, rotPt, List.length_append, List.length_drop, List.length_take, List.length_append, hGl, hTl, hmu, ← e]
  omega

/-- **The words past the ring grind's nonce**, on a memory reading the stream's buffer. -/
theorem VsCtx.ws_reads {x : VsCtx} {L : LinkNat} {rest xs ws : List E} {n : E} {rd : Reader}
    (hb : L.bits x.lay ≠ 0) (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream) (hm : L.msg.length = 144) (hr : rest = xs ++ n :: ws)
    (h0 : ReadsAt rd (ptrAt (x.base 18)) (x.bw.getD 18 [])) :
    ReadsAt rd (ptrAt (x.natBm L + 144 + xs.length + 1)) ws := by
  have hs := (x.sw_nat hb hw hb18 hm).2 rest.length le_rfl
  rw [List.take_length] at hs
  have hbm : x.base 18 ≤ x.natBm L := by simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]; omega
  have r := readsAt_slice h0 (x.natBm L - x.base 18 + 144) rest.length
  have e1 : x.base 18 + (x.natBm L - x.base 18 + 144) = x.natBm L + 144 := by omega
  rw [e1] at r
  have r' : ReadsAt rd (ptrAt (x.natBm L + 144)) rest := by rw [← hs]; exact r
  have r2 := VsC.readsAt_drop (m := xs.length + 1) r'
  rw [hr, ← Nat.add_assoc] at r2
  simpa using r2

set_option maxRecDepth 100000 in
/-- `verify_keccak`'s frame holds `certify_stack`'s two arrays and its offset. -/
theorem fs_vk_ge : 136 ≤ B2C.fs "verify_keccak" := by
  rw [B2C.fs, coreProgram_indexOf?_at (j := idx% «verify_keccak») rfl]
  decide +kernel

/-- A buffer of the node's words, read on a memory holding them. -/
theorem VsCtx.readsBuf {y : VsCtx} {rd : Reader} (hbw : y.bw.map List.length = vsAllocSz y.p)
    (hW : HoldsWords rd y.Wo) {j : ℕ} (hj : j < 24) (h13 : j ≠ 13) {l : List E} (hl : y.bw.getD j [] = l) :
    ReadsAt rd (ptrAt (y.base j)) l :=
  hl ▸ hW _ (VsCtx.memWo hbw hj h13)

/-- A run read on its prefix. -/
theorem readsAt_padTo {rd : Reader} {p : E} {n : ℕ} {l : List E} (h : ReadsAt rd p (padTo n l)) : ReadsAt rd p l := by
  have h' := readsAt_takeV h l.length
  rwa [padTo_take rfl] at h'

/-- **The pinned ends' order**: `certify_stack`'s arrays (`104` words from `32` past its frame) end before
`open_stacked`'s end, through `verify_keccak`'s frame. -/
theorem VsCtx.fpc_le_ec16 {y : VsCtx} {N : NatOpen} {bp bp1 : ℕ} (hE : VsEcFacts y N bp bp1) :
    y.fpc + B2C.fs "certify_stack" + 136 ≤ y.ec 16 := by
  have h4 := hE.cs
  have h6 := hE.sp
  obtain ⟨h7, h9⟩ := hE.lk
  have h13 := hE.hlt
  have h14 := hE.hvk
  have h15 := hE.hrt
  have h16 := hE.hos
  unfold CsCall at h4
  unfold SpCall at h6
  unfold LrCall at h7
  unfold LrsCall at h9
  unfold LtCall at h13
  unfold VkCall at h14
  unfold RtCall at h15
  obtain ⟨_, _, c4, _⟩ := h4
  obtain ⟨_, _, c6, _⟩ := h6
  obtain ⟨_, _, c7, _⟩ := h7
  obtain ⟨_, _, c9, _⟩ := h9
  obtain ⟨_, _, c13, _⟩ := h13
  obtain ⟨_, _, c14, _⟩ := h14
  obtain ⟨_, _, c15, _⟩ := h15
  obtain ⟨_, _, c16, _⟩ := h16
  have e12 := hE.e12
  have a1 : y.ec 4 ≤ y.fpsp := by
    unfold VsCtx.fpsp; exact le_trans le_leafEnd (le_trans le_leafEnd (le_allocBase _ _))
  have a2 : y.ec 6 ≤ ph7Fp B2C.fs y.al y.wdS (y.ec 6) := by
    unfold ph7Fp; exact le_trans le_leafEnd (le_allocBase _ _)
  have a3 : y.ec 7 ≤ ph8End B2C.fs y.al y.wdS (y.ec 7) := by
    unfold ph8End
    have := le_allocBase (y.al (Link.isNames.getD (y.wdS - 19) "")) (y.ec 7)
    have := le_allocBase (y.al (Link.imNames.getD (y.wdS - 19) ""))
      (allocBase (y.al (Link.isNames.getD (y.wdS - 19) "")) (y.ec 7) + B2C.fs (Link.isNames.getD (y.wdS - 19) ""))
    omega
  have a4 := le_allocBase (y.al (lrsNames.getD (chunkCount y.wdS - 6) "")) (ph8End B2C.fs y.al y.wdS (y.ec 7))
  have a5 : y.ec 9 ≤ ph11End B2C.fs y.al y.nS y.h0S (y.ec 9) := by
    unfold ph11End; exact le_trans le_leafEnd (le_trans le_leafEnd le_leafEnd)
  have a6 := tpKc_ge B2C.fs y.al y.hgS 5 (y.ec 12)
  have a7 := le_allocBase (y.al (Link.ltNames.getD (y.wdS - 19) "")) (tpKc B2C.fs y.al y.hgS 5 (y.ec 12))
  have a8 := le_allocBase (y.al "verify_keccak") (y.ec 13)
  have a9 := le_allocBase (y.al "ring_switch_target") (y.ec 14)
  have a10 := le_allocBase (y.al (openName N.layout.stackLog)) (y.ec 15)
  have := fs_vk_ge
  omega

set_option maxRecDepth 200000 in
theorem vsC_802 : (atomsOf ((vsC.drop 270).take 1200)).contains (.load (.n 802) (.n 801) 0) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem vsSL_802 : vsSL.contains (.load (.n 802) (.n 801) 0) = false := by
  decide +kernel

/-- A part of a run in memory. -/
theorem readsAt_subD {rd : Reader} {p : E} {xs ys : List E} {o : ℕ} (h : ReadsAt rd p xs)
    (hl : o + ys.length ≤ xs.length) (hv : ∀ i < ys.length, xs.getD (o + i) 0 = ys.getD i 0) :
    ReadsAt rd (p * gen ^ o) ys := by
  intro i hi
  have := h (o + i) (by omega)
  rw [← List.getD_eq_getElem _ 0, hv i hi, List.getD_eq_getElem _ _ hi] at this
  exact (loadHolds_mul_gen_pow rd p o i _).mpr this

/-- `check_stack_terminal`'s arrays at `verify_sub`'s values, listed. -/
theorem cstArrays_cstArgsOf (σ : Val) (w : ℕ → E) (chi r kOut kIn f g z : List E) :
    cstArrays (cstArgsOf σ w) chi r kOut kIn f g z =
      [(σ (.n 4), winTabAt + 2 ^ winTabBits), (σ (.n 112), 2 + nTables), (σ (.n 486), nStkBlocks),
        (σ (.n 487), nStkBlocks), (σ (.n 15), chi.length),
        (σ (.n 17) * gen ^ guest_const% EQ_Q_AT, guest_const% N_POINTERS), (σ (.n 12), r.length),
        (σ (.n 20), kOut.length), (σ (.n 20) * gen ^ guest_const% QKECCAK_VARS_CAP, kIn.length),
        (σ (.n 3040), (ringCoefficients f g).length), (w 3992, 40), (w 3993, 40), (σ (.n 22), z.length)] := rfl

namespace VsCtx

section
variable {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ} (hok : x.Ok) (hN : N.Ok x.seed x.c)

local notation "Y" => VsCtx.honCtx x N ec bp bp1
local notation "Z" => VsCtx.honCtx x N (fun _ => 0) 0 0

set_option linter.constructorNameAsVariable false in
include hN in
/-- **`VsD3Left.h489`**: `.n 489` is `certify_stack`'s `g^stackLog` over `g^16`. -/
theorem honCtx_h489 : (Y).σ0 (.n 489) = gen ^ (N.layout.stackLog - 16) := by
  have ha : (Y).args.length = 6 := rfl
  have hgC := vsVal_goodC (rd := (Y).rd0) (w := (Y).w) ha
  have hg3 : ∀ a ∈ vsC3p, Good (Y).rd0 (storesOf 482 vsC) (Y).w (Y).σ0 a := fun a h =>
    hgC (.atom a) (List.mem_of_mem_drop (List.mem_of_mem_take
      (by rw [vsC3_eq]; exact List.mem_append_left _ (List.mem_map_of_mem h))))
  have e485 : (Y).σ0 (.n 485) = gen ^ N.layout.stackLog := by
    rw [← VsCtx.lay_nat (x := Y) hN]
    exact (vsVal_retC (rd0 := (Y).rd0) (w := (Y).w) ha vsC2_eq (.n 485) (by simp)).trans
      (vsW_retC ha honCtx_hret (by decide) honCtx_r485)
  have e488 : (Y).σ0 (.n 488) = word 8198521646651277316 0 := hg3 (.const (.n 488) _) (by simp [vsC3p])
  rw [good_mulF (hg3 (.mul (.n 489) (.n 485) (.n 488)) (by simp [vsC3p])) (by omega) (by omega), e485, e488,
    pow_mul_winv16 hN.sl16]

set_option linter.constructorNameAsVariable false in
include hok hN in
theorem honCtx_hPo1 (rd : Reader) (hW : HoldsWords rd (Y).Wo) :
    ReadsAt rd (ptrAt ((Y).natBm N.L + 144 + N.xs.length + 1)) N.ws := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨hbits, -⟩ := honCtx_link0 hok hN
  have hbw := honCtx_hbw (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have h0 := hW _ (VsCtx.memWo (x := Y) (j := 18) hbw (by norm_num) (by norm_num))
  exact VsCtx.ws_reads (x := Y) hbits hw rfl hL.lenM hN.hrest h0

theorem honCtx_hPo2 (rd : Reader) (hp : (Y).Pre rd) : WinTabs rd (ptrAt ((Y).qt + 178)) := by
  have h := winTabs_of_expWinTab (vsPreA_exp hp).2
  rw [ptrAt_add] at h
  exact h

include hok hN in
/-- **`VsD3Left.hPo`**: the opening's words in the stream's buffer, the window tables from `Pre`. -/
theorem honCtx_hPo : ∀ rd, (Y).Pre rd → HoldsWords rd (Y).Wo →
    ReadsAt rd (ptrAt ((Y).natBm N.L + 144 + N.xs.length + 1)) N.ws ∧ WinTabs rd (ptrAt ((Y).qt + 178)) :=
  fun rd hp hW => ⟨honCtx_hPo1 hok hN rd hW, honCtx_hPo2 rd hp⟩

include hok hN in
/-- **The Keccak claim's two points** have `τ + 6` coordinates, `τ` the Keccak table's log height. -/
theorem honCtx_kLen : N.op.length = N.layout.tableLogHeights.getD opKeccak 0 + qkeccakSlotBits ∧
    N.kp.length = N.op.length := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨hbits, -, hq6, -⟩ := honCtx_link0 hok hN
  obtain ⟨-, -, -, -, -, hτ0, hτ1, hrun⟩ := honCtx_kec (ec := fun _ => 0) (bp := 0) (bp1 := 0) hok hN
  obtain ⟨-, h24, -⟩ := ctx_nums x hok
  have hbw := honCtx_hbw (ec := fun _ => 0) (bp := 0) (bp1 := 0) hok hN
  have hq0 : linkQVars x.lay ≠ 0 := by rw [hq6]; decide
  have hc := VsCtx.hcar_nat (x := Z) honCtx_hret hbits hq0 hw rfl hL.lenM honCtx_r1287
  have h5 : (Z).hgS 5 ≤ 24 := (ctx_nums x hok).2.2.2.1 5 (by norm_num)
  have hl9 : ((Z).bw.getD 9 []).length = 24 := VsCtx.lenbw hbw (by norm_num)
  have hl18 : ((Z).bw.getD 18 []).length = 256 * (Z).p := VsCtx.lenbw hbw (by norm_num)
  obtain ⟨hs1, hs2⟩ := honCtx_stream hok hN
  have hbm : (Z).base 18 ≤ (Z).natBm N.L := by simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]; omega
  have hsw : ((Z).sw ((Z).natBm N.L) 55 25).length = 25 := by
    simp only [VsCtx.sw, List.length_take, List.length_drop, hl18]
    have e1 : (Z).natBm N.L = x.natBm N.L := rfl
    have e2 : (Z).p = x.p := rfl
    have e3 : (Z).base 18 = x.base 18 := rfl
    omega
  obtain ⟨D, hτ, -, hchis, -, -, -, hD, -, hop, hpt, -⟩ := VerifySub.vkData_of_run
    (by have : keccakTauMin = 9 := rfl; omega) (by have : keccakTauMax = 24 := rfl; omega) (by omega) hsw rfl hc
    hrun
  have e1 := VerifySub.VkData.op_length hD
  have e2 := VerifySub.VkData.point_length hD
  rw [hop, hτ] at e1
  rw [hpt, hτ] at e2
  rw [e1, e2, ← VsCtx.hgS_nat (x := Z) hN]
  exact ⟨rfl, rfl⟩


set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 4000000 in
include hok hN in
/-- **`VsD3Left.stk` at the honest context**: `check_stack_terminal`'s arrays (the exponent tables, the kappa sources,
`certify_stack`'s offsets and kappas, the own buffers `.n 15`, `.n 17`'s level, `.n 12`, `.n 20` and its input
half, `.n 3040`, `open_stacked`'s two point buffers, `.n 22`), below `open_stacked`'s end and in the region, the own
buffers, `certify_stack`'s data or `open_stacked`'s; and `StackCtxAt` on every memory with `Pre`, the node's words,
the stack placed and `open_stacked`'s post. -/
theorem honCtx_stk (hE : VsEcFacts Y N bp bp1) : ∃ carr : List (ℕ × ℕ),
    cstArrays (cstArgsOf (Y).σ0 (Y).w) (VsCtx.honD3 (Y) N bp bp1 carr).chi (VsCtx.honD3 (Y) N bp bp1 carr).r
        (VsCtx.honD3 (Y) N bp bp1 carr).kOut (VsCtx.honD3 (Y) N bp bp1 carr).kIn (VsCtx.honD3 (Y) N bp bp1 carr).f
        (VsCtx.honD3 (Y) N bp bp1 carr).g (VsCtx.honD3 (Y) N bp bp1 carr).z = carr.map (fun q => (ptrAt q.1, q.2)) ∧
      (∀ q ∈ carr, q.1 + q.2 ≤ (Y).ec 16) ∧
      (∀ q ∈ carr, ∀ t < q.2, ((Y).R (q.1 + t) ∨ (Y).OwnB (q.1 + t)) ∨
        ((Y).StkCells (q.1 + t) ∨ (VsCtx.honD3 (Y) N bp bp1 carr).Do (q.1 + t))) ∧
      ∀ rd, (Y).Pre rd → HoldsWords rd (Y).Wo →
        StackPlaced rd N.layout ((Y).σ0 (.n 485)) ((Y).σ0 (.n 486)) ((Y).σ0 (.n 487)) →
        (VsCtx.honD3 (Y) N bp bp1 carr).Oo rd →
        StackCtxAt rd (cstArgsOf (Y).σ0 (Y).w) N.layout N.link (VsCtx.honD3 (Y) N bp bp1 carr).chi
          (VsCtx.honD3 (Y) N bp bp1 carr).r (VsCtx.honD3 (Y) N bp bp1 carr).qPoint N.op N.kp (ringF N.S) (ringG N.S)
          N.wE.point (VsCtx.honD3 (Y) N bp bp1 carr).z (ringRho N.S) (ringLam N.S) (N.rm (Y).seed (Y).c) N.outs := by
  have hokY : (Y).Ok := honCtx_ok hok
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨hbits, -, hq6, -⟩ := honCtx_link0 hok hN
  obtain ⟨-, h24, hn24, -, -, hp32⟩ := ctx_nums x hok
  obtain ⟨hout, -, hpend, hopl, hkpl, -⟩ := honCtx_kec (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  obtain ⟨hkl1, hkl2⟩ := honCtx_kLen hok hN
  have hbw := honCtx_hbw (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have h6 := honCtx_num6 (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have htab := tab_ctx hN
  have hlay : N.layout = x.lay := (VsCtx.lay_nat hN).symm
  have hsl16 := hN.sl16
  have hsl30 := hN.sl30
  have hwl := hN.wE_point_length
  have ha : (Y).args.length = 6 := rfl
  obtain ⟨layout, r0, hann, -, hFN⟩ := frontNum_of_child hok.child
  have hl0 : x.lay = layout := VsCtx.lay_of hann
  -- the pointers
  have e4 : (Y).σ0 (.n 4) = ptrAt (Y).qt := vsVal_param ha (i := 4) (by norm_num)
  have e112 : (Y).σ0 (.n 112) = ptrAt ((Y).base 20) :=
    (vsA_run_good ha vsW6_eq vsW6_ne (.hint (.alloc (.n 112) 8)) (by simp [vsW6])).trans
      (vsW_buf (rd1 := (Y).rd1) ha honCtx_hret (j := 20) (by norm_num) rfl)
  have e486 : (Y).σ0 (.n 486) = ptrAt (csOffsAt ((Y).fpc + B2C.fs "certify_stack")) :=
    (vsVal_retC (rd0 := (Y).rd0) (w := (Y).w) ha vsC2_eq (.n 486) (by simp)).trans
      (vsW_retC ha honCtx_hret (by decide) honCtx_r486)
  have e487 : (Y).σ0 (.n 487) = ptrAt (csOffsAt ((Y).fpc + B2C.fs "certify_stack") + 52) :=
    (vsVal_retC (rd0 := (Y).rd0) (w := (Y).w) ha vsC2_eq (.n 487) (by simp)).trans
      (vsW_retC ha honCtx_hret (by decide) honCtx_r487)
  have e15 : (Y).σ0 (.n 15) = ptrAt ((Y).base 9) := VsCtx.ptrBuf honCtx_hret rfl (by norm_num)
  have e12 : (Y).σ0 (.n 12) = ptrAt ((Y).base 6) := VsCtx.ptrBuf honCtx_hret rfl (by norm_num)
  have e17 : (Y).σ0 (.n 17) = ptrAt ((Y).base 11) := VsCtx.ptrBuf honCtx_hret rfl (by norm_num)
  have e20 : (Y).σ0 (.n 20) = ptrAt ((Y).base 14) := VsCtx.ptrBuf honCtx_hret rfl (by norm_num)
  have e22 : (Y).σ0 (.n 22) = ptrAt ((Y).base 16) := VsCtx.ptrBuf honCtx_hret rfl (by norm_num)
  have e3040 : (Y).σ0 (.n 3040) = ptrAt ((Y).base 22) := by
    have g : (Y).σ0 (.n 3040) = (Y).w 3040 := vsC_atoms_good (rd0 := (Y).rd0) (w := (Y).w) ha 2501 984
      (.hint (.alloc (.n 3040) 64)) (by
        rw [as36_eq]
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))))
    exact g.trans (vsW_buf (rd1 := (Y).rd1) ha honCtx_hret (j := 22) (by norm_num) rfl)
  have e3992 : (Y).w 3992 = ptrAt bp := VsCtx.wRet honCtx_hret (by decide) (fun σ => honCtx_ro 1 (by norm_num) σ)
  have e3993 : (Y).w 3993 = ptrAt bp1 := VsCtx.wRet honCtx_hret (by decide) (fun σ => honCtx_ro 2 (by norm_num) σ)
  -- the values
  have hq0 : linkQVars x.lay ≠ 0 := by rw [hq6]; decide
  obtain ⟨-, -, -, r1287⟩ := ret_of_honRet (honCtx_honRet (x := x) (N := N) (ec := ec) (bp := bp) (bp1 := bp1))
  have h1287 : (Y).σ0 (.n 1287) = N.rm x.seed x.c :=
    (VsCtx.rm_nat (x := Y) honCtx_hret hbits hq0 hw rfl hL.lenM r1287).trans (VsCtx.rm_natOpen (x := Y) hN).symm
  have hrd := VsCtx.nonce_reads (x := Y) hbits hw rfl hL.lenM hN.hrest (VsCtx.reads18 (x := Y) hokY hbw)
  obtain ⟨-, hrho, hlam, -⟩ := VsCtx.ring_nat (x := Y) honCtx_hret honCtx_rvk hpend hrd
  have hIR := VsCtx.irReads_nat hokY hbw honCtx_hret (honCtx_fs1 hok hN) (honCtx_bw1 hok hN) h6 hw hL (lb_ctx hN)
    honCtx_bwNat rfl honCtx_honRet honCtx_ret3
  have e802 : (Y).σ0 (.n 802) = N.link.memoryScales.1 := by
    have g : Good (Y).rd0 vsSL (Y).w (Y).σ0 (.load (.n 802) (.n 801) 0) :=
      vsC_atoms_good (rd0 := (Y).rd0) (w := (Y).w) ha 270 1200 _ (by simpa using vsC_802)
    have g' : (Y).σ0 (.n 802) = rdAt (Y).rd0 ((Y).σ0 (.n 801)) 0 :=
      (g : Atom.load (.n 802) (.n 801) 0 ∈ vsSL ∨ _).resolve_left (by simpa using vsSL_802)
    rw [g', hL.link]
    exact hIR.belowMem
  -- the lengths
  have hchl : (N.L.chi (Y).lay (Y).nF).length = (Y).nS := natChi_length
  have hrl : (N.L.r (Y).lay (Y).nF).length = (Y).wdS := natR_length hL
  have hql : (N.L.qPoint (Y).lay (Y).nF).length = 6 := natQ_length htab
  have hzl : (natOodZ x.seed x.c N.layout.stackLog).length = N.layout.stackLog := by
    simp only [natOodZ, List.length_cons, honSqN_length]; omega
  have hcl : (ringCoefficients (ringF N.S) (ringG N.S)).length = 64 :=
    ringCoefficients_length _ _ (honRingF_length _) (honRingG_length _)
  have hNP : guest_const% N_POINTERS ≤ 64 := by decide
  have hch := VsCtx.fpc_le_ec16 hE
  have hfp := VsCtx.le_fpc (x := Y)
  have hs := vsAllocSz_sum (Y).p
  have ht := hokY.ht
  have hf := hokY.hfc
  have e1 : expTabLen = 2226 := rfl
  obtain ⟨-, -, -, -, B6, -, -, B9, -, B11, -, -⟩ := bases_of (x := Y)
  have B14 := VsCtx.base_14 (x := Y)
  have B16 := VsCtx.base_16 (x := Y)
  have B20 : (Y).base 20 = (Y).cur + (824 + 256 * (Y).p) + 6 := vsBaseF_20 _ _
  obtain ⟨-, B22, -⟩ := VsCtx.base_wc (x := Y)
  have hA : (Y).a1 = (Y).cur + (824 + 256 * (Y).p) + 14 := rfl
  have hbp := hE.hbp
  have hbp1 := hE.hbp1
  have hnS : (Y).nS ≤ 24 := hn24
  have hwd : (Y).wdS ≤ 24 := h24
  have hpc : pointCap = 40 := rfl
  have hw2 : winTabAt + 2 ^ winTabBits = 2226 := rfl
  have hnt : nTables = 6 := rfl
  have hsb : nStkBlocks = 52 := rfl
  have hEQ : guest_const% EQ_Q_AT = 62 := rfl
  have hQV : guest_const% QKECCAK_VARS_CAP = 39 := rfl
  have hQV' : qkeccakVarsCap = 39 := rfl
  have hzl' : (natOodZ (Y).seed (Y).c N.layout.stackLog).length = N.layout.stackLog := hzl
  refine ⟨[((Y).qt, winTabAt + 2 ^ winTabBits), ((Y).base 20, 2 + nTables),
    (csOffsAt ((Y).fpc + B2C.fs "certify_stack"), nStkBlocks),
    (csOffsAt ((Y).fpc + B2C.fs "certify_stack") + 52, nStkBlocks), ((Y).base 9, (N.L.chi (Y).lay (Y).nF).length),
    ((Y).base 11 + guest_const% EQ_Q_AT, guest_const% N_POINTERS), ((Y).base 6, (N.L.r (Y).lay (Y).nF).length),
    ((Y).base 14, N.op.length), ((Y).base 14 + guest_const% QKECCAK_VARS_CAP, N.kp.length),
    ((Y).base 22, (ringCoefficients (ringF N.S) (ringG N.S)).length), (bp, 40), (bp1, 40),
    ((Y).base 16, (natOodZ (Y).seed (Y).c N.layout.stackLog).length)], ?_, ?_, ?_, ?_⟩
  · -- the arrays
    dsimp only [VsCtx.honD3]
    rw [cstArrays_cstArgsOf, e4, e112, e486, e487, e15, e17, e12, e20, e3040, e3992, e3993, e22, ptrAt_add, ptrAt_add]
    rfl
  · -- below `open_stacked`'s end
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;>
      (try simp only [hchl, hrl, hcl, hzl', csOffsAt]) <;> omega
  · -- in the region, the own buffers or the callees' data
    dsimp only [VsCtx.honD3]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) t htq <;>
      dsimp only at htq ⊢ <;> (try simp only [hchl, hrl, hcl, hzl'] at htq) <;>
      first
      | exact Or.inl (Or.inl (Or.inl ⟨by omega, by omega⟩))
      | exact Or.inl (Or.inr ⟨by omega, by omega⟩)
      | exact Or.inr (Or.inl ⟨by simp only [csOffsAt]; omega, by simp only [csOffsAt]; omega⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · -- the stack terminal's context
    intro rd hp hW hS hOo
    dsimp only [VsCtx.honD3] at hOo ⊢
    obtain ⟨hpt, hpt1⟩ := hOo
    have rb := fun (j : ℕ) (hj : j < 24) (h13 : j ≠ 13) (l : List E) (hl : (Y).bw.getD j [] = l) =>
      VsCtx.readsBuf hbw hW hj h13 hl
    have r20 := rb 20 (by norm_num) (by norm_num) (1 :: gen ^ x.lay.logMemory :: heightsW x.hg) rfl
    have r9 := readsAt_padTo (rb 9 (by norm_num) (by norm_num) (padTo 24 (N.L.chi x.lay x.nF)) rfl)
    have r6 := readsAt_padTo (rb 6 (by norm_num) (by norm_num) (padTo 24 (N.L.r x.lay x.nF)) rfl)
    have r11 := rb 11 (by norm_num) (by norm_num) (eqLevels ((N.L.qPoint x.lay x.nF).take 6) 6) rfl
    have r14 := rb 14 (by norm_num) (by norm_num) (padTo qkeccakVarsCap N.op ++ padTo qkeccakVarsCap N.kp) rfl
    have r22 := rb 22 (by norm_num) (by norm_num) (ringCoefficients (ringF N.S) (ringG N.S)) rfl
    have r16 := readsAt_padTo (rb 16 (by norm_num) (by norm_num) (padTo 30 (natOodZ x.seed x.c x.lay.stackLog)) rfl)
    obtain ⟨lm, rows, hb⟩ := hN.build
    dsimp only [cstArgsOf, StackCtxAt]
    refine ⟨⟨guestBytecode, rows, by rw [(Stack.buildLayout_some hb).1]; exact hb⟩, by rw [e4]; exact (vsPreA_exp hp).1,
      by rw [e112, hlay]; exact r20, hS, by rw [e15]; exact r9, by rw [hchl]; exact h6.n408,
      by rw [hchl]; exact hn24, fun t ht => ?_, ?_, ?_, hql, ?_, by rw [e12]; exact r6,
      by rw [hrl, hlay]; have h := hFN.hmw; rw [← hl0] at h; exact h, by rw [hlay]; exact h6.n101, by rw [hL.link, hlay]; rfl, e802, ?_,
      h1287, ?_, ?_, ⟨N.kw, hout⟩, hkl1, hkl2, honRingF_length _, honRingG_length _, by rw [e3040]; exact r22,
      hrho, hlam, hwl, by rw [e3992, hwl]; exact hpt, by rw [e3993, hwl]; exact hpt1, by rw [hzl'],
      by rw [e22, hlay]; exact r16⟩
    · rw [hchl, hlay]
      have h := hFN.hht t ht
      rw [← hl0] at h
      exact h
    · rw [hL.link, hlay]
      exact VerifySub.end_pieces htab _ _ _ _ _ _ _ _ _ hL.lenM
    · rw [hL.link, hlay]
      exact VerifySub.end_columns_shape htab _ _ _ _ _ _ _ _ _ hL.lenM
    · -- `eq_q`'s level of the pointer weights' point
      rw [e17]
      have hl6 : 6 ≤ ((N.L.qPoint x.lay x.nF).take 6).length := by rw [List.length_take, natQ_length htab]; omega
      have hlen := eqLevels_length hl6
      have hq6' : (N.L.qPoint x.lay x.nF).take 6 = N.L.qPoint x.lay x.nF :=
        List.take_of_length_le (by rw [natQ_length htab])
      refine readsAt_subD r11 ?_ fun i hi => ?_
      · rw [hlen, List.length_take]
        show 62 + _ ≤ _
        omega
      · rw [List.length_take] at hi
        have hi' : i < 2 ^ 6 := by omega
        have e := eqLevels_lev hl6 6 (by norm_num) le_rfl i hi'
        have hk : eqKernel (((N.L.qPoint x.lay x.nF).take 6).take 6) = eqKernel (N.L.qPoint x.lay x.nF) := by
          rw [List.take_take, Nat.min_self, hq6']
        rw [hk] at e
        rw [List.getD_eq_getElem?_getD, show guest_const% EQ_Q_AT + i = 2 ^ 6 - 2 + i from rfl, e,
          Option.getD_some, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
        rfl
    · show word 0 1 * (Y).σ0 (.n 802) = N.link.memoryScales.2
      rw [e802, hL.link, word_y]
      rfl
    · rw [e20]
      have h := readsAt_takeV r14 N.op.length
      rwa [List.take_append_of_le_length (by rw [padTo_length hopl]; omega), padTo_take rfl] at h
    · rw [e20, ptrAt_add]
      have h := readsAt_slice r14 qkeccakVarsCap N.kp.length
      rwa [List.drop_left' (padTo_length hopl), padTo_take rfl] at h

end

/-- **`VsD3Left` at the honest context**, from the pinned calls. -/
theorem honCtx_d3Left {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ} (_hal : x.al = alW) (hok : x.Ok)
    (hN : N.Ok x.seed x.c) (hE : VsEcFacts (x.honCtx N ec bp bp1) N bp bp1) :
    VsD3Left (x.honCtx N ec bp bp1) N bp bp1 :=
  ⟨honCtx_hchd hok hN, honCtx_h489 hN, honCtx_hPo hok hN, honCtx_stk hok hN hE⟩

end VsCtx

end
end LeanVM.Guest.B1.VsC
