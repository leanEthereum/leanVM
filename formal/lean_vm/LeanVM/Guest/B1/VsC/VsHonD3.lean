/-
  LeanVM.Guest.B1.VsC.VsHonD3

  `Bw3.d3` at the honest context: the data from the native run, its facts from the pinned calls.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonAsm
public import LeanVM.Guest.B1.VsC.VsNatSec

/-!
# `D3` at the honest context

**`VsCtx.honD3 y N bp bp1 carr`**: `Ph12` to the end's data from the native run `N`. **`VsD3Left y N bp bp1`**: the
facts of `D3.Ok` not yet proved here (the chunks' `d` bound, `.n 489`, the opening's post `hPo`, the stack terminal's
arrays and context). **`VsCtx.honD3_ok`**: `D.Ok` at the honest context from the pinned calls and `VsD3Left`.
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

/-- **`Ph12` to the end's honest data**, from the native run `N`, `open_stacked`'s buffers and the stack terminal's
arrays `carr`. -/
noncomputable def honD3 (y : VsCtx) (N : NatOpen) (bp bp1 : ℕ) (carr : List (ℕ × ℕ)) : D3 where
  bm := y.natBm N.L
  nx := N.xs.length
  nxo := N.ws.length
  ch := N.L.chunks
  op := N.op
  point := N.kp
  kw := N.kw
  s' := N.s'
  sl := N.layout.stackLog
  wE := N.wE
  bp := bp
  bp1 := bp1
  Ro := fun i => y.R i ∨ y.OwnB i
  Do := fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap)
  Oo := fun rd => ReadsAt rd (ptrAt bp) (N.wE.point ++ List.replicate (pointCap - N.layout.stackLog) 0) ∧
    ReadsAt rd (ptrAt bp1) (N.wE.point.map (1 + ·) ++ List.replicate (pointCap - N.layout.stackLog) 1)
  Po := fun rd => ReadsAt rd (ptrAt (y.natBm N.L + 144 + N.xs.length + 1)) N.ws ∧ WinTabs rd (ptrAt (y.qt + 178))
  Qo := fun rd t => SameStreams (t.pops coreProgram rd)
      (Prover.merkleHints true (Prover.childQueries guestBytecode y.seed y.c) y.c.proof.openings) ∧
    t.Every (ExactAt coreProgram rd)
  layout := N.layout
  link := N.link
  chi := N.L.chi y.lay y.nF
  r := N.L.r y.lay y.nF
  qPoint := N.L.qPoint y.lay y.nF
  kOut := N.op
  kIn := N.kp
  f := ringF N.S
  g := ringG N.S
  xq := N.wE.point
  z := natOodZ y.seed y.c N.layout.stackLog
  rho := ringRho N.S
  lam := ringLam N.S
  rm := N.rm y.seed y.c
  outputs := N.outs
  keccakSlices := N.ks
  oodValue := y.c.proof.stream.getD 11 0
  v0 := N.v0
  v1 := N.v1
  claims := N.claims y.seed y.c
  carr := carr

end VsCtx

/-- **What `D3.Ok` still takes at the honest context** `y`: the chunks' `d` within `.n 10`'s words, `.n 489`, the
opening's post from the node's words and `Pre`, and the stack terminal's arrays `carr` (`hcarr`, `hfc`, `hcc`) and
context (`hPc`) at `honD3`. -/
structure VsD3Left (y : VsCtx) (N : NatOpen) (bp bp1 : ℕ) : Prop where
  hchd : 89 + y.nS + y.wdS + N.L.chunks.d ≤ 153
  h489 : y.σ0 (.n 489) = gen ^ (N.layout.stackLog - 16)
  hPo : ∀ rd, y.Pre rd → HoldsWords rd y.Wo →
    ReadsAt rd (ptrAt (y.natBm N.L + 144 + N.xs.length + 1)) N.ws ∧ WinTabs rd (ptrAt (y.qt + 178))
  stk : ∃ carr : List (ℕ × ℕ),
    cstArrays (cstArgsOf y.σ0 y.w) (VsCtx.honD3 y N bp bp1 carr).chi (VsCtx.honD3 y N bp bp1 carr).r
        (VsCtx.honD3 y N bp bp1 carr).kOut (VsCtx.honD3 y N bp bp1 carr).kIn (VsCtx.honD3 y N bp bp1 carr).f
        (VsCtx.honD3 y N bp bp1 carr).g (VsCtx.honD3 y N bp bp1 carr).z = carr.map (fun q => (ptrAt q.1, q.2)) ∧
      (∀ q ∈ carr, q.1 + q.2 ≤ y.ec 16) ∧
      (∀ q ∈ carr, ∀ t < q.2, (y.R (q.1 + t) ∨ y.OwnB (q.1 + t)) ∨
        (y.StkCells (q.1 + t) ∨ (VsCtx.honD3 y N bp bp1 carr).Do (q.1 + t))) ∧
      ∀ rd, y.Pre rd → HoldsWords rd y.Wo →
        StackPlaced rd N.layout (y.σ0 (.n 485)) (y.σ0 (.n 486)) (y.σ0 (.n 487)) →
        (VsCtx.honD3 y N bp bp1 carr).Oo rd →
        StackCtxAt rd (cstArgsOf y.σ0 y.w) N.layout N.link (VsCtx.honD3 y N bp bp1 carr).chi
          (VsCtx.honD3 y N bp bp1 carr).r (VsCtx.honD3 y N bp bp1 carr).qPoint N.op N.kp (ringF N.S) (ringG N.S)
          N.wE.point (VsCtx.honD3 y N bp bp1 carr).z (ringRho N.S) (ringLam N.S) (N.rm y.seed y.c) N.outs

namespace VsCtx

section
variable {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ} (hok : x.Ok) (hN : N.Ok x.seed x.c)

local notation "Y" => VsCtx.honCtx x N ec bp bp1

include hok hN in
theorem honCtx_w1076 : (Y).w 1076 = ptrAt (x.natBm N.L) := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨-, hR0, hq6, -⟩ := honCtx_link0 hok hN
  obtain ⟨-, -, r1071, -⟩ := ret_of_honRet (honCtx_honRet (x := x) (N := N) (ec := ec) (bp := bp) (bp1 := bp1))
  have hq6Y : linkQVars (Y).lay = 6 := hq6
  have hne3 : (Y).natLC N.L ≠ [] := natChain_ne (by omega) _ _
  have hcapC : (Link.chainLast ⟨[], 0, 0⟩ ((Y).natLC N.L)).cap.length = 5 := natChain_last_cap (by omega) _ _ _
  rw [honCtx_w (by decide) (r1071 5 (by norm_num)), cells_getD_5 hcapC]
  exact VsCtx.natLC_cur (x := Y) hL hR0 (by omega)

include hok hN in
/-- **`D3.Ok.hid`'s link section values** at the honest context. -/
theorem honCtx_sec : LinkSecVals Y N.L := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  have hokY : (Y).Ok := honCtx_ok hok
  have hbw := honCtx_hbw (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  exact VsCtx.linkSecVals_of_runs (x := Y) hL (tab_ctx hN) (lb_ctx hN) (honCtx_fresh hok hN)
    (VsCtx.linkSecAtoms_honest hokY honCtx_hret hbw (honCtx_bw1 hok hN))
    (VsCtx.irReads_nat hokY hbw honCtx_hret (honCtx_fs1 hok hN) (honCtx_bw1 hok hN) (honCtx_num6 hok hN) hw hL
      (lb_ctx hN) honCtx_bwNat rfl honCtx_honRet honCtx_ret3)

end

/-- **`D3.Ok` at the honest context** from the pinned calls and `VsD3Left`. -/
theorem honD3_ok {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ} (hok : x.Ok) (hN : N.Ok x.seed x.c)
    (hE : VsEcFacts (x.honCtx N ec bp bp1) N bp bp1) (hl : VsD3Left (x.honCtx N ec bp bp1) N bp bp1) :
    ∃ D : D3, D.Ok (x.honCtx N ec bp bp1) := by
  obtain ⟨hw, hL⟩ := natL_ctx hN
  obtain ⟨hbits, hR0, hq6, hwd⟩ := honCtx_link0 hok hN
  obtain ⟨hs1, hs2⟩ := honCtx_stream hok hN
  obtain ⟨h19, h24, -⟩ := ctx_nums x hok
  have hokY : (x.honCtx N ec bp bp1).Ok := honCtx_ok hok
  have hq0 : linkQVars (x.honCtx N ec bp bp1).lay ≠ 0 := by
    rw [show linkQVars (x.honCtx N ec bp bp1).lay = 6 from hq6]; decide
  have hrl : (x.honCtx N ec bp bp1).lay.tableRows.length = 6 := by
    rw [VsCtx.lay_nat (x := x.honCtx N ec bp bp1) hN, hN.shape.rows_length]; rfl
  have hbw := honCtx_hbw (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  obtain ⟨hout, hks, hpend, hopl, hkpl, hτ0, hτ1, hrun⟩ := honCtx_kec (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  have hrd := VsCtx.nonce_reads (x := x.honCtx N ec bp bp1) hbits hw rfl hL.lenM hN.hrest
    (VsCtx.reads18 (x := x.honCtx N ec bp bp1) hokY hbw)
  have hmsg : (x.honCtx N ec bp bp1).sw (x.natBm N.L) 0 144 = N.L.msg :=
    VsCtx.msg_nat (x := x.honCtx N ec bp bp1) hbits hw rfl hL.lenM
  obtain ⟨-, -, -, b23⟩ := honCtx_ring (ec := ec) (bp := bp) (bp1 := bp1) hok hN
  obtain ⟨-, r767, r1071, r1287⟩ :=
    ret_of_honRet (honCtx_honRet (x := x) (N := N) (ec := ec) (bp := bp) (bp1 := bp1))
  have hb15 : ((x.honCtx N ec bp bp1).bw.getD 15 []).take 64 = N.ks := by
    show N.ks.take 64 = N.ks
    exact List.take_of_length_le (by omega)
  obtain ⟨hrun', hop, hpt, hptl⟩ := VsCtx.kec_bufs (x := x.honCtx N ec bp bp1) (bm := x.natBm N.L) hb15 rfl hopl hkpl
    hrun
  have r3810 := VsCtx.r3810_nat (x := x.honCtx N ec bp bp1) rfl honCtx_hret honCtx_rvk hpend hrd
    (by intro σ; rw [honCtx_r3810, hmsg]; rfl)
  have h3810 := VsCtx.h3810_nat (x := x.honCtx N ec bp bp1) hN honCtx_hret r3810 hb15 hks hmsg
    (VsCtx.ringVals_nat (x := x.honCtx N ec bp bp1) rfl honCtx_hret honCtx_rvk hpend hrd).2.2.2.2
    ((VsCtx.ringVals_nat (x := x.honCtx N ec bp bp1) rfl honCtx_hret honCtx_rvk hpend hrd).1.trans
      (ringChs_take16 _).symm)
  have hm1 := VsCtx.m1_nat (x := x.honCtx N ec bp bp1) hw hbits (by omega) hL.lenI honCtx_hret rfl
    (VsCtx.reads18 (x := x.honCtx N ec bp bp1) hokY hbw) r767
  have h1287 : (x.honCtx N ec bp bp1).σ0 (.n 1287) = N.rm x.seed x.c := by
    exact (VsCtx.rm_nat (x := x.honCtx N ec bp bp1) honCtx_hret hbits hq0 hw rfl hL.lenM r1287).trans
      (VsCtx.rm_natOpen (x := x.honCtx N ec bp bp1) hN).symm
  obtain ⟨carr, hcarr, hfc, hcc, hPc⟩ := hl.stk
  set D := honD3 (x.honCtx N ec bp bp1) N bp bp1 carr with hD
  have hos := VsCtx.hos_honest (x.honCtx N ec bp bp1) D hN hout (honCtx_honB hok hN) rfl honCtx_ret1F honCtx_bwFs
    rfl honCtx_rvk hpend hrd h3810 hm1 h1287 (congrArg (List.take 55) hmsg) hE.hos
  refine ⟨D, {
    hbm := honCtx_w1076 hok hN
    hbmIn := ⟨by show x.base 18 ≤ x.natBm N.L; simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]; omega, by
      show x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p; omega⟩
    hch := hL.chunks
    hchw := by show N.L.chunks.width ≤ 24; omega
    hchd := hl.hchd
    hid := VsCtx.hid_nat (x := x.honCtx N ec bp bp1) honCtx_hret (honCtx_bw1 hok hN) (honCtx_fs1 hok hN)
      (honCtx_hood hok hN) hw hL (tab_ctx hN) (lb_ctx hN) hrl h19 h24 hR0 rfl rfl r1071
      hL.chunks rfl (honCtx_sec hok hN)
    hτ0 := hτ0
    hτ1 := hτ1
    hcar := VsCtx.hcar_nat (x := x.honCtx N ec bp bp1) honCtx_hret hbits hq0 hw rfl hL.lenM r1287
    hrun := hrun'
    hpend := hpend
    hop := hop
    hopl := hopl
    hpt := hpt
    hptl := hptl
    rvk := honCtx_rvk
    r3810 := r3810
    b23 := b23
    h16 := hN.sl16
    h30 := hN.sl30
    h489 := hl.h489
    hos := hos
    ro := honCtx_ro
    hRo := fun _ h => h
    hPo := hl.hPo
    hQo := VsCtx.hQo_nat _ _
    hbp := hE.hbp
    hbp1 := hE.hbp1
    hlay := (VsCtx.lay_nat hN).symm
    hcl := hN.hcl
    hsl := hN.sl30
    hsid := VsCtx.hsid_nat _ D honCtx_hret honCtx_ro hN.hacc rfl
    hcarr := hcarr
    hfc := hfc
    hcc := hcc
    hPc := hPc
    hlt := hE.hlt
    hvk := hE.hvk
    hrt := by
      have h := VsCtx.hrt_nat (x := x.honCtx N ec bp bp1) rfl honCtx_hret honCtx_rvk hpend hrd hE.hrt
      rw [← hmsg] at h
      exact h }⟩

end VsCtx

end
end LeanVM.Guest.B1.VsC
