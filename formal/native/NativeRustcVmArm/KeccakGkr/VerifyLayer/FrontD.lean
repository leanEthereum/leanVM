module

public import NativeRustcVmArm.Code.Vm.InstanceWeights.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Code.Vm.SumE.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontC
public import NativeRustcVm.Top.Phases

/-!
# `verify_layer`'s front: the instance weights and the equality-mode sumcheck

From `b31` (`k + NativeRustcVmArm.Vm.VerifyLayer.b31Offset`, `AtH`): the instance weights of `s` into the frame at `968`
(`instance_weights`), their sum `κ` (`sum_e`), the product at `s` (`poly_eval`), the
equality-mode sumcheck over the claim's point into the frame at `1232` and `1712`
(`sumcheck<verify_layer>`), to `b36` (`k + NativeRustcVmArm.Vm.VerifyLayer.b36Offset`, `AtK`, `layer_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Bus.Gkr (Fr.runBlock at_pc)

@[expose] public section

/-- The frame's words from `s` on: the scratch, the claim, its instance weights' count's
address, the layer's weights, the local kernel's second entry. -/
def eWords (m0 : MachineData) : List (Nat × UInt64) :=
  [(120, m0.regs.X4), (136, m0.regs.X3), (80, UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 16)),
    (88, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 51200)),
    (96, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107528))]

/-- **After the equality-mode sumcheck** (`b36`, `k + NativeRustcVmArm.Vm.VerifyLayer.b36Offset`): its challenges `pt` in the frame at
`1232`, its final claim `v` at `1720`, the instance weights of `ch` at `968`, their sum in X25,
X26, the state `s3`. -/
structure AtK [Labels] (m0 : MachineData) (a : DecArea) (ch : EW) (pt : Array EW) (v : EW)
    (s3 : TState) (st : MachineData) : Prop where
  fb : FB m0 st
  fw : Bus.FrameWords st.dmem (base m0 2032) (eWords m0)
  mu : NativeRustcVm.BufEWAt st.dmem (loc m0 968) 16 (keccakInstanceWeights ch).toList
  hpt : NativeRustcVm.EWsAt st.dmem (loc m0 1232) pt.toList
  hps : pt.size ≤ 30
  v0 : NativeRustcVm.WordAt st.dmem (loc m0 1720) v.c0
  v1 : NativeRustcVm.WordAt st.dmem (loc m0 1728) v.c1
  ts : TStateAt st.dmem (tA m0) a s3
  x22 : st.regs.X22 = m0.regs.X0
  x24 : st.regs.X24.toNat = pt.size
  kap : (⟨st.regs.X25, st.regs.X26⟩ : EW) = sumE (keccakInstanceWeights ch)

end

public section

theorem eWords_le (m0 : MachineData) : ∀ q ∈ eWords m0, q.1 + 8 ≤ 152 := by
  intro q hq
  simp only [eWords, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp

theorem eWords_sub (m0 : MachineData) : ∀ q ∈ eWords m0, q ∈ iWords m0 := by
  intro q hq
  simp only [eWords, iWords, pWords, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
  rcases hq with h | h | h | h | h <;> simp [h]

/-- A body's state with the claim at X20. -/
theorem match_claim20 [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
    (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m)
    (hx : m.regs.X20 = m0.regs.X3) :
    Match (Env.ofMachine m [(base m0 2032, 2032), (cA m0, 768)]) claim20S m :=
  match_ofMachine (sregions := [(2032, true), (768, false)])
    (regions := [(base m0 2032, 2032), (cA m0, 768)])
    ⟨rfl, fun _ ↦ Bus.base_aligned hpre.1 (by decide) (by decide), rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hb.sp]; simp)
    ⟨by simp only [Sym.eval, Env.base_ofMachine_eq]
        show (m.regs.X20).toBitVec = _
        rw [hx]; simp, trivial⟩ trivial trivial trivial

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The instance weights and the equality-mode sumcheck**, from `b31` to `b36`. -/
theorem layer_run (hp : Placed code k) (h : VerifyLayerPre a s c m0)
    (hiw : Spec (label NativeRustcVmArm.Vm.InstanceWeights.entryLabel) InstanceWeightsPre InstanceWeightsPost)
    (hsum : Spec (label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hpe : Spec (label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hsl : ∀ s pt, Spec (label NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.entryLabel) (SumcheckLayerPre a s pt)
      (SumcheckLayerPost a s pt))
    {p : Array EW} {ch : EW} {s2 : TState} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b31Offset)) (hh : AtH m0 a p ch s2 st.data)
    (hrun : runL s c m0 = rest3 c p ch s2)
    (cont : ∀ (st' : MachineState) (pt : Array EW) (v : EW) (s3 : TState),
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b36Offset) → AtK m0 a ch pt v s3 st'.data →
      runL s c m0 = rest4 c ch pt v s3 → Eventually (step1 Host.exe) (Goal a s c m0) st') :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have hS := pre_stack h
  have g := geo_of h
  have cx := ctx h
  have := g.hN; have := Geo.sp_lt m0; have := g.hc; have := g.hcs; have := g.htc
  have hcm := hh.cm
  -- `b31`: `instance_weights(frame + 968, s)`.
  refine at_pc hpc (Fr.runBlock hS N_ge rfl hh.fb (blk hp b31_in_code (by simp [b31])) e31 rfl
    rfl (by decide) (by decide) fun st1 hfb1 hd1 hm1 hpc1 ↦ ?_)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b31Offset + b31.length = k + NativeRustcVmArm.Vm.VerifyLayer.b32Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b31_next]] at hpc1
  have x0v : st1.data.regs.X0.toBitVec = loc m0 968 := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ rfl, ev_ptr]
    rfl
  have ech : (⟨st1.data.regs.X1, st1.data.regs.X2⟩ : EW) = ch := by
    rw [show st1.data.regs.X1 = _ from reg_of (r := .X1) hm1 (r' := .X0) rfl,
      show st1.data.regs.X2 = _ from reg_of (r := .X2) hm1 (r' := .X1) rfl]
    show (⟨st.data.regs.X0, st.data.regs.X1⟩ : EW) = ch
    rw [hh.x0, hh.x1]
  have r19 : (st1.data.regs.getXReg .X19).toBitVec = loc m0 968 := by
    rw [hm1.regs .X19 _ rfl, ev_ptr]
    rfl
  have r27 : st1.data.regs.getXReg .X27 = ch.c0 := (reg_of hm1 (r' := .X0) rfl).trans hh.x0
  have r28 : st1.data.regs.getXReg .X28 = ch.c1 := (reg_of hm1 (r' := .X1) rfl).trans hh.x1
  have k1 : Bus.KeepRegs [.X20, .X22] st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
  have hiwN : instanceWeightsStack ≤ 1616 := by have := le_iw; rw [stack_eq] at this; omega
  refine local_call h le_iw (X := InRange (loc m0 968) 264) (o := 968) (n := 264) (by omega)
    (fun q hq ↦ .inr hq) hiw hfb1 hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (writes_split hq.2.1) fun q hq' ↦
      hq'.elim .inl fun ⟨r, hr, hq''⟩ ↦ by
        simp only [List.mem_singleton] at hr
        subst hr
        have h2 : InRange st1.data.regs.X0.toBitVec 264 q := hq''
        rw [x0v] at h2
        exact .inr h2, hq.2.2⟩)
    fun m2 hfb2 hq2 hcs2 hs2 ↦ ?_
  · have hrd := readable_loc h hfb1 (o := 968) (n := 264) (by omega)
    have hof := offStack_loc h hfb1 (o := 968) (n := 264) (N' := instanceWeightsStack)
      (by omega) hiwN
    refine ⟨hfb1.stackOk hS rfl le_iw, ?_⟩
    show Areas st1.data instanceWeightsStack [⟨st1.data.regs.X0.toBitVec, 264⟩] []
    rw [x0v]
    refine ⟨fun r hr ↦ ?_, NativeRustcVm.disjoint_cons_iff.mpr ⟨fun r hr ↦ ?_, by simp⟩,
      fun _ _ _ hr ↦ by simp at hr⟩
    · simp only [List.append_nil, List.mem_singleton] at hr
      subst hr
      exact hrd
    · simp only [List.mem_singleton] at hr
      subst hr
      exact NativeRustcVm.Apart.symm hof
  have hmu2 : NativeRustcVm.BufEWAt m2.dmem (loc m0 968) 16 (keccakInstanceWeights ch).toList := by
    have := hq2.1
    rw [x0v, ech] at this
    exact this
  have hR2 : ∀ q, (InRange (stackBelow st1.data instanceWeightsStack) instanceWeightsStack q ∨
      InRange (loc m0 968) 264 q) →
      Bel m0 q ∨ InRange (loc m0 968) 264 q ∨ ¬InRange (base m0 2032) 2032 q :=
    fun q hq ↦ hq.elim (fun h' ↦ .inl (bel_of g hfb1.sp hiwN h')) (fun h' ↦ .inr (.inl h'))
  have fw2 : Bus.FrameWords m2.dmem (base m0 2032) (eWords m0) :=
    fw_call g hs2 hR2 (by omega) (fun q hq ↦ by have := eWords_le m0 q hq; omega)
      (by rw [hd1]; exact fw_sub hcm.fw (eWords_sub m0))
  have prod2 : NativeRustcVm.EWsAt m2.dmem (loc m0 152) p.toList :=
    ewsAt_same (by rw [hd1]; exact hcm.prod)
      (same_call g hs2 hR2 (by omega) (o' := 152) (n' := 752) (by omega) (by omega))
      (by rw [Array.length_toList, hcm.psz])
  have w32 : NativeRustcVm.WordAt m2.dmem (loc m0 32)
      (UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 288)) :=
    same_word (by rw [hd1]; exact FrameWords.get hcm.fw (by simp [iWords]))
      (same_call g hs2 hR2 (by omega) (o' := 32) (n' := 8) (by omega) (by omega))
  have ts2 : TStateAt m2.dmem (tA m0) a s2 :=
    ts_call h hfb1.sp hiwN hs2 hq2.2.2.2.2 (fun q hq ↦ loc_ts h (o := 968) (n := 264)
      (by omega) hq) (by rw [hd1]; exact hh.ts)
  -- `b32`: `κ`, the instance weights' sum.
  refine Fr.runBlock hS N_ge rfl hfb2 (blk hp b32_in_code (by simp [b32])) e32 rfl rfl
    (by decide) (by decide) fun st3 hfb3 hd3 hm3 hpc3 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b32Offset + b32.length = k + NativeRustcVmArm.Vm.VerifyLayer.b33Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b32_next]] at hpc3
  have hsz : (keccakInstanceWeights ch).toList.length = 16 := by
    rw [Array.length_toList, NativeVm.Math.Keccak.instanceWeights_size]
  have l968 : (Sym.load 0 968 8).eval (Env.ofMachine m2 [(base m0 2032, 2032)]) =
      (BitVec.ofNat 64 16) := by
    rw [ldF (v := (16 : Nat).toUInt64) (by have := hmu2.2.1; rw [hsz] at this; exact this)]
    rfl
  have hc3 : (SBool.cmp .ult .W64 (.load 0 968 8) (.lit 17)).eval
      (Env.ofMachine m2 [(base m0 2032, 2032)]) = true := by
    rw [sb_cmp, ult_apply, l968, litN 17]
    rfl
  have x30 : st3.data.regs.X0.toBitVec = loc m0 976 := by
    show (st3.data.regs.getXReg .X0).toBitVec = _
    rw [hm3.regs .X0 _ rfl, iteT hc3, ev_bin, ev_regU, hcs2 .X19 rfl, r19, ev_lit, add_apply,
      NativeRustcVm.addr_add_add]
  have x31 : st3.data.regs.X1.toNat = 16 := by
    show (st3.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm3.regs .X1 _ rfl, iteT hc3, l968]
    rfl
  have k3 : Bus.KeepRegs [.X20, .X22, .X27, .X28] m2 st3.data := Bus.KeepRegs.of_block hm3 rfl
  refine fleaf h le_sum hsum (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ hq' ↦
      hq'.elim (fun h' ↦ absurd h' (Bus.not_inRange_zero _ _)) id, hq.2.2⟩) hfb3 hpc3
    ⟨by rw [x31], by rw [x30, x31]; exact readable_loc h hfb3 (by omega)⟩
    fun m4 hfb4 hq4 hcs4 hs4 hk4 ↦ ?_
  have K4 : (⟨m4.regs.X0, m4.regs.X1⟩ : EW) = sumE (keccakInstanceWeights ch) := by
    have e := hq4.1
    have hmuw : NativeRustcVm.EWsAt st3.data.dmem (loc m0 976)
        (keccakInstanceWeights ch).toList := by
      have := hmu2.2.2
      rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add] at this
      rw [hd3]; exact this
    rw [slice_eq hmuw x30 (by rw [x31, hsz]), Array.toArray_toList] at e
    exact e
  rw [← hd3] at fw2 prod2 w32 ts2 hmu2
  have fw4 := fw_call g hs4 (o := 0) (n := 0) (fun q hq ↦ .inl hq) (by omega)
    (fun q hq ↦ by have := eWords_le m0 q hq; omega) fw2
  have prod4 := ewsAt_same prod2 (loc_bel g hs4 (o := 152) (n := 752) (by omega))
    (by rw [Array.length_toList, hcm.psz])
  have w32' := same_word w32 (loc_bel g hs4 (o := 32) (n := 8) (by omega))
  have mu4 := NativeRustcVm.Layout.BufEWAt.of_same hmu2
    (loc_bel g hs4 (o := 968) (n := 264) (by omega)) (by omega)
  have ts4 := ts_bel h hk4 hs4 ts2
  -- `b33`: `poly_eval(product, 47, s)`, the point's slots zeroed.
  have hb4 := FB.body h hfb4
  have x20 : m4.regs.X20 = m0.regs.X3 := by
    show m4.regs.getXReg .X20 = _
    rw [hcs4 .X20 rfl, kg k3 .X20, hcs2 .X20 rfl, kg k1 .X20]
    exact hh.x20
  have hwf5 := wf_claim h hb4
  refine exec_at (blk hp b33_in_code (by simp [b33])) e33 hwf5 rfl (match_claim20 h hb4 x20)
    fun st5 hm5 hpc5 ↦ ?_
  have hfb5 := fb_blkW h hfb4 hm5 hwf5 rfl (by decide)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b33Offset + b33.length = k + NativeRustcVmArm.Vm.VerifyLayer.b34Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b33_next]] at hpc5
  have hc4 := claimAt_fb h hfb4
  have hL := hc4.2.2.1
  rw [Array.length_toList] at hL
  have hLw := hc4.2.2.2.1
  rw [Array.length_toList] at hLw
  simp only [NativeRustcVm.KeccakGkr.off, NativeRustcVm.KeccakGkr.pointOff] at hLw
  have hLn : (c.point.size.toUInt64).toBitVec.toNat = c.point.size := by
    simp only [NativeRustcVm.KeccakGkr.claimPointCap] at hL; simp; omega
  have l280 := ld1 (m := m4) (b0 := base m0 2032) (n0 := 2032) (n1 := 768) (o := 280) hLw
  have hcL : (SBool.cmp .ult .W64 (.load 1 280 8) (.lit 31)).eval
      (Env.ofMachine m4 [(base m0 2032, 2032), (cA m0, 768)]) = true := by
    rw [sb_cmp, ult_apply, l280, hLn, litN 31]
    simp only [NativeRustcVm.KeccakGkr.claimPointCap] at hL
    exact decide_eq_true (by omega)
  have x50 : st5.data.regs.X0.toBitVec = loc m0 152 := by
    show (st5.data.regs.getXReg .X0).toBitVec = _
    rw [hm5.regs .X0 _ rfl, ev_ptr]
    rfl
  have x51 : st5.data.regs.X1.toNat = 47 := by
    show (st5.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm5.regs .X1 _ rfl, litN 47]
  have e5 : (⟨st5.data.regs.X2, st5.data.regs.X3⟩ : EW) = ch := by
    rw [show st5.data.regs.X2 = _ from reg_of (r := .X2) hm5 (r' := .X27) rfl,
      show st5.data.regs.X3 = _ from reg_of (r := .X3) hm5 (r' := .X28) rfl,
      hcs4 .X27 rfl, hcs4 .X28 rfl, kg k3 .X27, kg k3 .X28, hcs2 .X27 rfl, hcs2 .X28 rfl, r27,
      r28]
  have r24 : (st5.data.regs.getXReg .X24).toBitVec.toNat = c.point.size := by
    rw [hm5.regs .X24 _ rfl, iteT hcL, l280, hLn]
  have r25 : st5.data.regs.getXReg .X25 = m4.regs.X0 := reg_of hm5 (r' := .X0) rfl
  have r26 : st5.data.regs.getXReg .X26 = m4.regs.X1 := reg_of hm5 (r' := .X1) rfl
  have r29 : (st5.data.regs.getXReg .X29).toBitVec = cA m0 + BitVec.ofNat 64 288 := by
    rw [hm5.regs .X29 _ rfl, iteT hcL, ld0 w32']
  have k5 : Bus.KeepRegs [.X22] m4 st5.data := Bus.KeepRegs.of_block hm5 rfl
  have fw5 := fw_blk hm5 hwf5 [120, 136, 80, 88, 96] rfl (by decide) fw4
  have prod5 := ewsAt_same prod4
    (same_blk hm5 hwf5 (o' := 152) (n' := 752) (by omega) (by decide))
    (by rw [Array.length_toList, hcm.psz])
  have mu5 := NativeRustcVm.Layout.BufEWAt.of_same mu4
    (same_blk hm5 hwf5 (o' := 968) (n' := 264) (by omega) (by decide)) (by omega)
  have ts5 := ts_frame h hm5 hwf5 (by decide) ts4
  have hpeN : polyEvalStack ≤ 1616 := by have := le_pe; rw [stack_eq] at this; omega
  refine fleaf h le_pe hpe (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ hq' ↦
      hq'.elim (fun h' ↦ absurd h' (Bus.not_inRange_zero _ _)) id, hq.2.2⟩) hfb5 hpc5
    ⟨hfb5.stackOk hS rfl le_pe, by rw [x51]; decide,
      by rw [x50, x51]; exact readable_loc h hfb5 (by omega),
      by rw [x50, x51]; exact offStack_loc h hfb5 (by omega) hpeN⟩
    fun m6 hfb6 hq6 hcs6 hs6 hk6 ↦ ?_
  have P6 : (⟨m6.regs.X0, m6.regs.X1⟩ : EW) = polyEval p ch := by
    have e := hq6.1
    rw [slice_eq prod5 x50 (by rw [x51, Array.length_toList, hcm.psz]), Array.toArray_toList,
      show ewArg st5.data.regs.X2 st5.data.regs.X3 = ch from e5] at e
    exact e
  have fw6 := fw_call g hs6 (o := 0) (n := 0) (fun q hq ↦ .inl hq) (by omega)
    (fun q hq ↦ by have := eWords_le m0 q hq; omega) fw5
  have mu6 := NativeRustcVm.Layout.BufEWAt.of_same mu5
    (loc_bel g hs6 (o := 968) (n := 264) (by omega)) (by omega)
  have ts6 := ts_bel h hk6 hs6 ts5
  -- `b34`: the equality-mode sumcheck.
  refine Fr.runBlock hS N_ge rfl hfb6 (blk hp b34_in_code (by simp [b34])) e34 rfl rfl
    (by decide) (by decide) fun st7 hfb7 hd7 hm7 hpc7 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b34Offset + b34.length = k + NativeRustcVmArm.Vm.VerifyLayer.b35Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b34_next]] at hpc7
  have hpt7 : NativeRustcVm.EWsAt st7.data.dmem (cA m0 + BitVec.ofNat 64 288)
      c.point.toList := by
    have := (claimAt_fb h hfb7).2.2.2.2
    rwa [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.KeccakGkr.off,
      NativeRustcVm.KeccakGkr.pointOff, NativeRustcVm.addr_add_add] at this
  have y0 : st7.data.regs.X0.toBitVec = loc m0 1712 := by
    show (st7.data.regs.getXReg .X0).toBitVec = _
    rw [hm7.regs .X0 _ rfl, ev_ptr]
    rfl
  have y22 : st7.data.regs.getXReg .X22 = m0.regs.X0 := by
    rw [reg_of hm7 (r' := .X22) rfl, hcs6 .X22 rfl, kg k5 .X22, hcs4 .X22 rfl, kg k3 .X22,
      hcs2 .X22 rfl, kg k1 .X22]
    exact hh.x22
  have y1 : st7.data.regs.X1.toBitVec = tA m0 := by
    show (st7.data.regs.getXReg .X1).toBitVec = _
    rw [reg_of hm7 (r' := .X22) rfl, hcs6 .X22 rfl, kg k5 .X22, hcs4 .X22 rfl, kg k3 .X22,
      hcs2 .X22 rfl, kg k1 .X22, show st.data.regs.getXReg .X22 = _ from hh.x22]
  have y23 : (⟨st7.data.regs.X2, st7.data.regs.X3⟩ : EW) = polyEval p ch := by
    rw [show st7.data.regs.X2 = _ from reg_of (r := .X2) hm7 (r' := .X0) rfl,
      show st7.data.regs.X3 = _ from reg_of (r := .X3) hm7 (r' := .X1) rfl]
    exact P6
  have y4 : st7.data.regs.X4.toBitVec = cA m0 + BitVec.ofNat 64 288 := by
    show (st7.data.regs.getXReg .X4).toBitVec = _
    rw [reg_of hm7 (r' := .X29) rfl, hcs6 .X29 rfl]
    exact r29
  have y5 : st7.data.regs.X5.toNat = c.point.size := by
    show (st7.data.regs.getXReg .X5).toNat = _
    rw [reg_of hm7 (r' := .X24) rfl, hcs6 .X24 rfl]
    exact r24
  have y6 : st7.data.regs.X6.toBitVec = loc m0 1232 := by
    show (st7.data.regs.getXReg .X6).toBitVec = _
    rw [hm7.regs .X6 _ rfl, ev_ptr]
    rfl
  have y7 : st7.data.regs.X7.toNat = c.point.size := by
    show (st7.data.regs.getXReg .X7).toNat = _
    rw [reg_of hm7 (r' := .X24) rfl, hcs6 .X24 rfl]
    exact r24
  have k7 : Bus.KeepRegs [.X22, .X24, .X25, .X26] m6 st7.data := Bus.KeepRegs.of_block hm7 rfl
  have hslN : sumcheckLayerStack ≤ 1616 := by have := le_sl; rw [stack_eq] at this; omega
  have hat := FB.at_ h hfb7
  have hL30 : c.point.size ≤ 30 := by
    simp only [NativeRustcVm.KeccakGkr.claimPointCap] at hL; exact hL
  refine local_call h le_sl
    (X := fun q ↦ InRange (loc m0 1232) 504 q ∨ InRange (tA m0) tstateBytes q)
    (o := 1232) (n := 504) (by omega) (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h'))
    (hsl s2 c.point) hfb7 hpc7 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q h' ↦ by
      rcases h' with h' | h' | h' | h'
      · rw [y0] at h'
        exact .inr (.inl (loc_mono g (o' := 1712) (n' := 24) (by omega) (by omega) (by omega) h'))
      · rw [y6, y7] at h'
        exact .inr (.inl (loc_mono g (o' := 1232) (n' := 16 * c.point.size) (by omega)
          (by omega) (by omega) h'))
      · rw [y1] at h'
        exact .inr (.inr h')
      · exact .inl h', hq.2.2⟩)
    fun m8 hfb8 hq8 hcs8 hs8 ↦ ?_
  · refine ⟨⟨hfb7.stackOk hS rfl le_sl, cx.rcAt hat le_sl, ?_, ?_, by decide, by decide, ?_, ?_,
      ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show TStateAt st7.data.dmem st7.data.regs.X1.toBitVec a s2
      rw [y1, hd7]; exact ts6
    · show TStateOk st7.data st7.data.regs.X1.toBitVec a sumcheckLayerStack
      rw [y1]; exact cx.tstateOk hat le_sl
    · show OutOk st7.data st7.data.regs.X1.toBitVec a st7.data.regs.X0.toBitVec 24
        sumcheckLayerStack
      rw [y0, y1]; exact cx.outOk hat le_sl (o := 1712) (by omega)
    · show OutOk st7.data st7.data.regs.X1.toBitVec a st7.data.regs.X6.toBitVec
        (16 * st7.data.regs.X7.toNat) sumcheckLayerStack
      rw [y1, y6, y7]; exact cx.outOk hat le_sl (o := 1232) (by omega)
    · show Apart st7.data.regs.X0.toBitVec 24 st7.data.regs.X6.toBitVec
        (16 * st7.data.regs.X7.toNat)
      rw [y0, y6, y7]
      unfold Apart
      rw [g.fa (by omega), g.fa (by omega)]
      omega
    · show c.point.size = st7.data.regs.X5.toNat
      rw [y5]
    · show NativeRustcVm.EWsAt st7.data.dmem st7.data.regs.X4.toBitVec c.point.toList
      rw [y4]; exact hpt7
    · show NoWrap st7.data.regs.X4.toBitVec (16 * c.point.size)
      rw [y4]; exact (readable_cl h hfb7 (o := 288) (n := 16 * c.point.size) (by omega)
        (by omega)).2
    · show Apart st7.data.regs.X4.toBitVec (16 * c.point.size)
        (stackBelow st7.data sumcheckLayerStack) sumcheckLayerStack
      rw [y4]; exact offStack_cl h hfb7 (by omega) (by omega) hslN
    · show Apart st7.data.regs.X4.toBitVec (16 * c.point.size) st7.data.regs.X1.toBitVec
        tstateBytes
      rw [y4, y1]
      unfold Apart
      rw [g.ca (by omega)]
      simp only [tstateBytes]
      omega
    · show Apart st7.data.regs.X4.toBitVec (16 * c.point.size) st7.data.regs.X6.toBitVec
        (16 * st7.data.regs.X7.toNat)
      rw [y4, y6, y7]
      unfold Apart
      rw [g.ca (by omega), g.fa (by omega)]
      omega
  obtain ⟨⟨hopt, hslots, hnext⟩, -, hsv⟩ := hq8
  have hRr : (NativeRustcVm.Sumcheck.sumcheckFn ⟨st7.data.regs.X2, st7.data.regs.X3⟩ 3
      (fun i ↦ c.point[i]?)
      st7.data.regs.X7.toNat).run s2 = (sumcheck (polyEval p ch) 3 (c.point.map some)).run s2 := by
    rw [y7, y23, NativeRustcVm.Sumcheck.sumcheckFn_getElem?]
  rw [hRr, y0] at hopt
  rw [hRr, y6] at hslots
  rw [hRr, y1] at hnext
  have hR8 : ∀ q, (InRange (stackBelow st7.data sumcheckLayerStack) sumcheckLayerStack q ∨
      (InRange (loc m0 1232) 504 q ∨ InRange (tA m0) tstateBytes q)) →
      Bel m0 q ∨ InRange (loc m0 1232) 504 q ∨ ¬InRange (base m0 2032) 2032 q :=
    fun q hq ↦ hq.elim (fun h' ↦ .inl (bel_of g hfb7.sp hslN h'))
      fun h' ↦ h'.elim (fun h'' ↦ .inr (.inl h''))
        fun h'' ↦ .inr (.inr (fouts_not_frame h q (.inl h'')))
  rw [← hd7] at fw6 mu6
  have fw8 := fw_call g hs8 hR8 (by omega) (fun q hq ↦ by have := eWords_le m0 q hq; omega) fw6
  have mu8 := NativeRustcVm.Layout.BufEWAt.of_same mu6
    (same_call g hs8 hR8 (by omega) (o' := 968) (n' := 264) (by omega) (by omega)) (by omega)
  -- `b35`: `None` from the sumcheck?
  refine Fr.runBlock hS N_ge rfl hfb8 (blk hp b35_in_code (by simp [b35])) e35 rfl rfl
    (by decide) (by decide) fun st9 hfb9 hd9 hm9 hpc9 ↦ ?_
  have k9 : Bus.KeepRegs [.X22, .X24, .X25, .X26] m8 st9.data := Bus.KeepRegs.of_block hm9 rfl
  cases hr : (sumcheck (polyEval p ch) 3 (c.point.map some)).run s2 with
  | none =>
    rw [hr] at hopt
    have hc9 : SBool.eval (Env.ofMachine m8 [(base m0 2032, 2032)])
        (.cmp .eq .W64 (.load 0 1712 8) (.lit 0)) = true := by
      rw [sb_cmp, eq_apply, ldF (hopt : NativeRustcVm.WordAt _ _ 0), litN 0]
      rfl
    refine reject hp h ((pc_true hpc9 hc9).trans (label37 hp)) (FB.body h hfb9) ?_
    rw [hrun, rest3, hr]
    rfl
  | some r =>
    obtain ⟨⟨pt, v⟩, s3⟩ := r
    rw [hr] at hopt
    obtain ⟨h1, hv⟩ := hopt
    have hc9 : SBool.eval (Env.ofMachine m8 [(base m0 2032, 2032)])
        (.cmp .eq .W64 (.load 0 1712 8) (.lit 0)) = false := by
      rw [sb_cmp, eq_apply, ldF h1, litN 0]
      rfl
    have hpc9' := pc_false hpc9 hc9
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b35Offset + b35.length = k + NativeRustcVmArm.Vm.VerifyLayer.b36Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b35_next]] at hpc9'
    have hv' := NativeRustcVm.ewAt_iff.mp hv
    rw [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
      at hv'
    have hpsz : pt.size = c.point.size := by
      have := (NativeRustcVm.Top.sumcheck_size _ _ _).gives s2 _ s3 hr
      simpa using this
    refine cont st9 pt v s3 hpc9' ⟨hfb9, by rw [hd9]; exact fw8, by rw [hd9]; exact mu8,
      by rw [hd9]; exact hslots pt v s3 hr, by omega, ?_, ?_, by rw [hd9]; exact hnext _ s3 hr,
      ?_, ?_, ?_⟩ ?_
    · rw [hd9]; exact hv'.1
    · rw [hd9]; exact hv'.2
    · show st9.data.regs.getXReg .X22 = _
      rw [kg k9 .X22, hcs8 .X22 rfl]
      exact y22
    · show (st9.data.regs.getXReg .X24).toNat = _
      rw [kg k9 .X24, hcs8 .X24 rfl, kg k7 .X24, hcs6 .X24 rfl, hpsz]
      exact r24
    · show (⟨st9.data.regs.getXReg .X25, st9.data.regs.getXReg .X26⟩ : EW) = _
      rw [kg k9 .X25, kg k9 .X26, hcs8 .X25 rfl, hcs8 .X26 rfl, kg k7 .X25, kg k7 .X26,
        hcs6 .X25 rfl, hcs6 .X26 rfl, r25, r26]
      exact K4
    · rw [hrun, rest3, hr]
      rfl

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
