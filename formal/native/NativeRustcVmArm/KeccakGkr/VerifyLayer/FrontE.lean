module

public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontD

/-!
# `verify_layer`'s front: the plain sumcheck, the three values, the local kernel

From `b36` (`k + NativeRustcVmArm.Vm.VerifyLayer.b36Offset`, `AtK`): the plain sumcheck over the `11` local bits into the frame at
`1712` and `1888` (`sumcheck<sumcheck_plain>`), the three values into the frame at `1888`
(`read_scalars`), the equality kernel of the local point into the scratch at `107520`
(`eq_kernel`), to `b42` (`k + NativeRustcVmArm.Vm.VerifyLayer.b42Offset`, `AtL`, `plain_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Bus.Gkr (Fr.runBlock at_pc)

@[expose] public section

/-- **After the local kernel** (`b42`, `k + NativeRustcVmArm.Vm.VerifyLayer.b42Offset`): the local point `lp` and its kernel in the
scratch at `107520` (the frame's word `144`), the three values `tv` in the frame at `1888`, the
plain sumcheck's claim `val` in X20, X19, the state `s5`. -/
structure AtL [Labels] (m0 : MachineData) (a : DecArea) (ch : EW) (pt lp tv : Array EW)
    (val : EW) (s5 : TState) (st : MachineData) : Prop where
  fb : FB m0 st
  fw : Bus.FrameWords st.dmem (base m0 2032) (eWords m0)
  f144 : NativeRustcVm.WordAt st.dmem (loc m0 144)
    (UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107520))
  mu : NativeRustcVm.BufEWAt st.dmem (loc m0 968) 16 (keccakInstanceWeights ch).toList
  hpt : NativeRustcVm.EWsAt st.dmem (loc m0 1232) pt.toList
  hps : pt.size ≤ 30
  heq : NativeRustcVm.EWsAt st.dmem (sA m0 + BitVec.ofNat 64 107520) (eqKernel lp).toList
  hlp : lp.size = 11
  htv : NativeRustcVm.EWsAt st.dmem (loc m0 1888) tv.toList
  tsz : tv.size = 3
  ts : TStateAt st.dmem (tA m0) a s5
  x22 : st.regs.X22 = m0.regs.X0
  x24 : st.regs.X24.toNat = pt.size
  kap : (⟨st.regs.X25, st.regs.X26⟩ : EW) = sumE (keccakInstanceWeights ch)
  x20 : st.regs.X20 = val.c0
  x19 : st.regs.X19 = val.c1
  x21 : st.regs.X21.toBitVec = sA m0

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- What a callee writing its stack, a range of the frame and the `TState` changes, for
`fw_call`/`same_call`. -/
theorem rloc (h : VerifyLayerPre a s c m0) {m : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 2032) {N' : Nat} (hle : N' ≤ 1616) {o n : Nat}
    (q : BitVec 64)
    (hq : InRange (stackBelow m N') N' q ∨
      (InRange (loc m0 o) n q ∨ InRange (tA m0) tstateBytes q)) :
    Bel m0 q ∨ InRange (loc m0 o) n q ∨ ¬InRange (base m0 2032) 2032 q :=
  hq.elim (fun h' ↦ .inl (bel_of (geo_of h) hsp hle h')) fun h' ↦
    h'.elim (fun h'' ↦ .inr (.inl h'')) fun h'' ↦ .inr (.inr (fouts_not_frame h q (.inl h'')))

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The plain sumcheck, the values, the local kernel**, from `b36` to `b42`. -/
theorem plain_run (hp : Placed code k) (h : VerifyLayerPre a s c m0)
    (hspl : ∀ s, Spec (label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s) (SumcheckPlainPost a s))
    (hrs : ∀ s, Spec (label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hek : Spec (label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    {ch : EW} {pt : Array EW} {v : EW} {s3 : TState} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b36Offset)) (hk : AtK m0 a ch pt v s3 st.data)
    (hrun : runL s c m0 = rest4 c ch pt v s3)
    (cont : ∀ (st' : MachineState) (lp tv : Array EW) (val : EW) (s5 : TState),
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b42Offset) → AtL m0 a ch pt lp tv val s5 st'.data →
      runL s c m0 = (if checkB c (sumE (keccakInstanceWeights ch)) lp tv val then
        rest6 ch pt lp tv s5 else none) →
      Eventually (step1 Host.exe) (Goal a s c m0) st') :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have hS := pre_stack h
  have g := geo_of h
  have cx := ctx h
  have := g.hN; have := Geo.sp_lt m0; have := g.hs; have := g.hss
  have hps := hk.hps
  -- `b36`: the plain sumcheck, its slots zeroed.
  have hb0 := FB.body h hk.fb
  have hwf1 := wf_fr h hb0
  refine exec_at (blk hp b36_in_code (by simp [b36])) e36 hwf1 hpc (match_fr h hb0)
    fun st1 hm1 hpc1 ↦ ?_
  have hfb1 := fb_blkW h hk.fb hm1 hwf1 rfl (by decide)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b36Offset + b36.length = k + NativeRustcVmArm.Vm.VerifyLayer.b37Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b36_next]] at hpc1
  have y0 : st1.data.regs.X0.toBitVec = loc m0 1888 := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ rfl, ev_ptr]
    rfl
  have y22 : st1.data.regs.getXReg .X22 = m0.regs.X0 :=
    (reg_of hm1 (r' := .X22) rfl).trans hk.x22
  have y1 : st1.data.regs.X1.toBitVec = tA m0 := by
    show (st1.data.regs.getXReg .X1).toBitVec = _
    rw [reg_of hm1 (r' := .X22) rfl, show st.data.regs.getXReg .X22 = _ from hk.x22]
  have y23 : (⟨st1.data.regs.X2, st1.data.regs.X3⟩ : EW) = v := by
    rw [show st1.data.regs.X2 = _ from reg_val (r := .X2) hm1 rfl (ldF hk.v0),
      show st1.data.regs.X3 = _ from reg_val (r := .X3) hm1 rfl (ldF hk.v1)]
  have y4 : st1.data.regs.X4.toNat = 4 := by
    show (st1.data.regs.getXReg .X4).toBitVec.toNat = _
    rw [hm1.regs .X4 _ rfl, litN 4]
  have y5 : st1.data.regs.X5.toBitVec = loc m0 1712 := by
    show (st1.data.regs.getXReg .X5).toBitVec = _
    rw [hm1.regs .X5 _ rfl, ev_ptr]
    rfl
  have y6 : st1.data.regs.X6.toNat = 11 := by
    show (st1.data.regs.getXReg .X6).toBitVec.toNat = _
    rw [hm1.regs .X6 _ rfl, litN 11]
  have k1 : Bus.KeepRegs [.X22, .X24, .X25, .X26] st.data st1.data :=
    Bus.KeepRegs.of_block hm1 rfl
  have fw1 := fw_blk hm1 hwf1 [120, 136, 80, 88, 96] rfl (by decide) hk.fw
  have mu1 := NativeRustcVm.Layout.BufEWAt.of_same hk.mu
    (same_blk hm1 hwf1 (o' := 968) (n' := 264) (by omega) (by decide)) (by omega)
  have pt1 := ewsAt_same hk.hpt (same_blk hm1 hwf1 (o' := 1232) (n' := 480) (by omega)
    (by decide)) (by rw [Array.length_toList]; omega)
  have ts1 := ts_frame h hm1 hwf1 (by decide) hk.ts
  have hspN : sumcheckPlainStack ≤ 1616 := by have := le_sp; rw [stack_eq] at this; omega
  have hat := FB.at_ h hfb1
  refine local_call h le_sp
    (X := fun q ↦ InRange (loc m0 1712) 200 q ∨ InRange (tA m0) tstateBytes q)
    (o := 1712) (n := 200) (by omega) (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h'))
    (hspl s3) hfb1 hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q h' ↦ by
      rcases h' with h' | h' | h' | h'
      · rw [y0] at h'
        exact .inr (.inl (loc_mono g (o' := 1888) (n' := 24) (by omega) (by omega) (by omega) h'))
      · rw [y5, y6] at h'
        exact .inr (.inl (loc_mono g (o' := 1712) (n' := 16 * 11) (by omega) (by omega)
          (by omega) h'))
      · rw [y1] at h'
        exact .inr (.inr h')
      · exact .inl h', hq.2.2⟩)
    fun m2 hfb2 hq2 hcs2 hs2 ↦ ?_
  · refine ⟨hfb1.stackOk hS rfl le_sp, cx.rcAt hat le_sp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show TStateAt st1.data.dmem st1.data.regs.X1.toBitVec a s3
      rw [y1]; exact ts1
    · show TStateOk st1.data st1.data.regs.X1.toBitVec a sumcheckPlainStack
      rw [y1]; exact cx.tstateOk hat le_sp
    · show 2 ≤ st1.data.regs.X4.toNat
      rw [y4]; decide
    · show st1.data.regs.X4.toNat ≤ maxCount
      rw [y4]; decide
    · show OutOk st1.data st1.data.regs.X1.toBitVec a st1.data.regs.X0.toBitVec 24
        sumcheckPlainStack
      rw [y0, y1]; exact cx.outOk hat le_sp (o := 1888) (by omega)
    · show OutOk st1.data st1.data.regs.X1.toBitVec a st1.data.regs.X5.toBitVec
        (16 * st1.data.regs.X6.toNat) sumcheckPlainStack
      rw [y1, y5, y6]; exact cx.outOk hat le_sp (o := 1712) (by omega)
    · show Apart st1.data.regs.X0.toBitVec 24 st1.data.regs.X5.toBitVec
        (16 * st1.data.regs.X6.toNat)
      rw [y0, y5, y6]
      unfold Apart
      rw [g.fa (by omega), g.fa (by omega)]
      omega
  obtain ⟨⟨hopt, hslots, hnext⟩, -, -⟩ := hq2
  have hR : (sumcheckPlain ⟨st1.data.regs.X2, st1.data.regs.X3⟩ st1.data.regs.X4.toNat
      st1.data.regs.X6.toNat).run s3 =
        (sumcheckPlain v 4 LeanVM.Protocol.Verifier.keccakLocalBits).run s3 := by
    rw [y23, y4, y6]
    rfl
  rw [hR, y0] at hopt
  rw [hR, y5] at hslots
  rw [hR, y1] at hnext
  have hR2 := rloc h hfb1.sp hspN (o := 1712) (n := 200)
  have fw2 := fw_call g hs2 hR2 (by omega) (fun q hq ↦ by have := eWords_le m0 q hq; omega) fw1
  have mu2 := NativeRustcVm.Layout.BufEWAt.of_same mu1
    (same_call g hs2 hR2 (by omega) (o' := 968) (n' := 264) (by omega) (by omega)) (by omega)
  have pt2 := ewsAt_same pt1
    (same_call g hs2 hR2 (by omega) (o' := 1232) (n' := 480) (by omega) (by omega))
    (by rw [Array.length_toList]; omega)
  -- `b37`: `None` from the plain sumcheck?
  refine Fr.runBlock hS N_ge rfl hfb2 (blk hp b37_in_code (by simp [b37])) e37 rfl rfl
    (by decide) (by decide) fun st3 hfb3 hd3 hm3 hpc3 ↦ ?_
  have k3 : Bus.KeepRegs [.X22, .X24, .X25, .X26] m2 st3.data := Bus.KeepRegs.of_block hm3 rfl
  cases hr : (sumcheckPlain v 4 LeanVM.Protocol.Verifier.keccakLocalBits).run s3 with
  | none =>
    rw [hr] at hopt
    have hl : (Env.ofMachine m2 [(base m0 2032, 2032)]).load 0 1888 4 = BitVec.ofNat 64 0 :=
      NativeRustcVmArm.Transcript.load4_of_tag (w := 0) (.inl rfl)
        (hopt : NativeRustcVm.WordAt _ _ 0)
    have hc : SBool.eval (Env.ofMachine m2 [(base m0 2032, 2032)])
        (.not (.bit .W32 (.load 0 1888 4) 0)) = true := by
      show (!(low .W32 ((Env.ofMachine m2 [(base m0 2032, 2032)]).load 0 1888 4)).getLsbD 0) =
        true
      rw [hl]
      rfl
    refine reject hp h ((pc_true hpc3 hc).trans (label37 hp)) (FB.body h hfb3) ?_
    rw [hrun, rest4, hr]
    rfl
  | some u =>
    obtain ⟨⟨lp, val⟩, s4⟩ := u
    rw [hr] at hopt
    obtain ⟨h1, hv⟩ := hopt
    have hl : (Env.ofMachine m2 [(base m0 2032, 2032)]).load 0 1888 4 = BitVec.ofNat 64 1 :=
      NativeRustcVmArm.Transcript.load4_of_tag (w := 1) (.inr rfl) h1
    have hc : SBool.eval (Env.ofMachine m2 [(base m0 2032, 2032)])
        (.not (.bit .W32 (.load 0 1888 4) 0)) = false := by
      show (!(low .W32 ((Env.ofMachine m2 [(base m0 2032, 2032)]).load 0 1888 4)).getLsbD 0) =
        false
      rw [hl]
      rfl
    have hpc3' := pc_false hpc3 hc
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b37Offset + b37.length = k + NativeRustcVmArm.Vm.VerifyLayer.b38Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b37_next]] at hpc3'
    have hv' := NativeRustcVm.ewAt_iff.mp hv
    rw [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
      at hv'
    have hlp : lp.size = 11 := by
      have := (NativeRustcVm.Top.sumcheck_size v 4 (Array.replicate 11 none)).gives s3 _ s4 hr
      simpa using this
    have lp2 := hslots lp val s4 hr
    have ts2 := hnext _ s4 hr
    -- `b38`: `read_scalars(t, frame + 1888, 3)`.
    have hb3 := FB.body h hfb3
    have hwf4 := wf_fr h hb3
    refine exec_at (blk hp b38_in_code (by simp [b38])) e38 hwf4 hpc3' (match_fr h hb3)
      fun st4 hm4 hpc4 ↦ ?_
    have hfb4 := fb_blkW h hfb3 hm4 hwf4 rfl (by decide)
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b38Offset + b38.length = k + NativeRustcVmArm.Vm.VerifyLayer.b39Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b38_next]] at hpc4
    have z20 : st4.data.regs.getXReg .X20 = val.c0 :=
      reg_val hm4 rfl (ldF (by rw [hd3]; exact hv'.1))
    have z19 : st4.data.regs.getXReg .X19 = val.c1 :=
      reg_val hm4 rfl (ldF (by rw [hd3]; exact hv'.2))
    have z22 : st4.data.regs.getXReg .X22 = m0.regs.X0 := by
      rw [reg_of hm4 (r' := .X22) rfl, kg k3 .X22, hcs2 .X22 rfl]; exact y22
    have k4 : Bus.KeepRegs [.X22, .X24, .X25, .X26] st3.data st4.data :=
      Bus.KeepRegs.of_block hm4 rfl
    rw [← hd3] at fw2 mu2 pt2 lp2 ts2
    have fw4 := fw_blk hm4 hwf4 [120, 136, 80, 88, 96] rfl (by decide) fw2
    have mu4 := NativeRustcVm.Layout.BufEWAt.of_same mu2
      (same_blk hm4 hwf4 (o' := 968) (n' := 264) (by omega) (by decide)) (by omega)
    have pt4 := ewsAt_same pt2 (same_blk hm4 hwf4 (o' := 1232) (n' := 480) (by omega)
      (by decide)) (by rw [Array.length_toList]; omega)
    have lp4 := ewsAt_same lp2 (same_blk hm4 hwf4 (o' := 1712) (n' := 176) (by omega)
      (by decide)) (by rw [Array.length_toList, hlp])
    have ts4 := ts_frame h hm4 hwf4 (by decide) ts2
    refine rs_call h hrs (o := 1888) (n := 3) (by omega) hfb4 hpc4
      ((reg_of hm4 (r := .X0) (r' := .X22) rfl).trans (by
        rw [kg k3 .X22, hcs2 .X22 rfl]; exact y22))
      (by show (st4.data.regs.getXReg .X1).toBitVec = _; rw [hm4.regs .X1 _ rfl, ev_ptr]; rfl)
      (by show (st4.data.regs.getXReg .X2).toBitVec.toNat = _; rw [hm4.regs .X2 _ rfl, litN 3])
      ts4 fun m5 hfb5 hx5 hok5 hcs5 hs5 ↦ ?_
    have hrsN : readScalarsStack ≤ 1616 := by have := le_rs; rw [stack_eq] at this; omega
    have hR5 := rloc h hfb4.sp hrsN (o := 1888) (n := 16 * 3)
    have fw5 := fw_call g hs5 hR5 (by omega) (fun q hq ↦ by have := eWords_le m0 q hq; omega)
      fw4
    have mu5 := NativeRustcVm.Layout.BufEWAt.of_same mu4
      (same_call g hs5 hR5 (by omega) (o' := 968) (n' := 264) (by omega) (by omega)) (by omega)
    have pt5 := ewsAt_same pt4
      (same_call g hs5 hR5 (by omega) (o' := 1232) (n' := 480) (by omega) (by omega))
      (by rw [Array.length_toList]; omega)
    have lp5 := ewsAt_same lp4
      (same_call g hs5 hR5 (by omega) (o' := 1712) (n' := 176) (by omega) (by omega))
      (by rw [Array.length_toList, hlp])
    -- `b39`: `None` from the values?
    refine Fr.runBlock hS N_ge rfl hfb5 (blk hp b39_in_code (by simp [b39])) e39 rfl rfl
      (by decide) (by decide) fun st6 hfb6 hd6 hm6 hpc6 ↦ ?_
    have hc6 : SBool.eval (Env.ofMachine m5 [(base m0 2032, 2032)])
        (.not (.bit .W32 (.reg .X0) 0)) = !((readScalars 3).run s4).isSome := by
      show (!(low .W32 (m5.regs.getXReg .X0).toBitVec).getLsbD 0) = _
      rw [show m5.regs.getXReg .X0 = m5.regs.X0 from rfl, hx5, NativeRustcVmArm.Bus.Gkr.okWord_bit]
    have k6 : Bus.KeepRegs [.X19, .X20, .X22, .X24, .X25, .X26] m5 st6.data :=
      Bus.KeepRegs.of_block hm6 rfl
    cases hr2 : (readScalars 3).run s4 with
    | none =>
      refine reject hp h ((pc_true hpc6 (by rw [hc6, hr2]; rfl)).trans (label37 hp))
        (FB.body h hfb6) ?_
      rw [hrun, rest4, hr]
      show rest5 c ch pt lp val s4 = none
      rw [rest5, hr2]
      rfl
    | some w =>
      obtain ⟨tv, s5⟩ := w
      have hpc6' := pc_false hpc6 (by rw [hc6, hr2]; rfl)
      rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b39Offset + b39.length = k + NativeRustcVmArm.Vm.VerifyLayer.b40Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b39_next]] at hpc6'
      obtain ⟨tv5, ts5⟩ := hok5 tv s5 hr2
      have htsz : tv.size = 3 := NativeRustcVm.Sumcheck.readScalars_size hr2
      have z21 : (st6.data.regs.getXReg .X21).toBitVec = sA m0 :=
        hm6.regs .X21 _ rfl |>.trans (ldF (FrameWords.get fw5 (o := 120) (by simp [eWords])))
      -- `b40`: `eq_kernel(local point, 11, scratch + 107520, 2048)`.
      have hb6 := FB.body h hfb6
      have hwf7 := wf_fr h hb6
      refine exec_at (blk hp b40_in_code (by simp [b40])) e40 hwf7 hpc6' (match_fr h hb6)
        fun st7 hm7 hpc7 ↦ ?_
      have hfb7 := fb_blkW h hfb6 hm7 hwf7 rfl (by decide)
      rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b40Offset + b40.length = k + NativeRustcVmArm.Vm.VerifyLayer.b41Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b40_next]] at hpc7
      have u0 : st7.data.regs.X0.toBitVec = loc m0 1712 := by
        show (st7.data.regs.getXReg .X0).toBitVec = _
        rw [hm7.regs .X0 _ rfl, ev_ptr]
        rfl
      have u1 : st7.data.regs.X1.toNat = 11 := by
        show (st7.data.regs.getXReg .X1).toBitVec.toNat = _
        rw [hm7.regs .X1 _ rfl, litN 11]
      have u2 : st7.data.regs.X2.toBitVec = sA m0 + BitVec.ofNat 64 107520 := by
        show (st7.data.regs.getXReg .X2).toBitVec = _
        rw [hm7.regs .X2 _ rfl, ev_bin, ev_regU, z21, ev_lit, add_apply]
      have u3 : st7.data.regs.X3.toNat = 2048 := by
        show (st7.data.regs.getXReg .X3).toBitVec.toNat = _
        rw [hm7.regs .X3 _ rfl, litN 2048]
      have w144 := Bus.wordAt_write (r := 0) (o := 144) hm7 rfl (by omega)
        (v := .bin .add .W64 (.reg .X21) (.lit 107520)) (fun i hi ↦ by interval_cases i <;> rfl)
      rw [ev_bin, ev_regU, z21, ev_lit, add_apply] at w144
      have k7 : Bus.KeepRegs [.X19, .X20, .X21, .X22, .X24, .X25, .X26] st6.data st7.data :=
        Bus.KeepRegs.of_block hm7 rfl
      rw [← hd6] at fw5 mu5 pt5 lp5 tv5 ts5
      have fw7 := fw_blk hm7 hwf7 [120, 136, 80, 88, 96] rfl (by decide) fw5
      have mu7 := NativeRustcVm.Layout.BufEWAt.of_same mu5
        (same_blk hm7 hwf7 (o' := 968) (n' := 264) (by omega) (by decide)) (by omega)
      have pt7 := ewsAt_same pt5 (same_blk hm7 hwf7 (o' := 1232) (n' := 480) (by omega)
        (by decide)) (by rw [Array.length_toList]; omega)
      have lp7 := ewsAt_same lp5 (same_blk hm7 hwf7 (o' := 1712) (n' := 176) (by omega)
        (by decide)) (by rw [Array.length_toList, hlp])
      have tv7 := ewsAt_same tv5 (same_blk hm7 hwf7 (o' := 1888) (n' := 48) (by omega)
        (by decide)) (by rw [Array.length_toList, htsz])
      have ts7 := ts_frame h hm7 hwf7 (by decide) ts5
      have hekN : eqKernelStack ≤ 1616 := by have := le_ek; rw [stack_eq] at this; omega
      refine local_call h le_ek (X := InRange (sA m0 + BitVec.ofNat 64 107520) 32768) (o := 0)
        (n := 0) (by omega) (fun q hq ↦ .inl (.inr hq)) hek hfb7 hpc7
        ⟨hfb7.stackOk hS rfl le_ek, by rw [u1]; decide,
          ⟨by rw [u0, u1]; exact readable_loc h hfb7 (by omega),
            by rw [u0, u1]; exact offStack_loc h hfb7 (by omega) hekN⟩,
          ⟨by rw [u2, u3]; exact readable_scr h hfb7 (by omega) (by omega),
            by rw [u2, u3]; exact offStack_scr h hfb7 (by omega) (by omega) hekN⟩,
          by
            rw [u0, u1, u2, u3]
            unfold Apart
            rw [g.fa (by omega), g.sa (by omega)]
            omega⟩
        (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q h' ↦ by
            rw [u2, u3] at h'; exact h'.elim .inr .inl, hq.2.2⟩)
        fun m8 hfb8 hq8 hcs8 hs8 ↦ ?_
      obtain ⟨hk8, -, hsv8⟩ := hq8
      rw [u1, u3, ite_eq_left (by decide : 2 ^ 11 ≤ 2048)] at hk8
      obtain ⟨x80, -, heq8⟩ := hk8
      rw [u2, slice_eq lp7 u0 (by rw [u1, Array.length_toList, hlp]), Array.toArray_toList]
        at heq8
      have hR8 : ∀ q, (InRange (stackBelow st7.data eqKernelStack) eqKernelStack q ∨
          InRange (sA m0 + BitVec.ofNat 64 107520) 32768 q) →
          Bel m0 q ∨ InRange (loc m0 0) 0 q ∨ ¬InRange (base m0 2032) 2032 q :=
        fun q hq ↦ hq.elim (fun h' ↦ .inl (bel_of g hfb7.sp hekN h'))
          fun h' ↦ .inr (.inr (scr_not_frame g (by omega) (by omega) h'))
      have keep8 : ∀ {o' n' : Nat}, o' + n' ≤ 2032 →
          NativeRustcVm.Layout.Same st7.data.dmem m8.dmem (loc m0 o') n' :=
        fun hon ↦ same_call g hs8 hR8 (by omega) hon (by omega)
      -- `b41`: the kernel's size fits.
      refine Fr.runBlock hS N_ge rfl hfb8 (blk hp b41_in_code (by simp [b41])) e41 rfl rfl
        (by decide) (by decide) fun st9 hfb9 hd9 hm9 hpc9 ↦ ?_
      have hc9 : SBool.eval (Env.ofMachine m8 [(base m0 2032, 2032)])
          (.not (.bit .W32 (.reg .X0) 0)) = false := by
        show (!(low .W32 (m8.regs.getXReg .X0).toBitVec).getLsbD 0) = _
        rw [show m8.regs.getXReg .X0 = m8.regs.X0 from rfl, x80]
        rfl
      have hpc9' := pc_false hpc9 hc9
      rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b41Offset + b41.length = k + NativeRustcVmArm.Vm.VerifyLayer.b42Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b41_next]] at hpc9'
      have k9 : Bus.KeepRegs [.X19, .X20, .X21, .X22, .X24, .X25, .X26] m8 st9.data :=
        Bus.KeepRegs.of_block hm9 rfl
      have kk : ∀ r ∈ [XReg.X19, .X20, .X22, .X24, .X25, .X26],
          st9.data.regs.getXReg r = st4.data.regs.getXReg r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [kg k9 _, hcs8 _ rfl, kg k7 _, kg k6 _, hcs5 _ rfl]
      have tsk : TStateAt m8.dmem (tA m0) a s5 :=
        ts_call h hfb7.sp hekN hs8 hsv8.2.2 (fun q hq ↦ ⟨fun ht ↦
          (sc_miss h (o := 107520) (n := 32768) (by omega) (by omega) hq).1 ht,
          fun ha ↦ (sc_miss h (o := 107520) (n := 32768) (by omega) (by omega) hq).2 ha⟩) ts7
      refine cont st9 lp tv val s5 hpc9' ⟨hfb9, ?_, ?_, ?_, ?_, hps, ?_, hlp, ?_, htsz, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩ ?_
      · rw [hd9]
        exact fun q hq ↦ same_word (fw7 q hq) (keep8 (by have := eWords_le m0 q hq; omega))
      · rw [hd9]; exact same_word w144 (keep8 (by omega))
      · rw [hd9]
        exact NativeRustcVm.Layout.BufEWAt.of_same mu7 (keep8 (o' := 968) (n' := 264) (by omega))
          (by omega)
      · rw [hd9]
        exact ewsAt_same pt7 (keep8 (o' := 1232) (n' := 480) (by omega))
          (by rw [Array.length_toList]; omega)
      · rw [hd9]; exact heq8
      · rw [hd9]
        exact ewsAt_same tv7 (keep8 (o' := 1888) (n' := 48) (by omega))
          (by rw [Array.length_toList, htsz])
      · rw [hd9]; exact tsk
      · show st9.data.regs.getXReg .X22 = _
        rw [kk .X22 (by simp)]; exact z22
      · show (st9.data.regs.getXReg .X24).toNat = _
        rw [kk .X24 (by simp), kg k4 .X24, kg k3 .X24, hcs2 .X24 rfl, kg k1 .X24]
        exact hk.x24
      · show (⟨st9.data.regs.getXReg .X25, st9.data.regs.getXReg .X26⟩ : EW) = _
        rw [kk .X25 (by simp), kk .X26 (by simp), kg k4 .X25, kg k4 .X26, kg k3 .X25,
          kg k3 .X26, hcs2 .X25 rfl, hcs2 .X26 rfl, kg k1 .X25, kg k1 .X26]
        exact hk.kap
      · show st9.data.regs.getXReg .X20 = _
        rw [kk .X20 (by simp)]; exact z20
      · show st9.data.regs.getXReg .X19 = _
        rw [kk .X19 (by simp)]; exact z19
      · show (st9.data.regs.getXReg .X21).toBitVec = _
        rw [kg k9 .X21, hcs8 .X21 rfl, kg k7 .X21]; exact z21
      · rw [hrun, rest4, hr]
        show rest5 c ch pt lp val s4 = _
        rw [rest5, hr2]
        rfl

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
