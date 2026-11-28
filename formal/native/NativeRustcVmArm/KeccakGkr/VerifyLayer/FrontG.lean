module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontDefs

/-!
# `verify_layer`'s front: from the second check to the weights loop

From `b48` (`k + NativeRustcVmArm.Vm.VerifyLayer.b48Offset`, the second check passed, `AtG`): `bit_length(1)`, a grind of no bits, `β`
(`squeeze`), and `b52` sets the weights loop's registers: `AtLoop` at `.LVerifyLayer_30`
(`k + NativeRustcVmArm.Vm.VerifyLayer.b57Offset`), no weight written yet (`g_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Bus.Gkr (Fr.runBlock)

@[expose] public section

/-- **At the weights loop's head** (`k + NativeRustcVmArm.Vm.VerifyLayer.b57Offset`), no weight written: the values `t0`, `t1`, `t2`,
`β`, the instance weights `mu`, the point, the local equality kernel `eq`, the state `s'`. -/
structure AtLoop [Labels] (m0 : MachineData) (a : DecArea) (s : TState) (c : KeccakClaimW)
    (t0 t1 t2 beta : EW) (mu point eq : Array EW) (s' : TState) (m : MachineData) : Prop where
  fb : FB m0 m
  x19 : m.regs.X19.toNat = 0
  x26 : m.regs.X26.toNat = 25600
  x29 : m.regs.X29.toBitVec = sA m0 + BitVec.ofNat 64 51200
  x20 : m.regs.X20.toBitVec = sA m0 + BitVec.ofNat 64 51208
  x23 : m.regs.X23 = beta.c0
  x25 : m.regs.X25 = beta.c1
  x24 : m.regs.X24.toNat = point.size
  fw : Bus.FrameWords m.dmem (base m0 2032) (tailWords m0 t0 t1 t2)
  f144 : NativeRustcVm.WordAt m.dmem (loc m0 144) (UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107520))
  f96 : NativeRustcVm.WordAt m.dmem (loc m0 96) (UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107528))
  hmu : NativeRustcVm.BufEWAt m.dmem (loc m0 968) 16 mu.toList
  hpt : NativeRustcVm.EWsAt m.dmem (loc m0 1232) point.toList
  heqw : NativeRustcVm.EWsAt m.dmem (sA m0 + BitVec.ofNat 64 107520) eq.toList
  ts : TStateAt m.dmem (tA m0) a s'
  heq : eq.size = 2048
  hps : point.size ≤ 30
  run : runL s c m0 = some (⟨t0 + beta * (t1 + beta * t2), mu, point,
    keccakLinearTranspose (layerWeights eq beta)⟩, s')

/-- The memory the front keeps from the second check on. -/
structure GMem (m0 : MachineData) (ch : EW) (pt lp tv : Array EW) (d : DataMem) : Prop where
  fw : Bus.FrameWords d (base m0 2032) (tailWords m0 (tv.getD 0 0) (tv.getD 1 0) (tv.getD 2 0))
  f144 : NativeRustcVm.WordAt d (loc m0 144) (UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107520))
  f96 : NativeRustcVm.WordAt d (loc m0 96) (UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107528))
  mu : NativeRustcVm.BufEWAt d (loc m0 968) 16 (keccakInstanceWeights ch).toList
  pt : NativeRustcVm.EWsAt d (loc m0 1232) pt.toList
  eq : NativeRustcVm.EWsAt d (sA m0 + BitVec.ofNat 64 107520) (eqKernel lp).toList

/-- **After the second check** (`b48`, `k + NativeRustcVmArm.Vm.VerifyLayer.b48Offset`): the challenge `ch`, the sumchecks' points
`pt` and `lp`, the values `tv`, the state `sg`. -/
structure AtG [Labels] (m0 : MachineData) (a : DecArea) (s : TState) (c : KeccakClaimW)
    (ch : EW) (pt lp tv : Array EW) (sg : TState) (m : MachineData) : Prop where
  fb : FB m0 m
  x22 : m.regs.X22 = m0.regs.X0
  x24 : m.regs.X24.toNat = pt.size
  mem : GMem m0 ch pt lp tv m.dmem
  ts : TStateAt m.dmem (tA m0) a sg
  hps : pt.size ≤ 30
  hlp : lp.size = 11
  run : runL s c m0 = rest6 ch pt lp tv sg

end

public section

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- The memory kept by a call writing its stack and the `TState`. -/
theorem GMem.call [Labels] (h : VerifyLayerPre a s c m0) {ch : EW} {pt lp tv : Array EW}
    {m m' : MachineData} (hsp : m.regs.SP.toBitVec = base m0 2032) {N' : Nat} (hle : N' ≤ 1616)
    (hs : SameOutside m.dmem m'.dmem fun q ↦
      InRange (stackBelow m N') N' q ∨ InRange (tA m0) tstateBytes q)
    (hps : pt.size ≤ 30) (hlp : lp.size = 11) (g : GMem m0 ch pt lp tv m.dmem) :
    GMem m0 ch pt lp tv m'.dmem := by
  have hfr := fr_same h hsp hle hs
  have hsc := scr_same h hsp hle hs (o := 107520) (n := 32768) (by omega) (by omega)
    fun j hj ↦ scr_not_ts h (by omega) (by omega) hj
  have hle' : (eqKernel lp).toList.length = 2048 := by
    rw [Array.length_toList, NativeVm.Math.Keccak.eqKernel_size, hlp]; rfl
  exact ⟨FrameWords.of_same g.fw hfr (tailWords_le _ _ _ _),
    NativeRustcVm.Layout.WordAt.of_same g.f144 (hfr.sub (o := 144) (k := 8) (by omega))
      (Nat.le_refl _),
    NativeRustcVm.Layout.WordAt.of_same g.f96 (hfr.sub (o := 96) (k := 8) (by omega))
      (Nat.le_refl _),
    NativeRustcVm.Layout.BufEWAt.of_same g.mu (hfr.sub (o := 968) (k := 264) (by omega))
      (by omega),
    ewsAt_same g.pt (hfr.sub (o := 1232) (k := 480) (by omega))
      (by rw [Array.length_toList]; omega),
    ewsAt_same g.eq hsc (by rw [hle'])⟩

/-- A register a block set to the frame's word at `o`. -/
theorem fw_val [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {r : XReg} {o : Nat} {v : UInt64}
    (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (h : S.reg r = some (.load 0 o 8))
    (hw : NativeRustcVm.WordAt m.dmem (base m0 2032 + BitVec.ofNat 64 o) v) :
    m'.regs.getXReg r = v :=
  fw_reg hm h hw

/-- `csel w1, wzr, w8, lo` after `subs w8, w0, #3`, `w0 = x`. -/
theorem csel3_aux : ∀ x < 64, (if CmpOp.ult.apply .W32 (BitVec.ofNat 64 x) 3#64 = true then 0#64
    else BinOp.sub.apply .W32 (BitVec.ofNat 64 x) 3#64).toNat = x - 3 := by decide

theorem csel3 [Labels] (env : Env) {x : Nat} (hx : x < 64) (h : env.regs .X0 = BitVec.ofNat 64 x) :
    ((Sym.ite (.cmp .ult .W32 (.reg .X0) (.lit 3)) (.lit 0)
      (.bin .sub .W32 (.reg .X0) (.lit 3))).eval env).toNat = x - 3 := by
  simp only [Sym.eval, SBool.eval, h]
  exact csel3_aux x hx

theorem label30 [Host] {k : Nat} (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_30 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b57Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b57Offset) NativeRustcVmArm.Vm.VerifyLayer.label_30_at

/-- **From the second check to the weights loop.** -/
theorem g_run [Host] {k : Nat} (hp : Placed code k) (h : VerifyLayerPre a s c m0)
    (hbl : Spec (label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hloop : ∀ (st : MachineState) (t0 t1 t2 beta : EW) (mu point eq : Array EW) (s' : TState),
      st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b57Offset) → AtLoop m0 a s c t0 t1 t2 beta mu point eq s' st.data →
      Eventually (step1 Host.exe) (Goal a s c m0) st)
    {ch : EW} {pt lp tv : Array EW} {sg : TState} {m : MachineData}
    (hg : AtG m0 a s c ch pt lp tv sg m) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b48Offset)⟩ := by
  have hS := pre_stack h
  have hsp0 := hg.fb.sp
  -- `b48`: `bit_length(1)`.
  refine Fr.runBlock hS N_ge rfl hg.fb (blk hp b48_in_code (by simp [b48])) e48 rfl rfl
    (by decide) (by decide) fun st1 hfb1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.VerifyLayer.b48_length, NativeRustcVmArm.Vm.VerifyLayer.b48Length, show k + NativeRustcVmArm.Vm.VerifyLayer.b48Offset + 2 = k + NativeRustcVmArm.Vm.VerifyLayer.b49Offset by simpa only [NativeRustcVmArm.Vm.VerifyLayer.b48_length, NativeRustcVmArm.Vm.VerifyLayer.b48Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.VerifyLayer.b48_next] at hpc1
  have k1 := Bus.KeepRegs.of_block (L := [.X22, .X24]) hm1 (by decide)
  refine leaf_call h le_bl hbl (fun _ _ hq ↦ ⟨hq.2.1, hq.2.2⟩) hfb1 hpc1 trivial
    fun m2 hfb2 hq2 hcs2 hs2 hk2 ↦ ?_
  have e0 : m2.regs.X0.toNat = 1 := by
    have h1 : st1.data.regs.X0.toNat = 1 := congrArg BitVec.toNat (hm1.regs .X0 _ rfl)
    rw [hq2.1, h1]
    rfl
  have hm2 : GMem m0 ch pt lp tv m2.dmem :=
    GMem.call h hfb1.sp (by decide) (NativeRustcVm.SameOutside.mono hs2 fun q hq ↦
      hq.elim .inl False.elim) hg.hps hg.hlp (hd1 ▸ hg.mem)
  have hts2 : TStateAt m2.dmem (tA m0) a sg :=
    ts_call h hfb1.sp (by decide) hs2 hk2 (fun _ h' ↦ h'.elim) (hd1 ▸ hg.ts)
  have r22 : m2.regs.getXReg .X22 = m0.regs.X0 := (hcs2 _ rfl).trans ((k1 _ (by simp)).trans hg.x22)
  have r24 : m2.regs.getXReg .X24 = m.regs.X24 := (hcs2 _ rfl).trans (k1 _ (by simp))
  -- `b49`: `grind(t, 0)`.
  refine Fr.runBlock hS N_ge rfl hfb2 (blk hp b49_in_code (by simp [b49])) e49 rfl rfl
    (by decide) (by decide) fun st3 hfb3 hd3 hm3 hpc3 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.VerifyLayer.b49_length, NativeRustcVmArm.Vm.VerifyLayer.b49Length, show k + NativeRustcVmArm.Vm.VerifyLayer.b49Offset + 4 = k + NativeRustcVmArm.Vm.VerifyLayer.b50Offset by simpa only [NativeRustcVmArm.Vm.VerifyLayer.b49_length, NativeRustcVmArm.Vm.VerifyLayer.b49Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.VerifyLayer.b49_next] at hpc3
  have k3 := Bus.KeepRegs.of_block (L := [.X22, .X24]) hm3 (by decide)
  have g0 : st3.data.regs.X0 = m0.regs.X0 := (reg_of hm3 (r := .X0) (r' := .X22) rfl).trans r22
  have g1 : grindBits st3.data = 0 := by
    have hx : (Env.ofMachine m2 [(base m0 2032, 2032)]).regs .X0 = BitVec.ofNat 64 1 :=
      BitVec.eq_of_toNat_eq (by rw [show (Env.ofMachine m2 [(base m0 2032, 2032)]).regs .X0 =
        m2.regs.X0.toBitVec from rfl]; exact e0)
    unfold grindBits
    rw [show st3.data.regs.X1.toNat = (st3.data.regs.getXReg .X1).toBitVec.toNat from rfl,
      hm3.regs .X1 _ rfl, csel3 _ (by decide) hx]
    rfl
  refine grind_call h hgr hfb3 hpc3 g0 g1 (by decide) (hd3 ▸ hts2)
    fun m4 hfb4 hx4 hnext4 hcs4 hs4 ↦ ?_
  have hm4 : GMem m0 ch pt lp tv m4.dmem :=
    GMem.call h hfb3.sp (by decide) hs4 hg.hps hg.hlp (hd3 ▸ hm2)
  have r22' : m4.regs.getXReg .X22 = m0.regs.X0 := (hcs4 _ rfl).trans ((k3 _ (by simp)).trans r22)
  have r24' : m4.regs.getXReg .X24 = m.regs.X24 := (hcs4 _ rfl).trans ((k3 _ (by simp)).trans r24)
  -- `b50`: the grind's result.
  refine Fr.runBlock hS N_ge rfl hfb4 (blk hp b50_in_code (by simp [b50])) e50 rfl rfl
    (by decide) (by decide) fun st5 hfb5 hd5 hm5 hpc5 ↦ ?_
  have hc5 : SBool.eval (Env.ofMachine m4 [(base m0 2032, 2032)])
      (.cmp .eq .W32 (.reg .X0) (.lit 0)) = !((grind 0).run sg).isSome := by
    show CmpOp.eq.apply .W32 (m4.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = _
    rw [show m4.regs.getXReg .X0 = m4.regs.X0 from rfl, hx4, okw_eq0]
  simp only [PcOk, hc5, NativeRustcVmArm.Vm.VerifyLayer.b50_length, NativeRustcVmArm.Vm.VerifyLayer.b50Length, show k + NativeRustcVmArm.Vm.VerifyLayer.b50Offset + 1 = k + NativeRustcVmArm.Vm.VerifyLayer.b51Offset by simpa only [NativeRustcVmArm.Vm.VerifyLayer.b50_length, NativeRustcVmArm.Vm.VerifyLayer.b50Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.VerifyLayer.b50_next] at hpc5
  have k5 := Bus.KeepRegs.of_block (L := [.X22, .X24]) hm5 (by decide)
  cases hr0 : (grind 0).run sg with
  | none =>
    simp only [hr0, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc5
    exact reject hp h (hpc5.trans (label37 hp)) (FB.body h hfb5)
      (by rw [hg.run, rest6, grindingBits_2, hr0]; rfl)
  | some w =>
    simp only [hr0, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5
    have hts4 : TStateAt m4.dmem (tA m0) a w.2 := hnext4 w.1 w.2 (by rw [hr0])
    -- `b51`: `β`.
    refine NativeRustcVmArm.Bus.Gkr.at_pc hpc5 (Fr.runBlock hS N_ge rfl hfb5
      (blk hp b51_in_code (by simp [b51])) e51
      rfl rfl (by decide) (by decide) fun st6 hfb6 hd6 hm6 hpc6 ↦ ?_)
    simp only [PcOk, NativeRustcVmArm.Vm.VerifyLayer.b51_length, NativeRustcVmArm.Vm.VerifyLayer.b51Length, show k + NativeRustcVmArm.Vm.VerifyLayer.b51Offset + 2 = k + NativeRustcVmArm.Vm.VerifyLayer.b52Offset by simpa only [NativeRustcVmArm.Vm.VerifyLayer.b51_length, NativeRustcVmArm.Vm.VerifyLayer.b51Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.VerifyLayer.b51_next] at hpc6
    have k6 := Bus.KeepRegs.of_block (L := [.X22, .X24]) hm6 (by decide)
    have d6 : st6.data.dmem = m4.dmem := hd6.trans hd5
    refine sq_call h hsq hfb6 hpc6 ((reg_of hm6 (r := .X0) (r' := .X22) rfl).trans
      ((k5 _ (by simp)).trans r22')) (d6 ▸ hts4) fun m7 hfb7 hts7 hx70 hx71 hcs7 hs7 ↦ ?_
    have hm7 : GMem m0 ch pt lp tv m7.dmem :=
      GMem.call h hfb6.sp (by decide) hs7 hg.hps hg.hlp (d6 ▸ hm4)
    have r24'' : m7.regs.getXReg .X24 = m.regs.X24 :=
      (hcs7 _ rfl).trans ((k6 _ (by simp)).trans ((k5 _ (by simp)).trans r24'))
    -- `b52`: the loop's registers.
    refine Fr.runBlock hS N_ge rfl hfb7 (blk hp b52_in_code (by simp [b52])) e52 rfl rfl
      (by decide) (by decide) fun st8 hfb8 hd8 hm8 hpc8 ↦ ?_
    simp only [PcOk] at hpc8
    have h88 := FrameWords.get hm7.fw (o := 88)
      (v := UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 51200))
      (by simp [tailWords])
    have l88 : (Env.ofMachine m7 [(base m0 2032, 2032)]).load 0 88 8 =
        sA m0 + BitVec.ofNat 64 51200 := fw_load rfl h88
    refine hloop st8 (tv.getD 0 0) (tv.getD 1 0) (tv.getD 2 0) (sqS w.2).1
      (keccakInstanceWeights ch) pt (eqKernel lp) (sqS w.2).2 (hpc8.trans (label30 hp))
      ⟨hfb8, congrArg BitVec.toNat (hm8.regs .X19 _ rfl),
        congrArg BitVec.toNat (hm8.regs .X26 _ rfl),
        (hm8.regs .X29 _ rfl).trans l88, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hg.hps, ?_⟩
    · show (st8.data.regs.getXReg .X20).toBitVec = _
      rw [hm8.regs .X20 _ rfl]
      show BinOp.apply .add .W64 ((Env.ofMachine m7 [(base m0 2032, 2032)]).load 0 88 8)
        (BitVec.ofNat 64 8) = _
      rw [l88]
      simp only [BinOp.apply, low_W64, ext_W64]
      exact NativeRustcVm.addr_add_add _ _ _
    · exact (reg_of hm8 (r := .X23) (r' := .X0) rfl).trans hx70
    · exact (reg_of hm8 (r := .X25) (r' := .X1) rfl).trans hx71
    · show (st8.data.regs.getXReg .X24).toNat = _
      rw [reg_of hm8 (r := .X24) (r' := .X24) rfl, r24'']
      exact hg.x24
    · rw [hd8]; exact hm7.fw
    · rw [hd8]; exact hm7.f144
    · rw [hd8]; exact hm7.f96
    · rw [hd8]; exact hm7.mu
    · rw [hd8]; exact hm7.pt
    · rw [hd8]; exact hm7.eq
    · rw [hd8]; exact hts7
    · rw [NativeVm.Math.Keccak.eqKernel_size, hg.hlp]; rfl
    · rw [hg.run, rest6, grindingBits_2, hr0]
      rfl

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
