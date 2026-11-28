module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.GluedEval.Names
public import NativeRustcVmArm.Whir.FinalLevel.GluedStep

/-!
# `final_level`: the glued claims

`glued`: from `b27`, the sumcheck's claim stored at the frame's byte `24`, the weight loaded into
(X21, X23), the glued claims' bounds (`b28`), then each claim (`loop`, by induction on the claims
left, each one `gstep`), to `.LFinalLevel_20` with the weight `finalWeight`.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (load_ofMachine eval_ptr wordAt_write)

public section

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The glued claims' loop.** -/
theorem loop (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hge : ∀ g, Spec (Labels.label NativeRustcVmArm.Vm.GluedEval.entryLabel) (GluedEvalPre g) (GluedEvalPost g))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {folded tail : Array EW} {claim : EW} {s5 : TState}
    (done : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b33Offset) →
      GBase a level w m0 st'.data folded tail claim s5 →
      st'.data.regs.X21 = (finalWeight m0.regs.X4.toNat b w tail).c0 →
      st'.data.regs.X23 = (finalWeight m0.regs.X4.toNat b w tail).c1 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st') :
    ∀ (n i : Nat) (st : MachineState), i + n = w.glued.size → i < w.glued.size →
      st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b29Offset) → GInv a level b w m0 st.data folded tail claim s5 i →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  intro n
  induction n with
  | zero => intro i st hn hi; exact absurd hi (by omega)
  | succ n ih =>
    intro i st hn hi hpc h
    exact gstep hp c hge hmul hpc hi h
      (fun st' hpc' hi' h' ↦ ih (i + 1) st' (by omega) hi' hpc' h')
      fun st' hpc' hB h21 h23 ↦ done st' hpc' hB (by rw [← weightAt_size]; exact h21)
        (by rw [← weightAt_size]; exact h23)

/-- **The glued claims.** -/
theorem glued (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hge : ∀ g, Spec (Labels.label NativeRustcVmArm.Vm.GluedEval.entryLabel) (GluedEvalPre g) (GluedEvalPost g))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} {folded tail : Array EW} {claim : EW} {s5 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b27Offset)) (hc : Core level m0 st.data folded)
    (htn : tail.size = mu m0) (hx22 : st.data.regs.X22.toBitVec = loc m0 1584)
    (hx29 : st.data.regs.X29.toNat = (w.alphas ++ tail).size)
    (hx23 : st.data.regs.X23 = claim.c0) (hx24 : st.data.regs.X24 = claim.c1)
    (htail : NativeRustcVm.EWsAt st.data.dmem (loc m0 1096) tail.toList)
    (hpt : NativeRustcVm.EWsAt st.data.dmem (loc m0 1584) (w.alphas ++ tail).toList)
    (hopt : OptEWAt st.data.dmem (loc m0 2552) (some (weightAt m0.regs.X4.toNat b w tail 0)))
    (hts : TStateAt st.data.dmem (tA m0) a s5)
    (done : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b33Offset) →
      GBase a level w m0 st'.data folded tail claim s5 →
      st'.data.regs.X21 = (finalWeight m0.regs.X4.toNat b w tail).c0 →
      st'.data.regs.X23 = (finalWeight m0.regs.X4.toNat b w tail).c1 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hf := hc.fr
  have hgl : w.glued.size ≤ 10 := (c.state_at hf).glued_le
  set wt := weightAt m0.regs.X4.toNat b w tail 0
  -- `b27`: the claim stored, the weight loaded, the claims' bounds.
  have x27 : (st.data.regs.getXReg .X27).toBitVec = pA m0 :=
    congrArg UInt64.toBitVec hc.base.x27
  have hin : WhirIn m0 (pA m0) 512 finalLevelStack := whirIn_pre c.pIn (by decide)
  have hwf := c.wf1 hf hin
  have hm := c.match1 (n := 512) hf x27
  refine exec_at (inf hp b27_in_code (by simp [b27])) run_b27 hwf hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  have hS : ∀ w ∈ (after b27 (wS 512)).mem, w.r = 0 ∧ w.off + w.n ≤ 2576 := by
    rw [after_eq run_b27]; decide +kernel
  have hS' : ∀ w ∈ (after b27 (wS 512)).mem, w.r = 0 ∧ w.off + w.n ≤ 2672 := fun w hw ↦
    ⟨(hS w hw).1, by have := (hS w hw).2; omega⟩
  have hf1 : FFr m0 st1.data := c.fr_block hf hm hm1 hwf rfl
    (by rw [← after_eq run_b27]; exact hS)
  have hsame : NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem (loc m0 40) 2512 :=
    Ctx.same_block hm1 hwf (by decide +kernel) (by decide)
  have hts1 : TStateAt st1.data.dmem (tA m0) a s5 :=
    c.ts_block hm1 hwf (by rw [← after_eq run_b27]; exact hS') hts
  -- The values `b27` computes.
  have l504 : (fenv m0 st.data [(pA m0, 512)]).load 1 504 8 = w.glued.size.toUInt64.toBitVec :=
    load_ofMachine (r := 1) (o := 504) rfl (c.state_at hf).glued_len
  have hlt : ((Sym.load 1 504 8).eval (fenv m0 st.data [(pA m0, 512)])).toNat < 11 := by
    show ((fenv m0 st.data [(pA m0, 512)]).load 1 504 8).toNat < 11
    rw [l504]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have hx8 : ((Sym.ite (.cmp .ult .W64 (.load 1 504 8) (.lit 11))
      (.bin .mul .W64 (.load 1 504 8) (.lit 6064)) (.lit 0)).eval
        (fenv m0 st.data [(pA m0, 512)])).toNat = 6064 * w.glued.size := by
    rw [ite_ult hlt (by decide)]
    show (BinOp.apply .mul .W64 ((fenv m0 st.data [(pA m0, 512)]).load 1 504 8)
      (BitVec.ofNat 64 6064)).toNat = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, l504, BitVec.toNat_ofNat,
      UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have x8 : st1.data.regs.X8.toBitVec = BitVec.ofNat 64 (6064 * w.glued.size) := by
    apply BitVec.eq_of_toNat_eq
    show (st1.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [reg_val hm1 (r := .X8) rfl, hx8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have x24 : st1.data.regs.X24.toBitVec = pA m0 + BitVec.ofNat 64 512 := by
    show (st1.data.regs.getXReg .X24).toBitVec = _
    rw [reg_val hm1 (r := .X24) rfl, ite_ult hlt (by decide)]
    rfl
  obtain ⟨-, hwt⟩ := id hopt
  rw [loc_off] at hwt
  obtain ⟨hw0, hw1⟩ := ewAt_iff.mp hwt
  rw [loc_off] at hw1
  have x21 : st1.data.regs.X21 = wt.c0 := reg_of hm1 (r := .X21) (v := .load 0 2560 8) rfl
    (load_ofMachine (r := 0) (o := 2560) rfl hw0)
  have x23 : st1.data.regs.X23 = wt.c1 := reg_of hm1 (r := .X23) (v := .load 0 2568 8) rfl
    (load_ofMachine (r := 0) (o := 2568) rfl hw1)
  -- The claim at the frame's byte `24`.
  have w24 : NativeRustcVm.WordAt st1.data.dmem (loc m0 24) claim.c0 := by
    have := wordAt_write hm1 (r := 0) (o := 24) (b := base m0 2672) (sz := 2672) rfl (by decide)
      (v := .reg .X23) (by rw [← after_eq run_b27]; decide +kernel)
    rw [← hx23]; exact this
  have w32 : NativeRustcVm.WordAt st1.data.dmem (loc m0 32) claim.c1 := by
    have := wordAt_write hm1 (r := 0) (o := 32) (b := base m0 2672) (sz := 2672) rfl (by decide)
      (v := .reg .X24) (by rw [← after_eq run_b27]; decide +kernel)
    rw [← hx24]; exact this
  have hcl : NativeRustcVm.EWAt st1.data.dmem (loc m0 24) claim :=
    ewAt_iff.mpr ⟨w24, by rw [loc_off]; exact w32⟩
  have k1 : ∀ r ∈ gRegs, st1.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦
    reg_of hm1 (kept_of (by decide) r hr) rfl
  have hB1 : GBase a level w m0 st1.data folded tail claim s5 := {
    fr := hf1
    x19 := by rw [show st1.data.regs.X19 = _ from k1 .X19 (by simp [gRegs])]; exact hc.base.x19
    x20 := (k1 .X20 (by simp [gRegs])).trans hc.base.x20
    x22 := by rw [show st1.data.regs.X22 = _ from k1 .X22 (by simp [gRegs])]; exact hx22
    x29 := by rw [show st1.data.regs.X29 = _ from k1 .X29 (by simp [gRegs])]; exact hx29
    size := hc.size
    le64 := c.two_mu_le
    le30 := by
      have : w.alphas.size + mu m0 ≤ 30 := c.alphas
      simp only [Array.size_append, htn]; omega
    fold := ewsAt_same hc.fold (same_sub hsame (o := 40) (len := 1024) (by decide) (by decide))
      (by rw [Array.length_toList, hc.size]; have := c.two_mu_le; omega)
    tl := ewsAt_same htail (same_sub hsame (o := 1096) (len := 480) (by decide) (by decide))
      (by rw [Array.length_toList, htn]; have := c.two_mu_le; have := mu_le this; omega)
    pts := ewsAt_same hpt (same_sub hsame (o := 1584) (len := 480) (by decide) (by decide)) (by
      have : w.alphas.size + mu m0 ≤ 30 := c.alphas
      simp only [Array.length_toList, Array.size_append, htn]; omega)
    cl := hcl
    ts := hts1 }
  -- The branch: no glued claims, to `.LFinalLevel_20`.
  simp only [PcOk] at hpc1
  have hcond : SBool.eval (fenv m0 st.data [(pA m0, 512)])
      (.cmp .eq .W64 (.ite (.cmp .ult .W64 (.load 1 504 8) (.lit 11))
        (.bin .mul .W64 (.load 1 504 8) (.lit 6064)) (.lit 0)) (.lit 0)) =
      decide (w.glued.size = 0) := by
    show CmpOp.apply .eq .W64 (Sym.eval _ (.ite (.cmp .ult .W64 (.load 1 504 8) (.lit 11))
      (.bin .mul .W64 (.load 1 504 8) (.lit 6064)) (.lit 0))) (BitVec.ofNat 64 0) = _
    simp only [CmpOp.apply, low_W64, bv_beq_toNat, hx8, BitVec.toNat_ofNat, Nat.zero_mod]
    by_cases h0 : w.glued.size = 0
    · simp [h0]
    · rw [decide_eq_false (by omega), decide_eq_false h0]
  rw [hcond] at hpc1
  by_cases h0 : w.glued.size = 0
  · simp only [h0, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.FinalLevel.b33Offset) NativeRustcVmArm.Vm.FinalLevel.label_20_at] at hpc1
    refine done st1 hpc1 hB1 ?_ ?_
    · rw [← weightAt_size, h0]; exact x21
    · rw [← weightAt_size, h0]; exact x23
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmArm.Vm.FinalLevel.b27Offset + b27.length = k + NativeRustcVmArm.Vm.FinalLevel.b28Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b27_next]] at hpc1
  -- `b28`: the claims' end, their stride.
  refine c.fblock hp b28_in_code (by simp [b28]) run_b28 rfl rfl hpc1 hf1
    fun st2 hm2 hpc2 hf2 hd2 hk2 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b28Offset + b28.length = k + NativeRustcVmArm.Vm.FinalLevel.b29Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b28_next]] at hpc2
  have hB2 : GBase a level w m0 st2.data folded tail claim s5 :=
    hB1.saved hf2 (fun r hr ↦ hk2 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd2])
      (by rw [hd2]; exact hts1)
  have y27 : st2.data.regs.X27.toBitVec = pA m0 + BitVec.ofNat 64 (512 + 6064 * w.glued.size) := by
    show (st2.data.regs.getXReg .X27).toBitVec = _
    rw [reg_val hm2 (r := .X27) rfl, ev_add2]
    show st1.data.regs.X24.toBitVec + st1.data.regs.X8.toBitVec = _
    rw [x24, x8, BitVec.add_assoc, ← BitVec.ofNat_add]
  have y28 : st2.data.regs.X28 = 6064 := reg_of hm2 (r := .X28) (v := .lit 6064) rfl rfl
  exact loop hp c hge hmul done w.glued.size 0 st2 (by omega) (by omega) hpc2
    ⟨hB2, (hk2 .X21 rfl).trans x21, (hk2 .X23 rfl).trans x23,
      (congrArg UInt64.toBitVec (hk2 .X24 rfl)).trans x24, y27, y28⟩

end

end NativeRustcVmArm.Whir.FinalLevel
