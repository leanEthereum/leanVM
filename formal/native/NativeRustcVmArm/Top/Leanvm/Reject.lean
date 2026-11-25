module

public import NativeRustcVmArm.Top.Leanvm.Decode

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt)
open NativeRustcVm.Top (Aligned Checks)
open NativeVm.Transcript (wd)

public section

private def countGuard : SBool :=
  .ite (.or (.not (.ite (.ite
    (.not (.cmp .ult .W64 (.load 1 88 8) (.lit 61944)))
    (.not (.cmp .ult .W64 (.load 1 72 8)
      (.bin .add .W64 (.bin .orr .W64 (.un (.ubfm 3 63) .W64 (.load 1 8 8)) (.lit 1)) (.lit 395289))))
    (.lit false))
    (.not (.cmp .ult .W64 (.load 1 24 8) (.lit 536870910))) (.lit true)))
    (.ite (.ite (.not (.cmp .ult .W64 (.load 1 88 8) (.lit 61944)))
      (.not (.cmp .ult .W64 (.load 1 72 8)
        (.bin .add .W64 (.bin .orr .W64 (.un (.ubfm 3 63) .W64 (.load 1 8 8)) (.lit 1)) (.lit 395289))))
      (.lit false)) (.cmp .eq .W64 (.load 1 24 8) (.lit 536870910)) (.lit false)))
    (.cmp .eq .W64 (.bin .and .W64 (.load 1 8 8) (.lit 18446744069414584320)) (.lit 0))
    (.lit false)

private theorem highMask (x : BitVec 64)
    (h : (x &&& 18446744069414584320#64 == 0#64) = true) : x.toNat < 2 ^ 32 := by
  have hz : x &&& 18446744069414584320#64 = 0#64 := by simpa only [beq_iff_eq] using h
  have hsplit : (x &&& 4294967295#64) ||| (x &&& 18446744069414584320#64) = x := by
    rw [← BitVec.and_or_distrib_left,
      show 4294967295#64 ||| 18446744069414584320#64 = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes]
  rw [hz, BitVec.or_zero] at hsplit
  have hn := congrArg BitVec.toNat hsplit
  rw [BitVec.toNat_and, BitVec.toNat_ofNat,
    show 4294967295 % 2 ^ 64 = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at hn
  have hm := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by decide)
  omega

private theorem guardBool (w d n e l : Bool) :
    (if (!(if (if !w then !d else false) then !n else true) ||
      (if (if !w then !d else false) then e else false)) then l else false) =
      ((!w && !d) && (n || e) && l) := by
  cases w <;> cases d <;> cases n <;> cases e <;> cases l <;> decide

private theorem countGuard_eval [Labels] (env : Env) :
    countGuard.eval env =
      ((!((env.load 1 88 8).ult 61944#64) &&
        !((env.load 1 72 8).ult (((env.load 1 8 8) >>> 3 ||| 1#64) + 395289#64))) &&
        ((env.load 1 24 8).ult 536870910#64 || (env.load 1 24 8 == 536870910#64)) &&
        (env.load 1 8 8 &&& 18446744069414584320#64 == 0#64)) := by
  simp only [countGuard, SBool.eval, Sym.eval, CmpOp.apply, low_W64, BinOp.apply,
    ext_W64, NativeRustcVmArm.Field.ubfm_lsr _ _ (show 3 < 64 by decide)]
  exact guardBool _ _ _ _ _

private theorem countGuard_ok [Labels] (env : Env) {a : Entry.Areas} {L n : Nat}
    (h8 : env.load 1 8 8 = BitVec.ofNat 64 L)
    (h24 : env.load 1 24 8 = BitVec.ofNat 64 n)
    (h72 : env.load 1 72 8 = a.decCount.toBitVec)
    (h88 : env.load 1 88 8 = a.workCount.toBitVec)
    (hL64 : L < 2 ^ 64) (hn64 : n < 2 ^ 64)
    (h : countGuard.eval env = true) : Entry.CountsOk a L n := by
  rw [countGuard_eval, h8, h24, h72, h88] at h
  have hparts := h
  simp only [Bool.and_eq_true] at hparts
  have hmask := hparts.2
  have hL : L < 2 ^ 32 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL64] using highMask _ hmask
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, BitVec.ult,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, dw_toNat hL, UInt64.toNat_toBitVec,
    ofNat_beq hn64 (show 536870910 < 2 ^ 64 by decide),
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  rcases h.1 with ⟨⟨hw, hd⟩, hn⟩
  exact ⟨hL, by rcases hn with hn | hn <;> omega, by omega,
    show 61944 ≤ a.workCount.toNat from by omega⟩

private structure RejectGeo (m : MachineData) : Prop where
  s : 19344 ≤ m.regs.SP.toBitVec.toNat
  al : m.regs.SP.toBitVec.toNat % 16 = 0
  F : (frameOf m).toNat = m.regs.SP.toBitVec.toNat - 128
  sb : (stackBelow m leanvmVerifyStack).toNat = m.regs.SP.toBitVec.toNat - 19344
  ctxN : m.regs.X0.toBitVec.toNat + 96 ≤ 2 ^ 64
  ctx : m.regs.X0.toBitVec.toNat + 96 ≤ m.regs.SP.toBitVec.toNat - 19344 ∨
    m.regs.SP.toBitVec.toNat ≤ m.regs.X0.toBitVec.toNat
  frame : Mapped m.dmem (frameOf m) 128
  context : Mapped m.dmem m.regs.X0.toBitVec 96

private theorem rejectGeo {a : Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m : MachineData}
    (hin : Entry.ContextAt m.dmem m.regs.X0 a bytes bytecode pub)
    (hs : StackOk m leanvmVerifyStack)
    (hc : NativeRustcVm.Apart m.regs.X0.toBitVec 96 (stackBelow m leanvmVerifyStack) leanvmVerifyStack) :
    RejectGeo m := by
  have hsN : 19344 ≤ m.regs.SP.toBitVec.toNat := hs.2.1
  have hF : (frameOf m).toNat = m.regs.SP.toBitVec.toNat - 128 := toNat_subAddr (by omega)
  have hsb : (stackBelow m leanvmVerifyStack).toNat = m.regs.SP.toBitVec.toNat - 19344 :=
    toNat_subAddr hsN
  have hfit : m.regs.X0.toBitVec.toNat + 96 ≤ 2 ^ 64 := hin.fitCtx
  have hctx : m.regs.X0.toBitVec.toNat + 96 ≤ m.regs.SP.toBitVec.toNat - 19344 ∨
      m.regs.SP.toBitVec.toNat ≤ m.regs.X0.toBitVec.toNat := by
    unfold NativeRustcVm.Apart at hc
    rw [hsb, leanvmVerifyStack_eq] at hc
    omega
  refine ⟨hsN, hs.1, hF, hsb, hfit, hctx, ?_, ?_⟩
  · have hsl := m.regs.SP.toBitVec.isLt
    exact Mapped.within hs.2.2 (by
      change (stackBelow m leanvmVerifyStack).toNat + leanvmVerifyStack ≤ _
      rw [hsb, leanvmVerifyStack_eq]; omega)
      (by change (stackBelow m leanvmVerifyStack).toNat ≤ _; rw [hsb, hF]; omega)
      (by change _ ≤ (stackBelow m leanvmVerifyStack).toNat + leanvmVerifyStack
          rw [hsb, hF, leanvmVerifyStack_eq]; omega)
  · exact NativeRustcVm.Mapped.mono (NativeRustcVm.mapped_of_wordView hin.ctxSome) (by decide)

private theorem rejectCtxEnv [Labels] {m st : MachineData} (g : RejectGeo m)
    (hB : Body m 128 slots (InStack m leanvmVerifyStack) st)
    (hx0 : st.regs.X0 = m.regs.X0) :
    (Env.ofMachine st [(frameOf m, 128), (m.regs.X0.toBitVec, 96)]).WF ∧
      Match (Env.ofMachine st [(frameOf m, 128), (m.regs.X0.toBitVec, 96)]) ctxS st := by
  have hs := g.s
  have hF := g.F
  have hc := g.ctx
  have hcN := g.ctxN
  have hsl := m.regs.SP.toBitVec.isLt
  have hcF : (frameOf m).toNat + 128 ≤ m.regs.X0.toBitVec.toNat ∨
      m.regs.X0.toBitVec.toNat + 96 ≤ (frameOf m).toNat := by omega
  refine ⟨Env.wf_of ⟨⟨Mapped.kept g.frame hB.kept,
      show (frameOf m).toNat + 128 ≤ 2 ^ 64 by omega⟩,
    ⟨Mapped.kept g.context hB.kept, hcN⟩, trivial⟩ (List.pairwise_pair.mpr hcF), ?_⟩
  exact match_ofMachine ⟨rfl, fun _ ↦ show (frameOf m).toNat % 16 = 0 by have := g.al; omega,
      rfl, fun h ↦ absurd h (by decide), trivial⟩
    (show st.regs.SP.toBitVec = frameOf m + BitVec.ofInt 64 0 by rw [hB.sp]; simp [frameOf])
    ⟨show (st.regs.getXReg .X0).toBitVec = m.regs.X0.toBitVec + BitVec.ofInt 64 0 by
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      exact congrArg UInt64.toBitVec hx0, trivial⟩ trivial trivial trivial

private theorem rejectWord {m st : MachineData} (g : RejectGeo m)
    (hB : Body m 128 slots (InStack m leanvmVerifyStack) st) {i : Nat} {v : UInt64}
    (hi : i < 12) (h : NativeRustcVm.wordView m.dmem (wd m.regs.X0 i) = some v) :
    WordAt st.dmem (m.regs.X0.toBitVec + BitVec.ofNat 64 (8 * i)) v := by
  have gc := g.ctx
  have gcN := g.ctxN
  exact bytesAt_keep (ctxWord h) hB.same (by
      rw [NativeRustcVm.length_wordBytes, toNat_addr (by omega)]; omega) fun q hq ↦ by
    rw [NativeRustcVm.length_wordBytes, toNat_addr (by omega)]
    unfold InStack at hq
    rw [leanvmVerifyStack_eq] at hq
    omega

private def RejectPost (m : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m ∧ st.data.regs.X0 = 0 ∧
    SameOutside m.dmem st.data.dmem (InStack m leanvmVerifyStack) ∧ Saved m st.data

variable [Host] {k : Nat}

private theorem rejectExit (hp : Placed code k) {m : MachineData} (g : RejectGeo m)
    {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b1Offset))
    (hB : Body m 128 slots (InStack m leanvmVerifyStack) st.data) :
    Eventually (step1 Host.exe) (RejectPost m) st :=
  failExit hp (by have := g.s; omega) g.al hpc hB (Mapped.kept g.frame hB.kept)

private theorem rejectExit2 (hp : Placed code k) {m : MachineData} (g : RejectGeo m)
    {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b2Offset))
    (hB : Body m 128 slots (InStack m leanvmVerifyStack) st.data)
    (hx8 : st.data.regs.X8 = 0) :
    Eventually (step1 Host.exe) (RejectPost m) st :=
  (exit2 hp (by have := g.s; omega) g.al hpc hB (Mapped.kept g.frame hB.kept)).mono
    fun _ h ↦ ⟨h.1, h.2.1.trans hx8, h.2.2⟩

private theorem rejectWire (hp : Placed code k) {a : Entry.Areas} {L : Nat}
    {m : MachineData} (g : RejectGeo m) (hL64 : L < 2 ^ 64)
    {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b10Offset))
    (hB : Body m 128 slots (InStack m leanvmVerifyStack) st.data)
    (hx19 : st.data.regs.X19 = L.toUInt64) (hx9 : st.data.regs.X9 = a.wire)
    (hbad : ¬ (0 < L → a.wire ≠ 0)) :
    Eventually (step1 Host.exe) (RejectPost m) st := by
  have hs : 128 ≤ m.regs.SP.toBitVec.toNat := by have := g.s; omega
  have hL : L ≠ 0 := by intro h; apply hbad; omega
  have hw : a.wire = 0 := by
    by_contra h
    exact hbad (fun _ ↦ h)
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b10Offset hp b10_in_code (by simp [b10]))
    run_b10 (Env.wf_nil _) hpc (match_nil _) fun st10 hm10 hpc10 ↦ ?_
  have hk10 := none_keeps b10 (by simp)
  rw [after_eq run_b10] at hk10
  have hB10 := bodyNo hB hs (match_nil _) hm10 (Env.wf_nil _) rfl hk10.1 hk10.2
  simp only [PcOk, evalRegNat0 (Env.ofMachine st.data []) (r := .X19)
    (congrArg UInt64.toBitVec hx19) hL64, hL, decide_false, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b10Offset + b10.length =
      k + NativeRustcVmArm.Vm.LeanvmVerify.b11Offset from by
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b10_next]] at hpc10
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b11Offset hp b11_in_code (by simp [b11]))
    run_b11 (Env.wf_nil _) hpc10 (match_nil _) fun st11 hm11 hpc11 ↦ ?_
  have hk11 := none_keeps b11 (by simp)
  rw [after_eq run_b11] at hk11
  have hB11 := bodyNo hB10 hs (match_nil _) hm11 (Env.wf_nil _) rfl hk11.1 hk11.2
  have hx9' : st10.data.regs.X9 = a.wire := (keepReg' .X9 hm10 rfl).trans hx9
  simp only [PcOk, evalReg0 (Env.ofMachine st10.data []) (r := .X9)
    (congrArg UInt64.toBitVec hx9'), hw, decide_true, ite_true, lbl_1 hp] at hpc11
  exact rejectExit hp g hpc11 hB11

private theorem rejectPointers (hp : Placed code k) {a : Entry.Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} {m : MachineData}
    (hin : Entry.ContextAt m.dmem m.regs.X0 a bytes bytecode pub) (g : RejectGeo m)
    {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b3Offset))
    (hB : Body m 128 slots (InStack m leanvmVerifyStack) st.data)
    (hx0 : st.data.regs.X0 = m.regs.X0)
    (hx19 : st.data.regs.X19 = bytes.length.toUInt64)
    (hx20 : st.data.regs.X20 = bytecode.length.toUInt64)
    (hbad : ¬ Aligned a bytes.length bytecode.length) :
    Eventually (step1 Host.exe) (RejectPost m) st := by
  have hs : 128 ≤ m.regs.SP.toBitVec.toNat := by have := g.s; omega
  obtain ⟨hwf3, hm3⟩ := rejectCtxEnv g hB hx0
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b3Offset hp b3_in_code (by simp [b3]))
    run_b3 hwf3 hpc hm3 fun st3 hm3' hpc3 ↦ ?_
  have hk3 := ctx_keeps.1
  rw [after_eq run_b3] at hk3
  have hB3 := bodyNo hB hs hm3 hm3' hwf3 rfl hk3.1 hk3.2
  have hz3 : st3.data.regs.X8 = 0 := UInt64.toBitVec_inj.mp (hm3'.regs .X8 _ rfl)
  have l64 := load_wordAt (r := 1) (env := Env.ofMachine st.data
    [(frameOf m, 128), (m.regs.X0.toBitVec, 96)])
    (rejectWord g hB (i := 8) (by decide) hin.decPtr)
  have hX23 : st3.data.regs.X23 = a.decoded :=
    UInt64.toBitVec_inj.mp ((hm3'.regs .X23 _ rfl).trans l64)
  simp only [PcOk, evalLoad0 _ l64] at hpc3
  by_cases hd0 : a.decoded = 0
  · simp only [hd0, decide_true, ite_true, lbl_2 hp] at hpc3
    exact rejectExit2 hp g hpc3 hB3 hz3
  simp only [hd0, decide_false, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b3Offset + b3.length =
      k + NativeRustcVmArm.Vm.LeanvmVerify.b4Offset from by
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b3_next]] at hpc3
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b4Offset hp b4_in_code (by simp [b4]))
    run_b4 (Env.wf_nil _) hpc3 (match_nil _) fun st4 hm4 hpc4 ↦ ?_
  have hk4 := none_keeps b4 (by simp)
  rw [after_eq run_b4] at hk4
  have hB4 := bodyNo hB3 hs (match_nil _) hm4 (Env.wf_nil _) rfl hk4.1 hk4.2
  simp only [PcOk, evalAnd7 (Env.ofMachine st3.data []) (r := .X23)
    (congrArg UInt64.toBitVec hX23)] at hpc4
  by_cases hd8 : a.decoded.toNat % 8 = 0
  swap
  · simp only [hd8, decide_false, Bool.not_false, ite_true, lbl_2 hp] at hpc4
    exact rejectExit2 hp g hpc4 hB4 ((keepReg' .X8 hm4 rfl).trans hz3)
  simp only [hd8, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b4Offset + b4.length =
      k + NativeRustcVmArm.Vm.LeanvmVerify.b5Offset from by
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b4_next]] at hpc4
  obtain ⟨hwf5, hm5⟩ := rejectCtxEnv g hB4
    ((keepReg' .X0 hm4 rfl).trans (x0_ctx hm3' rfl))
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b5Offset hp b5_in_code (by simp [b5]))
    run_b5 hwf5 hpc4 hm5 fun st5 hm5' hpc5 ↦ ?_
  have hk5 := ctx_keeps.2.1
  rw [after_eq run_b5] at hk5
  have hB5 := bodyNo hB4 hs hm5 hm5' hwf5 rfl hk5.1 hk5.2
  have hz5 : st5.data.regs.X8 = 0 := UInt64.toBitVec_inj.mp (hm5'.regs .X8 _ rfl)
  have l80 := load_wordAt (r := 1) (env := Env.ofMachine st4.data
    [(frameOf m, 128), (m.regs.X0.toBitVec, 96)])
    (rejectWord g hB4 (i := 10) (by decide) hin.workPtr)
  have hX22 : st5.data.regs.X22 = a.work :=
    UInt64.toBitVec_inj.mp ((hm5'.regs .X22 _ rfl).trans l80)
  simp only [PcOk, evalLoad0 _ l80] at hpc5
  by_cases hw0 : a.work = 0
  · simp only [hw0, decide_true, ite_true, lbl_2 hp] at hpc5
    exact rejectExit2 hp g hpc5 hB5 hz5
  simp only [hw0, decide_false, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b5Offset + b5.length =
      k + NativeRustcVmArm.Vm.LeanvmVerify.b6Offset from by
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b5_next]] at hpc5
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b6Offset hp b6_in_code (by simp [b6]))
    run_b6 (Env.wf_nil _) hpc5 (match_nil _) fun st6 hm6 hpc6 ↦ ?_
  have hk6 := none_keeps b6 (by simp)
  rw [after_eq run_b6] at hk6
  have hB6 := bodyNo hB5 hs (match_nil _) hm6 (Env.wf_nil _) rfl hk6.1 hk6.2
  simp only [PcOk, evalAnd7 (Env.ofMachine st5.data []) (r := .X22)
    (congrArg UInt64.toBitVec hX22)] at hpc6
  by_cases hw8 : a.work.toNat % 8 = 0
  swap
  · simp only [hw8, decide_false, Bool.not_false, ite_true, lbl_2 hp] at hpc6
    exact rejectExit2 hp g hpc6 hB6 ((keepReg' .X8 hm6 rfl).trans hz5)
  simp only [hw8, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b6Offset + b6.length =
      k + NativeRustcVmArm.Vm.LeanvmVerify.b7Offset from by
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b6_next]] at hpc6
  obtain ⟨hwf7, hm7⟩ := rejectCtxEnv g hB6
    ((keepReg' .X0 hm6 rfl).trans (x0_ctx hm5' rfl))
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b7Offset hp b7_in_code (by simp [b7]))
    run_b7 hwf7 hpc6 hm7 fun st7 hm7' hpc7 ↦ ?_
  have hk7 := ctx_keeps.2.2
  rw [after_eq run_b7] at hk7
  have hB7 := bodyNo hB6 hs hm7 hm7' hwf7 rfl hk7.1 hk7.2
  have lw : ∀ {i : Nat} {v : UInt64}, i < 12 →
      NativeRustcVm.wordView m.dmem (wd m.regs.X0 i) = some v →
      (Env.ofMachine st6.data [(frameOf m, 128), (m.regs.X0.toBitVec, 96)]).load 1 (8 * i) 8 =
        v.toBitVec := fun hi h ↦ load_wordAt (r := 1) (rejectWord g hB6 hi h)
  have hX9 : st7.data.regs.X9 = a.wire :=
    UInt64.toBitVec_inj.mp ((hm7'.regs .X9 _ rfl).trans (lw (i := 0) (by decide) hin.wirePtr))
  have hX24 : st7.data.regs.X24 = a.bytecode :=
    UInt64.toBitVec_inj.mp ((hm7'.regs .X24 _ rfl).trans (lw (i := 2) (by decide) hin.bcPtr))
  have hX19 : st7.data.regs.X19 = bytes.length.toUInt64 :=
    (keepReg' .X19 hm7' rfl).trans ((keepReg' .X19 hm6 rfl).trans
      ((keepReg' .X19 hm5' rfl).trans ((keepReg' .X19 hm4 rfl).trans
      ((keepReg' .X19 hm3' rfl).trans hx19))))
  have hX20 : st6.data.regs.X20 = bytecode.length.toUInt64 :=
    (keepReg' .X20 hm6 rfl).trans ((keepReg' .X20 hm5' rfl).trans
      ((keepReg' .X20 hm4 rfl).trans ((keepReg' .X20 hm3' rfl).trans hx20)))
  simp only [PcOk, evalRegNat0 (Env.ofMachine st6.data
    [(frameOf m, 128), (m.regs.X0.toBitVec, 96)]) (r := .X20)
    (congrArg UInt64.toBitVec hX20) hin.bc64] at hpc7
  by_cases hn0 : bytecode.length = 0
  · simp only [hn0, decide_true, ite_true, lbl_10 hp] at hpc7
    apply rejectWire hp g hin.L64 hpc7 hB7 hX19 hX9
    intro hw
    exact hbad ⟨⟨hd0, hd8⟩, ⟨hw0, hw8⟩, by simp [hn0], hw⟩
  simp only [hn0, decide_false, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b7Offset + b7.length =
      k + NativeRustcVmArm.Vm.LeanvmVerify.b8Offset from by
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b7_next]] at hpc7
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b8Offset hp b8_in_code (by simp [b8]))
    run_b8 (Env.wf_nil _) hpc7 (match_nil _) fun st8 hm8 hpc8 ↦ ?_
  have hk8 := none_keeps b8 (by simp)
  rw [after_eq run_b8] at hk8
  have hB8 := bodyNo hB7 hs (match_nil _) hm8 (Env.wf_nil _) rfl hk8.1 hk8.2
  have hz8 : st8.data.regs.X8 = 0 := UInt64.toBitVec_inj.mp (hm8.regs .X8 _ rfl)
  simp only [PcOk, evalReg0 (Env.ofMachine st7.data []) (r := .X24)
    (congrArg UInt64.toBitVec hX24)] at hpc8
  by_cases hb0 : a.bytecode = 0
  · simp only [hb0, decide_true, ite_true, lbl_2 hp] at hpc8
    exact rejectExit2 hp g hpc8 hB8 hz8
  simp only [hb0, decide_false, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b8Offset + b8.length =
      k + NativeRustcVmArm.Vm.LeanvmVerify.b9Offset from by
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b8_next]] at hpc8
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b9Offset hp b9_in_code (by simp [b9]))
    run_b9 (Env.wf_nil _) hpc8 (match_nil _) fun st9 hm9 hpc9 ↦ ?_
  have hk9 := none_keeps b9 (by simp)
  rw [after_eq run_b9] at hk9
  have hB9 := bodyNo hB8 hs (match_nil _) hm9 (Env.wf_nil _) rfl hk9.1 hk9.2
  have hX24' : st8.data.regs.X24 = a.bytecode := (keepReg' .X24 hm8 rfl).trans hX24
  simp only [PcOk, evalAnd7 (Env.ofMachine st8.data []) (r := .X24)
    (congrArg UInt64.toBitVec hX24')] at hpc9
  by_cases hb8 : a.bytecode.toNat % 8 = 0
  swap
  · simp only [hb8, decide_false, Bool.not_false, ite_true, lbl_2 hp] at hpc9
    exact rejectExit2 hp g hpc9 hB9 ((keepReg' .X8 hm9 rfl).trans hz8)
  simp only [hb8, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b9Offset + b9.length =
      k + NativeRustcVmArm.Vm.LeanvmVerify.b10Offset from by
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b9_next]] at hpc9
  apply rejectWire hp g hin.L64 hpc9 hB9
    ((keepReg' .X19 hm9 rfl).trans ((keepReg' .X19 hm8 rfl).trans hX19))
    ((keepReg' .X9 hm9 rfl).trans ((keepReg' .X9 hm8 rfl).trans hX9))
  intro hw
  exact hbad ⟨⟨hd0, hd8⟩, ⟨hw0, hw8⟩, fun _ ↦ ⟨hb0, hb8⟩, hw⟩

private theorem rejectEntry (hp : Placed code k) {a : Entry.Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} {m : MachineData}
    (hin : Entry.ContextAt m.dmem m.regs.X0 a bytes bytecode pub) (g : RejectGeo m)
    (hbad : ¬ Checks a bytes.length bytecode.length) :
    Eventually (step1 Host.exe) (RejectPost m)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b0Offset)⟩ := by
  have hs := g.s
  have hF := g.F
  have hsl := m.regs.SP.toBitVec.isLt
  have hc := g.ctx
  have hcF : (frameOf m).toNat + 128 ≤ m.regs.X0.toBitVec.toNat ∨
      m.regs.X0.toBitVec.toNat + 96 ≤ (frameOf m).toNat := by omega
  have hwf : (Env.ofMachine m [(frameOf m, 128), (m.regs.X0.toBitVec, 96)]).WF :=
    Env.wf_of ⟨⟨g.frame, show (frameOf m).toNat + 128 ≤ 2 ^ 64 by omega⟩,
      ⟨g.context, g.ctxN⟩, trivial⟩ (List.pairwise_pair.mpr hcF)
  have hm : Match (Env.ofMachine m [(frameOf m, 128), (m.regs.X0.toBitVec, 96)]) entryS m :=
    match_ofMachine ⟨rfl, fun _ ↦ show (frameOf m).toNat % 16 = 0 by have := g.al; omega,
      rfl, fun h ↦ absurd h (by decide), trivial⟩
      (show m.regs.SP.toBitVec = frameOf m + BitVec.ofInt 64 128 by
        rw [show BitVec.ofInt 64 128 = BitVec.ofNat 64 128 from rfl, frameOf,
          BitVec.sub_add_cancel])
      ⟨show (m.regs.getXReg .X0).toBitVec = m.regs.X0.toBitVec + BitVec.ofInt 64 0 by
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl,
        trivial⟩ trivial trivial trivial
  have hld : ∀ {i : Nat} {v : UInt64},
      NativeRustcVm.wordView m.dmem (wd m.regs.X0 i) = some v →
      (Env.ofMachine m [(frameOf m, 128), (m.regs.X0.toBitVec, 96)]).load 1 (8 * i) 8 =
        v.toBitVec := fun h ↦ load_wordAt (r := 1) (ctxWord h)
  refine exec_then (hb NativeRustcVmArm.Vm.LeanvmVerify.b0Offset hp b0_in_code (by simp [b0]))
    run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hB : Body m 128 slots (InStack m leanvmVerifyStack) st1.data := by
    refine ⟨?_, fun p hp' ↦ ?_, fun r hr hn ↦ ?_, fun q hq ↦ ?_, hm1.kept hwf⟩
    · rw [hm1.sp]; show frameOf m + BitVec.ofInt 64 0 = _; simp [frameOf]
    · have hw := b0_slots p hp'
      rw [after_eq run_b0] at hw
      have hsl' : p.1 + 8 ≤ 128 := by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with h | h | h | h | h | h | h <;> rw [h] <;> decide
      exact hm1.bytesAt_write (r := 0) (b := frameOf m) (sz := 128) rfl hsl' hw
    · have h := b0_regs r (nonslot hr hn)
      rw [after_eq run_b0] at h
      exact UInt64.toBitVec_inj.mp (hm1.regs r _ h)
    · refine hm1.get?_mem0 hwf fun hw ↦ hq ?_
      have hb0m := b0_mem
      rw [after_eq run_b0] at hb0m
      have := written_sub (r := 0) rfl hb0m hw
      unfold InStack
      rw [leanvmVerifyStack_eq]
      omega
  change st1.pc = if countGuard.eval (Env.ofMachine m
    [(frameOf m, 128), (m.regs.X0.toBitVec, 96)]) then
      Labels.label NativeRustcVmArm.Vm.LeanvmVerify.label_3
    else Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b0Offset + b0.length) at hpc1
  by_cases hc : countGuard.eval (Env.ofMachine m
      [(frameOf m, 128), (m.regs.X0.toBitVec, 96)]) = true
  · rw [ite_eq_left hc, lbl_3 hp] at hpc1
    have hcounts := countGuard_ok _ (hld (i := 1) hin.wireLen) (hld (i := 3) hin.bcLen)
      (hld (i := 9) hin.decCount) (hld (i := 11) hin.workCount) hin.L64 hin.bc64 hc
    apply rejectPointers hp hin g hpc1 hB
    · exact x0_ctx hm1 rfl
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans (hld (i := 1) hin.wireLen))
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X20 _ rfl).trans (hld (i := 3) hin.bcLen))
    · exact fun hal ↦ hbad ⟨hcounts, hal⟩
  · rw [ite_eq_right hc, show k + NativeRustcVmArm.Vm.LeanvmVerify.b0Offset + b0.length =
        k + NativeRustcVmArm.Vm.LeanvmVerify.b1Offset from by
        rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b0_next]] at hpc1
    exact rejectExit hp g hpc1 hB

/-- Failed entry checks return zero without accessing the pointed-to areas. -/
theorem reject (hp : Placed code k) {a : Entry.Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} {m : MachineData}
    (hin : Entry.ContextAt m.dmem m.regs.X0 a bytes bytecode pub)
    (hstack : StackOk m leanvmVerifyStack)
    (hctx : NativeRustcVm.Apart m.regs.X0.toBitVec 96 (stackBelow m leanvmVerifyStack) leanvmVerifyStack)
    (hbad : ¬ Checks a bytes.length bytecode.length) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ st.data.regs.X0 = 0 ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m leanvmVerifyStack) leanvmVerifyStack) ∧
      Saved m st.data) ⟨m, Labels.label NativeRustcVmArm.Vm.LeanvmVerify.entryLabel⟩ := by
  have g := rejectGeo hin hstack hctx
  rw [lbl_entry hp]
  refine (rejectEntry hp hin g hbad).mono fun st h ↦ ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro q hq
  apply h.2.2.1 q
  intro hq'
  apply hq
  have hs := g.s
  have hsb := g.sb
  have hsl := m.regs.SP.toBitVec.isLt
  rw [inRange_iff (by rw [hsb, leanvmVerifyStack_eq]; omega), hsb, leanvmVerifyStack_eq]
  unfold InStack at hq'
  rw [leanvmVerifyStack_eq] at hq'
  omega

#print axioms reject

end

end NativeRustcVmArm.Top.Leanvm
