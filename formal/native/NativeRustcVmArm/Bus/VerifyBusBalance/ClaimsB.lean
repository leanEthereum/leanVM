module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Code.Vm.BytecodeShare.Names
public import NativeRustcVmArm.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmArm.Code.Vm.Kpow.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.ClaimsPre
public import NativeRustcVmArm.Bus.VerifyBusBalance.Share

/-!
# `verify_bus_balance`'s four claims

From `b24` (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b24Offset`), the scalars read: `b24` empties the claims and pushes the first;
`b25` to `b31` check each `push_claim` and push the next three; then the bytecode share
(`claimsB_spec`). `ClSt cs`: the state between the pushes, `cs` the claims pushed.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section
variable [Labels]

/-- **Between the pushes**: the locals, the registers, the transcript at `s3`, the claims `cs`. -/
structure ClSt (L : LayoutW) (m0 : MachineData) (w pt tv mem : Array EW) (beta mf bf : EW)
    (a : DecArea) (s3 : TState) (cs : Array ColumnClaimW) (m : MachineData) : Prop where
  fr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m
  mem' : ClaimsMem m0 L w pt tv beta m.dmem
  hmem : NativeRustcVm.EWsAt m.dmem (loc m0 4144) mem.toList
  msz : mem.size = 2
  w88 : NativeRustcVm.WordAt m.dmem (loc m0 88) bf.c1
  w96 : NativeRustcVm.WordAt m.dmem (loc m0 96) bf.c0
  w104 : NativeRustcVm.WordAt m.dmem (loc m0 104) mf.c1
  w112 : NativeRustcVm.WordAt m.dmem (loc m0 112) mf.c0
  w120 : NativeRustcVm.WordAt m.dmem (loc m0 120) (min L.logBytecode pt.size).toUInt64
  x19 : m.regs.getXReg .X19 = m0.regs.X4
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : m.regs.getXReg .X21 = UInt64.ofBitVec (loc m0 3136)
  x22 : m.regs.getXReg .X22 = beta.c1
  x23 : m.regs.getXReg .X23 = m0.regs.X3
  x24 : m.regs.getXReg .X24 = m0.regs.X2
  x25 : m.regs.getXReg .X25 = m0.regs.X0
  x26 : (m.regs.getXReg .X26).toNat = pt.size
  x27 : m.regs.getXReg .X27 = (min L.logMemory pt.size).toUInt64
  x28 : m.regs.getXReg .X28 = m0.regs.X5
  x29 : (m.regs.getXReg .X29).toNat = L.logBytecode
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s3
  cl : ClaimsWAt m.dmem m0.regs.X5.toBitVec cs

omit [Labels] in
/-- **`ClSt` through changes** keeping the locals and the registers. -/
theorem ClSt.transfer {L : LayoutW} {m0 : MachineData} {w pt tv mem : Array EW}
    {beta mf bf : EW} {a : DecArea} {s3 : TState} {cs cs' : Array ColumnClaimW}
    {m m' : MachineData} (A : ClSt L m0 w pt tv mem beta mf bf a s3 cs m)
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m')
    (hk : KeepIv [(88, 4176)] m0 m.dmem m'.dmem) (hr : RegsEq csL m m')
    (hts : TStateAt m'.dmem m0.regs.X0.toBitVec a s3)
    (hcl : ClaimsWAt m'.dmem m0.regs.X5.toBitVec cs') :
    ClSt L m0 w pt tv mem beta mf bf a s3 cs' m' := by
  have wd : ∀ {o : Nat} {v : UInt64}, 88 ≤ o → o + 8 ≤ 4176 →
      NativeRustcVm.WordAt m.dmem (loc m0 o) v → NativeRustcVm.WordAt m'.dmem (loc m0 o) v :=
    fun h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn (by simp) h1 h2) le_rfl
  have g : ∀ r ∈ csL, m'.regs.getXReg r = m.regs.getXReg r := hr
  exact ⟨hfr, A.mem'.of_keep (hk.mono (ivSub (by decide))),
    NativeRustcVm.Tables.EWsAt.of_same A.hmem (hk.sameIn (lo := 88) (hi := 4176) (by simp)
      (o := 4144) (n := 32) (by omega) (by omega)) (by rw [Array.length_toList, A.msz]), A.msz,
    wd (by omega) (by omega) A.w88, wd (by omega) (by omega) A.w96,
    wd (by omega) (by omega) A.w104, wd (by omega) (by omega) A.w112,
    wd (by omega) (by omega) A.w120,
    (g .X19 (by simp)).trans A.x19, (g .X20 (by simp)).trans A.x20,
    (g .X21 (by simp)).trans A.x21, (g .X22 (by simp)).trans A.x22,
    (g .X23 (by simp)).trans A.x23, (g .X24 (by simp)).trans A.x24,
    (g .X25 (by simp)).trans A.x25, by rw [g .X26 (by simp)]; exact A.x26,
    (g .X27 (by simp)).trans A.x27, (g .X28 (by simp)).trans A.x28,
    by rw [g .X29 (by simp)]; exact A.x29, hts, hcl⟩

omit [Labels] in
/-- **`ClSt` through a block** without writes keeping the registers. -/
theorem ClSt.block {L : LayoutW} {m0 : MachineData} {w pt tv mem : Array EW}
    {beta mf bf : EW} {a : DecArea} {s3 : TState} {cs : Array ColumnClaimW}
    {m m' : MachineData} (A : ClSt L m0 w pt tv mem beta mf bf a s3 cs m)
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m') (hd : m'.dmem = m.dmem)
    (hr : RegsEq csL m m') : ClSt L m0 w pt tv mem beta mf bf a s3 cs m' :=
  A.transfer hfr (KeepIv.rfl' hd) hr (by rw [hd]; exact A.ts) (by rw [hd]; exact A.cl)

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **`ClSt` through `push_claim`.** -/
theorem ClSt.push (h : VerifyBusBalancePre a s0 L m0)
    (hpcl : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {w pt tv mem : Array EW} {beta mf bf : EW} {s3 : TState} {cs : Array ColumnClaimW}
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (A : ClSt L m0 w pt tv mem beta mf bf a s3 cs st.data) (hcs : cs.size < claimCap)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel ∧ retOf st.data = next)
    {j id : Nat} {v : EW} (hj : j ≤ 30)
    (x0 : st.data.regs.X0 = m0.regs.X5) (x1 : st.data.regs.X1.toNat = id)
    (x2 : st.data.regs.X2 = UInt64.ofBitVec (loc m0 3136))
    (x3 : st.data.regs.X3 = (min j pt.size).toUInt64)
    (x4 : st.data.regs.X4 = v.c0) (x5 : st.data.regs.X5 = v.c1)
    (cont : ∀ m2, ClSt L m0 w pt tv mem beta mf bf a s3 (cs.push ⟨id, pt.extract 0 j, v⟩) m2 →
      m2.regs.X0 = 1 → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have gp := gkr_parts A.mem'.gkr
  refine pc_call h hpcl A.fr hpc A.cl hcs gp.2.2.2.2.2.2.2.2.1 gp.2.2.2.2.2.2.2.2.2 hj x0 x1 x2 x3
    x4 x5 fun m2 hfr2 hx2 hcl2 hk2 hcs2 hs2 ↦ cont m2 (A.transfer hfr2 ?_ ?_ ?_ hcl2) hx2
  · refine keepIv_call hS A.fr.sp le_pc (X := InRange m0.regs.X5.toBitVec claimsBytes)
      (NativeRustcVm.SameOutside.mono hs2 fun q hq ↦ hq.elim .inr .inl) (by decide)
      fun j hj hq ↦ ?_
    have := inIv_lt (B := 4176) (by decide) hj
    exact cl_not_loc h hq (o := j) (n := 1) (by omega) (NativeRustcVm.inRange_self (by omega))
  · exact regsEq_call hcs2 (by decide)
  · refine A.ts.frame hk2 (fun q hq ↦ ?_) hs2
    rcases hq with hq | hq
    · exact cl_not_tsw h hq
    · have := callee_apart h A.fr le_pc hq
      exact ⟨fun h' ↦ this.2.1 (.inl h'), this.1⟩

/-- `push_claim`'s check passed. -/
theorem okOne_bit {env : Env} {m : MachineData} (h0 : m.regs.X0 = 1)
    (he : env.regs .X0 = (m.regs.getXReg .X0).toBitVec) :
    SBool.eval env (.not (.bit .W32 (.reg .X0) 0)) = false := by
  show (!(low .W32 (env.regs .X0)).getLsbD 0) = false
  rw [he, show m.regs.getXReg .X0 = m.regs.X0 from rfl, h0]
  rfl

/-- `push_claim`'s check passed (`cbz w0`). -/
theorem okOne_eq {env : Env} {m : MachineData} (h0 : m.regs.X0 = 1)
    (he : env.regs .X0 = (m.regs.getXReg .X0).toBitVec) :
    SBool.eval env (.cmp .eq .W32 (.reg .X0) (.lit 0)) = false := by
  show CmpOp.eq.apply .W32 (env.regs .X0) (BitVec.ofNat 64 0) = false
  rw [he, show m.regs.getXReg .X0 = m.regs.X0 from rfl, h0]
  rfl

/-- **The claims pushed** (`b25`, `k + NativeRustcVmArm.Vm.VerifyBusBalance.b25Offset`, after the first). -/
theorem claimsC_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hpcl : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hbs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s)
      (BytecodeSharePost a s))
    (hcbv : Spec (Labels.label NativeRustcVmArm.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost)
    (hkp : Spec (Labels.label NativeRustcVmArm.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmArm.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    (hfc : Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    {w pt tv mem : Array EW} {beta mf bf : EW} {s3 : TState} {m : MachineData}
    (hrun : (verifyBusBalance L).run s0 =
      ((bytecodeShare w (pt.extract 0 L.logBytecode)).run s3).bind fun y4 ↦
        ((computedBytecodeValue L.bytecode y4.1.2.1 y4.1.2.2).run y4.2).bind fun y5 ↦
          some (resultOf L w beta pt tv mem mf bf y4.1.1 y4.1.2.1, y5.2))
    (A : ClSt L m0 w pt tv mem beta mf bf a s3
      #[⟨LeanVM.Protocol.Verifier.memory0, pt.extract 0 L.logMemory, mem.getD 0 0⟩] m)
    (hx0 : m.regs.X0 = 1) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b25Offset)⟩ := by
  have hS := pre_stack h
  have hlm := (pre_lay h).log_memory_le
  have hlb := (pre_lay h).log_bytecode_le
  have hm4 := A.msz
  -- `b25`
  refine Fr.runBlock hS N_ge rfl A.fr (b25_in_code.trans hp.1 (by simp [b25])) run_b25 rfl rfl
    (by decide) (by decide) fun st1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have A1 := A.block hfr1 hd1 (regsEq_block hm1 (by decide))
  -- `b26`
  refine at_pc ((pass_cond hpc1 (okOne_bit hx0 rfl)).trans
    (show Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b25Offset + b25.length) = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b26Offset) from rfl))
    (Fr.runBlock hS N_ge rfl hfr1 (b26_in_code.trans hp.1 (by simp [b26])) run_b26
      rfl rfl (by decide) (by decide) fun st2 hfr2 hd2 hm2 hpc2 ↦ ?_)
  have A2 := A1.block hfr2 hd2 (regsEq_block hm2 (by decide))
  have g1 := ew_get A1.hmem (i := 1) (by omega)
  simp only [PcOk] at hpc2
  refine A2.push h hpcl (by simp [claimCap]) hpc2 (j := L.logMemory) (id := 1)
    (v := mem.getD 1 0) hlm
    ((reg_of hm2 (r := .X0) (r' := .X28) rfl).trans A1.x28)
    (by rw [show st2.data.regs.X1 = st2.data.regs.getXReg .X1 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm2 (r := .X1) (n := 1) rfl]; rfl)
    ((reg_of hm2 (r := .X2) (r' := .X21) rfl).trans A1.x21)
    ((reg_of hm2 (r := .X3) (r' := .X27) rfl).trans A1.x27)
    (reg_ld (x := .X4) hm2 rfl g1.1) (reg_ld (x := .X5) hm2 rfl g1.2)
    fun m3 A3 hx3 ↦ ?_
  -- `b27`
  refine Fr.runBlock hS N_ge rfl A3.fr (b27_in_code.trans hp.1 (by simp [b27])) run_b27 rfl rfl
    (by decide) (by decide) fun st4 hfr4 hd4 hm4' hpc4 ↦ ?_
  have A4 := A3.block hfr4 hd4 (regsEq_block hm4' (by decide))
  -- `b28`
  refine at_pc ((pass_cond hpc4 (okOne_eq hx3 rfl)).trans
    (show Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b27Offset + b27.length) = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b28Offset) from rfl))
    (Fr.runBlock hS N_ge rfl hfr4 (b28_in_code.trans hp.1 (by simp [b28])) run_b28
      rfl rfl (by decide) (by decide) fun st5 hfr5 hd5 hm5 hpc5 ↦ ?_)
  have A5 := A4.block hfr5 hd5 (regsEq_block hm5 (by decide))
  simp only [PcOk] at hpc5
  refine A5.push h hpcl (by simp [claimCap]) hpc5 (j := L.logMemory) (id := 2) (v := mf) hlm
    ((reg_of hm5 (r := .X0) (r' := .X28) rfl).trans A4.x28)
    (by rw [show st5.data.regs.X1 = st5.data.regs.getXReg .X1 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm5 (r := .X1) (n := 2) rfl]; rfl)
    ((reg_of hm5 (r := .X2) (r' := .X21) rfl).trans A4.x21)
    ((reg_of hm5 (r := .X3) (r' := .X27) rfl).trans A4.x27)
    (reg_ld (x := .X4) hm5 rfl A4.w112) (reg_ld (x := .X5) hm5 rfl A4.w104)
    fun m6 A6 hx6 ↦ ?_
  -- `b29`
  refine Fr.runBlock hS N_ge rfl A6.fr (b29_in_code.trans hp.1 (by simp [b29])) run_b29 rfl rfl
    (by decide) (by decide) fun st7 hfr7 hd7 hm7 hpc7 ↦ ?_
  have A7 := A6.block hfr7 hd7 (regsEq_block hm7 (by decide))
  -- `b30`
  refine at_pc ((pass_cond hpc7 (okOne_eq hx6 rfl)).trans
    (show Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b29Offset + b29.length) = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b30Offset) from rfl))
    (Fr.runBlock hS N_ge rfl hfr7 (b30_in_code.trans hp.1 (by simp [b30])) run_b30
      rfl rfl (by decide) (by decide) fun st8 hfr8 hd8 hm8 hpc8 ↦ ?_)
  have A8 := A7.block hfr8 hd8 (regsEq_block hm8 (by decide))
  simp only [PcOk] at hpc8
  refine A8.push h hpcl (by simp [claimCap]) hpc8 (j := L.logBytecode) (id := 3) (v := bf) hlb
    ((reg_of hm8 (r := .X0) (r' := .X28) rfl).trans A7.x28)
    (by rw [show st8.data.regs.X1 = st8.data.regs.getXReg .X1 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm8 (r := .X1) (n := 3) rfl]; rfl)
    ((reg_of hm8 (r := .X2) (r' := .X21) rfl).trans A7.x21)
    (reg_ld (x := .X3) hm8 rfl A7.w120)
    (reg_ld (x := .X4) hm8 rfl A7.w96) (reg_ld (x := .X5) hm8 rfl A7.w88)
    fun m9 A9 hx9 ↦ ?_
  -- `b31`
  refine Fr.runBlock hS N_ge rfl A9.fr (b31_in_code.trans hp.1 (by simp [b31])) run_b31 rfl rfl
    (by decide) (by decide) fun st10 hfr10 hd10 hm10 hpc10 ↦ ?_
  have A10 := A9.block hfr10 hd10 (regsEq_block hm10 (by decide))
  have gp := gkr_parts A10.mem'.gkr
  have M := A10.mem'
  refine at_pc (pass_cond hpc10 (okOne_eq hx9 rfl)) (share_spec hp h hbs hcbv hkp hacc hext hfc
    { fr := A10.fr, run := hrun,
      mem' := ⟨M.push, M.pull, M.count, M.hw, M.wsz, gp.2.1, gp.2.2.1, gp.2.2.2.1,
        gp.2.2.2.2.1, gp.2.2.2.2.2.1, gp.2.2.2.2.2.2.1, gp.2.2.2.2.2.2.2.2.1,
        gp.2.2.2.2.2.2.2.2.2, A10.hmem, A10.msz, A10.w88, A10.w96, A10.w104, A10.w112, A10.w120,
        M.w128⟩,
      x19 := A10.x19, x20 := A10.x20,
      x21 := by rw [A10.x21], x22 := A10.x22, x23 := A10.x23, x24 := A10.x24,
      x25 := A10.x25, x26 := A10.x26, x27 := A10.x27, x29 := A10.x29, ts := A10.ts,
      cl := by
        have := A10.cl
        unfold claimsOf
        exact this })

end

end NativeRustcVmArm.Bus.VerifyBusBalance
