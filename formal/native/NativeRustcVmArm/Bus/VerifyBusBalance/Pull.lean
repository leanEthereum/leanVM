module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.Count
public import NativeRustcVmArm.Bus.VerifyBusBalance.Locs

/-!
# `verify_bus_balance`'s pull side

From `b41` (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b41Offset`), after the push side: `b41` checks its total's tag; `b42` calls the
closure for the pull side's fingerprints (`pc_final`, the final counters); `b43` calls
`accumulate_side` on the pull side; then the count side (`pull_spec`).
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section
variable [Labels]

/-- **At `b41`** (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b41Offset`): the push side's total at `5320`, its forms at the bus. -/
structure AtPull (a : DecArea) (s0 : TState) (L : LayoutW) (m0 : MachineData)
    (w pt tv mem : Array EW) (beta mf bf share : EW) (bp : Array EW) (s' : TState)
    (m : MachineData) : Prop where
  fr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m
  run : (verifyBusBalance L).run s0 = some (resultOf L w beta pt tv mem mf bf share bp, s')
  locs : Locs m0 L w pt tv mem beta mf bf share m.dmem
  opt : OptEWAt m.dmem (loc m0 5320) (some (acc0 L w beta pt tv mem share).2)
  forms : FormsAt m.dmem m0.regs.X4.toBitVec (acc0 L w beta pt tv mem share).1
  fits : FitsUpTo (acc0 L w beta pt tv mem share).1 1
  x19 : m.regs.getXReg .X19 = m0.regs.X4
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : (m.regs.getXReg .X21).toBitVec = loc m0 2824
  x22 : m.regs.getXReg .X22 = beta.c1
  x23 : m.regs.getXReg .X23 = (tv.getD 2 0).c1
  x25 : (m.regs.getXReg .X25).toBitVec = loc m0 3136
  x26 : (m.regs.getXReg .X26).toNat = pt.size
  x27 : m.regs.getXReg .X27 = (tv.getD 1 0).c0
  x29 : m.regs.getXReg .X29 = (tv.getD 1 0).c1
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s'
  cl : ClaimsWAt m.dmem m0.regs.X5.toBitVec (claimsOf L pt mem mf bf)

omit [Labels] in
/-- The fingerprints' count. -/
theorem fingerprints_length (w mem ml bl : Array EW) (share pc mc bc : EW) :
    (fingerprints w mem ml bl share pc mc bc).toList.length = 3 := rfl

/-- A byte of the bus is not the stack's. -/
theorem bus_not_stack {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}
    (h : VerifyBusBalancePre a s0 L m0) {q : BitVec 64}
    (hq : InRange m0.regs.X4.toBitVec busBytes q) :
    ¬InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack q :=
  fun h' ↦ NativeRustcVm.Apart.not_inRange (pre_bus h).2.2.2.2.1 (pre_bus h).2.1
    (Bus.stack_noWrap (pre_stack h)) hq h'

omit [Labels] in
/-- **A callee's changes from the frame** are in the stack. -/
theorem callee_stack {m0 m : MachineData} (hS : StackOk m0 verifyBusBalanceStack)
    (hsp : m.regs.SP.toBitVec = base m0 5488) {N' : Nat} (hle : 5488 + N' ≤ verifyBusBalanceStack)
    {q : BitVec 64} (hq : InRange (stackBelow m N') N' q) :
    InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack q :=
  Bus.inRange_callee hS.2.1 hsp hle hq

omit [Labels] in
/-- A local of the frame is in the stack. -/
theorem loc_stack {m0 : MachineData} (hS : StackOk m0 verifyBusBalanceStack) {o n : Nat}
    (hon : o + n ≤ 5488) {q : BitVec 64} (hq : InRange (loc m0 o) n q) :
    InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack q :=
  Bus.inRange_local hS.2.1 N_ge hon hq

/-- A block's writes in the frame are in the stack. -/
theorem written_stack {m0 m : MachineData} {S : SState}
    (hS : StackOk m0 verifyBusBalanceStack)
    (hw : (S.mem.all fun w ↦ w.r == 0 && decide (0 ≤ w.off) && decide (w.off + w.n ≤ 5488)) = true)
    {q : BitVec 64} (hq : Written (Env.ofMachine m [(base m0 5488, 5488)]) S q) :
    InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack q :=
  loc_stack hS (o := 0) (n := 5488) le_rfl
    (written_loc hw hq (by have := N_ge; have := hS.2.1; omega))

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The pull side** (`b41`, `k + NativeRustcVmArm.Vm.VerifyBusBalance.b41Offset`). -/
theorem pull_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmArm.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    (hfc : Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    {w pt tv mem bp : Array EW} {beta mf bf share : EW} {s' : TState} {m : MachineData}
    (A : AtPull a s0 L m0 w pt tv mem beta mf bf share bp s' m) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b41Offset)⟩ := by
  have hS := pre_stack h
  have hN := hS.2.1
  have hbnw := (pre_bus h).2.1
  -- `b41`: the push side's tag.
  refine Fr.runBlock hS N_ge rfl A.fr (b41_in_code.trans hp.1 (by simp [b41])) run_b41 rfl rfl
    (by decide) (by decide) fun st1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have hc : SBool.eval (Env.ofMachine m [(base m0 5488, 5488)])
      (.cmp .eq .W64 (.load 0 5320 8) (.lit 0)) = false := by
    show CmpOp.eq.apply .W64 ((Sym.load 0 5320 8).eval (Env.ofMachine m [(base m0 5488, 5488)]))
      (BitVec.ofNat 64 0) = false
    rw [show (Sym.load 0 5320 8).eval (Env.ofMachine m [(base m0 5488, 5488)]) =
      (1 : UInt64).toBitVec from Transcript.load_ofMachine rfl A.opt.1]
    rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b42`: the closure's arguments.
  have hwf2 := Bus.wf_frame hS N_ge hfr1.kept
  have hm2 := Bus.match_frame hS N_ge rfl hfr1.sp
  refine exec_at (b42_in_code.trans hp.1 (by simp [b42])) run_b42 hwf2 hpc1 hm2
    fun st2 hm2' hpc2 ↦ ?_
  have hd2 : st2.data.dmem = st1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hfr2 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st2.data :=
    Bus.Fr.block hfr1 hN N_ge hm2' hwf2 rfl (by decide) (by decide) slots_le
  have hl1 : Locs m0 L w pt tv mem beta mf bf share st1.data.dmem :=
    A.locs.of_keep (KeepLoc.rfl' hd1)
  have hl2 : Locs m0 L w pt tv mem beta mf bf share st2.data.dmem := hl1.of_keep (KeepLoc.rfl' hd2)
  obtain ⟨t1a, t1b⟩ := NativeRustcVm.ewAt_iff.mp A.opt.2
  have r2 : st2.data.regs.X2 = gpowK (2 ^ L.logBytecode - 1) := reg_ld (x := .X2) hm2' rfl hl1.w120
  have r3 : st2.data.regs.X3 = mf.c0 := reg_ld (x := .X3) hm2' rfl hl1.w112
  have r4 : st2.data.regs.X4 = mf.c1 := reg_ld (x := .X4) hm2' rfl hl1.w104
  have r5 : st2.data.regs.X5 = bf.c0 := reg_ld (x := .X5) hm2' rfl hl1.w96
  have r6 : st2.data.regs.X6 = bf.c1 := reg_ld (x := .X6) hm2' rfl hl1.w88
  have r28 : st2.data.regs.getXReg .X28 = (acc0 L w beta pt tv mem share).2.c0 :=
    reg_ld hm2' (o := 5328) rfl
      (by rw [hd1]; simpa only [off, NativeRustcVm.addr_add_add] using t1a)
  have r24 : st2.data.regs.getXReg .X24 = (acc0 L w beta pt tv mem share).2.c1 :=
    reg_ld hm2' (o := 5336) rfl
      (by rw [hd1]; simpa only [off, NativeRustcVm.addr_add_add] using t1b)
  have k2 : ∀ r, r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X26, .X27, .X29] →
      st2.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (reg_of hm2' rfl).trans (reg_of hm1 rfl)
  simp only [PcOk] at hpc2
  refine fp_call h hfc hfr2 hpc2 hl2 (reg_ptr (x := .X0) 5344 hm2' rfl)
    (reg_ptr (x := .X1) 5264 hm2' rfl) fun m3 hfr3 hfp3 hk3 hcs3 hs3 ↦ ?_
  rw [r2, r3, r4, r5, r6] at hfp3
  have hpc3 : Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b41Offset + b41.length + b42.length) = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b43Offset) := rfl
  -- what the closure kept
  have kl3 : KeepLoc m0 st2.data.dmem m3.dmem :=
    keepLoc_call hS hfr2.sp le_fp hs3 (not_locs hS (o := 5344) (n := 48) (by omega)
      fun j hj ↦ by unfold InLocs at hj; omega)
  have hl3 := hl2.of_keep kl3
  have stk3 : ∀ q, (InRange (stackBelow st2.data fpClosureStack) fpClosureStack q ∨
      InRange (loc m0 5344) 48 q) →
      InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack q := fun q hq ↦
    hq.elim (fun hq ↦ callee_stack hS hfr2.sp le_fp hq) fun hq ↦ loc_stack hS (by omega) hq
  have tc3 := keep_tc h hk3 hs3 (fun q hq ↦ .inl (stk3 q hq))
    (by rw [hd2, hd1]; exact A.ts) (by rw [hd2, hd1]; exact A.cl)
  -- `b43`: the pull side's arguments.
  have hwf4 := Bus.wf_frame hS N_ge hfr3.kept
  have hm4 := Bus.match_frame hS N_ge rfl hfr3.sp
  refine exec_at (b43_in_code.trans hp.1 (by simp [b43])) run_b43 hwf4 hpc3 hm4
    fun st4 hm4' hpc4 ↦ ?_
  have hfr4 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st4.data :=
    Bus.Fr.block hfr3 hN N_ge hm4' hwf4 rfl (by decide) (by decide) slots_le
  have kl4 : KeepLoc m0 m3.dmem st4.data.dmem :=
    keepLoc_block hm4' hwf4 (sizes := [5488]) rfl (lo := 0) (hi := 72) (by decide)
      fun j hj ↦ by unfold InLocs at hj; omega
  have hl4 := hl3.of_keep kl4
  have hs4 : SameOutside m3.dmem st4.data.dmem
      (InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack) :=
    NativeRustcVm.SameOutside.mono (hm4'.sameOutside hwf4) fun q hq ↦
      written_stack hS (by decide) hq
  have kfp : NativeRustcVm.EWsAt st4.data.dmem (loc m0 5344)
      (fingerprints w mem (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share
        (gpow (2 ^ L.logBytecode - 1)) mf bf).toList :=
    keep_out hm4' hwf4 (sizes := [5488]) rfl (lo := 0) (hi := 72) (by decide)
      (by rw [NativeRustcVm.length_ewsBytes, fingerprints_length]; omega) (.inr (by omega)) hfp3
  -- registers
  have g : ∀ r, r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X26, .X27, .X29] →
      m3.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
    have hr' : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hcs3 r hr']
    exact k2 r hr
  have g19 := g .X19 (by simp)
  have g20 := g .X20 (by simp)
  have g21 := g .X21 (by simp)
  have g22 := g .X22 (by simp)
  have g23 := g .X23 (by simp)
  have g25 := g .X25 (by simp)
  have g26 := g .X26 (by simp)
  have g27 := g .X27 (by simp)
  have g29 := g .X29 (by simp)
  have y1 : st4.data.regs.X1 = m0.regs.X4 := (reg_of hm4' (r := .X1) (r' := .X19) rfl).trans
    (g19.trans A.x19)
  have y2 : st4.data.regs.X2.toNat = 1 := by
    rw [show st4.data.regs.X2 = st4.data.regs.getXReg .X2 from rfl,
      ← UInt64.toNat_toBitVec, hm4'.regs .X2 _ rfl]; rfl
  have y3 : st4.data.regs.X3.toBitVec = NativeRustcVmArm.rodataAddr .pullBlocks := by
    rw [show st4.data.regs.X3 = st4.data.regs.getXReg .X3 from rfl, hm4'.regs .X3 _ rfl]; rfl
  have y4 : st4.data.regs.X4.toNat = (sideBlocks 1).length := by
    rw [show st4.data.regs.X4 = st4.data.regs.getXReg .X4 from rfl,
      ← UInt64.toNat_toBitVec, hm4'.regs .X4 _ rfl]; rfl
  have y5 : st4.data.regs.X5 = m0.regs.X1 := (reg_of hm4' (r := .X5) (r' := .X20) rfl).trans
    (g20.trans A.x20)
  have y7 : st4.data.regs.X7.toBitVec = loc m0 5344 := reg_ptr (x := .X7) 5344 hm4' rfl
  have sa : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5488 →
      (∀ i < 8, findWrite 0 (o + i) _ = some (v, i)) →
      stackArg st4.data o = UInt64.ofBitVec (v.eval (Env.ofMachine m3 [(base m0 5488, 5488)])) :=
    fun ho hw ↦ stackArg_write hm4' hfr4.sp ho hw
  have s0' : stackArg st4.data 0 = 3 := sa (o := 0) (v := .lit 3) (by omega) (by decide)
  have s8 : stackArg st4.data 8 = UInt64.ofBitVec (loc m0 2824) := by
    rw [sa (o := 8) (v := .reg .X21) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [g21, A.x21]
  have s16 : stackArg st4.data 16 = 16 := sa (o := 16) (v := .lit 16) (by omega) (by decide)
  have s24 : stackArg st4.data 24 = beta.c0 := by
    rw [sa (o := 24) (v := .load 0 128 8) (by omega) (by decide)]
    simp only [Sym.eval]
    rw [Transcript.load_ofMachine (b := base m0 5488) (n := 5488) rfl hl3.w128]
  have s32 : stackArg st4.data 32 = beta.c1 := by
    rw [sa (o := 32) (v := .reg .X22) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [g22, A.x22]
  have s40 : stackArg st4.data 40 = UInt64.ofBitVec (loc m0 3136) := by
    rw [sa (o := 40) (v := .reg .X25) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [g25, A.x25]
  have s48 : (stackArg st4.data 48).toNat = pt.size := by
    rw [sa (o := 48) (v := .reg .X26) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [g26]; exact A.x26
  have s56 : stackArg st4.data 56 = (tv.getD 1 0).c0 := by
    rw [sa (o := 56) (v := .reg .X27) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [g27, A.x27]
  have s64 : stackArg st4.data 64 = (tv.getD 1 0).c1 := by
    rw [sa (o := 64) (v := .reg .X29) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [g29, A.x29]
  -- what the call reads
  obtain ⟨rows, -, -, -, hbb⟩ := (pre_lay h).rows
  have hpsz := hl4.psz
  have hfb : formsBytes ≤ busBytes := by decide
  have hF4 : FormsAt st4.data.dmem m0.regs.X4.toBitVec (acc0 L w beta pt tv mem share).1 := by
    have hnot : ∀ j < busPointOff, ¬InRange (stackBelow m0 verifyBusBalanceStack)
        verifyBusBalanceStack (m0.regs.X4.toBitVec + BitVec.ofNat 64 j) := fun j hj ↦
      bus_not_stack h (bus_sub hbnw (o := 0) (n := busPointOff) (by decide)
        (by rw [Bus.add_zero']; exact NativeRustcVm.inRange_add hj (by rw [busPointOff_eq]; omega)))
    refine FormsAt.of_same (FormsAt.of_same (by rw [hd2, hd1]; exact A.forms)
      (Same.of_sameOutside hs3 fun j hj hq ↦ hnot j hj (stk3 _ hq)))
      (Same.of_sameOutside hs4 fun j hj hq ↦ hnot j hj hq)
  simp only [PcOk] at hpc4
  refine acc_call h hacc hfr4 hpc4 (side := 1) (by decide) (it := .pullBlocks) rfl
    (o := 5320) (ol := 1048) (by omega) (by omega) hl4.pull
    (tables_size hbb (fwRows L) 1) hF4 A.fits (reg_ptr (x := .X0) 5320 hm4' rfl) y1 y2 y3 y4 y5
    (reg_ptr (x := .X6) 1048 hm4' rfl) (by omega)
    (fun _ ↦ by
      rw [s0', y7, show (3 : UInt64).toNat = 3 from rfl]
      exact ⟨loc_inOk h hfr4 le_acc (by omega), bus_apart h hfb (by omega)⟩)
    (fun _ ↦ by
      rw [s0', y7, busLayoutBytes_eq, show (3 : UInt64).toNat = 3 from rfl]
      exact loc_apart' hS (by omega) (by omega) (.inl (by omega)))
    (by
      rw [s8, s16, show (16 : UInt64).toNat = 16 from rfl]
      refine ⟨?_, ?_⟩
      · unfold SliceOk
        rw [UInt64.toBitVec_ofBitVec, show (16 : UInt64).toNat = 16 from rfl]
        exact loc_inOk h hfr4 le_acc (by omega)
      · rw [UInt64.toBitVec_ofBitVec]; exact bus_apart h hfb (by omega))
    (by rw [s40]) (by rw [s48]; exact hpsz)
    (fps := fingerprints w mem (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share
      (gpow (2 ^ L.logBytecode - 1)) mf bf) (w := w) (beta := beta) (pt := pt)
    (tree := tv.getD 1 0)
    (by
      rw [s0', y7]
      have := NativeRustcVm.ewsOf_of_ewsAt kfp
      rw [fingerprints_length] at this
      rw [show (3 : UInt64).toNat = 3 from rfl, this])
    (slice_of_ewsAt (by rw [s8, UInt64.toBitVec_ofBitVec]; exact hl4.hw)
      (by rw [s16]; exact hl4.wsz.symm))
    (by rw [s24, s32])
    (slice_of_ewsAt (by rw [s40, UInt64.toBitVec_ofBitVec]; exact hl4.hpt) s48)
    (by rw [s56, s64]) fun m5 hfr5 hopt5 hF5 hfits5 hk5 hcs5 hs5 ↦ ?_
  -- after the call: the count side
  have kl5 : KeepLoc m0 st4.data.dmem m5.dmem :=
    keepLoc_call hS hfr4.sp le_acc hs5 fun j hj hq ↦ by
      rcases hq with hq | hq
      · exact not_locs hS (o := 5320) (n := 24) (by omega)
          (fun j hj ↦ by unfold InLocs at hj; omega) j hj hq
      · exact bus_not_loc h (forms_sub hbnw hq) (o := j) (n := 1)
          (by unfold InLocs at hj; omega) (NativeRustcVm.inRange_self (by omega))
  have hl5 := hl4.of_keep kl5
  have tc4 := keep_tc h (hm4'.kept hwf4) hs4 (fun q hq ↦ .inl hq) tc3.1 tc3.2
  have htc := keep_tc h hk5 hs5 (fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact .inl (callee_stack hS hfr4.sp le_acc hq)
    · exact .inl (loc_stack hS (by omega) hq)
    · exact .inr (forms_sub hbnw hq)) tc4.1 tc4.2
  exact count_spec hp h hacc hext hfr5 A.run hopt5 hF5 hfits5 hl5.count hl5.hpt hpsz hl5.w80
    ((hcs5 .X23 rfl).trans ((reg_of hm4' rfl).trans (g23.trans A.x23)))
    ((hcs5 .X19 rfl).trans ((reg_of hm4' rfl).trans (g19.trans A.x19)))
    ((hcs5 .X20 rfl).trans ((reg_of hm4' rfl).trans (g20.trans A.x20)))
    (by rw [hcs5 .X25 rfl, reg_of hm4' rfl, g25]; exact A.x25)
    (by rw [hcs5 .X26 rfl, reg_of hm4' rfl, g26]; exact A.x26)
    ((hcs5 .X28 rfl).trans ((reg_of hm4' rfl).trans ((hcs3 .X28 rfl).trans r28)))
    ((hcs5 .X24 rfl).trans ((reg_of hm4' rfl).trans ((hcs3 .X24 rfl).trans r24)))
    htc.1 htc.2

end

end NativeRustcVmArm.Bus.VerifyBusBalance
