module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.Tail
public import NativeRustcVmArm.Bus.VerifyBusBalance.Acc

/-!
# `verify_bus_balance`'s count side

From `b44` (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b44Offset`), after the pull side: `b44` checks its total's tag; `b45` calls
`accumulate_side` on the count side (no fingerprints, the weights `&[ONE]`, `β = 0`); then the
tail (`count_spec`).
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- `&[ONE]` read as a slice. -/
theorem one_slice [Labels] {m : MachineData}
    (h : NativeRustcVm.BytesAt m.dmem (NativeRustcVmArm.rodataAddr .one)
      NativeRustcVm.Data.Item.one.bytes) :
    slice m (UInt64.ofBitVec (NativeRustcVmArm.rodataAddr .one)) 1 = #[1] :=
  slice_of_ewsAt (by
    show NativeRustcVm.EWsAt m.dmem (NativeRustcVmArm.rodataAddr .one) [⟨1, 0⟩]
    exact h) rfl

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The count side** (`b44`, `k + NativeRustcVmArm.Vm.VerifyBusBalance.b44Offset`). -/
theorem count_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmArm.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {w pt tv mem bp : Array EW} {beta mf bf share : EW} {s' : TState} {m : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m)
    (hr : (verifyBusBalance L).run s0 =
      some (resultOf L w beta pt tv mem mf bf share bp, s'))
    (hopt : OptEWAt m.dmem (loc m0 5320) (some (acc1 L w beta pt tv mem mf bf share).2))
    (hF : FormsAt m.dmem m0.regs.X4.toBitVec (acc1 L w beta pt tv mem mf bf share).1)
    (hfits : FitsUpTo (acc1 L w beta pt tv mem mf bf share).1 2)
    (hSL : BusLayoutWAt m.dmem (loc m0 1936) (countL L))
    (hpt : NativeRustcVm.EWsAt m.dmem (loc m0 3136) pt.toList) (hsz : pt.size ≤ 63)
    (w80 : NativeRustcVm.WordAt m.dmem (loc m0 80) (tv.getD 2 0).c0)
    (x23 : m.regs.getXReg .X23 = (tv.getD 2 0).c1)
    (x19 : m.regs.getXReg .X19 = m0.regs.X4) (x20 : m.regs.getXReg .X20 = m0.regs.X1)
    (x25 : (m.regs.getXReg .X25).toBitVec = loc m0 3136)
    (x26 : (m.regs.getXReg .X26).toNat = pt.size)
    (x28 : m.regs.getXReg .X28 = (acc0 L w beta pt tv mem share).2.c0)
    (x24 : m.regs.getXReg .X24 = (acc0 L w beta pt tv mem share).2.c1)
    (hts : TStateAt m.dmem m0.regs.X0.toBitVec a s')
    (hcl : ClaimsWAt m.dmem m0.regs.X5.toBitVec (claimsOf L pt mem mf bf)) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b44Offset)⟩ := by
  have hS := pre_stack h
  have hN := hS.2.1
  -- `b44`: the pull side's tag.
  refine Fr.runBlock hS N_ge rfl hfr (b44_in_code.trans hp.1 (by simp [b44])) run_b44 rfl rfl
    (by decide) (by decide) fun st1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have hl : (Env.ofMachine m [(base m0 5488, 5488)]).load 0 5320 4 = BitVec.ofNat 64 1 :=
    Transcript.load4_of_tag (w := 1) (.inr rfl) hopt.1
  have hc : SBool.eval (Env.ofMachine m [(base m0 5488, 5488)])
      (.not (.bit .W32 (.load 0 5320 4) 0)) = false := by
    show (!(low .W32 ((Env.ofMachine m [(base m0 5488, 5488)]).load 0 5320 4)).getLsbD 0) = false
    rw [hl]
    rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc1
  rw [← hd1] at hopt hF hSL hpt w80 hts hcl
  obtain ⟨t1a, t1b⟩ := NativeRustcVm.ewAt_iff.mp hopt.2
  -- `b45`: the count side's arguments.
  have hwf2 := Bus.wf_frame hS N_ge hfr1.kept
  have hm2 := Bus.match_frame hS N_ge rfl hfr1.sp
  refine exec_at (b45_in_code.trans hp.1 (by simp [b45])) run_b45 hwf2 hpc1 hm2
    fun st2 hm2' hpc2 ↦ ?_
  have hfr2 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st2.data :=
    Bus.Fr.block hfr1 hN N_ge hm2' hwf2 rfl (by decide) (by decide) slots_le
  have kb : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 5488 → 72 ≤ o →
      NativeRustcVm.BytesAt st1.data.dmem (loc m0 o) bs →
      NativeRustcVm.BytesAt st2.data.dmem (loc m0 o) bs := fun ho h72 hb ↦
    keep_out hm2' hwf2 (sizes := [5488]) rfl (lo := 0) (hi := 72) (by decide) ho (.inr h72) hb
  -- The registers and the stack arguments.
  have k19 : st1.data.regs.getXReg .X19 = m0.regs.X4 := (reg_of hm1 rfl).trans x19
  have k20 : st1.data.regs.getXReg .X20 = m0.regs.X1 := (reg_of hm1 rfl).trans x20
  have k23 : st1.data.regs.getXReg .X23 = (tv.getD 2 0).c1 := (reg_of hm1 rfl).trans x23
  have k25 : (st1.data.regs.getXReg .X25).toBitVec = loc m0 3136 := by
    rw [reg_of hm1 rfl]; exact x25
  have k26 : (st1.data.regs.getXReg .X26).toNat = pt.size := by rw [reg_of hm1 rfl]; exact x26
  have y0 : st2.data.regs.X0.toBitVec = loc m0 5344 := by
    rw [show st2.data.regs.X0 = st2.data.regs.getXReg .X0 from rfl, hm2'.regs .X0 _ rfl,
      eval_ptr_off rfl]; rfl
  have y1 : st2.data.regs.X1 = m0.regs.X4 :=
    (reg_of hm2' (r := .X1) (r' := .X19) rfl).trans k19
  have y2 : st2.data.regs.X2.toNat = 2 := by
    rw [show st2.data.regs.X2 = st2.data.regs.getXReg .X2 from rfl,
      ← UInt64.toNat_toBitVec, hm2'.regs .X2 _ rfl]; rfl
  have y3 : st2.data.regs.X3.toBitVec = NativeRustcVmArm.rodataAddr .countBlocks := by
    rw [show st2.data.regs.X3 = st2.data.regs.getXReg .X3 from rfl, hm2'.regs .X3 _ rfl]; rfl
  have y4 : st2.data.regs.X4.toNat = (sideBlocks 2).length := by
    rw [show st2.data.regs.X4 = st2.data.regs.getXReg .X4 from rfl,
      ← UInt64.toNat_toBitVec, hm2'.regs .X4 _ rfl]; rfl
  have y5 : st2.data.regs.X5 = m0.regs.X1 :=
    (reg_of hm2' (r := .X5) (r' := .X20) rfl).trans k20
  have y6 : st2.data.regs.X6.toBitVec = loc m0 1936 := by
    rw [show st2.data.regs.X6 = st2.data.regs.getXReg .X6 from rfl, hm2'.regs .X6 _ rfl,
      eval_ptr_off rfl]; rfl
  have y21 : st2.data.regs.getXReg .X21 = (acc1 L w beta pt tv mem mf bf share).2.c0 := by
    refine UInt64.toBitVec_inj.mp ((hm2'.regs .X21 _ rfl).trans
      (Transcript.load_ofMachine (b := base m0 5488) (n := 5488) (o := 5328) rfl ?_))
    simpa only [off, NativeRustcVm.addr_add_add] using t1a
  have y22 : st2.data.regs.getXReg .X22 = (acc1 L w beta pt tv mem mf bf share).2.c1 := by
    refine UInt64.toBitVec_inj.mp ((hm2'.regs .X22 _ rfl).trans
      (Transcript.load_ofMachine (b := base m0 5488) (n := 5488) (o := 5336) rfl ?_))
    simpa only [off, NativeRustcVm.addr_add_add] using t1b
  have sa : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5488 →
      (∀ i < 8, findWrite 0 (o + i) _ = some (v, i)) →
      stackArg st2.data o =
        UInt64.ofBitVec (v.eval (Env.ofMachine st1.data [(base m0 5488, 5488)])) :=
    fun ho hw ↦ stackArg_of hfr2.sp (frame_write hm2' ho hw)
  have s0' : stackArg st2.data 0 = 0 := sa (o := 0) (v := .lit 0) (by omega) (by decide)
  have s8 : stackArg st2.data 8 = UInt64.ofBitVec (NativeRustcVmArm.rodataAddr .one) :=
    sa (o := 8) (v := .label NativeRustcVmArm.Vm.Symbols.rodata9Label) (by omega) (by decide)
  have s16 : stackArg st2.data 16 = 1 := sa (o := 16) (v := .lit 1) (by omega) (by decide)
  have s24 : stackArg st2.data 24 = 0 := sa (o := 24) (v := .lit 0) (by omega) (by decide)
  have s32 : stackArg st2.data 32 = 0 := sa (o := 32) (v := .lit 0) (by omega) (by decide)
  have s40 : stackArg st2.data 40 = UInt64.ofBitVec (loc m0 3136) := by
    rw [sa (o := 40) (v := .reg .X25) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [k25]
  have s48 : (stackArg st2.data 48).toNat = pt.size := by
    rw [sa (o := 48) (v := .reg .X26) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    exact k26
  have s56 : stackArg st2.data 56 = (tv.getD 2 0).c0 := by
    rw [sa (o := 56) (v := .load 0 80 8) (by omega) (by decide)]
    simp only [Sym.eval]
    rw [Transcript.load_ofMachine (b := base m0 5488) (n := 5488) rfl w80]
  have s64 : stackArg st2.data 64 = (tv.getD 2 0).c1 := by
    rw [sa (o := 64) (v := .reg .X23) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [k23]
  -- The values the call reads.
  have hpt2 := kb (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; omega) (by omega) hpt
  have hone := (ro_ok h hfr2 le_acc .one).1
  obtain ⟨rows, -, -, -, hbb⟩ := (pre_lay h).rows
  have hbnw := (pre_bus h).2.1
  simp only [PcOk] at hpc2
  refine acc_call h hacc hfr2 hpc2 (side := 2) (by decide) (it := .countBlocks) rfl
    (o := 5344) (ol := 1936) (by omega) (by omega)
    (BusLayoutWAt.of_same hSL (same_out hm2' hwf2 (sizes := [5488]) rfl (lo := 0) (hi := 72)
      (by decide) (by rw [busLayoutBytes_eq]; omega) (.inr (by omega)))) (tables_size hbb #[] 2)
    (FormsAt.of_same hF (Same.of_sameOutside (hm2'.sameOutside hwf2) fun j hj hq ↦ ?_))
    hfits y0 y1 y2 y3 y4 y5 y6 (by omega) (fun hn ↦ by rw [s0'] at hn; cases hn)
    (fun hn ↦ by rw [s0'] at hn; cases hn) ?_
    (by rw [s40]) (by rw [s48]; exact hsz)
    (fps := #[]) (w := #[1]) (beta := 0) (pt := pt) (tree := tv.getD 2 0)
    (by rw [s0']; rfl) (by rw [s8, s16]; exact one_slice hone)
    (by rw [s24, s32]; rfl) (slice_of_ewsAt (by rw [s40]; exact hpt2) s48)
    (by rw [s56, s64]) fun m3 hfr3 hopt3 hF3 _ hk3 hcs3 hs3 ↦ ?_
  · have hq' := written_loc (m0 := m0) (by decide) hq (by have := N_ge; omega)
    rw [busPointOff_eq] at hj
    exact bus_not_loc h (bus_sub hbnw (o := 0) (n := 106704) (by rw [busBytes_eq]; omega)
      (by rw [Bus.add_zero']; exact NativeRustcVm.inRange_add hj (by omega)))
      (o := 0) (n := 5488) le_rfl hq'
  · rw [s8, s16]
    obtain ⟨-, hin, hap⟩ := ro_ok h hfr2 le_acc .one
    exact ⟨hin, NativeRustcVm.Apart.mono hap (Nat.le_refl _)
      (by have : formsBytes ≤ busBytes := (by decide); omega) (Nat.le_refl _)
      (Nat.le_refl _)⟩
  · -- After the call: the tail.
    have e2 : sideOf L 2 = L.count := rfl
    rw [e2] at hopt3 hF3
    have hk2 : Kept st1.data.dmem st2.data.dmem := fun p hp ↦ hm2'.kept hwf2 p hp
    have hs2 : SameOutside st1.data.dmem st2.data.dmem (InRange (loc m0 0) 5488) :=
      NativeRustcVm.SameOutside.mono (hm2'.sameOutside hwf2) fun q hq ↦
        written_loc (m0 := m0) (by decide) hq (by have := N_ge; omega)
    have hcallee : ∀ q, InRange (stackBelow st2.data accumulateSideStack) accumulateSideStack q →
        ¬InRange a.words (8 * a.len) q ∧ ¬outs m0 q ∧ ¬InRange (base m0 5488) 5488 q :=
      fun q hq ↦ callee_apart h hfr2 le_acc hq
    have hbusF : ∀ q, InRange m0.regs.X4.toBitVec formsBytes q →
        InRange m0.regs.X4.toBitVec busBytes q :=
      fun q hq ↦ forms_sub hbnw hq
    have hts3 : TStateAt m3.dmem m0.regs.X0.toBitVec a s' := by
      refine (hts.frame hk2 (fun q hq ↦ loc_not_tsw h (le_refl _) hq) hs2).frame hk3
        (fun q hq ↦ ?_) hs3
      rcases hq with hq | hq | hq
      · exact ⟨fun h' ↦ (hcallee q hq).2.1 (.inl h'), (hcallee q hq).1⟩
      · exact loc_not_tsw h (by omega) hq
      · exact bus_not_tsw h (hbusF q hq)
    have hcl3 : ClaimsWAt m3.dmem m0.regs.X5.toBitVec (claimsOf L pt mem mf bf) := by
      refine NativeRustcVm.Tables.ClaimsWAt.of_same hcl (Same.of_sameOutside
        (NativeRustcVm.SameOutside.trans hs2 hs3) fun j hj hq ↦ ?_)
      have hc := (pre_cl h).2.1
      have hin : InRange m0.regs.X5.toBitVec claimsBytes
          (m0.regs.X5.toBitVec + BitVec.ofNat 64 j) :=
        NativeRustcVm.inRange_add hj (by unfold NoWrap at hc; rw [claimsBytes_eq] at hc hj ⊢; omega)
      rcases hq with hq | hq | hq | hq
      · exact cl_not_loc h hin (o := 0) (n := 5488) le_rfl hq
      · exact (hcallee _ hq).2.1 (.inr (.inr hin))
      · exact cl_not_loc h hin (by omega) hq
      · exact bus_not_cl h (hbusF _ hq) hin
    have hpt3 : NativeRustcVm.EWsAt m3.dmem (loc m0 3136) pt.toList := by
      refine keep_loc hS hfr2.sp le_acc hs3
        (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; omega) (fun q hq ↦ ?_) hpt2
      rcases hq with hq | hq
      · exact loc_apart hS (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; omega)
          (by omega) (.inl (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; omega)) q hq
      · exact bus_not_loc h (hbusF q hq)
          (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; omega)
    exact tail_spec hp h hext hfr3 hr rfl
      ((hcs3 .X19 rfl).trans ((reg_of hm2' rfl).trans k19))
      (by rw [hcs3 .X25 rfl, reg_of hm2' rfl]; exact k25)
      (by rw [hcs3 .X26 rfl, reg_of hm2' rfl]; exact k26) hsz
      ((hcs3 .X28 rfl).trans ((reg_of hm2' rfl).trans ((reg_of hm1 rfl).trans x28)))
      ((hcs3 .X24 rfl).trans ((reg_of hm2' rfl).trans ((reg_of hm1 rfl).trans x24)))
      ((hcs3 .X21 rfl).trans y21) ((hcs3 .X22 rfl).trans y22) hpt3 hopt3 hF3 hts3 hcl3

end

end NativeRustcVmArm.Bus.VerifyBusBalance
