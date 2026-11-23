module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Code.Vm.BytecodeShare.Names
public import NativeRustcVmArm.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmArm.Code.Vm.Kpow.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.SharePre

/-!
# `verify_bus_balance`'s bytecode share

From `b32` (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b32Offset`), after the claims: `b32` empties the bytecode point and calls
`bytecode_share`; `b33` checks its tag; `b34` keeps the share at `5248` and checks the point's
length (`< 68`); `b35` calls `computed_bytecode_value`; `b36` checks it; then the push side
(`share_spec`).
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The bytecode share** (`b32`, `k + NativeRustcVmArm.Vm.VerifyBusBalance.b32Offset`). -/
theorem share_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
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
    (A : AtShare a s0 L m0 w pt tv mem beta mf bf s3 m) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b32Offset)⟩ := by
  have hS := pre_stack h
  have hN := hS.2.1
  have c := ctx h
  have hpsz := A.mem'.psz
  have hlb := (pre_lay h).log_bytecode_le
  have n4 : (min L.logBytecode pt.size).toUInt64.toNat = min L.logBytecode pt.size :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  -- `b32`: the bytecode point emptied; `bytecode_share`.
  have hwf1 := Bus.wf_frame hS N_ge A.fr.kept
  have hm1 := Bus.match_frame hS N_ge rfl A.fr.sp
  refine exec_then (b32_in_code.trans hp.1 (by simp [b32])) run_b32 hwf1 hm1
    fun st1 hm1' hpc1 ↦ ?_
  have hfr1 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st1.data :=
    Bus.Fr.block A.fr hN N_ge hm1' hwf1 rfl (by decide +kernel) (by decide) slots_le
  have ks1 : KeepIv shareIv m0 m.dmem st1.data.dmem :=
    keepIv_block hm1' hwf1 (sizes := [5488]) rfl (by decide) (by decide +kernel)
  have sm1 := A.mem'.of_keep ks1
  have tc1 := keep_tc h (hm1'.kept hwf1) (hm1'.sameOutside hwf1)
    (fun q hq ↦ .inl (written_stack hS (by decide) hq)) A.ts A.cl
  have hat1 := Fr.at_ c hfr1 (outs_not_rc h)
  have R1 : RegsEq [.X19, .X20, .X21, .X22, .X23, .X24, .X26, .X27, .X29] m st1.data :=
    regsEq_block hm1' (by decide)
  have z25 : (st1.data.regs.getXReg .X25).toBitVec = loc m0 3136 := by
    rw [reg_of hm1' (r := .X25) (r' := .X21) rfl]; exact A.x21
  have y0 : st1.data.regs.X0.toBitVec = loc m0 5264 := reg_ptr (x := .X0) 5264 hm1' rfl
  have y1 : st1.data.regs.X1 = m0.regs.X0 := (reg_of hm1' (r := .X1) (r' := .X25) rfl).trans A.x25
  have y2 : st1.data.regs.X2.toBitVec = loc m0 2824 := reg_ptr (x := .X2) 2824 hm1' rfl
  have y3 : st1.data.regs.X3 = UInt64.ofBitVec (loc m0 3136) := by
    apply UInt64.toBitVec_inj.mp
    rw [show st1.data.regs.X3 = st1.data.regs.getXReg .X3 from rfl,
      reg_of hm1' (r := .X3) (r' := .X21) rfl, A.x21]
  have y4 : st1.data.regs.X4 = (min L.logBytecode pt.size).toUInt64 :=
    reg_ld (x := .X4) hm1' rfl A.mem'.w120
  have y5 : st1.data.regs.X5.toBitVec = loc m0 4176 := reg_ptr (x := .X5) 4176 hm1' rfl
  have hpb : 16 * sharePointSlots = 1072 := rfl
  have hpre : BytecodeSharePre a s3 st1.data := by
    unfold BytecodeSharePre
    rw [y0, y1, y2, y3, y4, y5, n4, UInt64.toBitVec_ofBitVec, hpb]
    refine ⟨hfr1.stackOk hS rfl le_share, c.rcAt hat1 le_share, tc1.1, c.tstateOk hat1 le_share,
      loc_inOk h hfr1 le_share (by omega), by unfold busPointCap; omega,
      loc_inOk h hfr1 le_share (by omega), c.outOk hat1 le_share (o := 5264) (n := 48) (by omega),
      c.outOk hat1 le_share (o := 4176) (n := 1072) (by omega),
      loc_apart' hS (by omega) (by omega) (.inr (by omega)),
      loc_apart' hS (by omega) (by omega) (.inr (by omega)),
      c.apart_of_stack (o := 2824) (k := 256) (by omega) c.tok.1,
      c.apart_of_stack (o := 3136) (by omega) c.tok.1⟩
  simp only [PcOk] at hpc1
  refine Fr.callLocal (o := 4176) (n := 1136)
    (X := fun q ↦ InRange (loc m0 5264) 48 q ∨ InRange (loc m0 4176) 1072 q ∨
      InRange m0.regs.X0.toBitVec tstateBytes q)
    hfr1 hN le_share keep_callee (slots_lo (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (loc_mono hS (by omega) (by omega) (by omega) hq)
      · exact .inr (loc_mono hS (by omega) (by omega) (by omega) hq)
      · exact .inl (.inl hq))
    (hbs a s3) hpc1 hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [y0, y5, y1, hpb] at hq'
      rcases hq' with hq' | hq' | hq' | hq'
      · exact .inr (.inl hq')
      · exact .inr (.inr (.inl hq'))
      · exact .inr (.inr (.inr hq'))
      · exact .inl hq', hq.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  have hW : (NativeRustcVm.ewsOf st1.data.dmem st1.data.regs.X2.toBitVec 16).toArray = w := by
    rw [y2]
    have := NativeRustcVm.ewsOf_of_ewsAt sm1.hw
    rw [Array.length_toList, sm1.wsz] at this
    rw [this]
  have hP : slice st1.data st1.data.regs.X3 st1.data.regs.X4 = pt.extract 0 L.logBytecode := by
    rw [y3, y4]; exact slice_prefix sm1.hpt hpsz _
  dsimp only [BytecodeSharePost] at hq2
  rw [hW, hP, y0, y5, y1, UInt64.toBitVec_ofBitVec] at hq2
  obtain ⟨hopt, hres, -, -⟩ := hq2
  -- what the call kept
  have stk2 : ∀ q, InRange (stackBelow st1.data bytecodeShareStack) bytecodeShareStack q →
      InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack q := fun q hq ↦
    callee_stack hS hfr1.sp le_share hq
  have ks2 : KeepIv shareIv m0 st1.data.dmem m2.dmem :=
    keepIv_call hS hfr1.sp le_share hs2 (by decide) fun j hj hq ↦ by
      have hj5 := inIv_lt (B := 4176) (by decide) hj
      rcases hq with hq | hq | hq
      · exact loc_not_loc hS (by omega) (by omega) (.inl (by omega)) hq
      · exact loc_not_loc hS (by omega) (by omega) (.inl (by omega)) hq
      · exact loc_not_ts h (by omega) hq
  have sm2 := sm1.of_keep ks2
  have hcl2 : ClaimsWAt m2.dmem m0.regs.X5.toBitVec (claimsOf L pt mem mf bf) := by
    refine NativeRustcVm.Tables.ClaimsWAt.of_same tc1.2 (Same.of_sameOutside hs2
      fun j hj hq ↦ ?_)
    have hc := (pre_cl h).2.1
    have hin : InRange m0.regs.X5.toBitVec claimsBytes
        (m0.regs.X5.toBitVec + BitVec.ofNat 64 j) :=
      NativeRustcVm.inRange_add hj (by unfold NoWrap at hc; rw [claimsBytes_eq] at hc hj ⊢; omega)
    rcases hq with hq | hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange (pre_cl h).2.2.2.2.1 hc (Bus.stack_noWrap hS) hin
        (stk2 _ hq)
    · exact cl_not_loc h hin (by omega) hq
    · exact cl_not_loc h hin (by omega) hq
    · exact NativeRustcVm.Apart.not_inRange (pre_cl h).2.2.1 hc (pre_ts h).footprint.1.2 hin hq
  have R2 : RegsEq [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] st1.data m2 :=
    regsEq_call hcs2 (by decide)
  rw [NativeRustcVmArm.Vm.VerifyBusBalance.b32_length, NativeRustcVmArm.Vm.VerifyBusBalance.b32Length]
  cases hr : (bytecodeShare w (pt.extract 0 L.logBytecode)).run s3 with
  | none =>
    rw [hr] at hopt
    refine Fr.runBlock hS N_ge rfl hfr2 (b33_in_code.trans hp.1 (by simp [b33])) run_b33 rfl rfl
      (by decide) (by decide) fun st3 hfr3 _ _ hpc3 ↦ ?_
    refine fail_cond hp h hpc3 ?_ hfr3 (by rw [A.run, hr]; rfl)
    show CmpOp.apply .eq .W64 ((Env.ofMachine m2 [(base m0 5488, 5488)]).load 0 5264 8)
      (BitVec.ofNat 64 0) = true
    rw [Transcript.load_ofMachine rfl (show NativeRustcVm.WordAt m2.dmem (loc m0 5264) 0 from hopt),
      eq_lit_word _ (by decide)]
    rfl
  | some p =>
  obtain ⟨x, s4⟩ := p
  rw [hr] at hopt hres
  obtain ⟨o1, o2, o3, o4⟩ := hopt
  obtain ⟨hbp, hts4⟩ := hres x s4 rfl
  have hsz := bytecodeShare_size hr
  rw [Array.size_extract] at hsz
  have ns : x.2.1.size.toUInt64.toNat = x.2.1.size :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have e2 := NativeRustcVm.ewAt_iff.mp o2
  have e4 := NativeRustcVm.ewAt_iff.mp o4
  have w5272 : NativeRustcVm.WordAt m2.dmem (loc m0 5272) x.1.c0 := by
    simpa only [off, NativeRustcVm.addr_add_add] using e2.1
  have w5280 : NativeRustcVm.WordAt m2.dmem (loc m0 5280) x.1.c1 := by
    simpa only [off, NativeRustcVm.addr_add_add] using e2.2
  have w5288 : NativeRustcVm.WordAt m2.dmem (loc m0 5288) x.2.1.size.toUInt64 := by
    simpa only [off, NativeRustcVm.addr_add_add] using o3
  have w5296 : NativeRustcVm.WordAt m2.dmem (loc m0 5296) x.2.2.c0 := by
    simpa only [off, NativeRustcVm.addr_add_add] using e4.1
  have w5304 : NativeRustcVm.WordAt m2.dmem (loc m0 5304) x.2.2.c1 := by
    simpa only [off, NativeRustcVm.addr_add_add] using e4.2
  -- `b33`: the share's tag.
  refine Fr.runBlock hS N_ge rfl hfr2 (b33_in_code.trans hp.1 (by simp [b33])) run_b33 rfl rfl
    (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hc3 : SBool.eval (Env.ofMachine m2 [(base m0 5488, 5488)])
      (.cmp .eq .W64 (.load 0 5264 8) (.lit 0)) = false := by
    show CmpOp.apply .eq .W64 ((Env.ofMachine m2 [(base m0 5488, 5488)]).load 0 5264 8)
      (BitVec.ofNat 64 0) = false
    rw [Transcript.load_ofMachine rfl o1, eq_lit_word _ (by decide)]
    rfl
  have R3 : RegsEq [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] m2 st3.data :=
    regsEq_block hm3 (by decide)
  rw [← hd3] at w5272 w5280 w5288 w5296 w5304 hbp hts4 hcl2
  -- `b34`: the share kept, the point's length checked.
  have hwf4 := Bus.wf_frame hS N_ge hfr3.kept
  have hm4 := Bus.match_frame hS N_ge rfl hfr3.sp
  refine exec_at (b34_in_code.trans hp.1 (by simp [b34])) run_b34 hwf4 (pass_cond hpc3 hc3) hm4
    fun st4 hm4' hpc4 ↦ ?_
  have hfr4 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st4.data :=
    Bus.Fr.block hfr3 hN N_ge hm4' hwf4 rfl (by decide) (by decide) slots_le
  have hsh4 : NativeRustcVm.EWAt st4.data.dmem (loc m0 5248) x.1 :=
    NativeRustcVm.ewAt_iff.mpr ⟨wr_eval hm4' (o := 5248) (by omega) (.load 0 5272 8) (by decide)
      (by
        show (Env.ofMachine st3.data _).load 0 5272 8 = _
        exact Transcript.load_ofMachine rfl w5272), by
      rw [NativeRustcVm.addr_add_add]
      exact wr_eval hm4' (o := 5256) (by omega) (.load 0 5280 8) (by decide) (by
        show (Env.ofMachine st3.data _).load 0 5280 8 = _
        exact Transcript.load_ofMachine rfl w5280)⟩
  have hc4 : SBool.eval (Env.ofMachine st3.data [(base m0 5488, 5488)])
      (.not (.cmp .ult .W64 (.load 0 5288 8) (.lit 68))) = false := by
    show (!CmpOp.apply .ult .W64 ((Env.ofMachine st3.data [(base m0 5488, 5488)]).load 0 5288 8)
      (BitVec.ofNat 64 68)) = false
    rw [Transcript.load_ofMachine rfl w5288, ult_lit_word _ (by decide), ns,
      decide_eq_true (by omega : x.2.1.size < 68)]
    rfl
  have R4 : RegsEq [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] st3.data
      st4.data := regsEq_block hm4' (by decide)
  have k4 : KeepIv [(88, 136), (160, 5248)] m0 st3.data.dmem st4.data.dmem :=
    keepIv_block hm4' hwf4 (sizes := [5488]) rfl (by decide) (by decide)
  have tc4 := keep_tc h (hm4'.kept hwf4) (hm4'.sameOutside hwf4)
    (fun q hq ↦ .inl (written_stack hS (by decide) hq)) hts4 hcl2
  have u3 : st4.data.regs.X3 = x.2.1.size.toUInt64 := reg_ld' (x := .X3) hm4' rfl w5288
  have u4 : st4.data.regs.X4 = x.2.2.c0 := reg_ld' (x := .X4) hm4' rfl w5296
  have u5 : st4.data.regs.X5 = x.2.2.c1 := reg_ld' (x := .X5) hm4' rfl w5304
  -- `b35`: `computed_bytecode_value`.
  have hwf5 := Bus.wf_frame hS N_ge hfr4.kept
  have hm5 := Bus.match_frame hS N_ge rfl hfr4.sp
  refine exec_at (b35_in_code.trans hp.1 (by simp [b35])) run_b35 hwf5 (pass_cond hpc4 hc4) hm5
    fun st5 hm5' hpc5 ↦ ?_
  have hd5 : st5.data.dmem = st4.data.dmem := hm5'.dmem_eq hwf5 rfl
  have hfr5 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st5.data :=
    Bus.Fr.block hfr4 hN N_ge hm5' hwf5 rfl (by decide) (by decide) slots_le
  have hat5 := Fr.at_ c hfr5 (outs_not_rc h)
  have R5 : RegsEq [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] st4.data
      st5.data := regsEq_block hm5' (by decide)
  have R15 := (((R2.trans R3).trans R4).trans R5)
  have v0 : st5.data.regs.X0 = m0.regs.X2 :=
    (reg_of hm5' (r := .X0) (r' := .X24) rfl).trans (((R2.trans R3).trans R4 .X24 (by simp)).trans
      ((R1 .X24 (by simp)).trans A.x24))
  have v1 : st5.data.regs.X1 = m0.regs.X3 :=
    (reg_of hm5' (r := .X1) (r' := .X23) rfl).trans (((R2.trans R3).trans R4 .X23 (by simp)).trans
      ((R1 .X23 (by simp)).trans A.x23))
  have v2 : st5.data.regs.X2 = UInt64.ofBitVec (loc m0 4176) :=
    UInt64.toBitVec_inj.mp (reg_ptr (x := .X2) 4176 hm5' rfl)
  have v3 : st5.data.regs.X3 = x.2.1.size.toUInt64 :=
    (reg_of hm5' (r := .X3) (r' := .X3) rfl).trans u3
  have v4 : st5.data.regs.X4 = x.2.2.c0 := (reg_of hm5' (r := .X4) (r' := .X4) rfl).trans u4
  have v5 : st5.data.regs.X5 = x.2.2.c1 := (reg_of hm5' (r := .X5) (r' := .X5) rfl).trans u5
  have hbp5 : NativeRustcVm.EWsAt st5.data.dmem (loc m0 4176) x.2.1.toList := by
    rw [hd5]
    refine NativeRustcVm.Tables.EWsAt.of_same hbp (k4.sameIn (lo := 160) (hi := 5248) (by simp)
      (o := 4176) (n := 16 * x.2.1.size) (by omega) (by omega)) (by rw [Array.length_toList])
  have hpre5 : ComputedBytecodeValuePre st5.data := by
    unfold ComputedBytecodeValuePre
    rw [v0, v1, v2, v3]
    refine ⟨hfr5.stackOk hS rfl le_cbv, ⟨fun i hi ↦ hfr5.kept _ ((pre_bcR h).1 i hi),
      (pre_bcR h).2⟩, fun h0 ↦ c.apart hat5 le_cbv (pre_bcS h h0), ?_⟩
    unfold SliceOk
    rw [UInt64.toBitVec_ofBitVec, ns]
    exact loc_inOk h hfr5 le_cbv (by omega)
  simp only [PcOk] at hpc5
  refine Fr.callSpec hfr5 hN le_cbv keep_callee slots_le (outs_not_frame h) hcbv hpc5 hpre5
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ hq'.elim
      (fun h0 ↦ absurd h0 (by unfold InRange; omega)) .inl, hq.2.2⟩)
    fun m6 hfr6 hq6 hcs6 ↦ ?_
  obtain ⟨hx6, hch6, hsv6⟩ := hq6
  have hs6 : SameOutside st5.data.dmem m6.dmem (fun q ↦
      InRange (stackBelow st5.data computedBytecodeValueStack) computedBytecodeValueStack q ∨
        False) :=
    NativeRustcVm.SameOutside.mono hch6 fun q hq' ↦ hq'.elim
      (fun h0 ↦ absurd h0 (by unfold InRange; omega)) .inl
  have hws : wordSliceE st5.data st5.data.regs.X0 st5.data.regs.X1 = L.bytecode.map EW.ofK := by
    unfold wordSliceE
    rw [v0, v1, bc_words h hfr5]
    apply Array.ext'
    simp
  have hsl : slice st5.data st5.data.regs.X2 st5.data.regs.X3 = x.2.1 :=
    slice_of_ewsAt (by rw [v2, UInt64.toBitVec_ofBitVec]; exact hbp5) (by rw [v3, ns])
  rw [hws, hsl, v4, v5] at hx6
  have R6 : RegsEq [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] st5.data m6 :=
    regsEq_call hcs6 (by decide)
  have k6 : KeepIv [(88, 136), (160, 4176), (5248, 5264)] m0 st5.data.dmem m6.dmem :=
    keepIv_call hS hfr5.sp le_cbv hs6 (by decide) fun _ _ h' ↦ h'
  have tc6 := keep_tc h hsv6.2.2 hs6 (fun q hq ↦ hq.elim
    (fun hq ↦ .inl (callee_stack hS hfr5.sp le_cbv hq)) False.elim)
    (by rw [hd5]; exact tc4.1) (by rw [hd5]; exact tc4.2)
  -- `b36`: the bytecode's value checked.
  refine Fr.runBlock hS N_ge rfl hfr6 (b36_in_code.trans hp.1 (by simp [b36])) run_b36 rfl rfl
    (by decide) (by decide) fun st7 hfr7 hd7 hm7 hpc7 ↦ ?_
  have hc7 : SBool.eval (Env.ofMachine m6 [(base m0 5488, 5488)])
      (.cmp .eq .W32 (.reg .X0) (.lit 0)) =
        !(multilinearEval (L.bytecode.map EW.ofK) x.2.1 == x.2.2) := by
    show CmpOp.eq.apply .W32 (m6.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = _
    rw [show m6.regs.getXReg .X0 = m6.regs.X0 from rfl, hx6, okW_eq0]
    rfl
  have hrun : (verifyBusBalance L).run s0 =
      if (multilinearEval (L.bytecode.map EW.ofK) x.2.1 == x.2.2) = true then
        some (resultOf L w beta pt tv mem mf bf x.1 x.2.1, s4) else none := by
    rw [A.run, hr, Option.bind_some, cbv_run]
    split <;> rfl
  cases hb : (multilinearEval (L.bytecode.map EW.ofK) x.2.1 == x.2.2) with
  | false => exact fail_cond hp h hpc7 (by rw [hc7, hb]; rfl) hfr7 (by rw [hrun, hb]; rfl)
  | true =>
  have R7 : RegsEq [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] m6 st7.data :=
    regsEq_block hm7 (by decide)
  have R := (R15.trans R6).trans R7
  have kk : KeepIv [(88, 136), (160, 4176), (5248, 5264)] m0 st4.data.dmem st7.data.dmem :=
    ((KeepIv.rfl' hd5).trans k6).trans (KeepIv.rfl' hd7)
  have sm4 := sm2.of_keep ((KeepIv.rfl' hd3).trans (k4.mono (ivSub (by decide))))
  have sm7 := sm4.of_keep (kk.mono (ivSub (by decide)))
  have hsh7 : NativeRustcVm.EWAt st7.data.dmem (loc m0 5248) x.1 :=
    NativeRustcVm.Layout.EWAt.of_same hsh4 (kk.sameIn (lo := 5248) (hi := 5264) (by simp)
      (by omega) (by omega)) le_rfl
  have g : ∀ r, r ∈ [XReg.X19, .X20, .X22, .X26, .X27, .X29] →
      st7.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (R _ (by simp)).trans (R1 _ (by simp))
  refine at_pc (pass_cond hpc7 (by rw [hc7, hb]; rfl)) (push_spec hp h hkp hacc hext hfc
    { fr := hfr7, run := by rw [hrun, hb]; rfl, mem' := sm7.push' hsh7, w120 := sm7.w120,
      x19 := (g .X19 (by simp)).trans A.x19, x20 := (g .X20 (by simp)).trans A.x20,
      x22 := (g .X22 (by simp)).trans A.x22,
      x25 := by rw [R .X25 (by simp)]; exact z25,
      x26 := by rw [g .X26 (by simp)]; exact A.x26, x27 := (g .X27 (by simp)).trans A.x27,
      x29 := by rw [g .X29 (by simp)]; exact A.x29,
      ts := by rw [hd7]; exact tc6.1, cl := by rw [hd7]; exact tc6.2 })

end

end NativeRustcVmArm.Bus.VerifyBusBalance
