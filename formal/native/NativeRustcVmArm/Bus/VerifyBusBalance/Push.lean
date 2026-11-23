module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Code.Vm.Kpow.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.PushPre

/-!
# `verify_bus_balance`'s push side

From `b37` (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b37Offset`), after `computed_bytecode_value`: `b37` writes the closure's environment
and calls `kpow` for `pc_final`; `b38` empties the bus's forms, keeps `pc_final` and the tree's
third value, and calls `kpow` for `gpow(0)`; `b39` calls the closure for the push side's
fingerprints; `b40` calls `accumulate_side` on the push side; then the pull side (`push_spec`).
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section
variable [Labels] {m0 : MachineData}

/-- **A word a block wrote** at the frame's byte `o`, its value `x`. -/
theorem wr_eval {m st : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S st) {o : Nat} (ho : o + 8 ≤ 5488)
    (v : Sym) (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) {x : UInt64}
    (hx : v.eval (Env.ofMachine m ((base m0 5488, 5488) :: rs)) = x.toBitVec) :
    NativeRustcVm.WordAt st.dmem (loc m0 o) x := by
  have := Transcript.wordAt_write hm (r := 0) rfl ho hw
  rwa [hx, UInt64.ofBitVec_toBitVec] at this

/-- The frame's byte `o` as a symbolic pointer. -/
theorem ptr_eval {m : MachineData} {rs : List (BitVec 64 × Nat)} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (Env.ofMachine m ((base m0 5488, 5488) :: rs)) =
      (UInt64.ofBitVec (loc m0 o)).toBitVec := by
  rw [eval_ptr_off rfl, BitVec.ofInt_natCast]

omit [Labels] in
/-- **The locals from `b39` on**, from those at `b37` and the environment. -/
theorem Locs.of_push {L : LayoutW} {w pt tv mem : Array EW} {beta mf bf share : EW}
    {d : Mem 64} (hp : PushMem m0 L w pt tv mem beta mf bf share d) (he : EnvW m0 L pt d)
    (w80 : NativeRustcVm.WordAt d (loc m0 80) (tv.getD 2 0).c0)
    (w120 : NativeRustcVm.WordAt d (loc m0 120) (gpowK (2 ^ L.logBytecode - 1))) :
    Locs m0 L w pt tv mem beta mf bf share d :=
  ⟨hp.pull, hp.count, hp.hw, hp.wsz, hp.hpt, hp.psz, hp.hmem, hp.msz, w80, hp.w88, hp.w96,
    hp.w104, hp.w112, w120, hp.w128, hp.share, he.e0, he.e1, he.e2, he.e3, he.e4, he.e5, he.e6⟩

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The push side** (`b37`, `k + NativeRustcVmArm.Vm.VerifyBusBalance.b37Offset`). -/
theorem push_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hkp : Spec (Labels.label NativeRustcVmArm.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmArm.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    (hfc : Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    {w pt tv mem bp : Array EW} {beta mf bf share : EW} {s' : TState} {m : MachineData}
    (A : AtPush a s0 L m0 w pt tv mem beta mf bf share bp s' m) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b37Offset)⟩ := by
  have hS := pre_stack h
  have hN := hS.2.1
  have hbus := pre_bus h
  have hbnw := hbus.2.1
  have hlb := (pre_lay h).log_bytecode_le
  have hpsz := A.mem'.psz
  -- `b37`: the closure's environment; `kpow(2^log_bytecode - 1)`.
  have hwf1 := Bus.wf_frame hS N_ge A.fr.kept
  have hm1 := Bus.match_frame hS N_ge rfl A.fr.sp
  refine exec_then (b37_in_code.trans hp.1 (by simp [b37])) run_b37 hwf1 hm1
    fun st1 hm1' hpc1 ↦ ?_
  have hfr1 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st1.data :=
    Bus.Fr.block A.fr hN N_ge hm1' hwf1 rfl (by decide) (by decide) slots_le
  have kp1 : KeepIv pushIv m0 m.dmem st1.data.dmem :=
    keepIv_block hm1' hwf1 (sizes := [5488]) rfl (by decide) (by decide)
  have he1 : EnvW m0 L pt st1.data.dmem :=
    ⟨wr_eval hm1' (o := 5264) (by omega) (.ptr 0 (2824 : Nat)) (by decide) (ptr_eval 2824),
      wr_eval hm1' (o := 5272) (by omega) (.ptr 0 (4144 : Nat)) (by decide) (ptr_eval 4144),
      wr_eval hm1' (o := 5280) (by omega) (.reg .X25) (by decide)
        (by show (m.regs.getXReg .X25).toBitVec = _; rw [A.x25]),
      wr_eval hm1' (o := 5288) (by omega) (.reg .X27) (by decide)
        (by show (m.regs.getXReg .X27).toBitVec = _; rw [A.x27]),
      wr_eval hm1' (o := 5296) (by omega) (.reg .X25) (by decide)
        (by show (m.regs.getXReg .X25).toBitVec = _; rw [A.x25]),
      wr_eval hm1' (o := 5304) (by omega) (.load 0 120 8) (by decide)
        (by
          show (Env.ofMachine m [(base m0 5488, 5488)]).load 0 120 8 = _
          exact Transcript.load_ofMachine rfl A.w120),
      wr_eval hm1' (o := 5312) (by omega) (.ptr 0 (5248 : Nat)) (by decide) (ptr_eval 5248)⟩
  have tc1 := keep_tc h (hm1'.kept hwf1) (hm1'.sameOutside hwf1)
    (fun q hq ↦ .inl (written_stack hS (by decide) hq)) A.ts A.cl
  have hx0 : (st1.data.regs.X0).toNat = 2 ^ L.logBytecode - 1 := by
    rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl,
      ← UInt64.toNat_toBitVec, hm1'.regs .X0 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [mask_toNat (by rw [UInt64.toNat_toBitVec, A.x29]; omega), UInt64.toNat_toBitVec, A.x29]
  simp only [PcOk] at hpc1
  refine Fr.callSpec hfr1 hN le_kpow keep_callee slots_le (outs_not_frame h) hkp hpc1
    (hfr1.stackOk hS rfl le_kpow)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ .inl hq', hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 ↦ ?_
  obtain ⟨hk2x0, hk2s, hk2v⟩ := hq2
  rw [hx0] at hk2x0
  have kp2 : KeepIv pushIv m0 st1.data.dmem m2.dmem :=
    keepIv_call hS hfr1.sp le_kpow (X := fun _ ↦ False)
      (NativeRustcVm.SameOutside.mono hk2s fun q hq ↦ .inl hq) (by decide)
      fun _ _ h' ↦ h'
  have ke2 : KeepIv [(5264, 5320)] m0 st1.data.dmem m2.dmem :=
    keepIv_call hS hfr1.sp le_kpow (X := fun _ ↦ False)
      (NativeRustcVm.SameOutside.mono hk2s fun q hq ↦ .inl hq) (by decide)
      fun _ _ h' ↦ h'
  have tc2 := keep_tc h hk2v.2.2 hk2s
    (fun q hq ↦ .inl (callee_stack hS hfr1.sp le_kpow hq)) tc1.1 tc1.2
  -- `b38`: the forms emptied, `pc_final` and the tree's third value kept; `kpow(0)`.
  have r2 : ∀ r, r ∈ [XReg.X19, .X20, .X22, .X25, .X26] →
      m2.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact (hcs2 _ rfl).trans (reg_of hm1' rfl)
  have y21 : (m2.regs.getXReg .X21).toBitVec = BitVec.ofNat 64 59280 := by
    rw [hcs2 .X21 rfl]; exact reg_lit hm1' rfl
  have y23 : (m2.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 35568 := by
    rw [hcs2 .X23 rfl]; exact reg_lit hm1' rfl
  have y24 : (m2.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 53352 := by
    rw [hcs2 .X24 rfl]; exact reg_lit hm1' rfl
  have y27 : (m2.regs.getXReg .X27).toBitVec = BitVec.ofNat 64 47424 := by
    rw [hcs2 .X27 rfl]; exact reg_lit hm1' rfl
  have y29 : (m2.regs.getXReg .X29).toBitVec = BitVec.ofNat 64 41496 := by
    rw [hcs2 .X29 rfl]; exact reg_lit hm1' rfl
  have hwf3 : (Env.ofMachine m2 [(base m0 5488, 5488), (m0.regs.X4.toBitVec, 107768)]).WF :=
    Bus.wf_frame2 hS N_ge hfr2.kept ⟨hbus.1, hbus.2.1⟩ hbus.2.2.2.2.1
  have hm3 := match_frF hS hfr2.sp (by rw [r2 .X19 (by simp), A.x19]) y23 y29 y27 y24 y21
  refine exec_at (b38_in_code.trans hp.1 (by simp [b38])) run_b38 hwf3 rfl hm3
    fun st3 hm3' hpc3 ↦ ?_
  have hfr3 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st3.data :=
    Fr.ofBlockW hfr2 hm3 hm3' hwf3 rfl rfl (fun r hr ↦ by simp at hr) rfl N_ge hN slots_le
      (writeOk_bus (by decide))
  have kp3 : KeepIv pushIv m0 m2.dmem st3.data.dmem :=
    keepIv_block hm3' hwf3 (sizes := [5488, 107768]) rfl (by decide) (by decide)
  have ke3 : KeepIv [(5264, 5320)] m0 m2.dmem st3.data.dmem :=
    keepIv_block hm3' hwf3 (sizes := [5488, 107768]) rfl (by decide) (by decide)
  have pm2 := A.mem'.of_keep (kp1.trans kp2)
  have pm3 := pm2.of_keep kp3
  have he3 := he1.of_keep (ke2.trans ke3)
  have w80 : NativeRustcVm.WordAt st3.data.dmem (loc m0 80) (tv.getD 2 0).c0 :=
    wr_eval hm3' (o := 80) (by omega) (.load 0 3112 8) (by decide) (by
      show (Env.ofMachine m2 _).load 0 3112 8 = _
      exact Transcript.load_ofMachine rfl pm2.t2a)
  have w120 : NativeRustcVm.WordAt st3.data.dmem (loc m0 120)
      (gpowK (2 ^ L.logBytecode - 1)) :=
    wr_eval hm3' (o := 120) (by omega) (.reg .X0) (by decide) (by
      show (m2.regs.getXReg .X0).toBitVec = _
      rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hk2x0])
  have hl3 : Locs m0 L w pt tv mem beta mf bf share st3.data.dmem :=
    Locs.of_push pm3 he3 w80 w120
  have hF3 : FormsAt st3.data.dmem m0.regs.X4.toBitVec forms0 := forms0_at fun j hj ↦
    Transcript.wordAt_write hm3' (r := 1) (o := 5928 * j) rfl (by omega) (v := .lit 0)
      (by interval_cases j <;> decide)
  have tc3 := keep_tc h (hm3'.kept hwf3) (hm3'.sameOutside hwf3)
    (fun q hq ↦ written_fb h (by decide) hq) tc2.1 tc2.2
  have z19 : st3.data.regs.getXReg .X19 = m0.regs.X4 :=
    UInt64.toBitVec_inj.mp (by rw [hm3'.regs .X19 _ rfl, eval_ptr_off rfl]; simp)
  have z20 : st3.data.regs.getXReg .X20 = m0.regs.X1 :=
    (reg_of hm3' rfl).trans ((r2 .X20 (by simp)).trans A.x20)
  have z22 : st3.data.regs.getXReg .X22 = beta.c1 :=
    (reg_of hm3' rfl).trans ((r2 .X22 (by simp)).trans A.x22)
  have z25 : (st3.data.regs.getXReg .X25).toBitVec = loc m0 3136 := by
    rw [reg_of hm3' rfl, r2 .X25 (by simp)]; exact A.x25
  have z26 : (st3.data.regs.getXReg .X26).toNat = pt.size := by
    rw [reg_of hm3' rfl, r2 .X26 (by simp)]; exact A.x26
  have z21 : st3.data.regs.getXReg .X21 = (tv.getD 0 0).c0 := reg_ld' hm3' rfl pm2.t0a
  have z23 : st3.data.regs.getXReg .X23 = (tv.getD 2 0).c1 := reg_ld' hm3' rfl pm2.t2b
  have z24 : st3.data.regs.getXReg .X24 = (tv.getD 0 0).c1 := reg_ld' hm3' rfl pm2.t0b
  have z27 : st3.data.regs.getXReg .X27 = (tv.getD 1 0).c0 := reg_ld' hm3' rfl pm2.t1a
  have z29 : st3.data.regs.getXReg .X29 = (tv.getD 1 0).c1 := reg_ld' hm3' rfl pm2.t1b
  have hx3 : st3.data.regs.X0.toNat = 0 := by
    rw [show st3.data.regs.X0 = st3.data.regs.getXReg .X0 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm3' (r := .X0) (n := 0) rfl]
    rfl
  simp only [PcOk] at hpc3
  refine Fr.callSpec hfr3 hN le_kpow keep_callee slots_le (outs_not_frame h) hkp hpc3
    (hfr3.stackOk hS rfl le_kpow)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ .inl hq', hq.2.2⟩)
    fun m4 hfr4 hq4 hcs4 ↦ ?_
  obtain ⟨hk4x0, hk4s, hk4v⟩ := hq4
  rw [hx3] at hk4x0
  have kl4 : KeepLoc m0 st3.data.dmem m4.dmem :=
    keepLoc_call hS hfr3.sp le_kpow (X := fun _ ↦ False)
      (NativeRustcVm.SameOutside.mono hk4s fun q hq ↦ .inl hq) fun _ _ h' ↦ h'
  have tc4 := keep_tc h hk4v.2.2 hk4s
    (fun q hq ↦ .inl (callee_stack hS hfr3.sp le_kpow hq)) tc3.1 tc3.2
  have hnot : ∀ j < busPointOff, ¬InRange (stackBelow m0 verifyBusBalanceStack)
      verifyBusBalanceStack (m0.regs.X4.toBitVec + BitVec.ofNat 64 j) := fun j hj ↦
    bus_not_stack h (bus_sub hbnw (o := 0) (n := busPointOff) (by decide)
      (by rw [Bus.add_zero']; exact NativeRustcVm.inRange_add hj (by rw [busPointOff_eq]; omega)))
  have hF4 : FormsAt m4.dmem m0.regs.X4.toBitVec forms0 :=
    FormsAt.of_same hF3 (Same.of_sameOutside hk4s fun j hj hq ↦
      hnot j hj (callee_stack hS hfr3.sp le_kpow hq))
  -- `b39`: the closure for the push side's fingerprints.
  have hwf5 := Bus.wf_frame hS N_ge hfr4.kept
  have hm5 := Bus.match_frame hS N_ge rfl hfr4.sp
  refine exec_at (b39_in_code.trans hp.1 (by simp [b39])) run_b39 hwf5 rfl hm5
    fun st5 hm5' hpc5 ↦ ?_
  have hd5 : st5.data.dmem = m4.dmem := hm5'.dmem_eq hwf5 rfl
  have hfr5 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st5.data :=
    Bus.Fr.block hfr4 hN N_ge hm5' hwf5 rfl (by decide) (by decide) slots_le
  have hl5 : Locs m0 L w pt tv mem beta mf bf share st5.data.dmem :=
    (hl3.of_keep kl4).of_keep (KeepLoc.rfl' hd5)
  have v2 : st5.data.regs.X2 = gpowK 0 := (reg_of hm5' (r := .X2) (r' := .X0) rfl).trans hk4x0
  have v3 : st5.data.regs.X3 = 1 := UInt64.toBitVec_inj.mp (reg_lit hm5' (r := .X3) (n := 1) rfl)
  have v4 : st5.data.regs.X4 = 0 := UInt64.toBitVec_inj.mp (reg_lit hm5' (r := .X4) (n := 0) rfl)
  have v5 : st5.data.regs.X5 = 1 := UInt64.toBitVec_inj.mp (reg_lit hm5' (r := .X5) (n := 1) rfl)
  have v6 : st5.data.regs.X6 = 0 := UInt64.toBitVec_inj.mp (reg_lit hm5' (r := .X6) (n := 0) rfl)
  have q6 : ∀ r, r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] →
      st5.data.regs.getXReg r = st3.data.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (reg_of hm5' rfl).trans (hcs4 _ rfl)
  simp only [PcOk] at hpc5
  refine fp_call h hfc hfr5 hpc5 hl5 (reg_ptr (x := .X0) 5344 hm5' rfl)
    (reg_ptr (x := .X1) 5264 hm5' rfl) fun m6 hfr6 hfp6 hk6 hcs6 hs6 ↦ ?_
  rw [v2, v3, v4, v5, v6] at hfp6
  have kl6 : KeepLoc m0 st5.data.dmem m6.dmem :=
    keepLoc_call hS hfr5.sp le_fp hs6 (not_locs hS (o := 5344) (n := 48) (by omega)
      fun j hj ↦ by unfold InLocs at hj; omega)
  have stk6 : ∀ q, (InRange (stackBelow st5.data fpClosureStack) fpClosureStack q ∨
      InRange (loc m0 5344) 48 q) →
      InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack q := fun q hq ↦
    hq.elim (fun hq ↦ callee_stack hS hfr5.sp le_fp hq) fun hq ↦ loc_stack hS (by omega) hq
  have tc6 := keep_tc h hk6 hs6 (fun q hq ↦ .inl (stk6 q hq))
    (by rw [hd5]; exact tc4.1) (by rw [hd5]; exact tc4.2)
  have hF6 : FormsAt m6.dmem m0.regs.X4.toBitVec forms0 :=
    FormsAt.of_same (by rw [hd5]; exact hF4)
      (Same.of_sameOutside hs6 fun j hj hq ↦ hnot j hj (stk6 _ hq))
  have q7 : ∀ r, r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] →
      m6.regs.getXReg r = st3.data.regs.getXReg r := fun r hr ↦ by
    have hr' : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hcs6 r hr']
    exact q6 r hr
  -- `b40`: `accumulate_side` on the push side.
  have hwf7 := Bus.wf_frame hS N_ge hfr6.kept
  have hm7 := Bus.match_frame hS N_ge rfl hfr6.sp
  refine exec_at (b40_in_code.trans hp.1 (by simp [b40])) run_b40 hwf7 rfl hm7
    fun st7 hm7' hpc7 ↦ ?_
  have hfr7 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st7.data :=
    Bus.Fr.block hfr6 hN N_ge hm7' hwf7 rfl (by decide) (by decide) slots_le
  have kl7 : KeepLoc m0 m6.dmem st7.data.dmem :=
    keepLoc_block hm7' hwf7 (sizes := [5488]) rfl (lo := 0) (hi := 72) (by decide)
      fun j hj ↦ by unfold InLocs at hj; omega
  have hl7 := (hl5.of_keep kl6).of_keep kl7
  have hs7 : SameOutside m6.dmem st7.data.dmem
      (InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack) :=
    NativeRustcVm.SameOutside.mono (hm7'.sameOutside hwf7) fun q hq ↦
      written_stack hS (by decide) hq
  have kfp : NativeRustcVm.EWsAt st7.data.dmem (loc m0 5344)
      (fingerprints w mem (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share
        (gpow 0) 1 1).toList :=
    keep_out hm7' hwf7 (sizes := [5488]) rfl (lo := 0) (hi := 72) (by decide)
      (by rw [NativeRustcVm.length_ewsBytes, fingerprints_length]; omega) (.inr (by omega)) hfp6
  have hF7 : FormsAt st7.data.dmem m0.regs.X4.toBitVec forms0 :=
    FormsAt.of_same hF6 (Same.of_sameOutside hs7 fun j hj hq ↦ hnot j hj hq)
  have tc7 := keep_tc h (hm7'.kept hwf7) hs7 (fun q hq ↦ .inl hq) tc6.1 tc6.2
  have klP : KeepLoc m0 st3.data.dmem st7.data.dmem :=
    ((kl4.trans (KeepLoc.rfl' hd5)).trans kl6).trans kl7
  have hSL : BusLayoutWAt st7.data.dmem (loc m0 160) (pushL L) :=
    BusLayoutWAt.of_same pm3.push (klP.same fun j hj ↦ by
      unfold InLocs; rw [busLayoutBytes_eq] at hj; omega)
  have u : ∀ r, r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X29] →
      st7.data.regs.getXReg r = st3.data.regs.getXReg r := fun r hr ↦ by
    have hr' : r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h' | h' | h' | h' | h' | h' | h' | h' | h' <;> simp [h']
    rw [← q7 r hr']
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact reg_of hm7' rfl
  have y1 : st7.data.regs.X1 = m0.regs.X4 :=
    (reg_of hm7' (r := .X1) (r' := .X19) rfl).trans ((q7 .X19 (by simp)).trans z19)
  have y2 : st7.data.regs.X2.toNat = 0 := by
    rw [show st7.data.regs.X2 = st7.data.regs.getXReg .X2 from rfl,
      ← UInt64.toNat_toBitVec, hm7'.regs .X2 _ rfl]; rfl
  have y3 : st7.data.regs.X3.toBitVec = NativeRustcVmArm.rodataAddr .pushBlocks := by
    rw [show st7.data.regs.X3 = st7.data.regs.getXReg .X3 from rfl, hm7'.regs .X3 _ rfl]; rfl
  have y4 : st7.data.regs.X4.toNat = (sideBlocks 0).length := by
    rw [show st7.data.regs.X4 = st7.data.regs.getXReg .X4 from rfl,
      ← UInt64.toNat_toBitVec, hm7'.regs .X4 _ rfl]; rfl
  have y5 : st7.data.regs.X5 = m0.regs.X1 :=
    (reg_of hm7' (r := .X5) (r' := .X20) rfl).trans ((q7 .X20 (by simp)).trans z20)
  have y7 : st7.data.regs.X7.toBitVec = loc m0 5344 := reg_ptr (x := .X7) 5344 hm7' rfl
  have sa : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 5488 →
      (∀ i < 8, findWrite 0 (o + i) _ = some (v, i)) →
      stackArg st7.data o = UInt64.ofBitVec (v.eval (Env.ofMachine m6 [(base m0 5488, 5488)])) :=
    fun ho hw ↦ stackArg_write hm7' hfr7.sp ho hw
  have s0' : stackArg st7.data 0 = 3 := sa (o := 0) (v := .lit 3) (by omega) (by decide)
  have s8 : stackArg st7.data 8 = UInt64.ofBitVec (loc m0 2824) := by
    rw [sa (o := 8) (v := .ptr 0 (2824 : Nat)) (by omega) (by decide), ptr_eval,
      UInt64.ofBitVec_toBitVec]
  have s16 : stackArg st7.data 16 = 16 := sa (o := 16) (v := .lit 16) (by omega) (by decide)
  have s24 : stackArg st7.data 24 = beta.c0 := by
    rw [sa (o := 24) (v := .load 0 128 8) (by omega) (by decide)]
    simp only [Sym.eval]
    rw [Transcript.load_ofMachine (b := base m0 5488) (n := 5488) rfl
      (hl5.of_keep kl6).w128]
  have rv : ∀ {r : XReg} {x : UInt64}, m6.regs.getXReg r = x →
      UInt64.ofBitVec ((Sym.reg r).eval (Env.ofMachine m6 [(base m0 5488, 5488)])) = x :=
    fun hx ↦ by simp only [Sym.eval, Env.ofMachine_regs]; rw [hx]
  have s32 : stackArg st7.data 32 = beta.c1 := by
    rw [sa (o := 32) (v := .reg .X22) (by omega) (by decide)]
    exact rv ((q7 .X22 (by simp)).trans z22)
  have s40 : stackArg st7.data 40 = UInt64.ofBitVec (loc m0 3136) := by
    rw [sa (o := 40) (v := .reg .X25) (by omega) (by decide)]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [q7 .X25 (by simp), z25]
  have s48 : (stackArg st7.data 48).toNat = pt.size := by
    rw [sa (o := 48) (v := .reg .X26) (by omega) (by decide), rv (q7 .X26 (by simp))]
    exact z26
  have s56 : stackArg st7.data 56 = (tv.getD 0 0).c0 := by
    rw [sa (o := 56) (v := .reg .X21) (by omega) (by decide)]
    exact rv ((q7 .X21 (by simp)).trans z21)
  have s64 : stackArg st7.data 64 = (tv.getD 0 0).c1 := by
    rw [sa (o := 64) (v := .reg .X24) (by omega) (by decide)]
    exact rv ((q7 .X24 (by simp)).trans z24)
  obtain ⟨rows, -, -, -, hbb⟩ := (pre_lay h).rows
  have hfb : formsBytes ≤ busBytes := by decide
  simp only [PcOk] at hpc7
  refine acc_call h hacc hfr7 hpc7 (side := 0) (by decide) (it := .pushBlocks) rfl
    (o := 5320) (ol := 160) (by omega) (by omega) hSL
    (tables_size hbb (fwRows L) 0) hF7 fits_forms0 (reg_ptr (x := .X0) 5320 hm7' rfl) y1 y2 y3
    y4 y5 (reg_ptr (x := .X6) 160 hm7' rfl) (by omega)
    (fun _ ↦ by
      rw [s0', y7, show (3 : UInt64).toNat = 3 from rfl]
      exact ⟨loc_inOk h hfr7 le_acc (by omega), bus_apart h hfb (by omega)⟩)
    (fun _ ↦ by
      rw [s0', y7, busLayoutBytes_eq, show (3 : UInt64).toNat = 3 from rfl]
      exact loc_apart' hS (by omega) (by omega) (.inl (by omega)))
    (by
      rw [s8, s16, show (16 : UInt64).toNat = 16 from rfl]
      refine ⟨?_, ?_⟩
      · unfold SliceOk
        rw [UInt64.toBitVec_ofBitVec, show (16 : UInt64).toNat = 16 from rfl]
        exact loc_inOk h hfr7 le_acc (by omega)
      · rw [UInt64.toBitVec_ofBitVec]; exact bus_apart h hfb (by omega))
    (by rw [s40]) (by rw [s48]; exact hpsz)
    (fps := fingerprints w mem (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share
      (gpow 0) 1 1) (w := w) (beta := beta) (pt := pt) (tree := tv.getD 0 0)
    (by
      rw [s0', y7]
      have := NativeRustcVm.ewsOf_of_ewsAt kfp
      rw [fingerprints_length] at this
      rw [show (3 : UInt64).toNat = 3 from rfl, this])
    (slice_of_ewsAt (by rw [s8, UInt64.toBitVec_ofBitVec]; exact hl7.hw)
      (by rw [s16]; exact hl7.wsz.symm))
    (by rw [s24, s32])
    (slice_of_ewsAt (by rw [s40, UInt64.toBitVec_ofBitVec]; exact hl7.hpt) s48)
    (by rw [s56, s64]) fun m8 hfr8 hopt8 hF8 hfits8 hk8 hcs8 hs8 ↦ ?_
  -- after the call: the pull side
  have kl8 : KeepLoc m0 st7.data.dmem m8.dmem :=
    keepLoc_call hS hfr7.sp le_acc hs8 fun j hj hq ↦ by
      rcases hq with hq | hq
      · exact not_locs hS (o := 5320) (n := 24) (by omega)
          (fun j hj ↦ by unfold InLocs at hj; omega) j hj hq
      · exact bus_not_loc h (forms_sub hbnw hq) (o := j) (n := 1)
          (by unfold InLocs at hj; omega) (NativeRustcVm.inRange_self (by omega))
  have tc8 := keep_tc h hk8 hs8 (fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact .inl (callee_stack hS hfr7.sp le_acc hq)
    · exact .inl (loc_stack hS (by omega) hq)
    · exact .inr (forms_sub hbnw hq)) tc7.1 tc7.2
  have f : ∀ {r : XReg} {x : UInt64}, calleeSaved r = true →
      r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X29] →
      st3.data.regs.getXReg r = x → m8.regs.getXReg r = x := fun hr hm hx ↦
    (hcs8 _ hr).trans ((u _ hm).trans hx)
  exact pull_spec hp h hacc hext hfc
    { fr := hfr8, run := A.run, locs := hl7.of_keep kl8, opt := hopt8, forms := hF8,
      fits := hfits8, x19 := f rfl (by simp) z19, x20 := f rfl (by simp) z20,
      x21 := by rw [hcs8 .X21 rfl]; exact reg_ptr (x := .X21) 2824 hm7' rfl,
      x22 := f rfl (by simp) z22, x23 := f rfl (by simp) z23,
      x25 := by rw [hcs8 .X25 rfl, u .X25 (by simp)]; exact z25,
      x26 := by rw [hcs8 .X26 rfl, u .X26 (by simp)]; exact z26,
      x27 := f rfl (by simp) z27, x29 := f rfl (by simp) z29, ts := tc8.1, cl := tc8.2 }

end

end NativeRustcVmArm.Bus.VerifyBusBalance
