module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Code.Vm.BytecodeShare.Names
public import NativeRustcVmArm.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmArm.Code.Vm.Kpow.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.ClaimsB

/-!
# `verify_bus_balance`'s scalars and first claim

From `b18` (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b18Offset`), after the GKR walk: `b18` computes `memory_low`'s and `bytecode_low`'s
lengths and calls `read_scalars` for the memory's two scalars; `b19` to `b23` check it and read
the two final counters; `b24` empties the claims and pushes the first; then the other three
(`claims_spec`).
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

theorem toU64_bv (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

/-- **A call's changes keep the intervals**: below the frame, `n` bytes at `o` and the
`TState`, apart from them. -/
theorem keepIv_callT [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}
    (h : VerifyBusBalancePre a s0 L m0) {m d : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 5488) {N' : Nat} (hle : 5488 + N' ≤ verifyBusBalanceStack)
    {o n : Nat} (hon : o + n ≤ 5488)
    (hs : SameOutside m.dmem d.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨
      InRange (loc m0 o) n q ∨ InRange m0.regs.X0.toBitVec tstateBytes q))
    {ivs : List (Nat × Nat)} (hlt : ivs.all (fun p ↦ decide (p.2 ≤ 5488)) = true)
    (hd : ivs.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true) :
    KeepIv ivs m0 m.dmem d.dmem :=
  keepIv_call (pre_stack h) hsp hle hs hlt fun j hj hq ↦ by
    rcases hq with hq | hq
    · exact not_iv (pre_stack h) hon hlt hd j hj hq
    · exact loc_not_ts h (inIv_lt hlt hj) hq

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The scalars and the claims** (`b18`, `k + NativeRustcVmArm.Vm.VerifyBusBalance.b18Offset`). -/
theorem claims_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
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
    {w pt tv : Array EW} {beta : EW} {s : TState} {m : MachineData}
    (A : AtClaims a s0 L m0 w pt tv beta s m) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b18Offset)⟩ := by
  have hS := pre_stack h
  have hN := hS.2.1
  have c := ctx h
  have hlm := (pre_lay h).log_memory_le
  have hlb := (pre_lay h).log_bytecode_le
  have gp := gkr_parts A.mem'.gkr
  have hpsz := gp.2.2.2.2.2.2.2.2.2
  -- `b18`: the points' lengths, `read_scalars(t, memory, 2)`.
  have hwf1 := Bus.wf_frame hS N_ge A.fr.kept
  have hm1 := Bus.match_frame hS N_ge rfl A.fr.sp
  refine exec_then (b18_in_code.trans hp.1 (by simp [b18])) run_b18 hwf1 hm1
    fun st1 hm1' hpc1 ↦ ?_
  have hfr1 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st1.data :=
    Bus.Fr.block A.fr hN N_ge hm1' hwf1 rfl (by decide) (by decide) slots_le
  have k1 : KeepIv claimsIv m0 m.dmem st1.data.dmem :=
    keepIv_block hm1' hwf1 (sizes := [5488]) rfl (by decide) (by decide)
  have hl : (Env.ofMachine m [(base m0 5488, 5488)]).load 0 3128 8 = BitVec.ofNat 64 pt.size :=
    (Transcript.load_ofMachine rfl gp.2.2.2.2.2.2.2.1).trans (toU64_bv _)
  have hlen := ite_len hl (by omega)
  have w120 : NativeRustcVm.WordAt st1.data.dmem (loc m0 120)
      (min L.logBytecode pt.size).toUInt64 :=
    wr_eval hm1' (o := 120) (by omega)
      (.ite (.cmp .ult .W64 (.reg .X29) lenS) (.reg .X29) lenS) (by decide) (by
      rw [toU64_bv]
      exact ite_min (x := .X29) (by simp only [Env.ofMachine_regs]; exact bv_of_toNat A.x29)
        hlen (by omega) (by omega))
  have tc1 := (A.ts.frame (hm1'.kept hwf1) (fun q hq ↦ loc_not_tsw h (le_refl _)
    (written_loc (m0 := m0) (by decide) hq (by have := N_ge; omega))) (hm1'.sameOutside hwf1))
  have R1 : RegsEq [.X19, .X20, .X22, .X23, .X24, .X25, .X28, .X29] m st1.data :=
    regsEq_block hm1' (by decide)
  have z21 : st1.data.regs.getXReg .X21 = UInt64.ofBitVec (loc m0 3136) := by
    apply UInt64.toBitVec_inj.mp
    rw [hm1'.regs .X21 _ rfl, ite_ptr hl (by omega)]
    simp only [Env.ofMachine_regs]
    rw [A.x21, NativeRustcVm.addr_add_add]
  have z26 : (st1.data.regs.getXReg .X26).toNat = pt.size := by
    rw [← UInt64.toNat_toBitVec, hm1'.regs .X26 _ rfl, hlen, BitVec.toNat_ofNat]
    omega
  have z27 : st1.data.regs.getXReg .X27 = (min L.logMemory pt.size).toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    rw [hm1'.regs .X27 _ rfl, toU64_bv]
    exact ite_min (x := .X27) (by simp only [Env.ofMachine_regs]; exact bv_of_toNat A.x27) hlen
      (by omega) (by omega)
  have hat1 := Fr.at_ c hfr1 (outs_not_rc h)
  have y0 : st1.data.regs.X0 = m0.regs.X0 := (reg_of hm1' (r := .X0) (r' := .X25) rfl).trans A.x25
  have y1 : st1.data.regs.X1.toBitVec = loc m0 4144 := reg_ptr (x := .X1) 4144 hm1' rfl
  have y2 : st1.data.regs.X2.toNat = 2 := by
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm1' (r := .X2) (n := 2) rfl]; rfl
  simp only [PcOk] at hpc1
  refine Fr.callLocal (o := 4144) (n := 32)
    (X := fun q ↦ InRange (loc m0 4144) 32 q ∨ InRange m0.regs.X0.toBitVec tstateBytes q)
    hfr1 hN le_rss keep_callee (slots_lo (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hrss a s) hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq' ↦ by
      rw [y0, y1, y2] at hq'
      rcases hq' with hq' | hq' | hq'
      · exact .inr (.inl hq')
      · exact .inr (.inr hq')
      · exact .inl hq', hq.2.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · unfold ReadScalarsPre
    rw [y0, y1, y2]
    exact ⟨hfr1.stackOk hS rfl le_rss, c.rcAt hat1 le_rss, tc1, c.tstateOk hat1 le_rss,
      c.outOk hat1 le_rss (by omega)⟩
  dsimp only [ReadScalarsPost] at hq2
  rw [y0, y1, y2] at hq2
  obtain ⟨hx2, hxs2, hnx2, -, -⟩ := hq2
  have hpre := pre_tR h
  -- `b19`
  refine Fr.runBlock hS N_ge rfl hfr2 (b19_in_code.trans hp.1 (by simp [b19])) run_b19 rfl rfl
    (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hc3 : SBool.eval (Env.ofMachine m2 [(base m0 5488, 5488)])
      (.cmp .eq .W32 (.reg .X0) (.lit 0)) = !((readScalars 2).run s).isSome := by
    show CmpOp.eq.apply .W32 (m2.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = _
    rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hx2, okW_eq0]
  have hrun := A.run
  unfold tailRun at hrun
  cases hr1 : (readScalars 2).run s with
  | none =>
    exact fail_cond hp h hpc3 (by rw [hc3, hr1]; rfl) hfr3 (by rw [hrun, hr1]; rfl)
  | some p1 =>
  obtain ⟨mem, s1⟩ := p1
  rw [hr1, Option.bind_some] at hrun
  dsimp only at hrun
  have hmsz : mem.size = 2 := NativeRustcVm.Sumcheck.readScalars_size hr1
  have hmem2 := hxs2 mem s1 hr1
  have ts2 := hnx2 mem s1 hr1
  have k2 : KeepIv claimsIv m0 st1.data.dmem m2.dmem :=
    keepIv_callT h hfr1.sp le_rss (by omega) hs2 (by decide) (by decide)
  have k120 : KeepIv [(120, 128)] m0 st1.data.dmem m2.dmem :=
    keepIv_callT h hfr1.sp le_rss (by omega) hs2 (by decide) (by decide)
  have R2 : RegsEq csL st1.data m2 := regsEq_call hcs2 (by decide)
  -- `b20`: `read_scalar` for `memory_final`.
  have R3 : RegsEq csL m2 st3.data := regsEq_block hm3 (by decide)
  refine at_pc (pass_cond hpc3 (by rw [hc3, hr1]; rfl)) (exec_then
    (b20_in_code.trans hp.1 (by simp [b20])) run_b20 (Bus.wf_frame hS N_ge hfr3.kept)
    (Bus.match_frame hS N_ge rfl hfr3.sp) fun st4 hm4 hpc4 ↦ ?_)
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq (Bus.wf_frame hS N_ge hfr3.kept) rfl
  have hfr4 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st4.data :=
    Bus.Fr.block hfr3 hN N_ge hm4 (Bus.wf_frame hS N_ge hfr3.kept) rfl (by decide) (by decide)
      slots_le
  have R4 : RegsEq csL st3.data st4.data := regsEq_block hm4 (by decide)
  simp only [PcOk] at hpc4
  have g3 : ∀ r, r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X28, .X29] →
      st4.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    have hc : r ∈ csL := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h' | h' | h' | h' | h' | h' | h' | h' <;> simp [h']
    (R4 r hc).trans ((R3 r hc).trans ((R2 r hc).trans (R1 r hr)))
  refine rs_call h hrs hfr4 hpc4 (reg_ptr (x := .X0) 4176 hm4 rfl)
    ((reg_of hm4 (r := .X1) (r' := .X25) rfl).trans ((R3 .X25 (by simp)).trans
      ((R2 .X25 (by simp)).trans ((R1 .X25 (by simp)).trans A.x25))))
    (by rw [hd4, hd3]; exact ts2) fun m5 hfr5 hopt5 hnx5 hk5 hcs5 hs5 ↦ ?_
  -- `b21`: `memory_final`'s tag.
  have k5a : KeepIv [(120, 4176)] m0 st4.data.dmem m5.dmem :=
    keepIv_callT h hfr4.sp le_rs (by omega) hs5 (by decide) (by decide)
  have R5 : RegsEq csL st4.data m5 := regsEq_call hcs5 (by decide)
  refine Fr.runBlock hS N_ge rfl hfr5 (b21_in_code.trans hp.1 (by simp [b21])) run_b21 rfl rfl
    (by decide) (by decide) fun st6 hfr6 hd6 hm6 hpc6 ↦ ?_
  have R6 : RegsEq csL m5 st6.data := regsEq_block hm6 (by decide)
  cases hr2 : readScalar.run s1 with
  | none =>
    rw [hr2] at hopt5
    refine fail_cond hp h hpc6 ?_ hfr6 (by rw [hrun, hr2]; rfl)
    show (!(low .W32 ((Env.ofMachine m5 [(base m0 5488, 5488)]).load 0 4176 4)).getLsbD 0) = true
    rw [Transcript.load4_of_tag (w := 0) (.inl rfl)
      (show NativeRustcVm.WordAt m5.dmem (loc m0 4176) 0 from hopt5)]
    rfl
  | some p2 =>
  obtain ⟨mf, s2⟩ := p2
  rw [hr2] at hopt5 hnx5
  rw [hr2, Option.bind_some] at hrun
  dsimp only at hrun
  have ts5 := hnx5 mf s2 rfl
  obtain ⟨o5a, o5b⟩ := hopt5
  obtain ⟨e5a, e5b⟩ := NativeRustcVm.ewAt_iff.mp o5b
  have hc6 : SBool.eval (Env.ofMachine m5 [(base m0 5488, 5488)])
      (.not (.bit .W32 (.load 0 4176 4) 0)) = false := by
    show (!(low .W32 ((Env.ofMachine m5 [(base m0 5488, 5488)]).load 0 4176 4)).getLsbD 0) = false
    rw [Transcript.load4_of_tag (w := 1) (.inr rfl) o5a]
    rfl
  -- `b22`: `memory_final` kept; `read_scalar` for `bytecode_final`.
  have hwf7 := Bus.wf_frame hS N_ge hfr6.kept
  refine at_pc (pass_cond hpc6 hc6) (exec_then (b22_in_code.trans hp.1 (by simp [b22])) run_b22
    hwf7 (Bus.match_frame hS N_ge rfl hfr6.sp) fun st7 hm7 hpc7 ↦ ?_)
  have hfr7 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st7.data :=
    Bus.Fr.block hfr6 hN N_ge hm7 hwf7 rfl (by decide) (by decide) slots_le
  have R7 : RegsEq csL st6.data st7.data := regsEq_block hm7 (by decide)
  have k7 : KeepIv [(120, 4176)] m0 st6.data.dmem st7.data.dmem :=
    keepIv_block hm7 hwf7 (sizes := [5488]) rfl (by decide) (by decide)
  have w112 : NativeRustcVm.WordAt st7.data.dmem (loc m0 112) mf.c0 :=
    wr_eval hm7 (o := 112) (by omega) (.load 0 4184 8) (by decide) (by
      show (Env.ofMachine st6.data _).load 0 4184 8 = _
      refine Transcript.load_ofMachine rfl ?_
      rw [hd6]; simpa only [off, NativeRustcVm.addr_add_add] using e5a)
  have w104 : NativeRustcVm.WordAt st7.data.dmem (loc m0 104) mf.c1 :=
    wr_eval hm7 (o := 104) (by omega) (.load 0 4192 8) (by decide) (by
      show (Env.ofMachine st6.data _).load 0 4192 8 = _
      refine Transcript.load_ofMachine rfl ?_
      rw [hd6]; simpa only [off, NativeRustcVm.addr_add_add] using e5b)
  have ts7 : TStateAt st7.data.dmem m0.regs.X0.toBitVec a s2 :=
    (show TStateAt st6.data.dmem _ a s2 by rw [hd6]; exact ts5).frame (hm7.kept hwf7)
      (fun q hq ↦ loc_not_tsw h (le_refl _)
        (written_loc (m0 := m0) (by decide) hq (by have := N_ge; omega))) (hm7.sameOutside hwf7)
  simp only [PcOk] at hpc7
  refine rs_call h hrs hfr7 hpc7 (reg_ptr (x := .X0) 4176 hm7 rfl)
    ((reg_of hm7 (r := .X1) (r' := .X25) rfl).trans ((R6 .X25 (by simp)).trans
      ((R5 .X25 (by simp)).trans ((g3 .X25 (by simp)).trans A.x25))))
    ts7 fun m8 hfr8 hopt8 hnx8 hk8 hcs8 hs8 ↦ ?_
  have k8 : KeepIv [(104, 4176)] m0 st7.data.dmem m8.dmem :=
    keepIv_callT h hfr7.sp le_rs (by omega) hs8 (by decide) (by decide)
  have R8 : RegsEq csL st7.data m8 := regsEq_call hcs8 (by decide)
  -- `b23`: `bytecode_final`'s tag.
  refine Fr.runBlock hS N_ge rfl hfr8 (b23_in_code.trans hp.1 (by simp [b23])) run_b23 rfl rfl
    (by decide) (by decide) fun st9 hfr9 hd9 hm9 hpc9 ↦ ?_
  have R9 : RegsEq csL m8 st9.data := regsEq_block hm9 (by decide)
  cases hr3 : readScalar.run s2 with
  | none =>
    rw [hr3] at hopt8
    refine fail_cond hp h hpc9 ?_ hfr9 (by rw [hrun, hr3]; rfl)
    show (!(low .W32 ((Env.ofMachine m8 [(base m0 5488, 5488)]).load 0 4176 4)).getLsbD 0) = true
    rw [Transcript.load4_of_tag (w := 0) (.inl rfl)
      (show NativeRustcVm.WordAt m8.dmem (loc m0 4176) 0 from hopt8)]
    rfl
  | some p3 =>
  obtain ⟨bf, s3⟩ := p3
  rw [hr3] at hopt8 hnx8
  rw [hr3, Option.bind_some] at hrun
  dsimp only at hrun
  have ts8 := hnx8 bf s3 rfl
  obtain ⟨o8a, o8b⟩ := hopt8
  obtain ⟨e8a, e8b⟩ := NativeRustcVm.ewAt_iff.mp o8b
  have hc9 : SBool.eval (Env.ofMachine m8 [(base m0 5488, 5488)])
      (.not (.bit .W32 (.load 0 4176 4) 0)) = false := by
    show (!(low .W32 ((Env.ofMachine m8 [(base m0 5488, 5488)]).load 0 4176 4)).getLsbD 0) = false
    rw [Transcript.load4_of_tag (w := 1) (.inr rfl) o8a]
    rfl
  -- `b24`: `bytecode_final` kept, the claims emptied; `push_claim` of the first.
  have hcl := pre_cl h
  have hwf10 : (Env.ofMachine st9.data
      [(base m0 5488, 5488), (m0.regs.X5.toBitVec, 97288)]).WF :=
    Bus.wf_frame2 hS N_ge hfr9.kept ⟨hcl.1, hcl.2.1⟩ hcl.2.2.2.2.1
  have q28 : (st9.data.regs.getXReg .X28).toBitVec = m0.regs.X5.toBitVec := by
    rw [R9 .X28 (by simp), R8 .X28 (by simp), R7 .X28 (by simp), R6 .X28 (by simp),
      R5 .X28 (by simp), g3 .X28 (by simp), A.x28]
  have hm10 := match_frameW (n := 97288) hS N_ge rfl hfr9.sp (r := .X28) q28
  refine at_pc (pass_cond hpc9 hc9) (exec_then (b24_in_code.trans hp.1 (by simp [b24])) run_b24
    hwf10 hm10 fun st10 hm10' hpc10 ↦ ?_)
  have hfr10 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st10.data :=
    Fr.ofBlockW hfr9 hm10 hm10' hwf10 rfl rfl (fun r hr ↦ by simp at hr) rfl N_ge hN slots_le
      (writeOk_cl (by decide))
  have k10 : KeepIv [(104, 4176)] m0 st9.data.dmem st10.data.dmem :=
    keepIv_block hm10' hwf10 (sizes := [5488, 97288]) rfl (by decide) (by decide)
  have R10 : RegsEq [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] st9.data
      st10.data := regsEq_block hm10' (by decide)
  have ld : ∀ {o : Nat} {v : UInt64}, NativeRustcVm.WordAt m8.dmem (loc m0 o) v →
      (Env.ofMachine st9.data [(base m0 5488, 5488), (m0.regs.X5.toBitVec, 97288)]).load 0 o 8 =
        v.toBitVec := fun hw ↦ Transcript.load_ofMachine rfl (by rw [hd9]; exact hw)
  have w96 : NativeRustcVm.WordAt st10.data.dmem (loc m0 96) bf.c0 :=
    wr_eval hm10' (o := 96) (by omega) (.load 0 4184 8) (by decide)
      (ld (by simpa only [off, NativeRustcVm.addr_add_add] using e8a))
  have w88 : NativeRustcVm.WordAt st10.data.dmem (loc m0 88) bf.c1 :=
    wr_eval hm10' (o := 88) (by omega) (.load 0 4192 8) (by decide)
      (ld (by simpa only [off, NativeRustcVm.addr_add_add] using e8b))
  have cl10 : ClaimsWAt st10.data.dmem m0.regs.X5.toBitVec #[] := by
    have := Transcript.wordAt_write hm10' (r := 1) (o := 0) rfl (by decide) (v := .lit 0)
      (by decide)
    refine ⟨by simp [claimCap], ?_, fun i h' ↦ absurd h' (by simp)⟩
    rw [show off m0.regs.X5.toBitVec 0 = m0.regs.X5.toBitVec from Bus.add_zero' _] at this
    exact this
  have ts10 : TStateAt st10.data.dmem m0.regs.X0.toBitVec a s3 :=
    (show TStateAt st9.data.dmem _ a s3 by rw [hd9]; exact ts8).frame (hm10'.kept hwf10)
      (fun q hq ↦ by
        rcases written_fc h (by decide) hq with hq | hq
        · exact loc_not_tsw h (le_refl _) hq
        · exact cl_not_tsw h hq) (hm10'.sameOutside hwf10)
  -- the locals
  have kA : KeepIv [(120, 4144)] m0 st1.data.dmem m2.dmem :=
    keepIv_callT h hfr1.sp le_rss (by omega) hs2 (by decide) (by decide)
  have kB : KeepIv [(120, 4176)] m0 m2.dmem st9.data.dmem :=
    ((((((KeepIv.rfl' hd3).trans (KeepIv.rfl' hd4)).trans k5a).trans
      (KeepIv.rfl' hd6)).trans k7).trans (k8.mono (ivSub (by decide)))).trans (KeepIv.rfl' hd9)
  have kC : KeepIv [(120, 4176)] m0 m2.dmem st10.data.dmem :=
    kB.trans (k10.mono (ivSub (by decide)))
  have kD : KeepIv [(104, 4176)] m0 st7.data.dmem st10.data.dmem :=
    (k8.trans (KeepIv.rfl' hd9)).trans k10
  have cm : ClaimsMem m0 L w pt tv beta st10.data.dmem :=
    ((A.mem'.of_keep k1).of_keep (kA.mono (ivSub (by decide)))).of_keep
      (kC.mono (ivSub (by decide)))
  have hmem10 : NativeRustcVm.EWsAt st10.data.dmem (loc m0 4144) mem.toList :=
    NativeRustcVm.Tables.EWsAt.of_same hmem2 (kC.sameIn (lo := 120) (hi := 4176) (by simp)
      (o := 4144) (n := 32) (by omega) (by omega)) (by rw [Array.length_toList, hmsz])
  have wd : ∀ {d d' : Mem 64} {ivs : List (Nat × Nat)} {lo hi o : Nat} {v : UInt64},
      KeepIv ivs m0 d d' → (lo, hi) ∈ ivs → lo ≤ o → o + 8 ≤ hi →
      NativeRustcVm.WordAt d (loc m0 o) v → NativeRustcVm.WordAt d' (loc m0 o) v :=
    fun hk hm h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn hm h1 h2) le_rfl
  have g10 : ∀ r, r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X29] →
      st10.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
    have hc : r ∈ csL := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h' | h' | h' | h' | h' | h' | h' <;> simp [h']
    have hc' : r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h' | h' | h' | h' | h' | h' | h' <;> simp [h']
    have hc'' : r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X28, .X29] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h' | h' | h' | h' | h' | h' | h' <;> simp [h']
    rw [R10 r hc', R9 r hc, R8 r hc, R7 r hc, R6 r hc, R5 r hc, g3 r hc'']
  have f : ∀ r, r ∈ [XReg.X21, .X26, .X27] →
      st10.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hr ↦ by
    have hc : r ∈ csL := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h' | h' | h' <;> simp [h']
    have hc' : r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h' | h' | h' <;> simp [h']
    rw [R10 r hc', R9 r hc, R8 r hc, R7 r hc, R6 r hc, R5 r hc, R4 r hc, R3 r hc, R2 r hc]
  have x28' : st10.data.regs.getXReg .X28 = m0.regs.X5 :=
    UInt64.toBitVec_inj.mp (by rw [hm10'.regs .X28 _ rfl, eval_ptr_off rfl]; simp)
  have C : ClSt L m0 w pt tv mem beta mf bf a s3 #[] st10.data :=
    ⟨hfr10, cm, hmem10, hmsz, w88, w96,
      wd (lo := 104) (hi := 4176) kD (by simp) (by omega) (by omega) w104,
      wd (lo := 104) (hi := 4176) kD (by simp) (by omega) (by omega) w112,
      wd (lo := 120) (hi := 128) ((kA.mono (ivSub (ivs' := [(120, 128)]) (by decide))).trans
        (kC.mono (ivSub (by decide)))) (by simp) (by omega) (by omega) w120,
      (g10 .X19 (by simp)).trans A.x19, (g10 .X20 (by simp)).trans A.x20,
      (f .X21 (by simp)).trans z21, (g10 .X22 (by simp)).trans A.x22,
      (g10 .X23 (by simp)).trans A.x23, (g10 .X24 (by simp)).trans A.x24,
      (g10 .X25 (by simp)).trans A.x25, by rw [f .X26 (by simp)]; exact z26,
      (f .X27 (by simp)).trans z27, x28', by rw [g10 .X29 (by simp)]; exact A.x29, ts10, cl10⟩
  have hmem9 : NativeRustcVm.EWsAt st9.data.dmem (loc m0 4144) mem.toList :=
    NativeRustcVm.Tables.EWsAt.of_same hmem2 (kB.sameIn (lo := 120) (hi := 4176) (by simp)
      (o := 4144) (n := 32) (by omega) (by omega)) (by rw [Array.length_toList, hmsz])
  have g0 := ew_get hmem9 (i := 0) (by omega)
  simp only [PcOk] at hpc10
  refine C.push h hpcl (by simp [claimCap]) hpc10 (j := L.logMemory) (id := 0)
    (v := mem.getD 0 0) hlm
    (UInt64.toBitVec_inj.mp (by
      rw [show st10.data.regs.X0 = st10.data.regs.getXReg .X0 from rfl, hm10'.regs .X0 _ rfl,
        eval_ptr_off rfl]; simp))
    (by rw [show st10.data.regs.X1 = st10.data.regs.getXReg .X1 from rfl,
      ← UInt64.toNat_toBitVec, reg_lit hm10' (r := .X1) (n := 0) rfl]; rfl)
    ((reg_of hm10' (r := .X2) (r' := .X21) rfl).trans ((R10 .X21 (by simp)).symm.trans C.x21))
    ((reg_of hm10' (r := .X3) (r' := .X27) rfl).trans ((R10 .X27 (by simp)).symm.trans C.x27))
    (reg_ld' (x := .X4) hm10' rfl g0.1) (reg_ld' (x := .X5) hm10' rfl g0.2)
    fun m11 A11 hx11 ↦ claimsC_spec hp h hpcl hbs hcbv hkp hacc hext hfc hrun A11 hx11
end

end NativeRustcVmArm.Bus.VerifyBusBalance
