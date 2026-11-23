module

public import NativeRustcVmArm.Code.Vm.BusLayout.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.HeadCalls

/-!
# `verify_bus_balance`'s three layouts

From the entry: `b0` saves the registers, writes the framework sizes at `136` and calls
`bus_layout` on the push side; `b1` checks it; `b2` and `b3` move it to `160` (`memcpy`, its
depth stored) and call `bus_layout` on the pull side; `b4`, `b5` move it to `1048`; `b6` calls
`bus_layout` on the count side; `b7`, `b8` move it to `1936`; `b9` checks the push side's depth
(`head_spec`, then `AtGrind`).
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- The registers the head keeps values in. -/
abbrev csH : List XReg := [.X19, .X20, .X23, .X24, .X25, .X27, .X28, .X29]

/-- With the push side's depth. -/
abbrev csK : List XReg := [.X19, .X20, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

variable {m0 : MachineData}

/-- A call's changes keep the intervals: below the frame and `n` bytes of it at `o`. -/
theorem keepIv_callL {m d : MachineData} (hS : StackOk m0 verifyBusBalanceStack)
    (hsp : m.regs.SP.toBitVec = base m0 5488) {N' : Nat} (hle : 5488 + N' ≤ verifyBusBalanceStack)
    {o n : Nat} (hon : o + n ≤ 5488)
    (hs : SameOutside m.dmem d.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨
      InRange (loc m0 o) n q))
    {ivs : List (Nat × Nat)} (hlt : ivs.all (fun p ↦ decide (p.2 ≤ 5488)) = true)
    (hd : ivs.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true) :
    KeepIv ivs m0 m.dmem d.dmem :=
  keepIv_call hS hsp hle hs hlt (not_iv hS hon hlt hd)

/-- A word of the frame kept. -/
theorem KeepIv.word {ivs : List (Nat × Nat)} {d d' : Mem 64} (hk : KeepIv ivs m0 d d')
    {lo hi o : Nat} (hm : (lo, hi) ∈ ivs) (h1 : lo ≤ o) (h2 : o + 8 ≤ hi) {v : UInt64}
    (hw : NativeRustcVm.WordAt d (loc m0 o) v) : NativeRustcVm.WordAt d' (loc m0 o) v :=
  NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn hm h1 h2) le_rfl

/-- A side's layout in the frame kept. -/
theorem KeepIv.blw {ivs : List (Nat × Nat)} {d d' : Mem 64} (hk : KeepIv ivs m0 d d')
    {lo hi o : Nat} (hm : (lo, hi) ∈ ivs) (h1 : lo ≤ o) (h2 : o + 888 ≤ hi) {BL : BusLayoutW}
    (hb : BusLayoutWAt d (loc m0 o) BL) : BusLayoutWAt d' (loc m0 o) BL :=
  BusLayoutWAt.of_same hb (hk.sameIn hm h1 h2)

/-- A callee's stack below the frame, as a number. -/
theorem stk_toNat (hS : StackOk m0 verifyBusBalanceStack) {m : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 5488) {N' : Nat}
    (hle : 5488 + N' ≤ verifyBusBalanceStack) :
    (stackBelow m N').toNat = m0.regs.SP.toNat - 5488 - N' := by
  have hN := hS.2.1
  unfold stackBelow
  rw [hsp, NativeRustcVm.toNat_sub_ofNat (by rw [base_toNat (by omega)]; omega),
    base_toNat (by omega)]

/-- The push and pull sides' framework sizes. -/
theorem fw_nats {m : MachineData} {L : LayoutW} {x1 x2 : UInt64}
    (h1 : x1.toBitVec = loc m0 136) (h2 : x2.toNat = 3)
    (w0 : NativeRustcVm.WordAt m.dmem (loc m0 136) 0)
    (w1 : NativeRustcVm.WordAt m.dmem (loc m0 144) L.logMemory.toUInt64)
    (w2 : NativeRustcVm.WordAt m.dmem (loc m0 152) L.logBytecode.toUInt64)
    (hm : L.logMemory ≤ 30) (hb : L.logBytecode ≤ 30) : natsOf m x1 x2.toNat = fwRows L := by
  have hw : NativeRustcVm.WordsAt m.dmem (loc m0 136)
      [0, L.logMemory.toUInt64, L.logBytecode.toUInt64] :=
    NativeRustcVm.wordsAt_cons_iff.mpr ⟨w0, NativeRustcVm.wordsAt_cons_iff.mpr
      ⟨by rw [NativeRustcVm.addr_add_add]; exact w1, NativeRustcVm.wordsAt_cons_iff.mpr
        ⟨by rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]; exact w2,
          NativeRustcVm.wordsAt_nil _ _⟩⟩⟩
  have e : NativeRustcVm.wordsOf m.dmem (loc m0 136) 3 =
      [0, L.logMemory.toUInt64, L.logBytecode.toUInt64] := NativeRustcVm.wordsOf_of_wordsAt hw
  have e1 : L.logMemory.toUInt64.toNat = L.logMemory :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have e2 : L.logBytecode.toUInt64.toNat = L.logBytecode :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  unfold natsOf
  rw [h1, h2, e]
  simp only [List.map_cons, List.map_nil, e1, e2, fwRows]
  rfl

end

public section
variable [Labels] {m0 : MachineData}

/-- A register a block loaded from the second region's byte `o`. -/
theorem reg_ld1 {m m' : MachineData} {b : BitVec 64} {n : Nat} {S : SState} {x : XReg} {o : Nat}
    (hm : Match (Env.ofMachine m [(base m0 5488, 5488), (b, n)]) S m')
    (hx : S.reg x = some (.load 1 o 8)) {w : UInt64}
    (hw : NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) w) : m'.regs.getXReg x = w :=
  UInt64.toBitVec_inj.mp ((hm.regs x _ hx).trans (Transcript.load_ofMachine rfl hw))

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The three layouts** (`b0` to `b9`): the state at `b10`, or the failure. -/
theorem head_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hbl : ∀ L bl, Spec (Labels.label NativeRustcVmArm.Vm.BusLayout.entryLabel) (BusLayoutPre L bl) (BusLayoutPost L bl))
    (hmc : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hg : ∀ m, AtGrind a s0 L m0 m →
      Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b10Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b0Offset)⟩ := by
  have hS := pre_stack h
  have hN : verifyBusBalanceStack ≤ m0.regs.SP.toNat := hS.2.1
  have hNv := N_eq
  have hlo := pre_layOk h
  have hlay := pre_lay h
  have hlm := hlay.log_memory_le
  have hlb := hlay.log_bytecode_le
  obtain ⟨rows, -, -, -, hrows⟩ := hlay.rows
  have hob : optBusLayoutBytes = 896 := rfl
  -- `b0`: the prologue, the framework sizes; `bus_layout` of the push side.
  have hwf0 : (Env.ofMachine m0 [(base m0 5488, 5488), (m0.regs.X1.toBitVec, 3912)]).WF :=
    Bus.wf_frame2 hS N_ge (fun _ h ↦ h) hlo.1 hlo.2
  have hm0 : Match (Env.ofMachine m0 [(base m0 5488, 5488), (m0.regs.X1.toBitVec, 3912)])
      entryS m0 :=
    match_ofMachine (sregions := [(5488, true), (3912, false)])
      (regions := [(base m0 5488, 5488), (m0.regs.X1.toBitVec, 3912)])
      ⟨rfl, fun _ ↦ Bus.base_aligned hS N_ge rfl, rfl, nofun, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]
          rw [show BitVec.ofInt 64 5488 = BitVec.ofNat 64 5488 from rfl]
          exact base_add_eq.symm)
      ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st1.data :=
    Fr.ofPrologueW hN N_ge hm1 hwf0 rfl (by decide) slots_le (writeOk_frame (by decide))
      (fun r hr ↦ by simp at hr)
  have lm0 : NativeRustcVm.WordAt m0.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 0)
      L.logMemory.toUInt64 := by rw [Bus.add_zero']; exact hlay.log_memory
  have w136 : NativeRustcVm.WordAt st1.data.dmem (loc m0 136) 0 :=
    wr_eval hm1 (o := 136) (by omega) (.lit 0) (by decide) rfl
  have w144 : NativeRustcVm.WordAt st1.data.dmem (loc m0 144) L.logMemory.toUInt64 :=
    wr_eval hm1 (o := 144) (by omega) (.load 1 0 8) (by decide)
      (Transcript.load_ofMachine rfl lm0)
  have w152 : NativeRustcVm.WordAt st1.data.dmem (loc m0 152) L.logBytecode.toUInt64 :=
    wr_eval hm1 (o := 152) (by omega) (.load 1 8 8) (by decide)
      (Transcript.load_ofMachine rfl hlay.log_bytecode)
  have ts1 := ts_block h hm1 hwf0 (by decide) (pre_ts h)
  have e19 : st1.data.regs.getXReg .X19 = m0.regs.X4 := reg_of hm1 (r' := .X4) rfl
  have e20 : st1.data.regs.getXReg .X20 = m0.regs.X1 :=
    UInt64.toBitVec_inj.mp (by rw [hm1.regs .X20 _ rfl, eval_ptr_off rfl]; simp)
  have e23 : st1.data.regs.getXReg .X23 = m0.regs.X3 := reg_of hm1 (r' := .X3) rfl
  have e24 : st1.data.regs.getXReg .X24 = m0.regs.X2 := reg_of hm1 (r' := .X2) rfl
  have e25 : st1.data.regs.getXReg .X25 = m0.regs.X0 := reg_of hm1 (r' := .X0) rfl
  have e27 : st1.data.regs.getXReg .X27 = L.logMemory.toUInt64 := reg_ld1 hm1 rfl lm0
  have e28 : st1.data.regs.getXReg .X28 = m0.regs.X5 := reg_of hm1 (r' := .X5) rfl
  have e29 : st1.data.regs.getXReg .X29 = L.logBytecode.toUInt64 :=
    reg_ld1 hm1 rfl hlay.log_bytecode
  have e21 : (st1.data.regs.getXReg .X21).toBitVec = loc m0 4176 := reg_ptr 4176 hm1 rfl
  have y1 : st1.data.regs.X1.toBitVec = loc m0 136 := reg_ptr (x := .X1) 136 hm1 rfl
  have y2 : st1.data.regs.X2.toNat = 3 := by
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm1 (r := .X2) (n := 3) rfl]; rfl
  simp only [PcOk] at hpc1
  refine bl_call h hbl hfr1 hpc1 (side := 0) (it := .pushBlocks) rfl (by decide) (by decide)
    (by decide +kernel) hrows (fw_nats y1 y2 w136 w144 w152 hlm hlb) (by omega)
    (fun s hs ↦ by simp [fwRows] at hs; rcases hs with rfl | rfl | rfl <;> omega)
    (by rw [y1, y2]; exact loc_inOk h hfr1 le_bl (by omega))
    (by rw [y1, y2]; unfold Apart
        rw [loc_toNat hS (o := 4176) (by omega), loc_toNat hS (o := 136) (by omega), hob]
        omega)
    (reg_ptr (x := .X0) 4176 hm1 rfl)
    (by rw [show st1.data.regs.X3 = st1.data.regs.getXReg .X3 from rfl, hm1.regs .X3 _ rfl]; rfl)
    (by rw [show st1.data.regs.X4 = st1.data.regs.getXReg .X4 from rfl,
      ← UInt64.toNat_toBitVec, hm1.regs .X4 _ rfl]; rfl)
    (by rw [show st1.data.regs.X5 = st1.data.regs.getXReg .X5 from rfl]
        exact UInt64.toBitVec_inj.mp (by rw [hm1.regs .X5 _ rfl, eval_ptr_off rfl]; simp))
    fun m2 hfr2 ho2 hk2 hcs2 hs2 ↦ ?_
  have hP2 : BusLayoutWAt m2.dmem (loc m0 4184) (pushL L) := by
    have := ho2.2
    simp only [off, NativeRustcVm.addr_add_add] at this
    exact this
  have kf2 : KeepIv [(136, 160)] m0 st1.data.dmem m2.dmem :=
    keepIv_callL hS hfr1.sp le_bl (by rw [hob]; omega) hs2 (by decide) (by decide)
  have ts2 := ts_call h hfr1 le_bl (by rw [hob]; omega) hk2 hs2 ts1
  have R2 : RegsEq csH st1.data m2 := regsEq_call hcs2 (by decide)
  have f21 : (m2.regs.getXReg .X21).toBitVec = loc m0 4176 := by rw [hcs2 .X21 rfl]; exact e21
  -- `b1`: the push side's tag.
  refine Fr.runBlock hS N_ge rfl hfr2 (b1_in_code.trans hp.1 (by simp [b1])) run_b1 rfl rfl
    (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hc3 : SBool.eval (Env.ofMachine m2 [(base m0 5488, 5488)])
      (.cmp .eq .W64 (.load 0 4176 8) (.lit 0)) = false := by
    show CmpOp.apply .eq .W64 ((Env.ofMachine m2 [(base m0 5488, 5488)]).load 0 4176 8)
      (BitVec.ofNat 64 0) = false
    rw [Transcript.load_ofMachine rfl ho2.1]
    rfl
  have R3 : RegsEq csK m2 st3.data := regsEq_block hm3 (by decide)
  have g21 : (st3.data.regs.getXReg .X21).toBitVec = loc m0 4176 := by
    rw [reg_of hm3 (r := .X21) (r' := .X21) rfl]; exact f21
  -- `b2`: `memcpy` of the push side's layout to `168`.
  refine at_pc (pass_cond hpc3 hc3) (Fr.runBlock hS N_ge rfl hfr3
    (b2_in_code.trans hp.1 (by simp [b2])) run_b2 rfl rfl (by decide) (by decide)
    fun st4 hfr4 hd4 hm4 hpc4 ↦ ?_)
  have hdep4 : st4.data.regs.getXReg .X26 = (pushL L).depth.toUInt64 :=
    reg_ld' hm4 rfl (by rw [hd3]; exact hP2.depth)
  have R4 : RegsEq csH st3.data st4.data := regsEq_block hm4 (by decide)
  simp only [PcOk] at hpc4
  refine mc_call h hmc hfr4 hpc4 (dst := 168) (src := 4192) (n := 880) (by omega) (by omega)
    (by omega) (reg_ptr (x := .X0) 168 hm4 rfl)
    (reg_add (x := .X1) (o := 4176) (c := 16) hm4 rfl g21)
    (by rw [show st4.data.regs.X2 = st4.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm4 (r := .X2) (n := 880) rfl]; rfl)
    fun m5 hfr5 hb5 hk5 hcs5 hs5 ↦ ?_
  have kf5 : KeepIv [(136, 160)] m0 st4.data.dmem m5.dmem :=
    keepIv_callL hS hfr4.sp le_mem (by omega) hs5 (by decide) (by decide)
  have ts5 := ts_call h hfr4 le_mem (by omega) hk5 hs5
    (by rw [hd4, hd3]; exact ts2)
  have R5 : RegsEq csK st4.data m5 := regsEq_call hcs5 (by decide)
  -- `b3`: the push side's depth at `160`; `bus_layout` of the pull side.
  have hwf6 := Bus.wf_frame hS N_ge hfr5.kept
  refine exec_then (b3_in_code.trans hp.1 (by simp [b3])) run_b3 hwf6
    (Bus.match_frame hS N_ge rfl hfr5.sp) fun st6 hm6 hpc6 ↦ ?_
  have hfr6 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st6.data :=
    Bus.Fr.block hfr5 hN N_ge hm6 hwf6 rfl (by decide) (by decide) slots_le
  have kf6 : KeepIv [(136, 160)] m0 m5.dmem st6.data.dmem :=
    keepIv_block hm6 hwf6 (sizes := [5488]) rfl (by decide) (by decide)
  have ts6 := ts_block h hm6 hwf6 (by decide) ts5
  have R6 : RegsEq csK m5 st6.data := regsEq_block hm6 (by decide)
  have w160 : NativeRustcVm.WordAt st6.data.dmem (loc m0 160) (pushL L).depth.toUInt64 :=
    wr_eval hm6 (o := 160) (by omega) (.reg .X26) (by decide) (by
      show (m5.regs.getXReg .X26).toBitVec = _
      rw [hcs5 .X26 rfl, hdep4])
  have hc6 : NativeRustcVm.BytesAt st6.data.dmem (loc m0 168)
      (bytesOf st4.data.dmem (loc m0 4192) 880) :=
    keep_out hm6 hwf6 (sizes := [5488]) rfl (lo := 160) (hi := 168) (by decide)
      (by simp [NativeRustcArm.bytesOf]) (.inr (le_refl _)) hb5
  have hP6 : BusLayoutWAt st6.data.dmem (loc m0 160) (pushL L) :=
    blw_copy (d := st4.data.dmem) (a := loc m0 4184) (by rw [hd4, hd3]; exact hP2) w160 (by
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]; exact hc6)
  have kfA : KeepIv [(136, 160)] m0 st1.data.dmem st6.data.dmem :=
    (((kf2.trans (KeepIv.rfl' hd3)).trans (KeepIv.rfl' hd4)).trans kf5).trans kf6
  have g21' : (st6.data.regs.getXReg .X21).toBitVec = loc m0 4176 := reg_ptr 4176 hm6 rfl
  have z1 : st6.data.regs.X1.toBitVec = loc m0 136 := reg_ptr (x := .X1) 136 hm6 rfl
  have z2 : st6.data.regs.X2.toNat = 3 := by
    rw [show st6.data.regs.X2 = st6.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm6 (r := .X2) (n := 3) rfl]; rfl
  have RA : RegsEq csH st1.data st6.data := fun r hr ↦ by
    have hr' : r ∈ csK := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h' | h' | h' | h' | h' | h' | h' | h' <;> simp [h']
    rw [R6 r hr', R5 r hr', R4 r hr, R3 r hr', R2 r hr]
  simp only [PcOk] at hpc6
  refine bl_call h hbl hfr6 hpc6 (side := 1) (it := .pullBlocks) rfl (by decide) (by decide)
    (by decide +kernel) hrows
    (fw_nats z1 z2 (kfA.word (lo := 136) (hi := 160) (by simp) (by omega) (by omega) w136)
      (kfA.word (lo := 136) (hi := 160) (by simp) (by omega) (by omega) w144)
      (kfA.word (lo := 136) (hi := 160) (by simp) (by omega) (by omega) w152) hlm hlb)
    (by omega)
    (fun s hs ↦ by simp [fwRows] at hs; rcases hs with rfl | rfl | rfl <;> omega)
    (by rw [z1, z2]; exact loc_inOk h hfr6 le_bl (by omega))
    (by rw [z1, z2]; unfold Apart
        rw [loc_toNat hS (o := 4176) (by omega), loc_toNat hS (o := 136) (by omega), hob]
        omega)
    (reg_ptr (x := .X0) 4176 hm6 rfl)
    (by rw [show st6.data.regs.X3 = st6.data.regs.getXReg .X3 from rfl, hm6.regs .X3 _ rfl]; rfl)
    (by rw [show st6.data.regs.X4 = st6.data.regs.getXReg .X4 from rfl,
      ← UInt64.toNat_toBitVec, hm6.regs .X4 _ rfl]; rfl)
    ((reg_of hm6 (r := .X5) (r' := .X20) rfl).trans ((R6 .X20 (by simp)).symm.trans
      ((RA .X20 (by simp)).trans e20)))
    fun m7 hfr7 ho7 hk7 hcs7 hs7 ↦ ?_
  have hQ7 : BusLayoutWAt m7.dmem (loc m0 4184) (pullL L) := by
    have := ho7.2
    simp only [off, NativeRustcVm.addr_add_add] at this
    exact this
  have kp7 : KeepIv [(160, 1048)] m0 st6.data.dmem m7.dmem :=
    keepIv_callL hS hfr6.sp le_bl (by rw [hob]; omega) hs7 (by decide) (by decide)
  have ts7 := ts_call h hfr6 le_bl (by rw [hob]; omega) hk7 hs7 ts6
  have R7 : RegsEq csK st6.data m7 := regsEq_call hcs7 (by decide)
  have f21' : (m7.regs.getXReg .X21).toBitVec = loc m0 4176 := by rw [hcs7 .X21 rfl]; exact g21'
  -- `b4`: the pull side's tag.
  refine Fr.runBlock hS N_ge rfl hfr7 (b4_in_code.trans hp.1 (by simp [b4])) run_b4 rfl rfl
    (by decide) (by decide) fun st8 hfr8 hd8 hm8 hpc8 ↦ ?_
  have hc8 : SBool.eval (Env.ofMachine m7 [(base m0 5488, 5488)])
      (.not (.bit .W32 (.load 0 4176 4) 0)) = false := by
    show (!(low .W32 ((Env.ofMachine m7 [(base m0 5488, 5488)]).load 0 4176 4)).getLsbD 0) = false
    rw [Transcript.load4_of_tag (w := 1) (.inr rfl) ho7.1]
    rfl
  have R8 : RegsEq csK m7 st8.data := regsEq_block hm8 (by decide)
  have h21 : (st8.data.regs.getXReg .X21).toBitVec = loc m0 4176 := by
    rw [reg_of hm8 (r := .X21) (r' := .X21) rfl]; exact f21'
  -- `b5`: `memcpy` of the pull side's layout to `1048`.
  refine at_pc (pass_cond hpc8 hc8) (Fr.runBlock hS N_ge rfl hfr8
    (b5_in_code.trans hp.1 (by simp [b5])) run_b5 rfl rfl (by decide) (by decide)
    fun st9 hfr9 hd9 hm9 hpc9 ↦ ?_)
  have R9 : RegsEq csK st8.data st9.data := regsEq_block hm9 (by decide)
  simp only [PcOk] at hpc9
  refine mc_call h hmc hfr9 hpc9 (dst := 1048) (src := 4184) (n := 888) (by omega) (by omega)
    (by omega) (reg_ptr (x := .X0) 1048 hm9 rfl)
    (reg_add (x := .X1) (o := 4176) (c := 8) hm9 rfl h21)
    (by rw [show st9.data.regs.X2 = st9.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm9 (r := .X2) (n := 888) rfl]; rfl)
    fun m10 hfr10 hb10 hk10 hcs10 hs10 ↦ ?_
  have hQ10 : BusLayoutWAt m10.dmem (loc m0 1048) (pullL L) :=
    BusLayout.busLayoutWAt_transfer (get_of_copy hb10) (by rw [hd9, hd8]; exact hQ7)
  have kp10 : KeepIv [(160, 1048)] m0 st9.data.dmem m10.dmem :=
    keepIv_callL hS hfr9.sp le_mem (by omega) hs10 (by decide) (by decide)
  have ts10 := ts_call h hfr9 le_mem (by omega) hk10 hs10 (by rw [hd9, hd8]; exact ts7)
  have R10 : RegsEq csK st9.data m10 := regsEq_call hcs10 (by decide)
  -- `b6`: `bus_layout` of the count side.
  refine Fr.runBlock hS N_ge rfl hfr10 (b6_in_code.trans hp.1 (by simp [b6])) run_b6 rfl rfl
    (by decide) (by decide) fun st11 hfr11 hd11 hm11 hpc11 ↦ ?_
  have R11 : RegsEq csK m10 st11.data := regsEq_block hm11 (by decide)
  have g21'' : (st11.data.regs.getXReg .X21).toBitVec = loc m0 4176 := reg_ptr 4176 hm11 rfl
  have v1 : st11.data.regs.X1.toBitVec = BitVec.ofNat 64 8 := reg_lit hm11 (r := .X1) rfl
  have v2 : st11.data.regs.X2.toNat = 0 := by
    rw [show st11.data.regs.X2 = st11.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm11 (r := .X2) (n := 0) rfl]; rfl
  have hb8 : 5488 + busLayoutStack + 8 ≤ verifyBusBalanceStack := by decide
  have hst := stk_toNat hS hfr11.sp le_bl
  have l4176 := loc_toNat hS (o := 4176) (by omega)
  have RB : RegsEq csK st6.data st11.data := fun r hr ↦ by
    rw [R11 r hr, R10 r hr, R9 r hr, R8 r hr, R7 r hr]
  simp only [PcOk] at hpc11
  refine bl_call h hbl hfr11 hpc11 (side := 2) (it := .countBlocks) (fw := #[]) rfl (by decide)
    (by decide) (by decide +kernel) hrows (by rw [v2]; rfl) (by omega) (by simp)
    (by rw [v1, v2]
        refine ⟨⟨fun i hi ↦ absurd hi (by omega), by unfold NoWrap; simp⟩, ?_⟩
        unfold OffStack Apart
        rw [hst]
        left
        simp only [BitVec.toNat_ofNat]
        omega)
    (by rw [v1, v2]; unfold Apart; rw [l4176]; right; simp only [BitVec.toNat_ofNat]; omega)
    (reg_ptr (x := .X0) 4176 hm11 rfl)
    (by rw [show st11.data.regs.X3 = st11.data.regs.getXReg .X3 from rfl,
      hm11.regs .X3 _ rfl]; rfl)
    (by rw [show st11.data.regs.X4 = st11.data.regs.getXReg .X4 from rfl,
      ← UInt64.toNat_toBitVec, hm11.regs .X4 _ rfl]; rfl)
    ((reg_of hm11 (r := .X5) (r' := .X20) rfl).trans ((R11 .X20 (by simp)).symm.trans
      ((RB .X20 (by simp)).trans ((RA .X20 (by simp)).trans e20))))
    fun m12 hfr12 ho12 hk12 hcs12 hs12 ↦ ?_
  have hC12 : BusLayoutWAt m12.dmem (loc m0 4184) (countL L) := by
    have := ho12.2
    simp only [off, NativeRustcVm.addr_add_add] at this
    exact this
  have kq12 : KeepIv [(160, 1936)] m0 st11.data.dmem m12.dmem :=
    keepIv_callL hS hfr11.sp le_bl (by rw [hob]; omega) hs12 (by decide) (by decide)
  have ts12 := ts_call h hfr11 le_bl (by rw [hob]; omega) hk12 hs12
    (by rw [hd11]; exact ts10)
  have R12 : RegsEq csK st11.data m12 := regsEq_call hcs12 (by decide)
  have f21'' : (m12.regs.getXReg .X21).toBitVec = loc m0 4176 := by
    rw [hcs12 .X21 rfl]; exact g21''
  -- `b7`: the count side's tag.
  refine Fr.runBlock hS N_ge rfl hfr12 (b7_in_code.trans hp.1 (by simp [b7])) run_b7 rfl rfl
    (by decide) (by decide) fun st13 hfr13 hd13 hm13 hpc13 ↦ ?_
  have hc13 : SBool.eval (Env.ofMachine m12 [(base m0 5488, 5488)])
      (.not (.bit .W32 (.load 0 4176 4) 0)) = false := by
    show (!(low .W32 ((Env.ofMachine m12 [(base m0 5488, 5488)]).load 0 4176 4)).getLsbD 0) =
      false
    rw [Transcript.load4_of_tag (w := 1) (.inr rfl) ho12.1]
    rfl
  have R13 : RegsEq csK m12 st13.data := regsEq_block hm13 (by decide)
  have i21 : (st13.data.regs.getXReg .X21).toBitVec = loc m0 4176 := by
    rw [reg_of hm13 (r := .X21) (r' := .X21) rfl]; exact f21''
  -- `b8`: `memcpy` of the count side's layout to `1936`.
  refine at_pc (pass_cond hpc13 hc13) (Fr.runBlock hS N_ge rfl hfr13
    (b8_in_code.trans hp.1 (by simp [b8])) run_b8 rfl rfl (by decide) (by decide)
    fun st14 hfr14 hd14 hm14 hpc14 ↦ ?_)
  have R14 : RegsEq csK st13.data st14.data := regsEq_block hm14 (by decide)
  simp only [PcOk] at hpc14
  refine mc_call h hmc hfr14 hpc14 (dst := 1936) (src := 4184) (n := 888) (by omega) (by omega)
    (by omega) (reg_ptr (x := .X0) 1936 hm14 rfl)
    (reg_add (x := .X1) (o := 4176) (c := 8) hm14 rfl i21)
    (by rw [show st14.data.regs.X2 = st14.data.regs.getXReg .X2 from rfl,
      ← UInt64.toNat_toBitVec, reg_lit hm14 (r := .X2) (n := 888) rfl]; rfl)
    fun m15 hfr15 hb15 hk15 hcs15 hs15 ↦ ?_
  have hC15 : BusLayoutWAt m15.dmem (loc m0 1936) (countL L) :=
    BusLayout.busLayoutWAt_transfer (get_of_copy hb15) (by rw [hd14, hd13]; exact hC12)
  have kq15 : KeepIv [(160, 1936)] m0 st14.data.dmem m15.dmem :=
    keepIv_callL hS hfr14.sp le_mem (by omega) hs15 (by decide) (by decide)
  have ts15 := ts_call h hfr14 le_mem (by omega) hk15 hs15 (by rw [hd14, hd13]; exact ts12)
  have R15 : RegsEq csK st14.data m15 := regsEq_call hcs15 (by decide)
  -- `b9`: the push side's depth below `64`.
  refine Fr.runBlock hS N_ge rfl hfr15 (b9_in_code.trans hp.1 (by simp [b9])) run_b9 rfl rfl
    (by decide) (by decide) fun st16 hfr16 hd16 hm16 hpc16 ↦ ?_
  have R16 : RegsEq csK m15 st16.data := regsEq_block hm16 (by decide)
  have RC : RegsEq csK st4.data st16.data := fun r hr ↦ by
    rw [R16 r hr, R15 r hr, R14 r hr, R13 r hr, R12 r hr, RB r hr, R6 r hr, R5 r hr]
  have hz : m15.regs.getXReg .X26 = (pushL L).depth.toUInt64 := by
    rw [← R16 .X26 (by simp), RC .X26 (by simp), hdep4]
  have hzn : (pushL L).depth.toUInt64.toNat = (pushL L).depth :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; exact hP2.depth_lt)
  have hc16 : SBool.eval (Env.ofMachine m15 [(base m0 5488, 5488)])
      (.not (.cmp .ult .W64 (.reg .X26) (.lit 64))) = !decide ((pushL L).depth < 64) := by
    show (!CmpOp.apply .ult .W64 (m15.regs.getXReg .X26).toBitVec (BitVec.ofNat 64 64)) = _
    rw [hz, ult_lit_word _ (by decide), hzn]
  by_cases hdep : (pushL L).depth < 64
  swap
  · exact fail_cond hp h hpc16 (by rw [hc16]; simp [hdep]) hfr16
      (by rw [vbb_run]; simp [hdep])
  refine at_pc (pass_cond hpc16 (by rw [hc16]; simp [hdep])) (hg st16.data ?_)
  -- The layouts kept.
  have kpB : KeepIv [(160, 1048)] m0 st6.data.dmem st16.data.dmem :=
    ((((((((kp7.trans (KeepIv.rfl' hd8)).trans (KeepIv.rfl' hd9)).trans kp10).trans
      (KeepIv.rfl' hd11)).trans (kq12.mono (ivSub (by decide)))).trans (KeepIv.rfl' hd13)).trans
      (KeepIv.rfl' hd14)).trans (kq15.mono (ivSub (by decide)))).trans (KeepIv.rfl' hd16)
  have kqB : KeepIv [(1048, 1936)] m0 m10.dmem st16.data.dmem :=
    (((((KeepIv.rfl' hd11).trans (kq12.mono (ivSub (by decide)))).trans
      (KeepIv.rfl' hd13)).trans (KeepIv.rfl' hd14)).trans (kq15.mono (ivSub (by decide)))).trans
      (KeepIv.rfl' hd16)
  have RD : ∀ r ∈ csH, st16.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hr ↦ by
    have hr' : r ∈ csK := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h' | h' | h' | h' | h' | h' | h' | h' <;> simp [h']
    rw [R16 r hr', R15 r hr', R14 r hr', R13 r hr', R12 r hr', RB r hr', RA r hr]
  exact ⟨hfr16, kpB.blw (lo := 160) (hi := 1048) (by simp) (by omega) (by omega) hP6,
    kqB.blw (lo := 1048) (hi := 1936) (by simp) (by omega) (by omega) hQ10,
    by rw [hd16]; exact hC15, hdep,
    (RD .X19 (by simp)).trans e19, (RD .X20 (by simp)).trans e20,
    (RD .X23 (by simp)).trans e23, (RD .X24 (by simp)).trans e24,
    (RD .X25 (by simp)).trans e25,
    by rw [R16 .X26 (by simp), hz]; exact hzn,
    by rw [RD .X27 (by simp), e27]
       exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega),
    (RD .X28 (by simp)).trans e28,
    by rw [RD .X29 (by simp), e29]
       exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega),
    by rw [hd16]; exact ts15⟩

end

end NativeRustcVmArm.Bus.VerifyBusBalance
