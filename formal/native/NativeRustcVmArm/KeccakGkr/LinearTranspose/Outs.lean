module

public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Out
import Mathlib.Tactic.IntervalCases

/-!
# `linear_transpose`: the output

From the columns done (`b20`, X8 the lane, X9 to X11 the columns', the output's and `g`'s lanes
plus `8`), each lane's head (`b21`: its two columns, `l % 5` by a multiply-high), the output loop
(`b22`, `Out.lean`) and the next lane (`b23`): every element of the output (`output`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters

@[expose] public section

/-- The lane's head: its output so far. -/
structure OutHead [Labels] (m0 : MachineData) (ws : Array EW) (l : Nat) (st : MachineData) :
    Prop where
  regs : OutRegs m0 st l
  mem : OutMem m0 ws (64 * l) st

/-- **The output done**. -/
structure OutDone [Labels] (m0 : MachineData) (ws : Array EW) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  o : ElemsAt st.dmem (oA m0) (oF ws) 1600

/-- `x8 / 5`, by a multiply-high. -/
def q5 : Sym := .un (.ubfm 2 63) .W64 (.bin .umulh .W64 (.reg .X8) (.lit 14757395258967641293))
/-- `x8 % 5`. -/
def r5 : Sym := .bin .sub .W64 (.reg .X8) (.bin .add .W64 q5 (.un (.shift .LSL 2) .W64 q5))
/-- `b21`'s X14: the column one along, plus `8`. -/
def x14S : Sym := .bin .add .W64 (.reg .X9) (.un (.shift .LSL 4) .W64
  (.ite (.cmp .eq .W64 (.bin .add .W64 r5 (.lit 1)) (.lit 5)) (.lit 0)
    (.un (.ubfm 58 57) .W64 (.bin .add .W64 r5 (.lit 1)))))
/-- `b21`'s X15: the column four along. -/
def x15S : Sym := .bin .add .W64 (.reg .X19) (.ite (.cmp .eq .W64 r5 (.lit 0)) (.lit 4096)
  (.bin .sub .W64 (.un (.ubfm 54 53) .W64 r5) (.lit 1024)))

end

public section

theorem OutMem.of_dmem [Labels] {ws : Array EW} {m0 s s' : MachineData} {n : Nat}
    (h : OutMem m0 ws n s) (hd : s'.dmem = s.dmem) : OutMem m0 ws n s' :=
  ⟨by rw [hd]; exact h.g, by rw [hd]; exact h.c, by rw [hd]; exact h.o⟩

theorem x14_eval [Labels] (env : Env) (hl : (env.regs .X8).toNat < 25) :
    x14S.eval env =
      env.regs .X9 + BitVec.ofNat 64 (1024 * (((env.regs .X8).toNat % 5 + 1) % 5)) := by
  simp only [x14S, r5, q5]
  sym_simp
  generalize env.regs .X8 = x at hl ⊢
  obtain ⟨l, hl', rfl⟩ : ∃ l : Nat, l < 25 ∧ x = BitVec.ofNat 64 l := ⟨x.toNat, hl, by simp⟩
  congr 1
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show l < 2 ^ 64 by omega)]
  interval_cases l <;> decide

theorem x15_eval [Labels] (env : Env) (hl : (env.regs .X8).toNat < 25) :
    x15S.eval env =
      env.regs .X19 + BitVec.ofNat 64 (1024 * (((env.regs .X8).toNat % 5 + 4) % 5)) := by
  simp only [x15S, r5, q5]
  sym_simp
  generalize env.regs .X8 = x at hl ⊢
  obtain ⟨l, hl', rfl⟩ : ∃ l : Nat, l < 25 ∧ x = BitVec.ofNat 64 l := ⟨x.toNat, hl, by simp⟩
  congr 1
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show l < 2 ^ 64 by omega)]
  interval_cases l <;> decide

variable [NativeRustcArm.Host] {ws : Array EW} {m0 : MachineData} {k : Nat}

/-- **The output's set-up** (`b20`): from the columns done, lane `0`'s head. -/
theorem out_setup (hp : Placed code k) {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b20Offset))
    (hI : ColDone m0 ws 4 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b21Offset) ∧ OutHead m0 ws 0 s'.data)
      s := by
  refine exec_at (b20_in_code.trans hp.1 (by simp [b20])) e20 (Env.wf_nil _) hpc (match_nil _)
    fun s' hm' hpc' ↦ .done _ ⟨hpc', ?_⟩
  have hb := hI.ctx.body.of_block (match_nil _) hm' (Env.wf_nil _) rfl free_ok (by decide)
  have hctx := ctx_keep hI.ctx hb (KeccakGkr.Match.regs_keep (match_nil _) hm' _ (by decide))
  have hdm : s'.data.dmem = s.data.dmem := hm'.dmem_eq (Env.wf_nil _) rfl
  have h8 := hm'.regs .X8 _ rfl
  have h9 := hm'.regs .X9 _ rfl
  have h10 := hm'.regs .X10 _ rfl
  have h11 := hm'.regs .X11 _ rfl
  have h12 := hm'.regs .X12 _ rfl
  have h13 := hm'.regs .X13 _ rfl
  sym_simp at h8 h9 h10 h11 h12 h13
  simp only [Env.ofMachine_regs] at h9 h10 h11
  refine ⟨⟨hctx, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, fun _ h ↦ absurd h (by omega)⟩⟩
  · show (s'.data.regs.getXReg .X8).toBitVec.toNat = 0
    rw [h8]; rfl
  · show (s'.data.regs.getXReg .X9).toBitVec = _
    rw [h9, show s.data.regs.getXReg .X19 = m0.regs.X2 from hI.ctx.x19]
  · show (s'.data.regs.getXReg .X10).toBitVec = _
    rw [h10, show s.data.regs.getXReg .X21 = m0.regs.X3 from hI.ctx.x21]
  · show (s'.data.regs.getXReg .X11).toBitVec = _
    rw [h11, show s.data.regs.getXReg .X20 = m0.regs.X1 from hI.ctx.x20]
  · show (s'.data.regs.getXReg .X12).toBitVec = _
    rw [h12]
  · show (s'.data.regs.getXReg .X13).toBitVec = _
    rw [h13]
  · rw [hdm]; exact hI.mem.g
  · rw [hdm]; exact hI.mem.c

/-- **A lane's head** (`b21`): its two columns, the loop's pointers at position `0`. -/
theorem out_head (hp : Placed code k) {l : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b21Offset)) (hI : OutHead m0 ws l s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b22Offset) ∧ Out m0 ws l 0 s'.data)
      s := by
  have hl := hI.regs.lt
  have hm : Match (Env.ofMachine s.data []) outHeadS s.data :=
    match_ofMachine trivial rfl ⟨hI.regs.x12, hI.regs.x13, trivial⟩ trivial trivial trivial
  refine exec_at (b21_in_code.trans hp.1 (by simp [b21])) e21 (Env.wf_nil _) hpc hm
    fun s' hm' hpc' ↦ .done _ ⟨hpc', ?_⟩
  have hb := hI.regs.ctx.body.of_block hm hm' (Env.wf_nil _) rfl free_ok (by decide)
  have hregs := hI.regs.keep hb (KeccakGkr.Match.regs_keep hm hm' _ (by decide))
  have hdm : s'.data.dmem = s.data.dmem := hm'.dmem_eq (Env.wf_nil _) rfl
  have hx8 : ((Env.ofMachine s.data []).regs .X8).toNat = l := hI.regs.x8
  have h14 := hm'.regs .X14 x14S rfl
  have h15 := hm'.regs .X15 x15S rfl
  have h16 := hm'.regs .X16 _ rfl
  have h17 := hm'.regs .X17 _ rfl
  have h18 := hm'.regs .X18 _ rfl
  rw [x14_eval _ (by omega), hx8] at h14
  rw [x15_eval _ (by omega), hx8] at h15
  refine ⟨hregs, by rw [Nat.add_zero]; exact hI.mem.of_dmem hdm, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · show (s'.data.regs.getXReg .X14).toBitVec = _
    rw [h14, show (Env.ofMachine s.data []).regs .X9 = cA m0 + BitVec.ofNat 64 8 from hI.regs.x9,
      NativeRustcVm.addr_add_add]
    congr 2
  · show (s'.data.regs.getXReg .X15).toBitVec = _
    rw [h15, show (Env.ofMachine s.data []).regs .X19 = cA m0 from
      congrArg UInt64.toBitVec hI.regs.ctx.x19]
  · show (s'.data.regs.getXReg .X16).toBitVec = _
    rw [h16, Nat.mul_zero, Nat.add_zero]; exact hI.regs.x11
  · show (s'.data.regs.getXReg .X17).toBitVec = _
    rw [h17, Nat.mul_zero, Nat.add_zero]; exact hI.regs.x10
  · show (s'.data.regs.getXReg .X18).toBitVec.toNat = _
    rw [h18]; rfl

/-- **A lane of the output loop**, to its end. -/
theorem out_lane (hp : Placed code k) (hpre : LinearTransposePre ws m0) {l z : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b22Offset)) (hI : Out m0 ws l z s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b23Offset) ∧ OutRegs m0 s'.data l ∧
      OutMem m0 ws (64 * l + 64) s'.data) s :=
  Sym.loop (fun c s ↦ ∃ z, c = 64 - z ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b22Offset) ∧ Out m0 ws l z s.data)
    (fun _ s ⟨z, hc, hpc, hI⟩ ↦ (out_step hp hpre hpc hI).mono fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨64 - (z + 1), by have := hI.z_lt; omega, z + 1, rfl, hpc', hI'⟩
      · exact Or.inl h)
    ⟨z, rfl, hpc, hI⟩

/-- **The next lane** (`b23`): lane `l + 1`'s head, or the output done. -/
theorem out_next (hp : Placed code k) {l : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b23Offset)) (hr : OutRegs m0 s.data l)
    (hmem : OutMem m0 ws (64 * l + 64) s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (l + 1 < 25 ∧ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b21Offset) ∧
      OutHead m0 ws (l + 1) s'.data) ∨ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b24Offset) ∧ OutDone m0 ws s'.data)) s := by
  have hl := hr.lt
  refine exec_at (b23_in_code.trans hp.1 (by simp [b23])) e23 (Env.wf_nil _) hpc (match_nil _)
    fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hr.ctx.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl free_ok (by decide)
  have hdm : s1.data.dmem = s.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have e := KeccakGkr.Match.regs_keep (match_nil _) hm1 [.X9, .X12, .X13, .X19, .X20, .X21, .X22]
    (by decide)
  have hctx := ctx_keep hr.ctx hb1 fun r hr' ↦ e r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
    rcases hr' with rfl | rfl | rfl | rfl <;> simp)
  have h8 := hm1.regs .X8 _ rfl
  have h10 := hm1.regs .X10 _ rfl
  have h11 := hm1.regs .X11 _ rfl
  sym_simp at h8 h10 h11
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  simp only [Env.ofMachine_regs] at h8 h10 h11 hpc1
  have hx8 : (s.data.regs.getXReg .X8).toBitVec.toNat = l := hr.x8
  have hx8' : (s.data.regs.getXReg .X8).toBitVec + 1#64 = BitVec.ofNat 64 (l + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat' (by rw [hx8]; omega), hx8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [hx8'] at hpc1 h8
  by_cases hlast : l = 24
  · subst hlast
    simp only [show (BitVec.ofNat 64 (24 + 1) == 25#64) = true from rfl, Bool.not_true,
      Bool.false_eq_true, ite_false, NativeRustcVmArm.Vm.LinearTranspose.b23_length, NativeRustcVmArm.Vm.LinearTranspose.b23Length] at hpc1
    exact .done _ (Or.inr ⟨hpc1, hctx, by rw [hdm]; exact hmem.o⟩)
  · have hc : (BitVec.ofNat 64 (l + 1) == 25#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h
      simp at this; omega
    simp only [hc, Bool.not_false, ite_true] at hpc1
    refine .done _ (Or.inl ⟨by omega, hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b21Offset) NativeRustcVmArm.Vm.LinearTranspose.label_18_at),
      ⟨hctx, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    · show (s1.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · show (s1.data.regs.getXReg .X9).toBitVec = _
      rw [e .X9 (by simp)]; exact hr.x9
    · show (s1.data.regs.getXReg .X10).toBitVec = _
      rw [h10, show (s.data.regs.getXReg .X10).toBitVec = _ from hr.x10,
        show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, NativeRustcVm.addr_add_add,
        show 8 + 1024 * l + 1024 = 8 + 1024 * (l + 1) by omega]
    · show (s1.data.regs.getXReg .X11).toBitVec = _
      rw [h11, show (s.data.regs.getXReg .X11).toBitVec = _ from hr.x11,
        show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, NativeRustcVm.addr_add_add,
        show 8 + 1024 * l + 1024 = 8 + 1024 * (l + 1) by omega]
    · show (s1.data.regs.getXReg .X12).toBitVec = _
      rw [e .X12 (by simp)]; exact hr.x12
    · show (s1.data.regs.getXReg .X13).toBitVec = _
      rw [e .X13 (by simp)]; exact hr.x13
    · rw [show 64 * (l + 1) = 64 * l + 64 by omega]; exact hmem.of_dmem hdm

/-- **The output**: from the columns done, every element of the output, at the epilogue. -/
theorem output (hp : Placed code k) (hpre : LinearTransposePre ws m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b20Offset)) (hI : ColDone m0 ws 4 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b24Offset) ∧ OutDone m0 ws s'.data)
      s :=
  (out_setup hp hpc hI).bind fun s1 ⟨hpc1, hI1⟩ ↦
    Sym.loop (fun n s ↦ ∃ l, n = 25 - l ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b21Offset) ∧ OutHead m0 ws l s.data)
      (fun _ s ⟨l, hn, hpc, hI⟩ ↦ (out_head hp hpc hI).bind fun s2 ⟨hpc2, hI2⟩ ↦
        (out_lane hp hpre hpc2 hI2).bind fun s3 ⟨hpc3, hr3, hm3⟩ ↦
          (out_next hp hpc3 hr3 hm3).mono fun s' h ↦ by
            rcases h with ⟨hlt, hpc', hI'⟩ | h
            · exact Or.inr ⟨25 - (l + 1), by omega, l + 1, rfl, hpc', hI'⟩
            · exact Or.inl h)
      ⟨0, rfl, hpc1, hI1⟩

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
