module

public import NativeRustcVmArm.Code.Vm.FinalLevel.Names
public import NativeRustcVmArm.Code.Vm.FoldRounds.Names
public import NativeRustcVmArm.Code.Vm.NextLevel.Names
public import NativeRustcVmArm.Whir.WhirLevels.Facts

/-!
# `whir_levels`: levels `3` to `5`

From `Head k` at level `k`'s fold rounds' block, X26 the level count, the goal: the fold rounds,
`μ`, then the tail call of `final_level` (the last level) or `next_level` and level `k + 1`
(`level5`, `level4`, `level3`). The branch on the last level's index (X24) is `pc_eq24`,
`pc_ne24`.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Layout.Ladder
open NativeRustcVmArm.Vm.WhirLevels

@[expose] public section

/-- The callees' contracts. -/
structure Callees [Host] : Prop where
  fr : ∀ a s w, Spec (Labels.label NativeRustcVmArm.Vm.FoldRounds.entryLabel) (FoldRoundsPre a s w) (FoldRoundsPost a s w)
  nl : ∀ a s level w rounds, Spec (Labels.label NativeRustcVmArm.Vm.NextLevel.entryLabel)
    (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds)
  fl : ∀ a s level ba b w rounds, Spec (Labels.label NativeRustcVmArm.Vm.FinalLevel.entryLabel)
    (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds)

end

public section

section
variable [Labels] {m0 st : MachineData} {len k : Nat} {rs : List (BitVec 64 × Nat)}

theorem cmp24_eval (hr : Regs m0 len st) (hk : k < 2 ^ 64) :
    (SBool.cmp .eq .W64 (.reg .X24) (.lit k)).eval (Env.ofMachine st rs) = decide (len - 1 = k) := by
  rw [eval_cmp_eq _ _ hk]
  simp only [Env.ofMachine_regs]
  have := hr.x24
  show decide ((st.regs.getXReg .X24).toNat = k) = _
  rw [this]

theorem pc_eq24 (hr : Regs m0 len st) (hk : k < 2 ^ 64) {l : Label} {next : Int64}
    {st' : MachineState}
    (h : PcOk (Env.ofMachine st rs) (.cond (.cmp .eq .W64 (.reg .X24) (.lit k)) l) next st') :
    st'.pc = if len - 1 = k then Labels.label l else next := by
  simp only [PcOk] at h
  rw [cmp24_eval hr hk] at h
  by_cases hc : len - 1 = k <;> simp [hc] at h ⊢ <;> exact h

theorem pc_ne24 (hr : Regs m0 len st) (hk : k < 2 ^ 64) {l : Label} {next : Int64}
    {st' : MachineState}
    (h : PcOk (Env.ofMachine st rs) (.cond (.not (.cmp .eq .W64 (.reg .X24) (.lit k))) l) next st') :
    st'.pc = if len - 1 = k then next else Labels.label l := by
  have e : (SBool.not (.cmp .eq .W64 (.reg .X24) (.lit k))).eval (Env.ofMachine st rs) =
      !decide (len - 1 = k) := by
    rw [← cmp24_eval hr hk]; rfl
  simp only [PcOk, e] at h
  by_cases hc : len - 1 = k <;> simp [hc] at h ⊢ <;> exact h

/-- `X23 + c` after a `μ` block, the level's address. -/
theorem x8_val {S' : SState} {st1 : MachineData} {c : Nat}
    (hm : Match (Env.ofMachine st [(pA m0, 24)]) S' st1) (hr : Regs m0 len st)
    (h8 : S'.reg .X8 = some (.bin .add .W64 (.reg .X23) (.lit c))) :
    (st1.regs.getXReg .X8).toBitVec = lvA m0 + BitVec.ofNat 64 c := by
  rw [reg_val hm h8]
  sym_simp
  simp only [Env.ofMachine_regs]
  rw [hr.x23]

end

section
variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **Level `5`**, the last. -/
theorem level5 (hp : Placed code k0) (cs : Callees) (c : Ctx a s0 levels ba b claim m0 rate)
    {s : TState} {w : WhirStateW} {st : MachineState}
    (hh : Head a s0 levels b claim m0 5 s w st.data)
    (h26 : (st.data.regs.getXReg .X26).toNat = levels.length)
    (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.WhirLevels.b33Offset)) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hl6 := c.len_le.2
  have hlt := hh.lt
  refine fold_stage hp cs.fr c b33_in_code (by simp [b33])
    (by rw [NativeRustcVmArm.Vm.WhirLevels.b33_length, NativeRustcVmArm.Vm.WhirLevels.b33Length]; exact b2_eq.2.2.2.2.1 ▸ b34_in_code) run_b33
    (by rw [← after_eq run_b33]; exact ok_b33) (by decide) hh h26 hpc
    fun st1 hpc1 s1 w1 rs1 hm1 ↦ ?_
  rw [NativeRustcVmArm.Vm.WhirLevels.b33_next, show NativeRustcVmArm.Vm.WhirLevels.b34Offset + 1 = NativeRustcVmArm.Vm.WhirLevels.b35Offset from by simpa only [NativeRustcVmArm.Vm.WhirLevels.b34_length, NativeRustcVmArm.Vm.WhirLevels.b34Length] using NativeRustcVmArm.Vm.WhirLevels.b34_next] at hpc1
  refine w_stage hp c b35_in_code (by simp [b35]) run_b35
    (by rw [← after_eq run_b35]; exact ok_b35) hm1 hpc1 fun st2 hm2 hx5 _ hpc2 ↦ ?_
  have hpc2' := pc_ne24 hm1.regs (by decide) hpc2
  simp only [show levels.length - 1 = 5 by omega, ↓reduceIte] at hpc2'
  have hx26 := hm2.x26
  unfold X26Ok at hx26
  simp only [show ¬(5 < 5) by omega, ↓reduceIte] at hx26
  exact final_stage hp cs.fl c b36_in_code (by simp [b36]) run_b36
    (by rw [← after_eq run_b36]; exact ok_b36) (by simp only [Sym.eval, Env.ofMachine_regs]; exact hx26)
    hm2 (by omega) hx5 (by rw [hpc2']; rfl)

/-- **Level `4`**. -/
theorem level4 (hp : Placed code k0) (cs : Callees) (c : Ctx a s0 levels ba b claim m0 rate)
    {s : TState} {w : WhirStateW} {st : MachineState}
    (hh : Head a s0 levels b claim m0 4 s w st.data)
    (h26 : (st.data.regs.getXReg .X26).toNat = levels.length)
    (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.WhirLevels.b27Offset)) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hl6 := c.len_le.2
  have hlt := hh.lt
  refine fold_stage hp cs.fr c b27_in_code (by simp [b27])
    (by rw [NativeRustcVmArm.Vm.WhirLevels.b27_length, NativeRustcVmArm.Vm.WhirLevels.b27Length]; exact b2_eq.2.2.2.1 ▸ b28_in_code) run_b27
    (by rw [← after_eq run_b27]; exact ok_b27) (by decide) hh h26 hpc
    fun st1 hpc1 s1 w1 rs1 hm1 ↦ ?_
  rw [NativeRustcVmArm.Vm.WhirLevels.b27_next, show NativeRustcVmArm.Vm.WhirLevels.b28Offset + 1 = NativeRustcVmArm.Vm.WhirLevels.b29Offset from by simpa only [NativeRustcVmArm.Vm.WhirLevels.b28_length, NativeRustcVmArm.Vm.WhirLevels.b28Length] using NativeRustcVmArm.Vm.WhirLevels.b28_next] at hpc1
  refine w_stage hp c b29_in_code (by simp [b29]) run_b29
    (by rw [← after_eq run_b29]; exact ok_b29.1) hm1 hpc1 fun st2 hm2 hx5 hmm hpc2 ↦ ?_
  have hpc2' := pc_eq24 hm1.regs (by decide) hpc2
  by_cases hfin : levels.length - 1 = 4
  · simp only [hfin, ↓reduceIte] at hpc2'
    rw [hp.label (j := NativeRustcVmArm.Vm.WhirLevels.b17Offset) NativeRustcVmArm.Vm.WhirLevels.label_12_at] at hpc2'
    have h8 := x8_val hmm hm1.regs (after_eq run_b29 ▸ ok_b29.2)
    exact final_stage hp cs.fl c b17_in_code (by simp [b17]) run_b17
      (by rw [← after_eq run_b17]; exact ok_b17)
      (by simp only [Sym.eval, Env.ofMachine_regs]; exact h8) hm2 (by omega) hx5 hpc2'
  · simp only [hfin, ↓reduceIte] at hpc2'
    refine next_stage hp cs.nl c b30_in_code (by simp [b30]) run_b30
      (by rw [← after_eq run_b30]; exact ok_b30)
      (fun _ _ ↦ by show _ = lvA m0 + BitVec.ofNat 64 96; exact eval_ptr0 96) (by decide) hm2
      (by omega) hx5 (by rw [hpc2']; rfl) fun st3 hpc3 hf3 hr3 h263 hres ↦ ?_
    rw [show k0 + NativeRustcVmArm.Vm.WhirLevels.b30Offset + b30.length = k0 + NativeRustcVmArm.Vm.WhirLevels.b31Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.WhirLevels.b30_next]] at hpc3
    exact cmp_stage hp c b31_in_code (by simp [b31])
      (by rw [NativeRustcVmArm.Vm.WhirLevels.b31_length, NativeRustcVmArm.Vm.WhirLevels.b31Length]; exact b2_eq.2.2.2.2.2.2.2.2.2 ▸ b32_in_code) run_b31
      (by rw [← after_eq run_b31]; exact ok_b31) (by omega) hf3 hr3 h263 hpc3 hres
      fun st4 hpc4 s4 w4 hh4 h264 ↦ level5 hp cs c hh4 h264 hpc4

/-- **Level `3`**. -/
theorem level3 (hp : Placed code k0) (cs : Callees) (c : Ctx a s0 levels ba b claim m0 rate)
    {s : TState} {w : WhirStateW} {st : MachineState}
    (hh : Head a s0 levels b claim m0 3 s w st.data)
    (h26 : (st.data.regs.getXReg .X26).toNat = levels.length)
    (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.WhirLevels.b21Offset)) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hl6 := c.len_le.2
  have hlt := hh.lt
  refine fold_stage hp cs.fr c b21_in_code (by simp [b21])
    (by rw [NativeRustcVmArm.Vm.WhirLevels.b21_length, NativeRustcVmArm.Vm.WhirLevels.b21Length]; exact b2_eq.2.2.1 ▸ b22_in_code) run_b21
    (by rw [← after_eq run_b21]; exact ok_b21) (by decide) hh h26 hpc
    fun st1 hpc1 s1 w1 rs1 hm1 ↦ ?_
  rw [NativeRustcVmArm.Vm.WhirLevels.b21_next, show NativeRustcVmArm.Vm.WhirLevels.b22Offset + 1 = NativeRustcVmArm.Vm.WhirLevels.b23Offset from by simpa only [NativeRustcVmArm.Vm.WhirLevels.b22_length, NativeRustcVmArm.Vm.WhirLevels.b22Length] using NativeRustcVmArm.Vm.WhirLevels.b22_next] at hpc1
  refine w_stage hp c b23_in_code (by simp [b23]) run_b23
    (by rw [← after_eq run_b23]; exact ok_b23.1) hm1 hpc1 fun st2 hm2 hx5 hmm hpc2 ↦ ?_
  have hpc2' := pc_eq24 hm1.regs (by decide) hpc2
  by_cases hfin : levels.length - 1 = 3
  · simp only [hfin, ↓reduceIte] at hpc2'
    rw [hp.label (j := NativeRustcVmArm.Vm.WhirLevels.b17Offset) NativeRustcVmArm.Vm.WhirLevels.label_12_at] at hpc2'
    have h8 := x8_val hmm hm1.regs (after_eq run_b23 ▸ ok_b23.2)
    exact final_stage hp cs.fl c b17_in_code (by simp [b17]) run_b17
      (by rw [← after_eq run_b17]; exact ok_b17)
      (by simp only [Sym.eval, Env.ofMachine_regs]; exact h8) hm2 (by omega) hx5 hpc2'
  · simp only [hfin, ↓reduceIte] at hpc2'
    refine next_stage hp cs.nl c b24_in_code (by simp [b24]) run_b24
      (by rw [← after_eq run_b24]; exact ok_b24)
      (fun _ _ ↦ by show _ = lvA m0 + BitVec.ofNat 64 72; exact eval_ptr0 72) (by decide) hm2
      (by omega) hx5 (by rw [hpc2']; rfl) fun st3 hpc3 hf3 hr3 h263 hres ↦ ?_
    rw [show k0 + NativeRustcVmArm.Vm.WhirLevels.b24Offset + b24.length = k0 + NativeRustcVmArm.Vm.WhirLevels.b25Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.WhirLevels.b24_next]] at hpc3
    exact cmp_stage hp c b25_in_code (by simp [b25])
      (by rw [NativeRustcVmArm.Vm.WhirLevels.b25_length, NativeRustcVmArm.Vm.WhirLevels.b25Length]; exact b2_eq.2.2.2.2.2.2.2.2.1 ▸ b26_in_code) run_b25
      (by rw [← after_eq run_b25]; exact ok_b25) (by omega) hf3 hr3 h263 hpc3 hres
      fun st4 hpc4 s4 w4 hh4 h264 ↦ level4 hp cs c hh4 h264 hpc4

end

end

end NativeRustcVmArm.Whir.WhirLevels
