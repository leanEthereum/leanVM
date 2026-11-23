module

public import NativeRustcVmArm.Whir.WhirLevels.Late

/-!
# `whir_levels`: levels `0` to `2`

`level2`, `level1` from `Head k` at level `k`'s fold rounds' block; `level0` from `Mid 0` at `b3`
(after the entry's fold rounds): `μ`, `next_level` and level `1`. A ladder has at least `3`
levels, so levels `0` and `1` are never the last.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Layout.Ladder
open NativeRustcVmArm.Vm.WhirLevels

public section

section
variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **Level `2`**. -/
theorem level2 (hp : Placed code k0) (cs : Callees) (c : Ctx a s0 levels ba b claim m0 rate)
    {s : TState} {w : WhirStateW} {st : MachineState}
    (hh : Head a s0 levels b claim m0 2 s w st.data)
    (h26 : (st.data.regs.getXReg .X26).toNat = levels.length)
    (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.WhirLevels.b14Offset)) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hl6 := c.len_le.2
  have hlt := hh.lt
  refine fold_stage hp cs.fr c b14_in_code (by simp [b14])
    (by rw [NativeRustcVmArm.Vm.WhirLevels.b14_length, NativeRustcVmArm.Vm.WhirLevels.b14Length]; exact b2_eq.2.1 ▸ b15_in_code) run_b14
    (by rw [← after_eq run_b14]; exact ok_b14) (by decide) hh h26 hpc
    fun st1 hpc1 s1 w1 rs1 hm1 ↦ ?_
  rw [NativeRustcVmArm.Vm.WhirLevels.b14_next, show NativeRustcVmArm.Vm.WhirLevels.b15Offset + 1 = NativeRustcVmArm.Vm.WhirLevels.b16Offset from by simpa only [NativeRustcVmArm.Vm.WhirLevels.b15_length, NativeRustcVmArm.Vm.WhirLevels.b15Length] using NativeRustcVmArm.Vm.WhirLevels.b15_next] at hpc1
  refine w_stage hp c b16_in_code (by simp [b16]) run_b16
    (by rw [← after_eq run_b16]; exact ok_b16.1) hm1 hpc1 fun st2 hm2 hx5 hmm hpc2 ↦ ?_
  have hpc2' := pc_ne24 hm1.regs (by decide) hpc2
  by_cases hfin : levels.length - 1 = 2
  · simp only [hfin, ↓reduceIte] at hpc2'
    have h8 := x8_val hmm hm1.regs (after_eq run_b16 ▸ ok_b16.2)
    exact final_stage hp cs.fl c b17_in_code (by simp [b17]) run_b17
      (by rw [← after_eq run_b17]; exact ok_b17)
      (by simp only [Sym.eval, Env.ofMachine_regs]; exact h8) hm2 (by omega) hx5
      (by rw [hpc2']; rfl)
  · simp only [hfin, ↓reduceIte] at hpc2'
    rw [hp.label (j := NativeRustcVmArm.Vm.WhirLevels.b18Offset) NativeRustcVmArm.Vm.WhirLevels.label_13_at] at hpc2'
    refine next_stage hp cs.nl c b18_in_code (by simp [b18]) run_b18
      (by rw [← after_eq run_b18]; exact ok_b18)
      (fun _ _ ↦ by show _ = lvA m0 + BitVec.ofNat 64 48; exact eval_ptr0 48) (by decide) hm2
      (by omega) hx5 hpc2' fun st3 hpc3 hf3 hr3 h263 hres ↦ ?_
    rw [show k0 + NativeRustcVmArm.Vm.WhirLevels.b18Offset + b18.length = k0 + NativeRustcVmArm.Vm.WhirLevels.b19Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.WhirLevels.b18_next]] at hpc3
    exact cmp_stage hp c b19_in_code (by simp [b19])
      (by rw [NativeRustcVmArm.Vm.WhirLevels.b19_length, NativeRustcVmArm.Vm.WhirLevels.b19Length]; exact b2_eq.2.2.2.2.2.2.2.1 ▸ b20_in_code) run_b19
      (by rw [← after_eq run_b19]; exact ok_b19) (by omega) hf3 hr3 h263 hpc3 hres
      fun st4 hpc4 s4 w4 hh4 h264 ↦ level3 hp cs c hh4 h264 hpc4

/-- **Level `1`**. -/
theorem level1 (hp : Placed code k0) (cs : Callees) (c : Ctx a s0 levels ba b claim m0 rate)
    {s : TState} {w : WhirStateW} {st : MachineState}
    (hh : Head a s0 levels b claim m0 1 s w st.data)
    (h26 : (st.data.regs.getXReg .X26).toNat = levels.length)
    (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.WhirLevels.b7Offset)) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hl6 := c.len_le
  refine fold_stage hp cs.fr c b7_in_code (by simp [b7])
    (by rw [NativeRustcVmArm.Vm.WhirLevels.b7_length, NativeRustcVmArm.Vm.WhirLevels.b7Length]; exact b2_eq.1 ▸ b8_in_code) run_b7
    (by rw [← after_eq run_b7]; exact ok_b7) (by decide) hh h26 hpc
    fun st1 hpc1 s1 w1 rs1 hm1 ↦ ?_
  rw [NativeRustcVmArm.Vm.WhirLevels.b7_next, show NativeRustcVmArm.Vm.WhirLevels.b8Offset + 1 = NativeRustcVmArm.Vm.WhirLevels.b9Offset from by simpa only [NativeRustcVmArm.Vm.WhirLevels.b8_length, NativeRustcVmArm.Vm.WhirLevels.b8Length] using NativeRustcVmArm.Vm.WhirLevels.b8_next] at hpc1
  refine w_stage hp c b9_in_code (by simp [b9]) run_b9
    (by rw [← after_eq run_b9]; exact ok_b9) hm1 hpc1 fun st2 hm2 hx5 _ hpc2 ↦ ?_
  have hpc2' := pc_ne24 hm1.regs (by decide) hpc2
  simp only [show ¬(levels.length - 1 = 1) by omega, ↓reduceIte] at hpc2'
  rw [hp.label (j := NativeRustcVmArm.Vm.WhirLevels.b11Offset) NativeRustcVmArm.Vm.WhirLevels.label_8_at] at hpc2'
  refine next_stage hp cs.nl c b11_in_code (by simp [b11]) run_b11
    (by rw [← after_eq run_b11]; exact ok_b11)
    (fun _ hr ↦ by simp only [Sym.eval, Env.ofMachine_regs]; rw [hr.x27]; rfl) (by decide) hm2
    (by omega) hx5 hpc2' fun st3 hpc3 hf3 hr3 h263 hres ↦ ?_
  rw [show k0 + NativeRustcVmArm.Vm.WhirLevels.b11Offset + b11.length = k0 + NativeRustcVmArm.Vm.WhirLevels.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.WhirLevels.b11_next]] at hpc3
  exact cmp_stage hp c b12_in_code (by simp [b12])
    (by rw [NativeRustcVmArm.Vm.WhirLevels.b12_length, NativeRustcVmArm.Vm.WhirLevels.b12Length]; exact b2_eq.2.2.2.2.2.2.1 ▸ b13_in_code) run_b12
    (by rw [← after_eq run_b12]; exact ok_b12) (by omega) hf3 hr3 h263 hpc3 hres
    fun st4 hpc4 s4 w4 hh4 h264 ↦ level2 hp cs c hh4 h264 hpc4

/-- **Level `0`** after its fold rounds. -/
theorem level0 (hp : Placed code k0) (cs : Callees) (c : Ctx a s0 levels ba b claim m0 rate)
    {s : TState} {w : WhirStateW} {rs : Array FoldRoundW} {st : MachineState}
    (hm : Mid a s0 levels b claim m0 rate 0 s w rs st.data)
    (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.WhirLevels.b3Offset)) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hl6 := c.len_le
  have hx26 := hm.x26
  unfold X26Ok at hx26
  simp only [show 0 < 5 by omega, ↓reduceIte] at hx26
  refine w_stage hp c b3_in_code (by simp [b3]) run_b3
    (by rw [← after_eq run_b3]; exact ok_b3) hm hpc fun st2 hm2 hx5 _ hpc2 ↦ ?_
  have e : (SBool.not (.cmp .eq .W64 (.reg .X26) (.lit 1))).eval
      (Env.ofMachine st.data [(pA m0, 24)]) = true := by
    show (!(SBool.cmp .eq .W64 (.reg .X26) (.lit 1)).eval _) = true
    rw [eval_cmp_eq _ _ (by decide)]
    simp only [Env.ofMachine_regs]
    have h1 : (st.data.regs.getXReg .X26).toBitVec.toNat ≠ 1 := fun h ↦ by
      have : (st.data.regs.getXReg .X26).toNat = 1 := h
      omega
    simpa using h1
  simp only [PcOk, e, ↓reduceIte] at hpc2
  rw [hp.label (j := NativeRustcVmArm.Vm.WhirLevels.b5Offset) NativeRustcVmArm.Vm.WhirLevels.label_4_at] at hpc2
  refine next_stage hp cs.nl c b5_in_code (by simp [b5]) run_b5
    (by rw [← after_eq run_b5]; exact ok_b5)
    (fun _ _ ↦ by show _ = lvA m0 + BitVec.ofNat 64 0; exact eval_ptr0 0) (by decide) hm2
    (by omega) hx5 hpc2 fun st3 hpc3 hf3 hr3 h263 hres ↦ ?_
  rw [show k0 + NativeRustcVmArm.Vm.WhirLevels.b5Offset + b5.length = k0 + NativeRustcVmArm.Vm.WhirLevels.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.WhirLevels.b5_next]] at hpc3
  exact cbz_next hp c (b2_eq.2.2.2.2.2.1 ▸ b6_in_code) hf3 hr3 h263 hpc3 hres
    fun st4 hpc4 s4 w4 hh4 h264 ↦ level1 hp cs c hh4 h264 hpc4

end

end

end NativeRustcVmArm.Whir.WhirLevels
