module

public import NativeRustcVmArm.Wire.WriteOpenings.B.Defs

/-!
# `write_openings`' leaf copy set up (`h = 0`, a leaf)

Query `j` found at position `i` (`FoundB`): four words at a time or one (`b29_step`, `b29`,
`b30`, `b31`); the last words set up (`b34_step`, `b34`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} {j i : Nat} [Host]

/-- **Four words at a time, or one** (`b29`, `b30`, `b31`). -/
theorem b29_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : FoundB R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ ChunkB R j i 0 st' ∨ AtB34 R j i 0 st') st := by
  have hlw := G.lw64
  have hwf := G.wf0 H.fr.kept
  have hm := frMatch G H.fr
  have C : CopyB R j i 0 st.data :=
    ⟨H.fr, H.rb, H.lt, H.ilt, H.hz, H.pos, H.mem, leaf_zero, Nat.zero_le _⟩
  refine run_block G hp b29_in_code (by simp [b29]) run_b29 H.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := .X13 :: .X14 :: rbRegs) (by decide)
  have C1 : CopyB R j i 0 s1.data :=
    C.keep hfr1 hd1 fun r hr ↦ hk1 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  have hc : (SBool.cmp .ult .W64 (.reg .X21) (.lit 4)).not.eval (envOf R st.data []) =
      decide (4 ≤ R.lw) := by
    simp only [SBool.eval, ult_apply, Sym.eval, Env.ofMachine_regs]
    rw [H.rb.x21, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    by_cases h : 4 ≤ R.lw
    · rw [decide_eq_false (by omega : ¬R.lw < 4), decide_eq_true h]; rfl
    · rw [decide_eq_true (by omega : R.lw < 4), decide_eq_false h]; rfl
  simp only [PcOk, hc] at hpc1
  have hwf2 := G.wf0 hfr1.kept
  have hm2 := frMatch G hfr1
  by_cases h4 : 4 ≤ R.lw
  · simp only [h4, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b31Offset) NativeRustcVmArm.Vm.WriteOpenings.label_27_at] at hpc1
    refine run_block G hp b31_in_code (by simp [b31]) run_b31 hfr1 hpc1 hwf2 hm2 rfl
      (writesOk_frame (by decide)) fun s2 hfr2 hm2' hpc2 ↦ ?_
    have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hk2 := regs_keep hm2 hm2' (rs := .X13 :: .X14 :: rbRegs) (by decide)
    refine .done _ (.inl ⟨hpc2.trans (congrArg Host.addrOf rfl),
      C1.keep hfr2 hd2 fun r hr ↦ hk2 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)),
      by rw [hk2 .X13 (by simp), hk1 .X13 (by simp)]; exact H.x13, ?_, ?_, ?_, rfl,
      by show 0 + 4 ≤ R.lw / 4 * 4; omega⟩)
    · rw [hk2 .X14 (by simp), hk1 .X14 (by simp), H.x14, Nat.mul_zero, Nat.add_zero]
    · rw [hm2'.regs .X15 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [C1.rb.x9, Nat.mul_zero, Nat.add_zero]
    · rw [hm2'.regs .X16 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [C1.rb.x21, and124 (by omega), Nat.sub_zero]
  · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine run_block G hp b30_in_code (by simp [b30]) run_b30 hfr1
      (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
      fun s2 hfr2 hm2' hpc2 ↦ ?_
    have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hk2 := regs_keep hm2 hm2' (rs := .X13 :: rbRegs) (by decide)
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b34Offset) NativeRustcVmArm.Vm.WriteOpenings.label_30_at] at hpc2
    refine .done _ (.inr ⟨hpc2, C1.keep hfr2 hd2 fun r hr ↦ hk2 r (List.mem_cons_of_mem _ hr),
      by rw [hk2 .X13 (by simp), hk1 .X13 (by simp)]; exact H.x13, ?_, H.lw0⟩)
    rw [hm2'.regs .X15 _ rfl]
    rfl

/-- **The last words set up** (`b34`). -/
theorem b34_step (hp : Placed code R.k) (G : Geo R) {t : Nat} {st : MachineState}
    (H : AtB34 R j i t st) : Eventually (step1 Host.exe) (RemB R j i t) st := by
  have C := H.c
  have hlw := G.lw64
  have ht := H.tlt
  have hwf := G.wf0 C.fr.kept
  have hm := frMatch G C.fr
  refine run_block G hp b34_in_code (by simp [b34]) run_b34 C.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ .done _ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := rbRegs) (by decide)
  refine ⟨hpc1.trans (congrArg Host.addrOf rfl), C.keep hfr1 hd1 hk1, ?_, ?_, ?_, ht⟩
  · rw [hm1.regs .X13 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, lsl3]
    rw [H.x13, H.x15, ofNat_toNat (by omega)]
    exact addr_add rfl
  · rw [hm1.regs .X14 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, lsl3]
    rw [C.rb.x10, H.x15, ofNat_toNat (by omega)]
    exact addr_add rfl
  · rw [hm1.regs .X15 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [C.rb.x21, H.x15, ofNat_sub (by omega)]

end

end NativeRustcVmArm.Wire.WriteOpenings
