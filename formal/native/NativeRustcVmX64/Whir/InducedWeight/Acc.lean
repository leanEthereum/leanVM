module

public import NativeRustcVmX64.Whir.InducedWeight.Outer

/-!
# `induced_weight`'s sum transition

Block `b6` adds the completed product, advances the query index and either returns the sum
or re-enters the outer loop. No memory is changed.
-/

namespace NativeRustcVmX64.Whir.InducedWeight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVmX64.Field (midS frameEnv)
open NativeRustcVmX64.Arrays (load8_eq eval_reg eval_lit eval_load eval_add eval_cmp_eq)

public section

variable [Host] {k : Nat}

theorem accumulate (hp : Placed code k) {m0 : MachineData} (hpre : InducedWeightPre m0)
    {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b6Offset))
    (hA : Acc m0 j st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b7Offset) ∧ OInv m0 (j + 1) st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b17Offset) ∧ Done m0 st'.data)) st := by
  have hS := hpre.1
  have hF := stack_le.1
  have hfr := hA.fr
  let env := frameEnv m0 st.data 1168 (fun _ ↦ 0) 0
  have hwf : env.WF := hfr.wf hS hF
  have hc64 : cntOf m0 < 2 ^ 64 := by
    unfold cntOf
    have := (reg m0 .r9).isLt
    omega
  have hj := hA.hj
  have l40 : env.load 0 40 8 = BitVec.ofNat 64 (tbOf m0).size := by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt
      (word_at hA.sp.ptrs 1 (by simp)))
  have l48 : env.load 0 48 8 = BitVec.ofNat 64 (cntOf m0) := by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt
      (word_at hA.sp.ptrs 2 (by simp)))
  have l72 : env.load 0 72 8 = BitVec.ofNat 64 j := by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt hA.lp.idx)
  obtain ⟨w80, w88⟩ := NativeRustcVm.ewAt_iff.mp hA.lp.tot
  rw [addr_add] at w88
  have l80 : env.load 0 80 8 = (totOf m0 j).c0.toBitVec := by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt w80)
  have l88 : env.load 0 88 8 = (totOf m0 j).c1.toBitVec := by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt w88)
  have hi : (Sym.bin .add .W64 (.load 0 72 8) (.lit 1)).eval env =
      BitVec.ofNat 64 (j + 1) := by
    rw [eval_add, eval_load, eval_lit, l72, ← BitVec.ofNat_add]
  refine exec_at (b6_in_code.trans hp.1 (by simp [b6])) run_b6 hwf
    (by intro l h; cases h) hpc hfr.mid_match fun st' hm hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq hwf rfl
  have hf' : Fr m0 st'.data := hfr.of_block hfr.mid_match hm hwf rfl
    (after_eq run_b6 ▸ b6_keeps)
  have hrsi : reg st'.data .rsi = BitVec.ofNat 64 (j + 1) := (hm.regs .rsi _ rfl).trans hi
  have hrcx : reg st'.data .rcx = (totOf m0 (j + 1)).c0.toBitVec := by
    rw [show reg st'.data .rcx = _ from hm.regs .rcx _ rfl]
    change env.load 0 80 8 ^^^ reg st.data .rbx = _
    rw [l80, hA.rbx, totOf_succ m0 hj]
    rfl
  have hrax : reg st'.data .rax = (totOf m0 (j + 1)).c1.toBitVec := by
    rw [show reg st'.data .rax = _ from hm.regs .rax _ rfl]
    change env.load 0 88 8 ^^^ reg st.data .r12 = _
    rw [l88, hA.r12, totOf_succ m0 hj]
    rfl
  have hrdx : reg st'.data .rdx = BitVec.ofNat 64 (tbOf m0).size :=
    (hm.regs .rdx _ rfl).trans l40
  have hr14 : reg st'.data .r14 = stackArg m0 0 :=
    (Match.reg_eq hfr.mid_match hm rfl rfl).trans hA.r14
  simp only [PcOk] at hpc'
  rw [eval_cmp_eq, hi, eval_load, l48, ofNat_beq (by omega) hc64] at hpc'
  obtain ⟨hT, hF'⟩ := Arrays.pc_cond hpc'
  by_cases hlast : j + 1 = cntOf m0
  · refine .done _ (.inr ⟨(hT (by simpa using hlast)).trans (hp.label NativeRustcVmX64.Vm.InducedWeight.label_10_at),
      hf', hd ▸ hA.sp.out, hA.mu, ?_, ?_⟩)
    · rwa [← hlast]
    · rwa [← hlast]
  · exact .done _ (.inl ⟨hF' (by simpa using hlast), hf', hA.sp.of_dmem hd, by omega,
      hA.mu, hrsi, hrcx, hrax, hrdx, hr14⟩)

end

end NativeRustcVmX64.Whir.InducedWeight
