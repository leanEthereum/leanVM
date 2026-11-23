module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Read
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names

/-!
# Arithmetic calls with identified input arrays

Specializing the input slices before a call lets the symbolic return registers use the model
value without unfolding machine memory in the register-link proofs.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeVm.Model

public section

variable [Host]

theorem mleCall (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel)
    MleOfMultilinearEvalPre MleOfMultilinearEvalPost) (xs pt : Array EW) :
    Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel)
      (fun m ↦ MleOfMultilinearEvalPre m ∧ slice m (reg m .rsi) (reg m .rdx) = xs ∧
        slice m (reg m .rcx) (reg m .r8) = pt)
      (fun m m' ↦ ewRet m' = multilinearEval xs pt ∧ Changes m m' mleStack 0 0 ∧ Saved m m') := by
  intro m ⟨hp, hx, ht⟩
  exact (hmle m hp).mono fun st ⟨hpc, hsp, hr, hc, hs⟩ ↦
    ⟨hpc, hsp, by rw [hx, ht] at hr; exact hr, hc, hs⟩

theorem dotCall (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost) (xs ys : Array EW) :
    Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel)
      (fun m ↦ DotPre m ∧ slice m (reg m .rdi) (reg m .rsi) = xs ∧
        slice m (reg m .rdx) (reg m .rcx) = ys)
      (fun m m' ↦ ewRet m' = dot xs ys ∧ Changes m m' dotStack 0 0 ∧ Saved m m') := by
  intro m ⟨hp, hx, hy⟩
  exact (hdot m hp).mono fun st ⟨hpc, hsp, hr, hc, hs⟩ ↦
    ⟨hpc, hsp, by rw [hx, hy] at hr; exact hr, hc, hs⟩

omit [Host] in
theorem ewRet_lo {m : MachineData} {v : EW} (h : ewRet m = v) :
    reg m .rax = v.c0.toBitVec := congrArg (fun x : EW ↦ x.c0.toBitVec) h

omit [Host] in
theorem ewRet_hi {m : MachineData} {v : EW} (h : ewRet m = v) :
    reg m .rdx = v.c1.toBitVec := congrArg (fun x : EW ↦ x.c1.toBitVec) h

omit [Host] in
theorem changes_zero {m m' : MachineData} {N : Nat} (h : Changes m m' N 0 0) :
    SameOutside m.dmem m'.dmem (InRange (stackBelow m N) N) := by
  intro q hq
  apply h q
  intro hr
  rcases hr with hr | hr
  · obtain ⟨j, hj, -⟩ := hr
  · exact hq hr

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
