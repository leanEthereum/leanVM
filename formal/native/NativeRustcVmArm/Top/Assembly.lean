module

public import NativeRustcVmArm.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmArm.Top.Correct
public import NativeRustcVmArm.Top.Assembly.VerifyExecution
public import NativeRustcVmArm.Top.Assembly.Bus
public import NativeRustcVmArm.Top.Assembly.Wire
public import NativeRustcVmArm.Top.Assembly.Whir
public import NativeRustcVmArm.Top.Leanvm.Reject

/-!
# The end-to-end AArch64 verifier theorem

`verify_correct` proves the rustc-generated `leanvm_verify` against the verifier model under its Rust safety contract, ABI stack, and loader facts. The entry's checks guard the result, and every callee contract is discharged by its assembly proof.
-/

namespace NativeRustcVmArm.VmVerifier

open NativeRustcArm NativeVm NativeRustcVm.Top NativeRustcVm.Transcript NativeVm.Model
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

variable [NativeRustcArm.Host]

/-- The complete verifier returns the model's verdict and preserves the caller's saved state. -/
theorem verify_correct (hP : NativeRustcArm.Host.prog = Vm.code)
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.EntryPre m.dmem m.regs.X0 a bytes bytecode pub)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack)
    (hapS : ApartFrom (entryRegions m.regs.X0 a bytes.length bytecode.length)
      (stackBelow m leanvmVerifyStack) leanvmVerifyStack)
    (hapR : ∀ r ∈ entryRegions m.regs.X0 a bytes.length bytecode.length, 0 < r.size →
      RodataApart r.addr r.size) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m ∧
      st.data.regs.X0 = (if Checks a bytes.length bytecode.length
        then verdictWord bytes bytecode pub else 0) ∧
      NativeRustcVm.SameOutside m.dmem st.data.dmem (NativeRustcVm.InAny
        [⟨a.decoded.toBitVec, 8 * NativeVm.decodedWords bytes.length⟩,
          ⟨a.work.toBitVec, NativeRustcVm.Top.workAreaBytes⟩, NativeRustcVmArm.stackR m leanvmVerifyStack]) ∧
      Saved m st.data) ⟨m, label NativeRustcVmArm.Vm.LeanvmVerify.entryLabel⟩ := by
  classical
  by_cases hc : Checks a bytes.length bytecode.length
  · have hR : ∀ r ∈ usedRegions m.regs.X0 a bytes.length bytecode.length, 0 < r.size →
        RodataApart r.addr r.size := by
      intro r hr hp t
      obtain ⟨s, hs, ha, hn⟩ := usedRegions_cover hc.1 hr
      have h := hapR s hs (by omega) t
      unfold NativeRustcVm.Apart at h ⊢
      rw [ha] at h
      omega
    simpa only [ite_eq_left hc, verdictWord] using verify_correct_of_specs hP (Assembly.decode hP)
      (Assembly.verifyExecution hP (Assembly.verifyBusBalance hP) (Assembly.keccakPhase hP)
        (Assembly.nextLevel hP) (Assembly.finalLevel hP))
      (hin.checked hc.1) hc.2 hstack hrod (hapS.used hc.1) hR
  · have hctx := hapS ⟨m.regs.X0.toBitVec, 96⟩
      (by simp [entryRegions, NativeVm.Entry.ctxWords]) (by change 0 < 96; decide)
    refine NativeRustcArm.Eventually.mono
      (Top.Leanvm.reject (Placement.placed_LeanvmVerify hP) hin.toContextAt hstack hctx hc)
      fun st ⟨hpc, hx, hm, hs⟩ ↦ ⟨hpc, ?_, ?_, hs⟩
    · simpa only [ite_eq_right hc] using hx
    · intro p hp
      exact hm p fun h ↦ hp ⟨stackR m leanvmVerifyStack,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), h⟩

end

end NativeRustcVmArm.VmVerifier
