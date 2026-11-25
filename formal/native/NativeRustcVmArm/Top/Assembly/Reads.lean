module

public import NativeRustcVmArm.Top.Assembly
public import NativeRustcVmArm.Top.ReadMemory

namespace NativeRustcVmArm.VmVerifier

open NativeRustcArm NativeVm NativeRustcVm.Top

@[expose] public section

/-- The verdict also holds with every byte outside the contract regions removed. Kraken faults on a load from those absent bytes. -/
theorem verify_correct_reads [Host] (hP : Host.prog = Vm.code)
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.EntryPre m.dmem m.regs.X0 a bytes bytecode pub)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack)
    (hapS : ApartFrom (entryRegions m.regs.X0 a bytes.length bytecode.length)
      (stackBelow m leanvmVerifyStack) leanvmVerifyStack)
    (hapR : ∀ r ∈ entryRegions m.regs.X0 a bytes.length bytecode.length, 0 < r.size →
      RodataApart r.addr r.size) :
    let confined := restrictedState m a bytes.length bytecode.length
    (∀ p, ¬ NativeRustc.ReadRegions (readRegions m a bytes.length bytecode.length) p →
      confined.dmem.get? p = none) ∧
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf confined ∧
      st.data.regs.X0 = (if Checks a bytes.length bytecode.length
        then verdictWord bytes bytecode pub else 0) ∧
      NativeRustcVm.SameOutside confined.dmem st.data.dmem (NativeRustcVm.InAny
        [⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩,
          ⟨a.work.toBitVec, workAreaBytes⟩, stackR confined leanvmVerifyStack]) ∧
      Saved confined st.data) ⟨confined, label Vm.LeanvmVerify.entryLabel⟩ := by
  dsimp only
  refine ⟨fun p hp ↦ NativeRustc.restrictMemory_outside m.dmem hp, ?_⟩
  obtain ⟨hi, hs, hr⟩ := restricted_pre hin hstack hrod
  exact verify_correct hP hi hs hr hapS hapR

end

end NativeRustcVmArm.VmVerifier
