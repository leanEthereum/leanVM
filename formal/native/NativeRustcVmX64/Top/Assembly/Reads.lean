module

public import NativeRustcVmX64.Top.Assembly
public import NativeRustcVmX64.Top.ReadMemory

namespace NativeRustcVmX64.VmVerifier

open NativeRustcX64 NativeVm NativeRustcVm.Top

@[expose] public section

/-- The verdict also holds with every byte outside the contract regions removed. Kraken faults on a load from those absent bytes. -/
theorem verify_correct_reads [Host] (hP : Host.prog = Vm.code)
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.EntryPre m.dmem (ctxOf m) a bytes bytecode pub)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack)
    (hapS : ApartFrom (entryRegions (ctxOf m) a bytes.length bytecode.length)
      (stackBelow m leanvmVerifyStack) (leanvmVerifyStack + 8))
    (hapR : ∀ r ∈ entryRegions (ctxOf m) a bytes.length bytecode.length, 0 < r.size →
      RodataApart r.addr r.size)
    (hgot : GotAt m leanvmVerifyStack
      ((entryRegions (ctxOf m) a bytes.length bytecode.length).map (fun r ↦ (r.addr, r.size)) ++
        rodataAreas) ["memcpy", "memset"]) :
    let confined := restrictedState m a bytes.length bytecode.length
    (∀ p, ¬ NativeRustc.ReadRegions (readRegions m a bytes.length bytecode.length) p →
      confined.dmem.get? p = none) ∧
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf confined ∧
      rspOf st.data = rspOf confined + 8#64 ∧
      reg st.data .rax = (if Checks a bytes.length bytecode.length
        then verdictWord bytes bytecode pub else 0).toBitVec ∧
      NativeRustcVm.SameOutside confined.dmem st.data.dmem (NativeRustcVm.InAny
        [⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩,
          ⟨a.work.toBitVec, workAreaBytes⟩, frameR confined leanvmVerifyStack]) ∧
      Saved confined st.data) ⟨confined, label Vm.LeanvmVerify.entryLabel⟩ := by
  dsimp only
  refine ⟨fun p hp ↦ NativeRustc.restrictMemory_outside m.dmem hp, ?_⟩
  obtain ⟨hi, hs, hr, hg⟩ := restricted_pre hin hstack hrod hgot
  exact verify_correct hP hi hs hr hapS hapR hg

end

end NativeRustcVmX64.VmVerifier
