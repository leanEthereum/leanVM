module

public import NativeRustcVmArm.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmArm.Spec.Top

/-!
# The end theorem from `leanvm_verify`'s contract

`verify_correct_of`: given `leanvm_verify`'s contract (`LeanvmVerifyPre`, `LeanvmVerifyPost`), from
its label with the context at X0 as `NativeVm.Entry.EntryPre` describes it, the alignment it
checks, its stack and the read-only data in place and apart from the caller's areas, the machine
inevitably returns to its caller with X0 `1` exactly when the wire bytes decode
(`Proof.fromBytes`) to a proof `verifyWith` accepts, else `0`, no byte changed outside the decoded
and working areas and its stack, and the callee-saved registers and SP kept.
-/

namespace NativeRustcVmArm.VmVerifier

open NativeRustcArm NativeVm NativeRustcVm.Top
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

variable [NativeRustcArm.Host]

/-- **The end theorem, from `leanvm_verify`'s contract.** -/
theorem verify_correct_of
    (hspec : ∀ a bytes bytecode pub, Spec (label NativeRustcVmArm.Vm.LeanvmVerify.entryLabel)
      (LeanvmVerifyPre a bytes bytecode pub) (LeanvmVerifyPost a bytes bytecode pub))
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.EntryPre (NativeRustcVm.wordView m.dmem) m.regs.X0 a bytes bytecode pub)
    (hal : Aligned a bytes.length bytecode.length)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack)
    (hapS : ApartFrom (entryRegions m.regs.X0 a bytes.length bytecode.length)
      (stackBelow m leanvmVerifyStack) leanvmVerifyStack)
    (hapR : ∀ r ∈ entryRegions m.regs.X0 a bytes.length bytecode.length, 0 < r.size →
      RodataApart r.addr r.size) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m ∧
      st.data.regs.X0 = (if (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false
          (fun π ↦ Id.run (verifyWith (m := Id) keccakF1600 (bytecode.map K.ofLane) pub π))
        then 1 else 0) ∧
      NativeRustcVm.SameOutside m.dmem st.data.dmem (NativeRustcVm.InAny
        [⟨a.decoded.toBitVec, 8 * NativeVm.decodedWords bytes.length⟩,
          ⟨a.work.toBitVec, NativeRustcVm.Top.workAreaBytes⟩, NativeRustcVmArm.stackR m leanvmVerifyStack]) ∧
      Saved m st.data) ⟨m, label NativeRustcVmArm.Vm.LeanvmVerify.entryLabel⟩ :=
  NativeRustcArm.Eventually.mono (hspec a bytes bytecode pub m ⟨hstack, hrod, hin, hal, hapS, hapR⟩)
    fun _ ⟨hpc, hx, ho, hs⟩ ↦ ⟨hpc, hx, ho, hs⟩

end

end NativeRustcVmArm.VmVerifier
