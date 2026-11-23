module

public import NativeRustcVmX64.Spec.Top
public import NativeRustcVmX64.Code.Vm.LeanvmVerify.Names

/-!
# The end theorem from `leanvm_verify`'s contract (x86-64)

`verify_correct_of`: given `leanvm_verify`'s contract (`LeanvmVerifyPre`, `LeanvmVerifyPost`), from
its label with the context at RDI as `NativeVm.Entry.EntryPre` describes it, the alignment it
checks, its stack and the read-only data in place and apart from the caller's areas, the machine
inevitably returns to its caller with RSP 8 above (the return address popped), RAX `1` exactly
when the wire bytes decode (`Proof.fromBytes`) to a proof `verifyWith` accepts, else `0`, no byte
changed outside the decoded and working areas and its stack, and the callee-saved registers kept.
-/

namespace NativeRustcVmX64.VmVerifier

open NativeRustcX64 NativeVm NativeRustcVm.Top
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

variable [Host]

/-- **The end theorem, from `leanvm_verify`'s contract.** -/
theorem verify_correct_of
    (hspec : ∀ a bytes bytecode pub, Spec (label NativeRustcVmX64.Vm.LeanvmVerify.entryLabel)
      (LeanvmVerifyPre a bytes bytecode pub) (LeanvmVerifyPost a bytes bytecode pub))
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.EntryPre (NativeRustcVm.wordView m.dmem) (ctxOf m) a bytes bytecode pub)
    (hal : Aligned a bytes.length bytecode.length)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack)
    (hapS : ApartFrom (entryRegions (ctxOf m) a bytes.length bytecode.length)
      (stackBelow m leanvmVerifyStack) (leanvmVerifyStack + 8))
    (hapR : ∀ r ∈ entryRegions (ctxOf m) a bytes.length bytecode.length, 0 < r.size →
      RodataApart r.addr r.size)
    (hgot : GotAt m leanvmVerifyStack
      ((entryRegions (ctxOf m) a bytes.length bytecode.length).map (fun r => (r.addr, r.size)) ++
        rodataAreas) ["memcpy", "memset"]) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧
      reg st.data .rax = (if (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false
          (fun π ↦ Id.run (verifyWith (m := Id) keccakF1600 (bytecode.map K.ofLane) pub π))
        then (1 : UInt64) else 0).toBitVec ∧
      NativeRustcVm.SameOutside m.dmem st.data.dmem (NativeRustcVm.InAny
        [⟨a.decoded.toBitVec, 8 * NativeVm.decodedWords bytes.length⟩,
          ⟨a.work.toBitVec, NativeRustcVm.Top.workAreaBytes⟩, NativeRustcVmX64.frameR m leanvmVerifyStack]) ∧
      Saved m st.data) ⟨m, label NativeRustcVmX64.Vm.LeanvmVerify.entryLabel⟩ :=
  Eventually.mono (hspec a bytes bytecode pub m ⟨hstack, hrod, hin, hal, hapS, hapR, hgot⟩)
    fun _ ⟨hpc, hsp, hx, ho, hs⟩ ↦ ⟨hpc, hsp, hx, ho, hs⟩

end

end NativeRustcVmX64.VmVerifier
