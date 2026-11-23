module

public import NativeRustcVmX64.Top.Correct
public import NativeRustcVmX64.Top.Assembly.VerifyExecution
public import NativeRustcVmX64.Top.Assembly.Wire
public import NativeRustcVmX64.Code.Vm.LeanvmVerify.Names

/-!
# The end-to-end x86-64 verifier theorem

`verify_correct` proves rustc's raw `leanvm_verify` assembly against the verifier model. Every callee contract is discharged by its assembly proof at its place in `Vm.code`; only the program placement, entry, memory, alignment, and loader-slot (`GotAt`) assumptions remain.
-/

namespace NativeRustcVmX64.VmVerifier

open NativeRustcX64 NativeVm NativeRustcVm.Top NativeRustcVm.Transcript NativeVm.Model
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

variable [Host]

/-- The complete verifier returns the model's verdict in RAX, pops its return address, and preserves the caller's saved state. -/
theorem verify_correct (hP : Host.prog = Vm.code)
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
  verify_correct_of_specs hP (Assembly.decode hP) (Assembly.verifyExecution hP)
    hin hal hstack hrod hapS hapR hgot

end

end NativeRustcVmX64.VmVerifier
