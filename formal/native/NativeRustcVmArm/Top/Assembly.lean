module

public import NativeRustcVmArm.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmArm.Top.Correct
public import NativeRustcVmArm.Top.Assembly.VerifyExecution
public import NativeRustcVmArm.Top.Assembly.Bus
public import NativeRustcVmArm.Top.Assembly.Wire
public import NativeRustcVmArm.Top.Assembly.Whir

/-!
# The end-to-end AArch64 verifier theorem

`verify_correct` proves the rustc-generated `leanvm_verify` against the verifier model. Every callee contract is discharged by its assembly proof at its place in `Vm.code`; only the program placement and natural entry, memory, and alignment assumptions remain.
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
  verify_correct_of_specs hP (Assembly.decode hP)
    (Assembly.verifyExecution hP (Assembly.verifyBusBalance hP) (Assembly.keccakPhase hP)
      (Assembly.nextLevel hP) (Assembly.finalLevel hP))
    hin hal hstack hrod hapS hapR

end

end NativeRustcVmArm.VmVerifier
