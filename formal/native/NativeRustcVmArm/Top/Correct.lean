module

public import NativeRustcVmArm.Code.Vm.Decode.Names
public import NativeRustcVmArm.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmArm.Code.Vm.VerifyExecution.Names
public import NativeRustcVmArm.Top.End
public import NativeRustcVmArm.Top.Leanvm
public import NativeRustcVmArm.Top.Verify
public import NativeRustcVmArm.Top.Seed
public import NativeRustcVmArm.Keccak
public import NativeRustcVmArm.Mem
public import NativeRustcVmArm.Transcript.PhaseCount
public import NativeRustcVmArm.Placed

/-!
# The end theorem from the contracts not yet proved

`verify_correct_of_specs`: the program `Vm.code`, the contracts of `decode` and
`verify_execution` given, the machine runs `leanvm_verify` to the verdict of `Proof.fromBytes`
then `verifyWith`. Every other function on the way (`leanvm_verify`, `verify`, `seed`,
`keccak256_words::<fiat_shamir_iv>`, `iv_word`, `keccak_f`, `memcpy`, `memset`,
`Decoded::phase_count`) is instantiated with its proved contract at its place in the program.
-/

namespace NativeRustcVmArm.VmVerifier

open NativeRustcArm NativeVm NativeRustcVm.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVmArm.Placement
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

variable [NativeRustcArm.Host]

/-- **`leanvm_verify`'s contract** from those of `decode` and `verify_execution`. -/
theorem leanvmVerify_spec_of (hP : NativeRustcArm.Host.prog = Vm.code)
    (hdec : Spec (label NativeRustcVmArm.Vm.Decode.entryLabel) DecodePre DecodePost)
    (hve : ∀ a s, Spec (label NativeRustcVmArm.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s)) (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) :
    Spec (label NativeRustcVmArm.Vm.LeanvmVerify.entryLabel) (LeanvmVerifyPre a bytes bytecode pub)
      (LeanvmVerifyPost a bytes bytecode pub) := by
  have hmemcpy := NativeRustcVmArm.Mem.memcpy_spec (placed_Memcpy hP)
  have hmemset := NativeRustcVmArm.Mem.memset_spec (placed_Memset hP)
  have hkf := keccakF_spec (placed_KeccakF hP) hmemcpy
  have hiv := keccak256WordsIv_spec (placed_Keccak256WordsOfFiatShamirIv hP) hmemset
    (NativeRustcVmArm.ivWord_spec (placed_IvWord hP)) hkf
  have hseed := Top.Seed.seed_spec (placed_Seed hP) hiv hmemset hkf hmemcpy
  have hpc := Transcript.PhaseCount.phaseCount_spec (placed_DecodedPhaseCount hP)
  have hver := Top.Verify.verify_spec (placed_Verify hP) hseed hve hpc
  exact Top.Leanvm.leanvmVerify_spec (placed_LeanvmVerify hP) hdec hver a bytes bytecode pub

/-- **The end theorem, from the contracts of `decode` and `verify_execution`.** -/
theorem verify_correct_of_specs (hP : NativeRustcArm.Host.prog = Vm.code)
    (hdec : Spec (label NativeRustcVmArm.Vm.Decode.entryLabel) DecodePre DecodePost)
    (hve : ∀ a s, Spec (label NativeRustcVmArm.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s))
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.CheckedEntryPre m.dmem m.regs.X0 a bytes bytecode pub)
    (hal : Aligned a bytes.length bytecode.length)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack)
    (hapS : ApartFrom (usedRegions m.regs.X0 a bytes.length bytecode.length)
      (stackBelow m leanvmVerifyStack) leanvmVerifyStack)
    (hapR : ∀ r ∈ usedRegions m.regs.X0 a bytes.length bytecode.length, 0 < r.size →
      RodataApart r.addr r.size) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m ∧
      st.data.regs.X0 = (if (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false
          (fun π ↦ Id.run (verifyWith (m := Id) keccakF1600 (bytecode.map K.ofLane) pub π))
        then 1 else 0) ∧
      NativeRustcVm.SameOutside m.dmem st.data.dmem (NativeRustcVm.InAny
        [⟨a.decoded.toBitVec, 8 * NativeVm.decodedWords bytes.length⟩,
          ⟨a.work.toBitVec, NativeRustcVm.Top.workAreaBytes⟩, NativeRustcVmArm.stackR m leanvmVerifyStack]) ∧
      Saved m st.data) ⟨m, label NativeRustcVmArm.Vm.LeanvmVerify.entryLabel⟩ :=
  verify_correct_of (leanvmVerify_spec_of hP hdec hve) hin hal hstack hrod hapS hapR

end

end NativeRustcVmArm.VmVerifier
