module

public import NativeRustcVmX64.Top.End
public import NativeRustcVmX64.Top.Leanvm
public import NativeRustcVmX64.Top.Verify
public import NativeRustcVmX64.Top.Seed
public import NativeRustcVmX64.Keccak
public import NativeRustcVmX64.Mem
public import NativeRustcVmX64.Transcript.PhaseCount
public import NativeRustcVmX64.Placed
public import NativeRustcVmX64.Code.Vm.Decode.Names
public import NativeRustcVmX64.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmX64.Code.Vm.VerifyExecution.Names

/-!
# The x86-64 end theorem from the contracts of `decode` and `verify_execution`

`verify_correct_of_specs`: the program `Vm.code`, the contracts of `decode` and
`verify_execution` given, the machine runs `leanvm_verify` to the verdict of `Proof.fromBytes`
then `verifyWith`. Every other function on the way (`leanvm_verify`, `verify`, `seed`,
`keccak256_words::<fiat_shamir_iv>`, `iv_word`, `keccak_f`, `memcpy`, `memset`,
`Decoded::phase_count`) is instantiated with its proved contract at its place in the program.
-/

namespace NativeRustcVmX64.VmVerifier

open NativeRustcX64 NativeVm NativeRustcVm.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVmX64.Placement
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

variable [Host]

/-- **`leanvm_verify`'s contract** from those of `decode` and `verify_execution`. -/
theorem leanvmVerify_spec_of (hP : Host.prog = Vm.code)
    (hdec : Spec (label NativeRustcVmX64.Vm.Decode.entryLabel) DecodePre DecodePost)
    (hve : ∀ a s, Spec (label NativeRustcVmX64.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s)) (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) :
    Spec (label NativeRustcVmX64.Vm.LeanvmVerify.entryLabel) (LeanvmVerifyPre a bytes bytecode pub)
      (LeanvmVerifyPost a bytes bytecode pub) := by
  have hmemcpy := NativeRustcVmX64.Mem.memcpy_spec (placed_Memcpy hP)
  have hmemset := NativeRustcVmX64.Mem.memset_spec (placed_Memset hP)
  have hkf := keccakF_spec (placed_KeccakF hP) hmemcpy
  have hiv := keccak256WordsIv_spec (placed_Keccak256WordsOfFiatShamirIv hP) hmemset
    (NativeRustcVmX64.IvWordRun.ivWord_spec (placed_IvWord hP)) hkf
  have hseed := Top.Seed.seed_spec (placed_Seed hP) hiv hmemset hkf hmemcpy
  have hpc := Transcript.PhaseCount.phaseCount_spec (placed_DecodedPhaseCount hP)
  have hver := Top.Verify.verify_spec (placed_Verify hP) hseed hve hpc
  exact Top.Leanvm.leanvmVerify_spec (placed_LeanvmVerify hP) hdec hver a bytes bytecode pub

/-- **The end theorem, from the contracts of `decode` and `verify_execution`.** -/
theorem verify_correct_of_specs (hP : Host.prog = Vm.code)
    (hdec : Spec (label NativeRustcVmX64.Vm.Decode.entryLabel) DecodePre DecodePost)
    (hve : ∀ a s, Spec (label NativeRustcVmX64.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s))
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {a : NativeVm.Entry.Areas}
    {m : MachineData}
    (hin : NativeVm.Entry.CheckedEntryPre m.dmem (ctxOf m) a bytes bytecode pub)
    (hal : Aligned a bytes.length bytecode.length)
    (hstack : StackOk m leanvmVerifyStack) (hrod : RodataAt m leanvmVerifyStack)
    (hapS : ApartFrom (usedRegions (ctxOf m) a bytes.length bytecode.length)
      (stackBelow m leanvmVerifyStack) (leanvmVerifyStack + 8))
    (hapR : ∀ r ∈ usedRegions (ctxOf m) a bytes.length bytecode.length, 0 < r.size →
      RodataApart r.addr r.size)
    (hgot : GotAt m leanvmVerifyStack
      ((usedRegions (ctxOf m) a bytes.length bytecode.length).map (fun r => (r.addr, r.size)) ++
        rodataAreas) ["memcpy", "memset"]) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧
      reg st.data .rax = (if (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false
          (fun π ↦ Id.run (verifyWith (m := Id) keccakF1600 (bytecode.map K.ofLane) pub π))
        then (1 : UInt64) else 0).toBitVec ∧
      NativeRustcVm.SameOutside m.dmem st.data.dmem (NativeRustcVm.InAny
        [⟨a.decoded.toBitVec, 8 * NativeVm.decodedWords bytes.length⟩,
          ⟨a.work.toBitVec, NativeRustcVm.Top.workAreaBytes⟩, NativeRustcVmX64.frameR m leanvmVerifyStack]) ∧
      Saved m st.data) ⟨m, label NativeRustcVmX64.Vm.LeanvmVerify.entryLabel⟩ :=
  verify_correct_of (leanvmVerify_spec_of hP hdec hve) hin hal hstack hrod hapS hapR hgot

end

end NativeRustcVmX64.VmVerifier
