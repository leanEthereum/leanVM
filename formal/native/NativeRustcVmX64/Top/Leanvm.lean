module

public import NativeRustcVmX64.Top.Leanvm.Stage3
public import NativeRustcVmX64.Code.Vm.Decode.Names
public import NativeRustcVmX64.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmX64.Code.Vm.Verify.Names

/-!
# `leanvm_verify` on x86-64

**`leanvmVerify_spec`**: rustc's `leanvm_verify`, placed anywhere in the program, meets its
contract (`LeanvmVerifyPre`, `LeanvmVerifyPost`) given the contracts of `decode` and `verify`. The
prologue and the checks (`checks`), the decoder (`stage2`: RAX `0` when it refuses the wire's
bytes), the verifier (`stage3`); the verdict is the model's (`verdict_none`, `verdict_some`).
-/

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcVmX64.Vm.LeanvmVerify NativeVm NativeRustcVm.Transcript

public section

variable [Host] {k : Nat}

/-- **`leanvm_verify` meets its contract.** -/
theorem leanvmVerify_spec (hp : Placed code k)
    (hdec : Spec (Labels.label NativeRustcVmX64.Vm.Decode.entryLabel) DecodePre DecodePost)
    (hver : ∀ a stream openings, Spec (Labels.label NativeRustcVmX64.Vm.Verify.entryLabel) (VerifyPre a stream openings)
      (VerifyPost stream openings))
    (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64) (pub : Vector UInt64 4) :
    Spec (Labels.label NativeRustcVmX64.Vm.LeanvmVerify.entryLabel) (LeanvmVerifyPre a bytes bytecode pub)
      (LeanvmVerifyPost a bytes bytecode pub) := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hOut : ∀ q, Out m0 a bytes.length q → NativeRustcVm.InAny
      [⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩, ⟨a.work.toBitVec,
        NativeRustcVm.Top.workAreaBytes⟩, frameR m0 leanvmVerifyStack] q := by
    rintro q (h | h | h)
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), h⟩
    · exact ⟨_, List.mem_cons_self, h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
  refine Eventually.bind (checks hp hpre) fun st1 ⟨hpc1, hC⟩ ↦ ?_
  refine Eventually.bind (stage2 hp hdec hpre hpc1 hC) fun st2 h2 ↦ ?_
  rcases h2 with ⟨hnone, hpc, hrsp, hx, hsame, hsv⟩ | ⟨r, hr, hpc3, hA, hD⟩
  · refine Eventually.done _ ⟨hpc, hrsp, ?_, fun q hq ↦ hsame q fun h ↦ hq (hOut q h), hsv⟩
    rw [hx, verdict_none hnone]
    rfl
  · refine Eventually.mono (stage3 hp hver hpre hpc3 hA hD) fun st ⟨h1, h2, h3, h4, h5⟩ ↦
      ⟨h1, h2, ?_, fun q hq ↦ h4 q fun h ↦ hq (hOut q h), h5⟩
    rw [h3, verdict_some hr]
    rfl

end

end NativeRustcVmX64.Top.Leanvm
