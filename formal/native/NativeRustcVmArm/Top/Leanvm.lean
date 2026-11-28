module

public import NativeRustcVmArm.Code.Vm.Decode.Names
public import NativeRustcVmArm.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmArm.Code.Vm.Verify.Names
public import NativeRustcVmArm.Top.Leanvm.Checks
public import NativeRustcVmArm.Top.Leanvm.Stage3

/-!
# `leanvm_verify` on AArch64

**`leanvmVerify_spec`**: rustc's `leanvm_verify`, placed anywhere in the program, meets its
contract (`LeanvmVerifyPre`, `LeanvmVerifyPost`) given the contracts of `decode` and `verify`.
The prologue and the counts' checks (`stage0`), the areas' checks (`stage1`), the decoder
(`stage2`: `0` when it refuses the wire's bytes), the verifier (`stage3`); the verdict is the
model's (`verdict_none`, `verdict_some`).
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm.Top (workAreaBytes)

public section

/-- The verifier's changes are in `LeanvmVerifyPost`'s areas. -/
theorem R2_inAny [Labels] {a : NativeVm.Entry.Areas} {L : Nat} {m0 : MachineData}
    (hs : leanvmVerifyStack ≤ m0.regs.SP.toBitVec.toNat) {q : BitVec 64}
    (h : R2 a L m0 q) : NativeRustcVm.InAny [⟨a.decoded.toBitVec, 8 * decodedWords L⟩,
      ⟨a.work.toBitVec, workAreaBytes⟩, stackR m0 leanvmVerifyStack] q := by
  rcases h with h | h | h
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
    show InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 leanvmVerifyStack) leanvmVerifyStack q
    rw [inRange_below hs]
    exact h
  · exact ⟨_, List.mem_cons_self, h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩

variable [Host] {k : Nat}

/-- **`leanvm_verify` meets its contract.** -/
theorem leanvmVerify_spec (hp : Placed code k)
    (hdec : Spec (Labels.label NativeRustcVmArm.Vm.Decode.entryLabel) DecodePre DecodePost)
    (hver : ∀ a stream openings, Spec (Labels.label NativeRustcVmArm.Vm.Verify.entryLabel) (VerifyPre a stream openings)
      (VerifyPost stream openings))
    (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64) (pub : Vector UInt64 4) :
    Spec (Labels.label NativeRustcVmArm.Vm.LeanvmVerify.entryLabel) (LeanvmVerifyPre a bytes bytecode pub)
      (LeanvmVerifyPost a bytes bytecode pub) := by
  intro m0 hpre
  have hs : leanvmVerifyStack ≤ m0.regs.SP.toBitVec.toNat := hpre.1.2.1
  rw [lbl_entry hp]
  refine Eventually.bind (stage0 hp hpre) fun st1 ⟨hpc1, hB1, hcM, hx0, hx19, hx20, hx21⟩ ↦ ?_
  refine Eventually.bind (stage1 hp hpre hpc1 hB1 hcM hx0 hx19 hx20 hx21)
    fun st2 ⟨hpc2, h2⟩ ↦ ?_
  refine Eventually.bind (stage2 hp hdec hpre hpc2 h2) fun st3 h3 ↦ ?_
  rcases h3 with ⟨hnone, hpc, hx, hsame, hsv⟩ | ⟨r, hr, hpc3, hC2⟩
  · refine Eventually.done _ ⟨hpc, ?_, fun q hq ↦ hsame q fun h ↦ hq (R2_inAny hs h), hsv⟩
    rw [hx, verdict_none hnone]
  · refine Eventually.mono (stage3 hp hver hpre hpc3 hC2) fun st ⟨h1, h2, h3, h4⟩ ↦
      ⟨h1, ?_, fun q hq ↦ h3 q fun h ↦ hq (R2_inAny hs h), h4⟩
    rw [h2, verdict_some hr]

end

end NativeRustcVmArm.Top.Leanvm
