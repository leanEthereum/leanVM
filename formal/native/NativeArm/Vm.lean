module

public import NativeArm.Verify
public import NativeVm.Code.Entry

/-!
# leanVM verification on AArch64

The machine code `Compile.program NativeVm.Code.body NativeVm.Code.onFail`, run on Kraken's
AArch64 from its entry with `rdi` (X0) at a context holding the wire bytes, the bytecode words and
the public input as `NativeVm.Input` lays them out, with room for the decoded proof and the working
area (`NativeVm.Code.EntryPre`), inevitably reaches a `RET`, the body's or the failure handler's,
with X0 `1` if the bytes decode (`Proof.fromBytes`) to a proof `verifyWith` accepts and `0` if not,
and every register AAPCS64 asks a procedure to preserve (X19 to X30, SP) as it was. Every layout of
the code is covered (`NativeArm.Host`).

The proof: from `EntryPre`, `body` ends with the verdict or fails and `onFail` ends with it
(`NativeVm.Code.entry_spec`, from the wire decoder's and the seven phases' contracts), the
compiled code does what they do (`Compile.program_correct`), and neither writes `rsp` (X25), which
the kernel checks.
-/

open Native
open NativeVm.Code (body onFail Areas EntryPre entry_spec verdict_input)
open LeanVM.Parameters (K)
open LeanVM.Semantics (keccakF1600)
open LeanVM.Protocol.Compile (Proof)
open LeanVM.Protocol.Verifier (verifyWith)

@[expose] public section

namespace NativeArm.VmVerifier

/-- **leanVM verification is correct on AArch64**. -/
theorem verify_correct [Host] (hP : Host.prog = Compile.program body onFail)
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {ctx : UInt64}
    {a : Areas} {s : QState} {m : MachineData} (hR : StateRel s m) (hrdi : s.reg .rdi = ctx)
    (hin : EntryPre s.mem ctx a bytes bytecode pub) :
    Eventually (step1 Host.exe) (fun st ↦
      (st.pc = Host.addrOf (Compile.retOkIndex body) ∨
        st.pc = Host.addrOf (Compile.retFailIndex body onFail)) ∧
      st.data.regs.X0 =
        (if (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false
            (fun π ↦ Id.run (verifyWith (m := Id) keccakF1600 (bytecode.map K.ofLane) pub π))
          then 1 else 0) ∧
      (∀ x : XReg, x.saved = true → st.data.regs.getXReg x = m.regs.getXReg x) ∧
      st.data.regs.SP = m.regs.SP)
      ⟨m, Host.addrOf 0⟩ := by
  obtain ⟨o, hx, ho⟩ := entry_spec hrdi hin
  refine eventually_weaken _ _ _ _ ?_ (Compile.program_correct hP hx hR fun s₁ h ↦ ?_)
  · rintro st (⟨s₁, rfl, hX, hpc⟩ | ⟨s₁, s₂, rfl, hE₂, hX, hpc⟩)
    · obtain ⟨hrax, hcs⟩ := ho
      refine ⟨Or.inl hpc, hX.1.trans ?_, hX.saved hR hcs (by decide +kernel)⟩
      rw [hrax, verdict_input]
    · obtain ⟨o', hx', ho'⟩ := ho
      obtain rfl := hx'.det hE₂
      obtain ⟨hrax, hcs⟩ := ho'
      refine ⟨Or.inr hpc, hX.1.trans ?_,
        Compile.Exits.saved (body := .seq body onFail) hR hX hcs (by decide +kernel)⟩
      rw [hrax, verdict_input]
  · subst h
    obtain ⟨o', hx', ho'⟩ := ho
    cases o' with
    | ok s₂ => exact ⟨s₂, hx'⟩
    | err _ => exact ho'.elim

end NativeArm.VmVerifier
