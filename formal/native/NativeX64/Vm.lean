module

public import NativeX64.Compile
public import NativeVm.Code.Entry

/-!
# leanVM verification on x86-64

The machine code `Compile.program NativeVm.Code.body NativeVm.Code.onFail`, run on Kraken's x86-64
from its entry with `rdi` at a context holding the wire bytes, the bytecode words and the public
input as `NativeVm.Input` lays them out, with room for the decoded proof and the working area
(`NativeVm.Code.EntryPre`), inevitably reaches a `ret`, the body's or the failure handler's, with
`rax = 1` if the bytes decode (`Proof.fromBytes`) to a proof `verifyWith` accepts and `0` if not,
and the callee-saved registers as they were. Every layout of the code is covered (Kraken's `Host`).

The proof: from `EntryPre`, `body` ends with the verdict or fails and `onFail` ends with it
(`NativeVm.Code.entry_spec`, from the wire decoder's and the seven phases' contracts), and
the compiled code does what they do (`Compile.program_correct`).
-/

open Native hiding Reg64 Width
open NativeVm.Code (body onFail Areas EntryPre entry_spec verdict_input)
open LeanVM.Parameters (K)
open LeanVM.Semantics (keccakF1600)
open LeanVM.Protocol.Compile (Proof)
open LeanVM.Protocol.Verifier (verifyWith)

@[expose] public section

namespace NativeX64.VmVerifier

/-- **leanVM verification is correct on x86-64**. -/
theorem verify_correct [Host] (hP : Host.prog = Compile.program body onFail)
    {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4} {ctx : UInt64}
    {a : Areas} {s : QState} {m : MachineData} (hR : StateRel s m) (hrdi : s.reg .rdi = ctx)
    (hin : EntryPre s.mem ctx a bytes bytecode pub) :
    Eventually (step1 Host.exe) (fun st ↦
      (st.pc = Host.addrOf (Compile.retOkIndex body) ∨
        st.pc = Host.addrOf (Compile.retFailIndex body onFail)) ∧
      st.data.regs.get64 .rax =
        (if (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false
            (fun π ↦ Id.run (verifyWith (m := Id) keccakF1600 (bytecode.map K.ofLane) pub π))
          then 1 else 0) ∧
      ∀ r ∈ Context.calleeSaved, st.data.regs.get64 r.toX64 = m.regs.get64 r.toX64)
      ⟨m, Host.addrOf 0⟩ := by
  obtain ⟨o, hx, ho⟩ := entry_spec hrdi hin
  refine eventually_weaken _ _ _ _ ?_ (Compile.program_correct hP hx hR fun s₁ h ↦ ?_)
  · rintro st (⟨s₁, rfl, hR₁, hpc⟩ | ⟨s₁, s₂, rfl, hE₂, hR₂, hpc⟩)
    · obtain ⟨hrax, hcs⟩ := ho
      refine ⟨Or.inl hpc, (hR₁.1 .rax).trans ?_, fun r hr ↦ ?_⟩
      · rw [hrax, verdict_input]
        split <;> rfl
      · rw [hR₁.1, hcs r hr, hR.1]
    · obtain ⟨o', hx', ho'⟩ := ho
      obtain rfl := hx'.det hE₂
      obtain ⟨hrax, hcs⟩ := ho'
      refine ⟨Or.inr hpc, (hR₂.1 .rax).trans ?_, fun r hr ↦ ?_⟩
      · rw [hrax, verdict_input]
        split <;> rfl
      · rw [hR₂.1, hcs r hr, hR.1]
  · subst h
    obtain ⟨o', hx', ho'⟩ := ho
    cases o' with
    | ok s₂ => exact ⟨s₂, hx'⟩
    | err _ => exact ho'.elim

end NativeX64.VmVerifier
