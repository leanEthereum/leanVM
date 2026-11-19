module

public import NativeX64.Compile
public import Native.Xmss

/-!
# leanXMSS verification on x86-64

The machine code `Compile.program XmssVerifier.body XmssVerifier.onFail`, run on Kraken's x86-64
from its entry with `rdi` at a context (`Native.Context`) whose input area holds the words of a
public key, a message and a signature (`XmssVerifier.encode`), inevitably reaches the body's `ret`
with `rax = 1` if `LeanXmss.verifyWithKeccak` accepts the signature and `0` if not, and the
callee-saved registers as they were. Every layout of the code is covered (Kraken's `Host`).

The proof: `body` verifies on the QM machine (`Native.XmssVerifier.body_spec`, `Native.Xmss`), and
the compiled code does what `body` does (`Compile.program_correct`).
-/

open Native hiding Reg64 Width

@[expose] public section

namespace NativeX64.XmssVerifier

open Native.XmssVerifier

/-- **leanXMSS verification is correct on x86-64.** -/
theorem verify_correct [Host] (hP : Host.prog = Compile.program body onFail)
    {pk : HashSig.PublicKey} {msg : HashSig.Message} {sig : LeanXmss.Signature} {base : UInt64}
    {s : QState} {m : MachineData} (hR : StateRel s m) (hrdi : s.reg .rdi = base)
    (hctx : Context.At s.mem base)
    (hin : Context.InputAt s.mem base inputWords (encode pk msg sig)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (Compile.retOkIndex body) ∧
      st.data.regs.get64 .rax = (if LeanXmss.verifyWithKeccak pk msg sig then 1 else 0) ∧
      ∀ r ∈ Context.calleeSaved, st.data.regs.get64 r.toX64 = m.regs.get64 r.toX64)
      ⟨m, Host.addrOf 0⟩ := by
  obtain ⟨o, hx, ho⟩ := body_spec hrdi hctx hin
  refine eventually_weaken _ _ _ _ ?_
    (Compile.program_correct hP hx hR fun s₁ h ↦ by subst h; exact ho.elim)
  rintro st (⟨s₁, rfl, hR₁, hpc⟩ | ⟨s₁, s₂, rfl, -, -, -⟩)
  · obtain ⟨hrax, hcs⟩ := ho
    refine ⟨hpc, (hR₁.1 .rax).trans ?_, fun r hr ↦ ?_⟩
    · rw [hrax]
      split <;> rfl
    · rw [hR₁.1, hcs r hr, hR.1]
  · exact ho.elim

end NativeX64.XmssVerifier
