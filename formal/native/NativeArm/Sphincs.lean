module

public import NativeArm.Verify
public import Native.Sphincs

/-!
# leanSPHINCS verification on AArch64

The machine code `Compile.program SphincsVerifier.body SphincsVerifier.onFail`, run on Kraken's
AArch64 from its entry with `rdi` (X0) at a context (`Native.Context`) whose input area holds the
words of a public key, a message and a signature (`SphincsVerifier.encode`), inevitably reaches the
body's `RET` with X0 `1` if `Sphincs.verifyWithKeccak` accepts the signature and `0` if not, and
every register AAPCS64 asks a procedure to preserve (X19 to X30, SP) as it was. Every layout of the
code is covered (`NativeArm.Host`).

The proof: `body` verifies on the QM machine (`Native.SphincsVerifier.body_spec`, `Native.Sphincs`),
the compiled code does what `body` does (`Compile.program_correct`), and `body` never writes `rsp`
(X25), which the kernel checks.
-/

open Native

@[expose] public section

namespace NativeArm.SphincsVerifier

open Native.SphincsVerifier

/-- **leanSPHINCS verification is correct on AArch64.** -/
theorem verify_correct [Host] (hP : Host.prog = Compile.program body onFail)
    {pk : _root_.Sphincs.PublicKey} {msg : HashSig.Message} {sig : _root_.Sphincs.Signature}
    {base : UInt64} {s : QState} {m : MachineData} (hR : StateRel s m) (hrdi : s.reg .rdi = base)
    (hctx : Context.At s.mem base)
    (hin : Context.InputAt s.mem base inputWords (encode pk msg sig)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (Compile.retOkIndex body) ∧
      st.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak pk msg sig then 1 else 0) ∧
      (∀ x : XReg, x.saved = true → st.data.regs.getXReg x = m.regs.getXReg x) ∧
      st.data.regs.SP = m.regs.SP)
      ⟨m, Host.addrOf 0⟩ := by
  obtain ⟨o, hx, ho⟩ := body_spec hrdi hctx hin
  refine eventually_weaken _ _ _ _ ?_
    (Compile.program_correct hP hx hR fun s₁ h ↦ by subst h; exact ho.elim)
  rintro st (⟨s₁, rfl, hX, hpc⟩ | ⟨s₁, s₂, rfl, -, -, -⟩)
  · obtain ⟨hrax, hcs⟩ := ho
    refine ⟨hpc, hX.1.trans ?_, hX.saved hR hcs (by decide +kernel)⟩
    rw [hrax]
  · exact ho.elim

end NativeArm.SphincsVerifier
