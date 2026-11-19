module

public import X86.Compile
public import X86.Sphincs.Body

/-!
# leanSPHINCS verification on x86-64

The machine code `Compile.program SphincsVerifier.body SphincsVerifier.onFail`, run on Kraken's
x86-64 from its entry with `rdi` at a context (`X86.Context`) whose input area holds the words of
a public key, a message and a signature (`SphincsVerifier.encode`), inevitably reaches the body's
`ret` with `rax = 1` if `Sphincs.verifyWithKeccak` accepts the signature and `0` if not, and the
callee-saved registers as they were. Every layout of the code is covered (Kraken's `Host`).

The proof: `body` computes `verifyWithKeccak` on the encoded input (`body_spec`), and the compiled
code does what `body` does (`Compile.program_correct`).

| module | proves |
|---|---|
| `X86.Sphincs.Code` | the code: `body`, `onFail` |
| `X86.Sphincs.Words`, `X86.Sphincs.Gadgets`, `X86.Sphincs.Hash` | the context's words, the gadgets, the addressed hash |
| `X86.Sphincs.DigestSpec`, `X86.Sphincs.Digest` | the message digest, its index and its FORS leaves |
| `X86.Sphincs.Path`, `X86.Sphincs.Fors` | a Merkle node's input; the FORS public key |
| `X86.Sphincs.LayerSpec` | the layers and `verifyWithKeccak` in `Id` |
| `X86.Sphincs.Chain`, `X86.Sphincs.Tree` | a one-time key's chains; a layer's tree |
| `X86.Sphincs.Encode`, `X86.Sphincs.Layer` | a layer's key, codeword and digits; one layer |
| `X86.Sphincs.Layers`, `X86.Sphincs.Body` | the hypertree and the result; the whole body |
-/

@[expose] public section

namespace X86.SphincsVerifier

/-- **leanSPHINCS verification is correct on x86-64.** -/
theorem verify_correct [Host] (hP : Host.prog = Compile.program body onFail)
    {pk : _root_.Sphincs.PublicKey} {msg : HashSig.Message} {sig : _root_.Sphincs.Signature}
    {base : UInt64} {s : QState} {m : MachineData} (hR : StateRel s m) (hrdi : s.reg .rdi = base)
    (hctx : Context.At s.mem base)
    (hin : Context.InputAt s.mem base inputWords (encode pk msg sig)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (Compile.retOkIndex body) ∧
      st.data.regs.get64 .rax = (if _root_.Sphincs.verifyWithKeccak pk msg sig then 1 else 0) ∧
      ∀ r ∈ Context.calleeSaved, st.data.regs.get64 r = m.regs.get64 r) ⟨m, Host.addrOf 0⟩ := by
  obtain ⟨o, hx, ho⟩ := body_spec hrdi hctx hin
  refine eventually_weaken _ _ _ _ ?_
    (Compile.program_correct hP hx hR fun s₁ h ↦ by subst h; exact ho.elim)
  rintro st (⟨s₁, rfl, hR₁, hpc⟩ | ⟨s₁, s₂, rfl, -, -, -⟩)
  · obtain ⟨hrax, hcs⟩ := ho
    refine ⟨hpc, ?_, fun r hr ↦ ?_⟩
    · rw [hR₁.1, hrax]
      split <;> rfl
    · rw [hR₁.1, hcs r hr, hR.1]
  · exact ho.elim

end X86.SphincsVerifier
