module

public import X86.Compile
public import X86.Xmss.Body
public import X86.Xmss.ModelSpec

/-!
# leanXMSS verification on x86-64

The machine code `Compile.program XmssVerifier.body XmssVerifier.onFail`, run on Kraken's x86-64
from its entry with `rdi` at a context (`X86.Context`) whose input area holds the words of a public
key, a message and a signature (`XmssVerifier.encode`), inevitably reaches the body's `ret` with
`rax = 1` if `LeanXmss.verifyWithKeccak` accepts the signature and `0` if not, and the callee-saved
registers as they were. Every layout of the code is covered (Kraken's `Host`).

The proof: `body` computes the word model `verifyW` (`X86.Xmss.Body`), which is
`verifyWithKeccak` on the encoded input (`X86.Xmss.ModelSpec`), and the compiled code does what
`body` does (`Compile.program_correct`).

| module | proves |
|---|---|
| `X86.Xmss.Code` | the code: `body`, `onFail` |
| `X86.Xmss.Model` | the word model `verifyW` |
| `X86.Xmss.ModelSpec` | `verifyW (encode pk msg sig) = verifyWithKeccak pk msg sig` |
| `X86.Xmss.Mem` | the context's words, steps through blocks, `Keccak.hash` on context words |
| `X86.Xmss.Chain` | a chain step, a chain, the 58 chains |
| `X86.Xmss.Message`, `X86.Xmss.Tree` | the message digest; the leaf, a node, the path |
| `X86.Xmss.Layer`, `X86.Xmss.Body` | one layer; the whole body |
-/

@[expose] public section

namespace X86.XmssVerifier

/-- **leanXMSS verification is correct on x86-64.** -/
theorem verify_correct [Host] (hP : Host.prog = Compile.program body onFail)
    {pk : HashSig.PublicKey} {msg : HashSig.Message} {sig : LeanXmss.Signature} {base : UInt64}
    {s : QState} {m : MachineData} (hR : StateRel s m) (hrdi : s.reg .rdi = base)
    (hctx : Context.At s.mem base)
    (hin : Context.InputAt s.mem base inputWords (encode pk msg sig)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (Compile.retOkIndex body) ∧
      st.data.regs.get64 .rax = (if LeanXmss.verifyWithKeccak pk msg sig then 1 else 0) ∧
      ∀ r ∈ Context.calleeSaved, st.data.regs.get64 r = m.regs.get64 r) ⟨m, Host.addrOf 0⟩ := by
  obtain ⟨o, hx, ho⟩ := body_spec hrdi hctx hin
  refine eventually_weaken _ _ _ _ ?_
    (Compile.program_correct hP hx hR fun s₁ h ↦ by subst h; exact ho.elim)
  rintro st (⟨s₁, rfl, hR₁, hpc⟩ | ⟨s₁, s₂, rfl, -, -, -⟩)
  · obtain ⟨hrax, hcs⟩ := ho
    refine ⟨hpc, ?_, fun r hr ↦ ?_⟩
    · rw [hR₁.1, hrax, verifyW_encode]
      split <;> rfl
    · rw [hR₁.1, hcs r hr, hR.1]
  · exact ho.elim

end X86.XmssVerifier
