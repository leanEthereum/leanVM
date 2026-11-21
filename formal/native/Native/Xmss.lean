module

public import Native.Xmss.Body
public import Native.Xmss.ModelSpec

/-!
# leanXMSS verification on the QM machine

`XmssVerifier.body_spec`: run with `rdi` at a context (`Native.Context`) whose input area holds the
words of a public key, a message and a signature (`XmssVerifier.encode`), `body` ends normally with
`rax = 1` if `LeanXmss.verifyWithKeccak` accepts the signature and `0` if not, and the callee-saved
registers as they were. Each backend's end theorem compiles `body` and carries this to its machine.

The proof: `body` computes the word model `verifyW` (`body_verifyW`), which is `verifyWithKeccak`
on the encoded input (`verifyW_encode`).

| module | proves |
|---|---|
| `Native.Xmss.Code` | the code: `body`, `onFail` |
| `Native.Xmss.Model` | the word model `verifyW` |
| `Native.Xmss.ModelSpec` | `verifyW (encode pk msg sig) = verifyWithKeccak pk msg sig` |
| `Native.Xmss.Mem` | the context's words, steps through blocks, `Keccak.hash` on context words |
| `Native.Xmss.Chain` | a chain step, a chain, the 58 chains |
| `Native.Xmss.Message`, `Native.Xmss.Tree` | the message digest; the leaf, a node, the path |
| `Native.Xmss.Layer`, `Native.Xmss.Body` | one layer; the whole body |
-/

@[expose] public section

namespace Native.XmssVerifier

/-- **`body` verifies**: it ends normally with `rax = 1` if `verifyWithKeccak` accepts the encoded
input and `0` if not, and keeps the callee-saved registers. -/
theorem body_spec {s : QState} {pk : HashSig.PublicKey} {msg : HashSig.Message}
    {sig : LeanXmss.Signature} {base : UInt64} (hrdi : s.reg .rdi = base)
    (hctx : Context.At s.mem base)
    (hin : Context.InputAt s.mem base inputWords (encode pk msg sig)) :
    WP body s (fun s' ↦ s'.reg .rax = (if LeanXmss.verifyWithKeccak pk msg sig then 1 else 0) ∧
      ∀ r ∈ Context.calleeSaved, s'.reg r = s.reg r) (fun _ ↦ False) :=
  WP.mono (body_verifyW hrdi hctx hin) (fun _ h ↦ ⟨by rw [h.1, verifyW_encode], h.2⟩)
    fun _ h ↦ h

end Native.XmssVerifier
