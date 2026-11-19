module

public import Native.Sphincs.Body

/-!
# leanSPHINCS verification on the QM machine

`SphincsVerifier.body_spec` (`Native.Sphincs.Body`): run with `rdi` at a context (`Native.Context`)
whose input area holds the words of a public key, a message and a signature
(`SphincsVerifier.encode`), `body` ends normally with `rax = 1` if `Sphincs.verifyWithKeccak`
accepts the signature and `0` if not, and the callee-saved registers as they were. Each backend's
end theorem compiles `body` and carries this to its machine.

| module | proves |
|---|---|
| `Native.Sphincs.Code` | the code: `body`, `onFail` |
| `Native.Sphincs.Words`, `Native.Sphincs.Gadgets`, `Native.Sphincs.Hash` | the context's words, the gadgets, the addressed hash |
| `Native.Sphincs.DigestSpec`, `Native.Sphincs.Digest` | the message digest, its index and its FORS leaves |
| `Native.Sphincs.Path`, `Native.Sphincs.Fors` | a Merkle node's input; the FORS public key |
| `Native.Sphincs.LayerSpec` | the layers and `verifyWithKeccak` in `Id` |
| `Native.Sphincs.Chain`, `Native.Sphincs.Tree` | a one-time key's chains; a layer's tree |
| `Native.Sphincs.Encode`, `Native.Sphincs.Layer` | a layer's key, codeword and digits; one layer |
| `Native.Sphincs.Layers`, `Native.Sphincs.Body` | the hypertree and the result; the whole body |
-/
