module

public import NativeRustcX64.SphincsVerify.Digest.Index

/-!
# Region 2, the digest: `DigestSpec` (x86-64)

From `AtHMsg` at `b43` to `AtFors` at `b58`: `h_msg`'s hasher (`absorb_spec`), its two calls
(`hash0_spec`, `hash1_spec`, `hMsg_spec`), `digest_fields`' leaves (`loop_spec`) and index, the
FORS loop's registers (`index_spec`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open Digest

public section

/-- **Region 2, the digest** (x86-64). -/
theorem digest_spec [ElfHost] : DigestSpec := by
  intro r hp hc hpre m hA
  exact Run.stage r (absorb_spec r hp hc hpre hA) fun m₁ h₁ ↦
    Run.stage r (hash0_spec r hp hc hpre h₁) fun m₂ h₂ ↦
    Run.stage r (hash1_spec r hp hc hpre h₂) fun m₃ h₃ ↦
    Run.stage r (hMsg_spec r hp hpre h₃) fun m₄ h₄ ↦
    Run.stage r (loop_spec r hp hpre (length_hMsgBytes r) h₄) fun m₅ h₅ ↦
    index_spec r hp hc hpre h₅

end

end NativeRustcX64.SphincsVerifyProof
