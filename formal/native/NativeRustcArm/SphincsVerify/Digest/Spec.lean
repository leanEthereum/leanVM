module

public import NativeRustcArm.SphincsVerify.Digest.Index

/-!
# Region 2, the digest: `DigestSpec`

From `AtHMsg` at `b45` to `AtFors` at `b59`: `h_msg`'s hasher (`absorb_spec`), its two calls
(`hash0_spec`, `hash1_spec`, `hMsg_spec`), `digest_fields`' leaves (`loop_spec`) and index
(`index_spec`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open Digest

public section

/-- **Region 2, the digest.** -/
theorem digest_spec [NativeRustcArm.Host] : DigestSpec := by
  intro r hp hc hpre m hA
  exact Run.stage r (absorb_spec r hp hc hpre hA) fun m₁ h₁ ↦
    Run.stage r (hash0_spec r hp hc hpre h₁) fun m₂ h₂ ↦
    Run.stage r (hash1_spec r hp hc hpre h₂) fun m₃ h₃ ↦
    Run.stage r (hMsg_spec r hp hpre h₃) fun m₄ h₄ ↦
    Run.stage r (loop_spec r hp hpre (length_hMsgBytes r) h₄) fun m₅ h₅ ↦
    index_spec r hp hc hpre h₅

end

end NativeRustcArm.SphincsVerifyProof
