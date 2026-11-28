module

public import NativeRustcX64.Code.Sphincs.SphincsVerify.Names

public import NativeRustcX64.SphincsVerify.Compose
public import NativeRustc.Sphincs.Verify

/-!
# `sphincs_verify` is leanSPHINCS verification, from its regions

`verify_correct_of`: placed in a program, given its callees' contracts and its regions'
statements, `sphincs_verify` on a context whose input words are `encode pk msg sig` returns to its
caller `Sphincs.verifyWithKeccak pk msg sig` in RAX, RSP 8 above, its registers and memory kept.
-/

namespace NativeRustcX64.SphincsVerifyProof

public section

variable [Host]

/-- **`sphincs_verify` from its regions is leanSPHINCS verification.** -/
theorem verify_correct_of {k : Nat} (hp : Placed Sphincs.SphincsVerify.code k) (hc : Callees)
    (h1 : ParseSpec) (h2 : DigestSpec) (h3 : ForsSpec) (h4 : ForsKeySpec) (he : EncodeSpec)
    (hch : ChainsSpec) (ht : TreeSpec)
    {pk : _root_.Sphincs.PublicKey} {msg : HashSig.Message} {sig : _root_.Sphincs.Signature}
    {m : MachineData} (hpre : (Run.mk m (Native.SphincsVerifier.encode pk msg sig) k).Pre) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧
      rspOf st.data = rspOf m + 8#64 ∧
      reg st.data .rax = (if _root_.Sphincs.verifyWithKeccak pk msg sig then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m sphincsStack) sphincsStack) ∧
      Saved m st.data) ⟨m, label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ := by
  have h0 := NativeRustcX64.Sphincs.SphincsVerify.entry_at
  have hl : label NativeRustcX64.Sphincs.SphincsVerify.entryLabel = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b0Offset) := hp.label h0
  rw [hl, NativeRustcX64.Sphincs.SphincsVerify.b0Offset, Nat.add_zero]
  have := run_correct ⟨m, Native.SphincsVerifier.encode pk msg sig, k⟩ hp hc hpre h1 h2 h3 h4 he hch
    ht
  rw [NativeRustc.Sphincs.verify_eq] at this
  exact this

end

end NativeRustcX64.SphincsVerifyProof
