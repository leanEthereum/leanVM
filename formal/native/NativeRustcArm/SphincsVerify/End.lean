module

public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.Compose
public import NativeRustc.Sphincs.Verify

/-!
# `sphincs_verify` is leanSPHINCS verification, from its regions

`verify_correct_of`: placed in a program, given its callees' contracts and its regions'
statements, `sphincs_verify` on a context whose input words are `encode pk msg sig` returns to its
caller `Sphincs.verifyWithKeccak pk msg sig` in X0, its registers and memory kept.
-/

namespace NativeRustcArm.SphincsVerifyProof

public section

variable [NativeRustcArm.Host]

/-- **`sphincs_verify` from its regions is leanSPHINCS verification.** -/
theorem verify_correct_of {k : Nat} (hp : Placed Sphincs.SphincsVerify.code k) (hc : Callees)
    (h1 : ParseSpec) (h2 : DigestSpec) (h3 : ForsSpec) (h4 : ForsKeySpec) (he : EncodeSpec)
    (hch : ChainsSpec) (ht : TreeSpec)
    {pk : _root_.Sphincs.PublicKey} {msg : HashSig.Message} {sig : _root_.Sphincs.Signature}
    {m : MachineData} (hpre : (Run.mk m (Native.SphincsVerifier.encode pk msg sig) k).Pre) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m ∧
      st.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak pk msg sig then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m sphincsStack) sphincsStack) ∧
      Saved m st.data) ⟨m, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ := by
  have h0 := NativeRustcArm.Sphincs.SphincsVerify.entry_at
  have hl : label NativeRustcArm.Sphincs.SphincsVerify.entryLabel = NativeRustcArm.Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b0Offset) := hp.label h0
  rw [hl, NativeRustcArm.Sphincs.SphincsVerify.b0Offset, Nat.add_zero]
  have := run_correct ⟨m, Native.SphincsVerifier.encode pk msg sig, k⟩ hp hc hpre h1 h2 h3 h4 he hch
    ht
  rw [NativeRustc.Sphincs.verify_eq] at this
  exact this

end

end NativeRustcArm.SphincsVerifyProof
