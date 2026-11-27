module

public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.Compose
public import NativeRustc.Sphincs.Verify

/-!
# `sphincs_verify` is leanSPHINCS verification, from its regions

`verify_correct_of`: placed in a program, given its callees' contracts and its regions'
statements, `sphincs_verify` on raw `(pk, msg, sig)` byte buffers returns to its caller
`Sphincs.verifyWithKeccak (decodePk pk) (decodeMsg msg) (decodeSig sig)` in X0, its registers and
memory kept.
-/

namespace NativeRustcArm.SphincsVerifyProof

public section

variable [ElfHost]

/-- **`sphincs_verify` from its regions is leanSPHINCS verification.** -/
theorem verify_correct_of {sec k : Nat} (hp : PlacedIn Sphincs.SphincsVerify.code sec k) (hc : Callees)
    (h1 : ParseSpec) (h2 : DigestSpec) (h3 : ForsSpec) (h4 : ForsKeySpec) (he : EncodeSpec)
    (hch : ChainsSpec) (ht : TreeSpec)
    {pk msg sig : List UInt8} (hpk : pk.length = 32) (hmsg : msg.length = 32)
    (hsig : sig.length = 7740)
    {m : MachineData} (hpre : (Run.mk m pk msg sig hpk hmsg hsig sec k).Pre) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = retOf m ∧
      st.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak (Native.SphincsVerifier.decodePk pk)
        (Native.SphincsVerifier.decodeMsg msg) (Native.SphincsVerifier.decodeSig sig) then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m sphincsStack) sphincsStack) ∧
      Saved m st.data) ⟨m, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ := by
  have h0 := NativeRustcArm.Sphincs.SphincsVerify.entry_at
  have hl : label NativeRustcArm.Sphincs.SphincsVerify.entryLabel =
      ElfHost.addrOf sec (k + NativeRustcArm.Sphincs.SphincsVerify.b0Offset) := hp.label h0
  rw [hl, NativeRustcArm.Sphincs.SphincsVerify.b0Offset, Nat.add_zero]
  have := run_correct ⟨m, pk, msg, sig, hpk, hmsg, hsig, sec, k⟩ hp hc hpre h1 h2 h3 h4 he hch ht
  rw [NativeRustc.Sphincs.verify_decode_bytes pk msg sig hpk hmsg hsig] at this
  exact this

end

end NativeRustcArm.SphincsVerifyProof
