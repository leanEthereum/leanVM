module

public import NativeRustcArm.Code.Xmss.XmssVerify.Names

public import NativeRustcArm.XmssVerify
public import NativeRustcArm.XmssVerify.Placed
public import NativeRustcArm.LayerRead
public import NativeRustcArm.WotsLeaf
public import NativeRustcArm.Mem.Memcpy
public import NativeRustcArm.Mem.Memset
public import NativeRustcArm.KeccakF.Spec
public import NativeRustcArm.Hasher.Update
public import NativeRustcArm.Hasher.Finalize
public import NativeRustc.Xmss.Verify

/-!
# The rustc-compiled leanXMSS verifier on AArch64 is correct

`NativeRustcArm.Xmss.code` (`xmss_verify` with `memcpy`, `memset`, `keccak_f`, `Hasher::update`,
`Hasher::finalize`, `from_bytes`'s closure and `wots_leaf`) as the host's program: from
`xmss_verify`'s entry on a context whose 309 input words from byte 1024 are `encode pk msg sig`,
with its stack and the round constants in place, the machine inevitably returns to its caller
with `LeanXmss.verifyWithKeccak pk msg sig` in X0, its callee-saved registers, SP and every byte
outside its stack kept.

The proof: each function's contract for this program (`memcpy_spec`, `memset_spec`,
`keccakF_spec`, `update_spec`, `finalize_spec`, `layerRead_spec`, `wotsLeaf_spec`,
`xmssVerify_spec`) and the byte model's equality with the statement (`NativeRustc.Xmss.verify_eq`).
-/

namespace NativeRustcArm.XmssVerifier

open NativeRustc NativeRustcArm.Xmss.Placement LeanVM.Protocol.KeccakHash

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Xmss.code)
include hP

/-- **The rustc-compiled leanXMSS verifier is correct on AArch64.** -/
theorem verify_correct (pk : HashSig.PublicKey) (msg : HashSig.Message) (sig : LeanXmss.Signature)
    (m : MachineData) (hstack : StackOk m xmssVerifyStack) (hrc : RcAt m xmssVerifyStack)
    (hin : BytesAt m.dmem (m.regs.X0.toBitVec + BitVec.ofNat 64 1024)
      (Native.Keccak.wordsBytes ((List.range 309).map (Native.XmssVerifier.encode pk msg sig))))
    (hinw : NoWrap (m.regs.X0.toBitVec + BitVec.ofNat 64 1024) (8 * 309))
    (hina : Apart (m.regs.X0.toBitVec + BitVec.ofNat 64 1024) (8 * 309)
      (stackBelow m xmssVerifyStack) xmssVerifyStack) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m ∧
      st.data.regs.X0 = (if LeanXmss.verifyWithKeccak pk msg sig then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m xmssVerifyStack) xmssVerifyStack) ∧
      Saved m st.data) ⟨m, label NativeRustcArm.Xmss.XmssVerify.entryLabel⟩ := by
  have hmemcpy := Mem.Memcpy.memcpy_spec (placed_memcpy hP)
  have hmemset := Mem.Memset.memset_spec (placed_memset hP)
  have hkf := keccakF_spec (placed_keccakF hP)
  have hupdate := Hasher.Update.update_spec (placed_update hP) hmemcpy hkf
  have hfinalize := Hasher.Finalize.finalize_spec (placed_finalize hP) hmemcpy hkf
  have hspec := Xmss.XmssVerify.xmssVerify_spec (placed hP)
    (w := Native.XmssVerifier.encode pk msg sig) hmemset hmemcpy hupdate hfinalize
    (WotsLeaf.wotsLeaf_spec (placed_wotsLeaf hP) hmemcpy hmemset hupdate hfinalize hkf)
    (Xmss.LayerRead.layerRead_spec (placed_layerRead hP) hmemcpy)
  have hwords : ∀ i < xmssInputWords, BytesAt m.dmem (xmssInput m + BitVec.ofNat 64 (8 * i))
      (wordBytes (Native.XmssVerifier.encode pk msg sig i)) := by
    intro i hi
    rw [Xmss.XmssVerify.wordsBytes_map] at hin
    exact bytesAt_flatten_piece 309 (fun _ _ => length_wordBytes _) hin i hi
  refine NativeRustcArm.Eventually.mono (hspec m ⟨hstack, hrc, hwords, hinw, hina⟩)
    fun st ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_, h3, h4⟩
  rw [h2, NativeRustc.Xmss.verify_eq]

end

end NativeRustcArm.XmssVerifier
