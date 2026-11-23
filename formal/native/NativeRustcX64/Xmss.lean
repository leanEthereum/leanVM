module

public import NativeRustcX64.Code.Xmss.XmssVerify.Names

public import NativeRustcX64.XmssVerify
public import NativeRustcX64.XmssVerify.Placed
public import NativeRustcX64.LayerRead
public import NativeRustcX64.WotsLeaf
public import NativeRustcX64.Mem.Memcpy
public import NativeRustcX64.Mem.Memset
public import NativeRustcX64.KeccakF.Spec
public import NativeRustcX64.Hasher.Update
public import NativeRustcX64.Hasher.Finalize
public import NativeRustc.Xmss.Verify

/-!
# The rustc-compiled leanXMSS verifier on x86-64 is correct

`NativeRustcX64.Xmss.code` (`xmss_verify` with `memcpy`, `memset`, `keccak_f`, `Hasher::update`,
`Hasher::finalize`, `LayerSignature::read` and `wots_leaf`) as the host's program: from
`xmss_verify`'s entry on a context whose 309 input words from byte 1024 are `encode pk msg sig`,
with its stack, round constants and read-only `memcpy` and `memset` GOT slots in place, the
slots disjoint from the stack including the return address and the 2472 input bytes, the machine
inevitably returns to its caller, RSP 8 above, with `LeanXmss.verifyWithKeccak pk msg sig` in RAX,
its callee-saved registers and every byte outside its stack kept.

The proof: each function's contract for this program (`memcpy_spec`, `memset_spec`,
`keccakF_spec`, `update_spec`, `finalize_spec`, `layerRead_spec`, `wotsLeaf_spec`,
`xmssVerify_spec`) and the byte model's equality with the statement (`NativeRustc.Xmss.verify_eq`).
-/

namespace NativeRustcX64.XmssVerifier

open NativeRustc NativeRustcX64.Xmss.Placement

public section

variable [Host] (hP : Host.prog = Xmss.code)
include hP

/-- **The rustc-compiled leanXMSS verifier is correct on x86-64.**
`hgot` supplies the actual eight-byte `memcpy` and `memset` pointers in data memory, with
nonwrapping, mutually disjoint slots apart from the stack including its return address and the
input words. -/
theorem verify_correct (pk : HashSig.PublicKey) (msg : HashSig.Message) (sig : LeanXmss.Signature)
    (m : MachineData) (hstack : StackOk m xmssVerifyStack) (hrc : RcAt m xmssVerifyStack)
    (hin : BytesAt m.dmem (reg m .rdi + BitVec.ofNat 64 1024)
      (Native.Keccak.wordsBytes ((List.range 309).map (Native.XmssVerifier.encode pk msg sig))))
    (hinw : NoWrap (reg m .rdi + BitVec.ofNat 64 1024) (8 * 309))
    (hina : Apart (reg m .rdi + BitVec.ofNat 64 1024) (8 * 309)
      (stackBelow m xmssVerifyStack) (xmssVerifyStack + 8))
    (hgot : GotAt m xmssVerifyStack
      [(reg m .rdi + BitVec.ofNat 64 1024, 8 * 309)] ["memcpy", "memset"]) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧
      reg st.data .rax = (if LeanXmss.verifyWithKeccak pk msg sig then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m xmssVerifyStack) xmssVerifyStack) ∧
      Saved m st.data) ⟨m, label NativeRustcX64.Xmss.XmssVerify.entryLabel⟩ := by
  have hmemcpy := Mem.Memcpy.memcpy_spec (placed_memcpy hP)
  have hmemset := Mem.Memset.memset_spec (placed_memset hP)
  have hkf := keccakF_spec (placed_keccakF hP)
  have hupdate := Hasher.Update.update_spec (placed_update hP) hmemcpy hkf
  have hfinalize := Hasher.Finalize.finalize_spec (placed_finalize hP) hmemcpy hmemset hkf
  have hspec := Xmss.XmssVerify.xmssVerify_spec (placed hP)
    (w := Native.XmssVerifier.encode pk msg sig) hmemset hmemcpy hupdate hfinalize
    (wotsLeaf_spec (placed_wotsLeaf hP) ⟨hmemcpy, hmemset, hupdate, hfinalize, hkf⟩)
    (Xmss.LayerRead.layerRead_spec (placed_layerRead hP) hmemcpy)
  refine Eventually.mono (hspec m ⟨hstack, hrc, Xmss.XmssVerify.words_at _ 309 hin, hinw, hina, hgot⟩)
    fun st ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, ?_, h4, h5⟩
  rw [h3, Xmss.verify_eq]

end

end NativeRustcX64.XmssVerifier
