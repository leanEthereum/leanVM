module

public import NativeRustcX64.Rodata.Names
public import NativeRustcX64.Code.Sphincs.SphincsVerify.Names

public import NativeRustcX64.SphincsVerify.End
public import NativeRustcX64.SphincsVerify.Placed
public import NativeRustcX64.SphincsVerify.Parse.Spec
public import NativeRustcX64.SphincsVerify.Digest.Spec
public import NativeRustcX64.SphincsVerify.Fors.Spec
public import NativeRustcX64.SphincsVerify.Encode.Spec
public import NativeRustcX64.SphincsVerify.Chains.Spec
public import NativeRustcX64.SphincsVerify.Tree.Spec
public import NativeRustcX64.Mem.Memcpy
public import NativeRustcX64.Mem.Memset
public import NativeRustcX64.KeccakF.Spec
public import NativeRustcX64.Hasher.Update
public import NativeRustcX64.Hasher.Finalize

/-!
# The rustc-compiled leanSPHINCS verifier on x86-64 is correct

`NativeRustcX64.Sphincs.code` (`sphincs_verify` with `memcpy`, `memset`, `keccak_f`,
`Hasher::update`, `Hasher::finalize`) as the host's program: from `sphincs_verify`'s entry on a
context whose 977 input words are `encode pk msg sig`, with its stack, the round constants and
`LAYER_HEIGHTS` and the loader-provided GOT slots in place, the machine inevitably returns to its caller, RSP 8 above, with
`Sphincs.verifyWithKeccak pk msg sig` in RAX, its callee-saved registers and every byte outside
its stack kept.

`callees`: the callees' contracts for this program; `verify_correct` composes them with the
regions' statements (`NativeRustcX64.SphincsVerify.End`).
-/

namespace NativeRustcX64.SphincsVerifier

open NativeRustc NativeRustc.Keccak NativeRustcX64.SphincsVerifyProof Native.Keccak

public section

variable [Host] (hP : Host.prog = Sphincs.code)
include hP

/-- **The callees' contracts** in `sphincs_verify`'s program. -/
theorem callees : Callees :=
  have hmemcpy := Mem.Memcpy.memcpy_spec (placed_memcpy hP)
  have hmemset := Mem.Memset.memset_spec (placed_memset hP)
  have hkf := keccakF_spec (placed_keccakF hP)
  ⟨hmemcpy, hmemset, Hasher.Update.update_spec (placed_update hP) hmemcpy hkf,
    Hasher.Finalize.finalize_spec (placed_finalize hP) hmemcpy hmemset hkf, hkf⟩

/-- **The rustc-compiled leanSPHINCS verifier is correct** (x86-64). -/
theorem verify_correct
    (pk : _root_.Sphincs.PublicKey) (msg : HashSig.Message) (sig : _root_.Sphincs.Signature)
    (m : MachineData) (hstack : StackOk m sphincsStack) (hrc : RcAt m sphincsStack)
    (hlh : BytesAt m.dmem (label NativeRustcX64.layerHeightsLabel).toBitVec lhBytes)
    (hlhw : NoWrap (label NativeRustcX64.layerHeightsLabel).toBitVec 24)
    (hlha : Apart (label NativeRustcX64.layerHeightsLabel).toBitVec 24 (stackBelow m sphincsStack) (sphincsStack + 8))
    (hin : BytesAt m.dmem (reg m .rdi + BitVec.ofNat 64 1024)
      (wordsBytes ((List.range 977).map (Native.SphincsVerifier.encode pk msg sig))))
    (hinw : NoWrap (reg m .rdi + BitVec.ofNat 64 1024) (8 * 977))
    (hina : Apart (reg m .rdi + BitVec.ofNat 64 1024) (8 * 977)
      (stackBelow m sphincsStack) (sphincsStack + 8))
    (hgot : GotAt m sphincsStack
      [(reg m .rdi + BitVec.ofNat 64 1024, 8 * 977),
        ((label NativeRustcX64.layerHeightsLabel).toBitVec, 24)] ["memcpy", "memset"]) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧
      reg st.data .rax = (if _root_.Sphincs.verifyWithKeccak pk msg sig then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m sphincsStack) sphincsStack) ∧
      Saved m st.data) ⟨m, label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ :=
  verify_correct_of (placed hP) (callees hP) Parse.parse_spec digest_spec fors_spec forsKey_spec
    encode_spec Chains.chainsSpec Tree.tree_spec (k := NativeRustcX64.Sphincs.SphincsVerify.programOffset)
    ⟨hstack, hrc, hlh, hlhw, hlha, hin, hinw, hina, hgot⟩

end

end NativeRustcX64.SphincsVerifier
