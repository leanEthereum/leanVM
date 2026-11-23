module

public import NativeRustcArm.Rodata.Names
public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.End
public import NativeRustcArm.SphincsVerify.Placed
public import NativeRustcArm.SphincsVerify.Digest.Spec
public import NativeRustcArm.SphincsVerify.Digest.ForsKeySpec
public import NativeRustcArm.SphincsVerify.Encode.Spec
public import NativeRustcArm.SphincsVerify.Chains.Spec
public import NativeRustcArm.SphincsVerify.Tree.Spec
public import NativeRustcArm.SphincsVerify.Parse.Head
public import NativeRustcArm.SphincsVerify.ParseTail.Spec
public import NativeRustcArm.SphincsVerify.Fors.Region
public import NativeRustcArm.Mem.Memcpy
public import NativeRustcArm.Mem.Memset
public import NativeRustcArm.KeccakF.Spec
public import NativeRustcArm.Hasher.Update
public import NativeRustcArm.Hasher.Finalize

/-!
# The rustc-compiled leanSPHINCS verifier on AArch64 is correct

`NativeRustcArm.Sphincs.code` (`sphincs_verify` with `memcpy`, `memset`, `keccak_f`,
`Hasher::update`, `Hasher::finalize`) as the host's program: from `sphincs_verify`'s entry on a
context whose 977 input words are `encode pk msg sig`, with its stack, the round constants and
`LAYER_HEIGHTS` in place, the machine inevitably returns to its caller with
`Sphincs.verifyWithKeccak pk msg sig` in X0, its callee-saved registers, SP and every byte outside
its stack kept.

`callees`: the callees' contracts for this program; the regions' statements are the regions'
theorems (`NativeRustcArm.SphincsVerify.*`), composed by `verify_correct_of`.
-/

namespace NativeRustcArm.SphincsVerifier

open NativeRustc NativeRustc.Keccak NativeRustcArm.SphincsVerifyProof Native.Keccak

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Sphincs.code)
include hP

/-- **The callees' contracts** in `sphincs_verify`'s program. -/
theorem callees : Callees :=
  have hmemcpy := Mem.Memcpy.memcpy_spec (placed_memcpy hP)
  have hkf := keccakF_spec (placed_keccakF hP)
  ⟨hmemcpy, Mem.Memset.memset_spec (placed_memset hP),
    Hasher.Update.update_spec (placed_update hP) hmemcpy hkf,
    Hasher.Finalize.finalize_spec (placed_finalize hP) hmemcpy hkf, hkf⟩

/-- **The rustc-compiled leanSPHINCS verifier is correct.** -/
theorem verify_correct
    (pk : _root_.Sphincs.PublicKey) (msg : HashSig.Message) (sig : _root_.Sphincs.Signature)
    (m : MachineData) (hstack : StackOk m sphincsStack) (hrc : RcAt m sphincsStack)
    (hlh : BytesAt m.dmem (label NativeRustcArm.layerHeightsLabel).toBitVec lhBytes)
    (hlhw : NoWrap (label NativeRustcArm.layerHeightsLabel).toBitVec 24)
    (hlha : Apart (label NativeRustcArm.layerHeightsLabel).toBitVec 24 (stackBelow m sphincsStack) sphincsStack)
    (hin : BytesAt m.dmem (m.regs.X0.toBitVec + BitVec.ofNat 64 1024)
      (wordsBytes ((List.range 977).map (Native.SphincsVerifier.encode pk msg sig))))
    (hinw : NoWrap (m.regs.X0.toBitVec + BitVec.ofNat 64 1024) (8 * 977))
    (hina : Apart (m.regs.X0.toBitVec + BitVec.ofNat 64 1024) (8 * 977)
      (stackBelow m sphincsStack) sphincsStack) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m ∧
      st.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak pk msg sig then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m sphincsStack) sphincsStack) ∧
      Saved m st.data) ⟨m, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ :=
  verify_correct_of (placed hP) (callees hP)
    (parseSpec_of Parse.parseHead_spec ParseTail.parseTail_spec) digest_spec fors_spec forsKey_spec
    encode_spec Chains.chainsSpec Tree.tree_spec (k := NativeRustcArm.Sphincs.SphincsVerify.programOffset)
    ⟨hstack, hrc, hlh, hlhw, hlha, hin, hinw, hina⟩

end

end NativeRustcArm.SphincsVerifier
