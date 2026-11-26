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
public import NativeRustcArm.Restrict

/-!
# The rustc-compiled leanSPHINCS verifier on AArch64 is correct

`NativeRustcArm.Sphincs.code` (`sphincs_verify` with `memcpy`, `memset`, `keccak_f`,
`Hasher::update`, `Hasher::finalize`) as the host's program: from `sphincs_verify`'s entry on raw
byte buffers `pk` (32 bytes at X0), `msg` (32 bytes at X1) and `sig` (7740 bytes at X2), with its
ABI stack, round constants and `LAYER_HEIGHTS` in place, the machine returns
`Sphincs.verifyWithKeccak` of the decoded input in X0 and preserves its callee-saved registers, SP
and every byte outside its stack. `verify_decode_bytes` connects the byte model to that Statement
specification for every input. `verify_confined` removes every data-memory byte outside the stated
regions.

`callees`: the callees' contracts for this program; the regions' statements are the regions'
theorems (`NativeRustcArm.SphincsVerify.*`), composed by `run_correct`.
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
theorem verify_correct (pk msg sig : List UInt8)
    (hpk : pk.length = 32) (hmsg : msg.length = 32) (hsig : sig.length = 7740)
    (m : MachineData) (hstack : StackOk m sphincsStack) (hrc : RcAt m sphincsStack)
    (hlh : BytesAt m.dmem (label NativeRustcArm.layerHeightsLabel).toBitVec lhBytes)
    (hlhw : NoWrap (label NativeRustcArm.layerHeightsLabel).toBitVec 24)
    (hlha : Apart (label NativeRustcArm.layerHeightsLabel).toBitVec 24 (stackBelow m sphincsStack) sphincsStack)
    (hpkAt : BytesAt m.dmem m.regs.X0.toBitVec pk)
    (hpkw : NoWrap m.regs.X0.toBitVec 32)
    (hpka : Apart m.regs.X0.toBitVec 32 (stackBelow m sphincsStack) sphincsStack)
    (hmsgAt : BytesAt m.dmem m.regs.X1.toBitVec msg)
    (hmsgw : NoWrap m.regs.X1.toBitVec 32)
    (hmsga : Apart m.regs.X1.toBitVec 32 (stackBelow m sphincsStack) sphincsStack)
    (hsigAt : BytesAt m.dmem m.regs.X2.toBitVec sig)
    (hsigw : NoWrap m.regs.X2.toBitVec 7740)
    (hsiga : Apart m.regs.X2.toBitVec 7740 (stackBelow m sphincsStack) sphincsStack) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m ∧
      st.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
        (Native.SphincsVerifier.decodePk pk)
        (Native.SphincsVerifier.decodeMsg msg)
        (Native.SphincsVerifier.decodeSig sig) then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m sphincsStack) sphincsStack) ∧
      Saved m st.data) ⟨m, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ := by
  rw [← NativeRustc.Sphincs.verify_decode_bytes pk msg sig hpk hmsg hsig]
  have hp := placed hP
  have hl := hp.label NativeRustcArm.Sphincs.SphincsVerify.entry_at
  rw [hl, NativeRustcArm.Sphincs.SphincsVerify.entryOffset, Nat.add_zero]
  exact run_correct ⟨m, pk, msg, sig, hpk, hmsg, hsig, NativeRustcArm.Sphincs.SphincsVerify.programOffset⟩
    hp (callees hP)
    ⟨hstack, hrc, hlh, hlhw, hlha, hpkAt, hpkw, hpka, hmsgAt, hmsgw, hmsga, hsigAt, hsigw, hsiga⟩
    (parseSpec_of Parse.parseHead_spec ParseTail.parseTail_spec) digest_spec fors_spec forsKey_spec
    encode_spec Chains.chainsSpec Tree.tree_spec


/-- Correctness with every byte outside the contract, ABI and loader regions unmapped.
Kraken gives `nonmem_load` the proposition `False`. -/
theorem verify_confined (pk msg sig : List UInt8)
    (hpk : pk.length = 32) (hmsg : msg.length = 32) (hsig : sig.length = 7740)
    (m : MachineData) (hstack : StackOk m sphincsStack) (hrc : RcAt m sphincsStack)
    (hlh : BytesAt m.dmem (label NativeRustcArm.layerHeightsLabel).toBitVec lhBytes)
    (hlhw : NoWrap (label NativeRustcArm.layerHeightsLabel).toBitVec 24)
    (hlha : Apart (label NativeRustcArm.layerHeightsLabel).toBitVec 24 (stackBelow m sphincsStack) sphincsStack)
    (hpkAt : BytesAt m.dmem m.regs.X0.toBitVec pk)
    (hpkw : NoWrap m.regs.X0.toBitVec 32)
    (hpka : Apart m.regs.X0.toBitVec 32 (stackBelow m sphincsStack) sphincsStack)
    (hmsgAt : BytesAt m.dmem m.regs.X1.toBitVec msg)
    (hmsgw : NoWrap m.regs.X1.toBitVec 32)
    (hmsga : Apart m.regs.X1.toBitVec 32 (stackBelow m sphincsStack) sphincsStack)
    (hsigAt : BytesAt m.dmem m.regs.X2.toBitVec sig)
    (hsigw : NoWrap m.regs.X2.toBitVec 7740)
    (hsiga : Apart m.regs.X2.toBitVec 7740 (stackBelow m sphincsStack) sphincsStack) :
    let areas := [(stackBelow m sphincsStack, sphincsStack),
      (m.regs.X0.toBitVec, 32), (m.regs.X1.toBitVec, 32), (m.regs.X2.toBitVec, 7740),
      (rcAddr, rcBytes.length),
      ((label NativeRustcArm.layerHeightsLabel).toBitVec, lhBytes.length)]
    let m' := { m with dmem := restrictMemory m.dmem areas }
    (∀ p, ¬ ReadRegions areas p → m'.dmem.get? p = none) ∧
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m' ∧
      st.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
        (Native.SphincsVerifier.decodePk pk)
        (Native.SphincsVerifier.decodeMsg msg)
        (Native.SphincsVerifier.decodeSig sig) then 1 else 0) ∧
      SameOutside m'.dmem st.data.dmem (InRange (stackBelow m' sphincsStack) sphincsStack) ∧
      Saved m' st.data) ⟨m', label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ := by
  dsimp only
  let areas := [(stackBelow m sphincsStack, sphincsStack),
      (m.regs.X0.toBitVec, 32), (m.regs.X1.toBitVec, 32), (m.regs.X2.toBitVec, 7740),
      (rcAddr, rcBytes.length),
      ((label NativeRustcArm.layerHeightsLabel).toBitVec, lhBytes.length)]
  let m' : MachineData := { m with dmem := restrictMemory m.dmem areas }
  have hs : StackOk m' sphincsStack :=
    ⟨hstack.1, hstack.2.1, hstack.2.2.restrict (by simp [areas, stackBelow])⟩
  have hr : RcAt m' sphincsStack :=
    ⟨hrc.1.restrict (by simp [areas]), hrc.2⟩
  refine ⟨fun p hp => restrictMemory_outside m.dmem hp, ?_⟩
  exact verify_correct hP pk msg sig hpk hmsg hsig m' hs hr (hlh.restrict (by simp [areas])) hlhw hlha
    (hpkAt.restrict (by simp [areas, hpk])) hpkw hpka
    (hmsgAt.restrict (by simp [areas, hmsg])) hmsgw hmsga
    (hsigAt.restrict (by simp [areas, hsig])) hsigw hsiga

end

end NativeRustcArm.SphincsVerifier
