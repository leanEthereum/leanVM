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
public import NativeRustcX64.Restrict

/-!
# The rustc-compiled leanSPHINCS verifier on x86-64 is correct

`NativeRustcX64.Sphincs.code` (`sphincs_verify` with `memcpy`, `memset`, `keccak_f`,
`Hasher::update`, `Hasher::finalize`) as the host's program: from `sphincs_verify`'s entry with
the raw public key (`rdi`, 32 bytes), message (`rsi`, 32 bytes), and signature (`rdx`, 7740 bytes),
with its ABI stack, round constants, `LAYER_HEIGHTS` and loader-provided GOT slots in place, the
machine returns `Sphincs.verifyWithKeccak` of the decoded inputs in RAX, RSP 8 above, preserving
its callee-saved registers and every byte outside its stack. `verify_decode_bytes` connects the
byte model to that Statement specification for every input. `verify_confined` removes every
data-memory byte outside the stated regions.

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
theorem verify_correct (pk msg sig : List UInt8)
    (hpk : pk.length = 32) (hmsg : msg.length = 32) (hsig : sig.length = 7740)
    (m : MachineData) (hstack : StackOk m sphincsStack) (hrc : RcAt m sphincsStack)
    (hlh : BytesAt m.dmem (label NativeRustcX64.layerHeightsLabel).toBitVec lhBytes)
    (hlhw : NoWrap (label NativeRustcX64.layerHeightsLabel).toBitVec 24)
    (hlha : Apart (label NativeRustcX64.layerHeightsLabel).toBitVec 24 (stackBelow m sphincsStack) (sphincsStack + 8))
    (hpkb : BytesAt m.dmem (reg m .rdi) pk)
    (hpkw : NoWrap (reg m .rdi) 32)
    (hpka : Apart (reg m .rdi) 32 (stackBelow m sphincsStack) (sphincsStack + 8))
    (hmsgb : BytesAt m.dmem (reg m .rsi) msg)
    (hmsgw : NoWrap (reg m .rsi) 32)
    (hmsga : Apart (reg m .rsi) 32 (stackBelow m sphincsStack) (sphincsStack + 8))
    (hsigb : BytesAt m.dmem (reg m .rdx) sig)
    (hsigw : NoWrap (reg m .rdx) 7740)
    (hsiga : Apart (reg m .rdx) 7740 (stackBelow m sphincsStack) (sphincsStack + 8))
    (hgot : GotAt m sphincsStack
      [(reg m .rdi, 32), (reg m .rsi, 32), (reg m .rdx, 7740),
        ((label NativeRustcX64.layerHeightsLabel).toBitVec, 24)] ["memcpy", "memset"]) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧
      reg st.data .rax = (if _root_.Sphincs.verifyWithKeccak (Native.SphincsVerifier.decodePk pk)
        (Native.SphincsVerifier.decodeMsg msg) (Native.SphincsVerifier.decodeSig sig) then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m sphincsStack) sphincsStack) ∧
      Saved m st.data) ⟨m, label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ := by
  rw [← NativeRustc.Sphincs.verify_decode_bytes pk msg sig hpk hmsg hsig]
  have hp := placed hP
  have hl := hp.label NativeRustcX64.Sphincs.SphincsVerify.entry_at
  rw [hl, NativeRustcX64.Sphincs.SphincsVerify.entryOffset, Nat.add_zero]
  exact run_correct ⟨m, pk, msg, sig, hpk, hmsg, hsig, NativeRustcX64.Sphincs.SphincsVerify.programOffset⟩
    hp (callees hP)
    ⟨hstack, hrc, hlh, hlhw, hlha, hpkb, hpkw, hpka, hmsgb, hmsgw, hmsga, hsigb, hsigw, hsiga, hgot⟩
    Parse.parse_spec digest_spec fors_spec forsKey_spec encode_spec Chains.chainsSpec Tree.tree_spec


/-- Correctness with every byte outside the contract, ABI and loader regions unmapped.
Kraken gives `nonmem_load` the proposition `False`. -/
theorem verify_confined (pk msg sig : List UInt8)
    (hpk : pk.length = 32) (hmsg : msg.length = 32) (hsig : sig.length = 7740)
    (m : MachineData) (hstack : StackOk m sphincsStack) (hrc : RcAt m sphincsStack)
    (hlh : BytesAt m.dmem (label NativeRustcX64.layerHeightsLabel).toBitVec lhBytes)
    (hlhw : NoWrap (label NativeRustcX64.layerHeightsLabel).toBitVec 24)
    (hlha : Apart (label NativeRustcX64.layerHeightsLabel).toBitVec 24 (stackBelow m sphincsStack) (sphincsStack + 8))
    (hpkb : BytesAt m.dmem (reg m .rdi) pk)
    (hpkw : NoWrap (reg m .rdi) 32)
    (hpka : Apart (reg m .rdi) 32 (stackBelow m sphincsStack) (sphincsStack + 8))
    (hmsgb : BytesAt m.dmem (reg m .rsi) msg)
    (hmsgw : NoWrap (reg m .rsi) 32)
    (hmsga : Apart (reg m .rsi) 32 (stackBelow m sphincsStack) (sphincsStack + 8))
    (hsigb : BytesAt m.dmem (reg m .rdx) sig)
    (hsigw : NoWrap (reg m .rdx) 7740)
    (hsiga : Apart (reg m .rdx) 7740 (stackBelow m sphincsStack) (sphincsStack + 8))
    (hgot : GotAt m sphincsStack
      [(reg m .rdi, 32), (reg m .rsi, 32), (reg m .rdx, 7740),
        ((label NativeRustcX64.layerHeightsLabel).toBitVec, 24)] ["memcpy", "memset"]) :
    let areas := [(stackBelow m sphincsStack, sphincsStack + 8),
      (reg m .rdi, 32), (reg m .rsi, 32), (reg m .rdx, 7740), (rcAddr, rcBytes.length),
      ((label NativeRustcX64.layerHeightsLabel).toBitVec, lhBytes.length), (gotAddr "memcpy", 8), (gotAddr "memset", 8)]
    let m' := { m with dmem := restrictMemory m.dmem areas }
    (∀ p, ¬ ReadRegions areas p → m'.dmem.get? p = none) ∧
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m' ∧
      rspOf st.data = rspOf m' + 8#64 ∧
      reg st.data .rax = (if _root_.Sphincs.verifyWithKeccak (Native.SphincsVerifier.decodePk pk)
        (Native.SphincsVerifier.decodeMsg msg) (Native.SphincsVerifier.decodeSig sig) then 1 else 0) ∧
      SameOutside m'.dmem st.data.dmem (InRange (stackBelow m' sphincsStack) sphincsStack) ∧
      Saved m' st.data) ⟨m', label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ := by
  dsimp only
  let areas := [(stackBelow m sphincsStack, sphincsStack + 8),
      (reg m .rdi, 32), (reg m .rsi, 32), (reg m .rdx, 7740), (rcAddr, rcBytes.length),
      ((label NativeRustcX64.layerHeightsLabel).toBitVec, lhBytes.length), (gotAddr "memcpy", 8), (gotAddr "memset", 8)]
  let m' : MachineData := { m with dmem := restrictMemory m.dmem areas }
  have hs : StackOk m' sphincsStack :=
    ⟨hstack.1, hstack.2.1, hstack.2.2.restrict (by simp [areas, stackBelow, rspOf])⟩
  have hr : RcAt m' sphincsStack :=
    ⟨hrc.1.restrict (by simp [areas]), hrc.2⟩
  refine ⟨fun p hp => restrictMemory_outside m.dmem hp, ?_⟩
  exact verify_correct hP pk msg sig hpk hmsg hsig m' hs hr (hlh.restrict (by simp [areas])) hlhw hlha
    (hpkb.restrict (by simp [areas, hpk])) hpkw hpka
    (hmsgb.restrict (by simp [areas, hmsg])) hmsgw hmsga
    (hsigb.restrict (by simp [areas, hsig])) hsigw hsiga (by
      refine ⟨?_, hgot.2⟩
      intro l hl
      obtain ⟨hb, hn, hs, ha⟩ := hgot.1 l hl
      refine ⟨hb.restrict ?_, hn, hs, ha⟩
      simp only [Int.toBytes_length]
      simp at hl
      rcases hl with rfl | rfl <;> simp [areas])

end

end NativeRustcX64.SphincsVerifier
