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
public import NativeRustc.ReadRegions

/-!
# The rustc-compiled leanXMSS verifier on AArch64 is correct

`NativeRustcArm.Xmss.code` (`xmss_verify` with `memcpy`, `memset`, `keccak_f`, `Hasher::update`,
`Hasher::finalize`, `from_bytes`'s closure and `wots_leaf`) as the host's program: from
`xmss_verify`'s entry on any 309 input words from byte 1024, with its ABI stack and loader
round constants in place, the machine returns `LeanXmss.verifyWithKeccak` of the decoded input
in X0 and preserves its callee-saved registers, SP and every byte outside its stack.
`verify_decode` connects the byte model to that Statement specification for every input.
`verify_confined` removes every data-memory byte outside the stated input, stack and loader regions.

The proof: each function's contract for this program (`memcpy_spec`, `memset_spec`,
`keccakF_spec`, `update_spec`, `finalize_spec`, `layerRead_spec`, `wotsLeaf_spec`,
`xmssVerify_spec`) and the byte model's equality with the statement (`NativeRustc.Xmss.verify_decode`).
-/

namespace NativeRustcArm

public section

theorem BytesAt.restrict {d : DataMem} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d a bs) {areas : List (BitVec 64 × Nat)}
    (ha : (a, bs.length) ∈ areas) : BytesAt (NativeRustc.restrictMemory d areas) a bs := by
  intro i hi
  rw [NativeRustc.restrictMemory_inside d ha hi]
  exact h i hi

theorem Mapped.restrict {d : DataMem} {a : BitVec 64} {n : Nat}
    (h : Mapped d a n) {areas : List (BitVec 64 × Nat)}
    (ha : (a, n) ∈ areas) : Mapped (NativeRustc.restrictMemory d areas) a n := by
  intro i hi
  rw [NativeRustc.restrictMemory_inside d ha hi]
  exact h i hi

end

end NativeRustcArm

namespace NativeRustcArm.XmssVerifier

open NativeRustc NativeRustcArm.Xmss.Placement LeanVM.Protocol.KeccakHash

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Xmss.code)
include hP

/-- **The rustc-compiled leanXMSS verifier is correct on AArch64.** -/
theorem verify_correct (w : Nat → UInt64)
    (m : MachineData) (hstack : StackOk m xmssVerifyStack) (hrc : RcAt m xmssVerifyStack)
    (hin : BytesAt m.dmem (m.regs.X0.toBitVec + BitVec.ofNat 64 1024)
      (Native.Keccak.wordsBytes ((List.range 309).map w)))
    (hinw : NoWrap (m.regs.X0.toBitVec + BitVec.ofNat 64 1024) (8 * 309))
    (hina : Apart (m.regs.X0.toBitVec + BitVec.ofNat 64 1024) (8 * 309)
      (stackBelow m xmssVerifyStack) xmssVerifyStack) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m ∧
      st.data.regs.X0 = (if LeanXmss.verifyWithKeccak (Native.XmssVerifier.decode w).1
        (Native.XmssVerifier.decode w).2.1 (Native.XmssVerifier.decode w).2.2 then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m xmssVerifyStack) xmssVerifyStack) ∧
      Saved m st.data) ⟨m, label NativeRustcArm.Xmss.XmssVerify.entryLabel⟩ := by
  rw [← NativeRustc.Xmss.verify_decode w]
  have hmemcpy := Mem.Memcpy.memcpy_spec (placed_memcpy hP)
  have hmemset := Mem.Memset.memset_spec (placed_memset hP)
  have hkf := keccakF_spec (placed_keccakF hP)
  have hupdate := Hasher.Update.update_spec (placed_update hP) hmemcpy hkf
  have hfinalize := Hasher.Finalize.finalize_spec (placed_finalize hP) hmemcpy hkf
  have hspec := Xmss.XmssVerify.xmssVerify_spec (placed hP)
    (w := w) hmemset hmemcpy hupdate hfinalize
    (WotsLeaf.wotsLeaf_spec (placed_wotsLeaf hP) hmemcpy hmemset hupdate hfinalize hkf)
    (Xmss.LayerRead.layerRead_spec (placed_layerRead hP) hmemcpy)
  have hwords : ∀ i < xmssInputWords, BytesAt m.dmem (xmssInput m + BitVec.ofNat 64 (8 * i))
      (wordBytes (w i)) := by
    intro i hi
    rw [Xmss.XmssVerify.wordsBytes_map] at hin
    exact bytesAt_flatten_piece 309 (fun _ _ => length_wordBytes _) hin i hi
  exact hspec m ⟨hstack, hrc, hwords, hinw, hina⟩


/-- Correctness with every byte outside the contract, ABI and loader regions unmapped.
Kraken gives `nonmem_load` the proposition `False`. -/
theorem verify_confined (w : Nat → UInt64)
    (m : MachineData) (hstack : StackOk m xmssVerifyStack) (hrc : RcAt m xmssVerifyStack)
    (hin : BytesAt m.dmem (m.regs.X0.toBitVec + BitVec.ofNat 64 1024)
      (Native.Keccak.wordsBytes ((List.range 309).map w)))
    (hinw : NoWrap (m.regs.X0.toBitVec + BitVec.ofNat 64 1024) (8 * 309))
    (hina : Apart (m.regs.X0.toBitVec + BitVec.ofNat 64 1024) (8 * 309)
      (stackBelow m xmssVerifyStack) xmssVerifyStack) :
    let areas := [(stackBelow m xmssVerifyStack, xmssVerifyStack),
      ((m.regs.X0.toBitVec + BitVec.ofNat 64 1024), (Native.Keccak.wordsBytes ((List.range 309).map w)).length), (rcAddr, rcBytes.length)]
    let m' := { m with dmem := restrictMemory m.dmem areas }
    (∀ p, ¬ ReadRegions areas p → m'.dmem.get? p = none) ∧
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m' ∧
      st.data.regs.X0 = (if LeanXmss.verifyWithKeccak (Native.XmssVerifier.decode w).1
        (Native.XmssVerifier.decode w).2.1 (Native.XmssVerifier.decode w).2.2 then 1 else 0) ∧
      SameOutside m'.dmem st.data.dmem (InRange (stackBelow m' xmssVerifyStack) xmssVerifyStack) ∧
      Saved m' st.data) ⟨m', label NativeRustcArm.Xmss.XmssVerify.entryLabel⟩ := by
  dsimp only
  let areas := [(stackBelow m xmssVerifyStack, xmssVerifyStack),
      ((m.regs.X0.toBitVec + BitVec.ofNat 64 1024), (Native.Keccak.wordsBytes ((List.range 309).map w)).length), (rcAddr, rcBytes.length)]
  let m' : MachineData := { m with dmem := restrictMemory m.dmem areas }
  have hs : StackOk m' xmssVerifyStack :=
    ⟨hstack.1, hstack.2.1, hstack.2.2.restrict (by simp [areas, stackBelow])⟩
  have hr : RcAt m' xmssVerifyStack :=
    ⟨hrc.1.restrict (by simp [areas]), hrc.2⟩
  refine ⟨fun p hp => restrictMemory_outside m.dmem hp, ?_⟩
  exact verify_correct hP w m' hs hr
    (hin.restrict (by simp [areas])) hinw hina

end

end NativeRustcArm.XmssVerifier
