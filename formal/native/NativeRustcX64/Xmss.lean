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
public import NativeRustc.ReadRegions

/-!
# The rustc-compiled leanXMSS verifier on x86-64 is correct

`NativeRustcX64.Xmss.code` (`xmss_verify` with `memcpy`, `memset`, `keccak_f`, `Hasher::update`,
`Hasher::finalize`, `LayerSignature::read` and `wots_leaf`) as the host's program: from
`xmss_verify`'s entry on any 309 input words from byte 1024, with its ABI stack, round constants
and loader-provided GOT slots in place, the machine returns `LeanXmss.verifyWithKeccak` of the
decoded input in RAX, RSP 8 above, preserving its callee-saved registers and every byte outside
its stack. `verify_decode` connects the byte model to that Statement specification for every input.
`verify_confined` removes every data-memory byte outside the stated regions.

The proof: each function's contract for this program (`memcpy_spec`, `memset_spec`,
`keccakF_spec`, `update_spec`, `finalize_spec`, `layerRead_spec`, `wotsLeaf_spec`,
`xmssVerify_spec`) and the byte model's equality with the statement (`NativeRustc.Xmss.verify_decode`).
-/

namespace NativeRustcX64

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

end NativeRustcX64

namespace NativeRustcX64.XmssVerifier

open NativeRustc NativeRustcX64.Xmss.Placement

public section

variable [Host] (hP : Host.prog = Xmss.code)
include hP

/-- **The rustc-compiled leanXMSS verifier is correct on x86-64.**
`hgot` supplies the actual eight-byte `memcpy` and `memset` pointers in data memory, with
nonwrapping, mutually disjoint slots apart from the stack including its return address and the
input words. -/
theorem verify_correct (w : Nat → UInt64)
    (m : MachineData) (hstack : StackOk m xmssVerifyStack) (hrc : RcAt m xmssVerifyStack)
    (hin : BytesAt m.dmem (reg m .rdi + BitVec.ofNat 64 1024)
      (Native.Keccak.wordsBytes ((List.range 309).map w)))
    (hinw : NoWrap (reg m .rdi + BitVec.ofNat 64 1024) (8 * 309))
    (hina : Apart (reg m .rdi + BitVec.ofNat 64 1024) (8 * 309)
      (stackBelow m xmssVerifyStack) (xmssVerifyStack + 8))
    (hgot : GotAt m xmssVerifyStack
      [(reg m .rdi + BitVec.ofNat 64 1024, 8 * 309)] ["memcpy", "memset"]) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧
      reg st.data .rax = (if LeanXmss.verifyWithKeccak (Native.XmssVerifier.decode w).1
        (Native.XmssVerifier.decode w).2.1 (Native.XmssVerifier.decode w).2.2 then 1 else 0) ∧
      SameOutside m.dmem st.data.dmem (InRange (stackBelow m xmssVerifyStack) xmssVerifyStack) ∧
      Saved m st.data) ⟨m, label NativeRustcX64.Xmss.XmssVerify.entryLabel⟩ := by
  rw [← NativeRustc.Xmss.verify_decode w]
  have hmemcpy := Mem.Memcpy.memcpy_spec (placed_memcpy hP)
  have hmemset := Mem.Memset.memset_spec (placed_memset hP)
  have hkf := keccakF_spec (placed_keccakF hP)
  have hupdate := Hasher.Update.update_spec (placed_update hP) hmemcpy hkf
  have hfinalize := Hasher.Finalize.finalize_spec (placed_finalize hP) hmemcpy hmemset hkf
  have hspec := Xmss.XmssVerify.xmssVerify_spec (placed hP)
    (w := w) hmemset hmemcpy hupdate hfinalize
    (wotsLeaf_spec (placed_wotsLeaf hP) ⟨hmemcpy, hmemset, hupdate, hfinalize, hkf⟩)
    (Xmss.LayerRead.layerRead_spec (placed_layerRead hP) hmemcpy)
  exact hspec m ⟨hstack, hrc, Xmss.XmssVerify.words_at _ 309 hin, hinw, hina, hgot⟩


/-- Correctness with every byte outside the contract, ABI and loader regions unmapped.
Kraken gives `nonmem_load` the proposition `False`. -/
theorem verify_confined (w : Nat → UInt64)
    (m : MachineData) (hstack : StackOk m xmssVerifyStack) (hrc : RcAt m xmssVerifyStack)
    (hin : BytesAt m.dmem (reg m .rdi + BitVec.ofNat 64 1024)
      (Native.Keccak.wordsBytes ((List.range 309).map w)))
    (hinw : NoWrap (reg m .rdi + BitVec.ofNat 64 1024) (8 * 309))
    (hina : Apart (reg m .rdi + BitVec.ofNat 64 1024) (8 * 309)
      (stackBelow m xmssVerifyStack) (xmssVerifyStack + 8))
    (hgot : GotAt m xmssVerifyStack
      [(reg m .rdi + BitVec.ofNat 64 1024, 8 * 309)] ["memcpy", "memset"]) :
    let areas := [(stackBelow m xmssVerifyStack, xmssVerifyStack + 8),
      ((reg m .rdi + BitVec.ofNat 64 1024), (Native.Keccak.wordsBytes ((List.range 309).map w)).length), (rcAddr, rcBytes.length), (gotAddr "memcpy", 8), (gotAddr "memset", 8)]
    let m' := { m with dmem := restrictMemory m.dmem areas }
    (∀ p, ¬ ReadRegions areas p → m'.dmem.get? p = none) ∧
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m' ∧
      rspOf st.data = rspOf m' + 8#64 ∧
      reg st.data .rax = (if LeanXmss.verifyWithKeccak (Native.XmssVerifier.decode w).1
        (Native.XmssVerifier.decode w).2.1 (Native.XmssVerifier.decode w).2.2 then 1 else 0) ∧
      SameOutside m'.dmem st.data.dmem (InRange (stackBelow m' xmssVerifyStack) xmssVerifyStack) ∧
      Saved m' st.data) ⟨m', label NativeRustcX64.Xmss.XmssVerify.entryLabel⟩ := by
  dsimp only
  let areas := [(stackBelow m xmssVerifyStack, xmssVerifyStack + 8),
      ((reg m .rdi + BitVec.ofNat 64 1024), (Native.Keccak.wordsBytes ((List.range 309).map w)).length), (rcAddr, rcBytes.length), (gotAddr "memcpy", 8), (gotAddr "memset", 8)]
  let m' : MachineData := { m with dmem := restrictMemory m.dmem areas }
  have hs : StackOk m' xmssVerifyStack :=
    ⟨hstack.1, hstack.2.1, hstack.2.2.restrict (by simp [areas, stackBelow, rspOf])⟩
  have hr : RcAt m' xmssVerifyStack :=
    ⟨hrc.1.restrict (by simp [areas]), hrc.2⟩
  refine ⟨fun p hp => restrictMemory_outside m.dmem hp, ?_⟩
  exact verify_correct hP w m' hs hr
    (hin.restrict (by simp [areas])) hinw hina (by
      refine ⟨?_, hgot.2⟩
      intro l hl
      obtain ⟨hb, hn, hs, ha⟩ := hgot.1 l hl
      refine ⟨hb.restrict ?_, hn, hs, ha⟩
      simp only [Int.toBytes_length]
      simp at hl
      rcases hl with rfl | rfl <;> simp [areas])

end

end NativeRustcX64.XmssVerifier
