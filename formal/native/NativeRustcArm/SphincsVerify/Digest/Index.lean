module

public import NativeRustcArm.SphincsVerify.Digest.Hash
import Mathlib.Tactic.IntervalCases

/-!
# `digest_fields`' index: `b58`

`b58` (directive 692) reads bytes `30 .. 33` of `h_msg` (`24750 .. 24753`): X22 the index (the
tree's 18 bits then the leaf's byte, `idxSym`, `idxSym_eval`), X20 its low byte, stores it at
`25744` and copies the 24 leaves' words from `16400` to `25752` (`memcpy`): `AtFors` at `b59`
(directive 712, `index_spec`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- X22 after `b58`: the index from `h_msg`'s bytes `30 .. 33`. -/
def idxSym : Sym :=
  .bin (.bfm 56 17) .W64 (.bin .and .W64 (.load 0 24753 1) (.lit 255))
    (.bin .orr .W32 (.bin .orr .W32 (.un (.ubfm 24 23) .W32 (.load 0 24751 1))
      (.un (.shift .LSL 16) .W32 (.load 0 24750 1))) (.load 0 24752 1))

end

public section

theorem ofNat_toNat_u8 (a : UInt8) : BitVec.ofNat 64 a.toNat = a.toBitVec.setWidth 64 := by
  rw [← BitVec.ofNat_toNat]
  rfl

/-- **The index's bits.** -/
theorem idxSym_eval [Labels] (env : Env) (a b c d : UInt8)
    (ha : env.load 0 24750 1 = BitVec.ofNat 64 a.toNat)
    (hb : env.load 0 24751 1 = BitVec.ofNat 64 b.toNat)
    (hc : env.load 0 24752 1 = BitVec.ofNat 64 c.toNat)
    (hd : env.load 0 24753 1 = BitVec.ofNat 64 d.toNat) :
    idxSym.eval env = (digestInt [a, b, c] 18 <<< 8 ||| digestInt [d] 8).toBitVec := by
  simp only [idxSym]
  sym_simp
  rw [ha, hb, hc, hd]
  simp only [ofNat_toNat_u8, digestInt, List.foldl_cons, List.foldl_nil, UInt64.toBitVec_or,
    UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64]
  generalize a.toBitVec = va
  generalize b.toBitVec = vb
  generalize c.toBitVec = vc
  generalize d.toBitVec = vd
  simp only [evalBFM, evalUBFM, maskOfLen, BitVec.take, RegWidth.bits]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [MemWidth.bits] at hi
  simp
  interval_cases i <;> simp

/-- **The index's low byte** is its leaf's byte. -/
theorem idx_low (a b c d : UInt8) :
    BitVec.ofNat 64 d.toNat = ((digestInt [a, b, c] 18 <<< 8 ||| digestInt [d] 8) &&& 255).toBitVec := by
  simp only [ofNat_toNat_u8, digestInt, List.foldl_cons, List.foldl_nil, UInt64.toBitVec_or,
    UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64]
  generalize a.toBitVec = va
  generalize b.toBitVec = vb
  generalize c.toBitVec = vc
  generalize d.toBitVec = vd
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp
  interval_cases i <;> simp

/-- Three bytes of a list. -/
theorem slice_three (H : List UInt8) {k : Nat} (hk : k + 3 ≤ H.length) :
    slice H k 3 = [H.getD k 0, H.getD (k + 1) 0, H.getD (k + 2) 0] := by
  apply List.ext_getElem (by simp [slice]; omega)
  intro i h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases i <;> simp [slice, List.getD_eq_getElem?_getD] <;>
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- One byte of a list. -/
theorem slice_one (H : List UInt8) {k : Nat} (hk : k + 1 ≤ H.length) :
    slice H k 1 = [H.getD k 0] := by
  apply List.ext_getElem (by simp [slice]; omega)
  intro i h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases i
  simp [slice, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < H.length)]

/-- **`digest_fields`' index** from bytes `30 .. 33`. -/
theorem digestFields_fst (H : List UInt8) (hH : H.length = 64) :
    (digestFields H).1 = digestInt [H.getD 30 0, H.getD 31 0, H.getD 32 0] 18 <<< 8 |||
      digestInt [H.getD 33 0] 8 := by
  rw [digestFields, slice_three H (by omega), slice_one H (by omega)]

theorem idx_eq (r : Run) : r.idx = (digestFields (hMsgBytes r)).1 := by
  rw [hMsgBytes_eq]
  rfl

theorem leaves_eq (r : Run) : r.leaves = (List.range 24).map (leafOf (hMsgBytes r)) := by
  rw [hMsgBytes_eq]
  rfl

theorem leaves_bytes (r : Run) :
    wordsBytes (r.leaves.map Nat.toUInt64) = leavesBytes (hMsgBytes r) 24 := by
  rw [leaves_eq, List.map_map]
  rfl

/-- A byte of the frame, loaded. -/
theorem frame_load_byte [Labels] {r : Run} {m : MachineData} {o : Nat} {H : List UInt8}
    (h : BytesAt m.dmem (r.off o) H) {k o' : Nat} (hk : k < H.length) (ho : o + k = o') :
    (r.env m).load 0 o' 1 = BitVec.ofNat 64 (H.getD k 0).toNat := by
  subst ho
  rw [Env.load_of_bytesAt (n := 1) (bs := [H.getD k 0]) rfl ?_]
  · simp [Int.ofBytes]
  · intro i hi
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff] at hi
    subst hi
    have := h k hk
    rw [Run.off_add] at this
    simpa [Run.off, List.getD_eq_getElem?_getD, hk] using this

variable [NativeRustcArm.Host]

/-- **The index, the leaves copied**: `b58` to `b59`. -/
theorem index_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : AfterLoop r (hMsgBytes r) m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b59Offset ∧ r.AtFors st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b58Offset⟩ := by
  obtain ⟨hK, h23, hH, hL⟩ := hA
  have hl := length_hMsgBytes r
  have hLl : (leavesBytes (hMsgBytes r) 24).length = 192 := length_leavesBytes _ _
  refine Run.memcpyCall r hp hpre hc Sphincs.SphincsVerify.b58_in_code rfl run_b58 rfl
    (a := 25752) (b := 16400) (n := 192) hK (knownOK_ptr h23 (knownOK_nil m)) rfl rfl rfl
    ⟨by decide, by decide⟩ (by decide) (by decide) hLl fun m₁ hm₁ hK₁ hkb₁ ↦
      ⟨hkb₁ 16400 _ (by omega) (by rw [hLl]; rfl) hL, fun m₂ hK₂ hS₂ _ hB₂ ↦ .done _ ⟨rfl, ?_⟩⟩
  have l30 := frame_load_byte (r := r) (m := m) hH (k := 30) (by omega) rfl
  have l31 := frame_load_byte (r := r) (m := m) hH (k := 31) (by omega) rfl
  have l32 := frame_load_byte (r := r) (m := m) hH (k := 32) (by omega) rfl
  have l33 := frame_load_byte (r := r) (m := m) hH (k := 33) (by omega) rfl
  obtain ⟨hF₂, hI₂, h392⟩ := hK₂
  refine ⟨hF₂, hI₂, ?_, ?_, regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .X24) (o := 25752) rfl),
    regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .X21) (o := 16400) rfl),
    regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .X23) (o := 21648) rfl), ?_, h392⟩
  · refine regIs_of_saved hS₂ rfl ?_
    unfold Run.RegIs
    rw [hm₁.regs .X22 idxSym rfl, idxSym_eval _ _ _ _ _ l30 l31 l32 l33, idx_eq,
      digestFields_fst _ hl]
  · refine regIs_of_saved hS₂ rfl ?_
    unfold Run.RegIs
    rw [hm₁.regs .X20 (.load 0 24753 1) rfl, show Sym.eval (r.env m) (.load 0 24753 1) =
      (r.env m).load 0 24753 1 from rfl, l33, idx_eq, digestFields_fst _ hl]
    exact idx_low _ _ _ _
  · rw [leaves_bytes]
    exact hB₂

end

end NativeRustcArm.SphincsVerifyProof.Digest
