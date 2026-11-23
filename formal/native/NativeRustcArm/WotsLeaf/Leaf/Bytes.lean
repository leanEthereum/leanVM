module

public import NativeRustcArm.Code.Xmss.WotsLeaf.Names

public import NativeRustcArm.WotsLeaf.Leaf.Exec
public import NativeRustcArm.WotsLeaf.Codeword.Facts

/-!
# The leaf's bytes

Part of a load written back (`bytesAt_write_loadTake`), `hi >> 16`'s low byte (`take_hi16`), the
leaf hash's address (`leaf_addr`), and what `outOK` says (`outOK_spec`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf
open NativeRustcArm.SphincsVerifyProof.InlineTh Leaf

public section

/-- **The first `n` bytes of a `k`-byte load written back.** -/
theorem bytesAt_write_loadTake [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {r o n : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + n ≤ sz) {r' o' k : Nat}
    (hw : covers S.mem r o n (.load r' o' k) = true) {bs : List UInt8} (hlen : bs.length = k)
    (hnk : n ≤ k) (hk : k ≤ 8) (h : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 o') bs) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) (bs.take n) := by
  have := hm.bytesAt_write hb hle (findWrite_of_covers hw)
  intro i hi
  simp only [List.length_take] at hi
  have h1 := this i (by simp; omega)
  simp only [List.getElem_map, List.getElem_range] at h1
  rw [h1, List.getElem_take]
  show some (byteOf (env.load r' o' k) i) = _
  rw [byteOf_load (by omega) hk, ← addr_add_add, h i (by omega)]
  rfl

theorem take_hi16 (h : UInt32) : (u32Bytes (h >>> 16)).take 1 = ((u32Bytes h).drop 2).take 1 := by
  simp only [u32Bytes, Native.XmssVerifier.bytes, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero, List.cons.injEq, and_true]
  apply u8_ext
  simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- What `b49` does, from `outOK`. -/
theorem outOK_spec : ∃ S, exec b49 s49 = some (S, .jump NativeRustcArm.Xmss.WotsLeaf.label_6) ∧
    (∀ i < 75, ∃ v t, findWrite 1 i S.mem = some (v, t) ∧ symByte 64 v t = some (outByte i)) ∧
    frameOrOut S = true ∧ Run.inRegions S = true ∧ Run.noWriteIn S 2656 96 = true ∧
    S.sp = .ptr 0 0 := by
  have h := outOK_b49
  unfold outOK at h
  split at h
  · rename_i S x hx
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hall, hf, hin, hn, hsp, rfl⟩ := h
    refine ⟨S, hx, fun i hi ↦ ?_, hf, hin, hn, hsp⟩
    have := List.all_eq_true.mp hall i (List.mem_range.mpr hi)
    revert this
    cases findWrite 1 i S.mem with
    | none => simp
    | some vt => exact fun h ↦ ⟨vt.1, vt.2, rfl, by simpa using h⟩
  · cases h

end

end NativeRustcArm.WotsLeafProof
