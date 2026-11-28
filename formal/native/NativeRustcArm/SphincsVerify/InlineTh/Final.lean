module

public import NativeRustcArm.SphincsVerify.InlineTh.ByteNF

/-!
# An inlined `finalize`: the final block XORed into the state

The inlined `finalize` copies the hasher's state to the other hasher's state `A`, zeroes a
136-byte block `K`, copies the `L` buffered bytes `T` there, XORs `0x01` into byte `L` and `0x80`
into byte 135 (the padded block `finalBlock T`), and XORs the block's 17 lanes into `A`'s rate, in
one block of code. `finalCheck` checks on the block's literal post-state that each of `A`'s 136
rate bytes is a write of the byte of `A` XOR the byte of `K` XOR the padding constant `padCst`,
and that the rest of `A` is not written; then `A` holds `xorBlock` of its state and the padded
block (`xorFinal`).
-/

namespace NativeRustcArm.SphincsVerifyProof.InlineTh

open NativeRustcArm.Sym NativeRustc NativeRustc.Keccak

@[expose] public section

/-- The padding's constant at byte `p` after `L` bytes: `0x01` at `L`, `0x80` at 135. -/
def padCst (L p : Nat) : UInt8 := (if p = L then 1 else 0) ^^^ (if p = 135 then 0x80 else 0)

/-- **The check of an inlined final absorb** in region `r`: each rate byte `p < 136` of the state
at `oA` is a write whose byte is the state's byte XOR the block's (at `oK`) XOR `padCst L p`; the
state's other 64 bytes are not written. -/
def finalCheck (ws : List Write) (r oA oK L : Nat) : Bool :=
  (List.range 136).all (fun p => match findWrite r (oA + p) ws with
    | some (v, t) => decide (symByte 64 v t = some ⟨padCst L p, [(r, oA + p), (r, oK + p)]⟩)
    | none => false) &&
  (List.range 64).all fun q => (findWrite r (oA + (136 + q)) ws).isNone

end

public section

theorem finalCheck_rate {ws : List Write} {r oA oK L : Nat} (h : finalCheck ws r oA oK L = true)
    {p : Nat} (hp : p < 136) : ∃ v t, findWrite r (oA + p) ws = some (v, t) ∧
      symByte 64 v t = some ⟨padCst L p, [(r, oA + p), (r, oK + p)]⟩ := by
  simp only [finalCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1 p hp
  revert this
  cases findWrite r (oA + p) ws with
  | none => simp
  | some vt => exact fun h ↦ ⟨vt.1, vt.2, rfl, of_decide_eq_true h⟩

theorem finalCheck_rest {ws : List Write} {r oA oK L : Nat} (h : finalCheck ws r oA oK L = true)
    {p : Nat} (hp1 : 136 ≤ p) (hp2 : p < 200) : findWrite r (oA + p) ws = none := by
  simp only [finalCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.2 (p - 136) (by omega)
  rw [show 136 + (p - 136) = p by omega] at this
  exact Option.isNone_iff_eq_none.mp this

theorem getD_eq_getElem' (l : List UInt8) {p : Nat} (h : p < l.length) : l[p] = l.getD p 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Byte `p` of the padded block: the bytes and zeros XOR the padding's constant. -/
theorem getD_finalBlock {T : List UInt8} {p : Nat} (hT : T.length < 136) (hp : p < 136) :
    (finalBlock T).getD p 0 =
      (T ++ List.replicate (136 - T.length) 0).getD p 0 ^^^ padCst T.length p := by
  have hl : (T ++ List.replicate (136 - T.length) 0).length = 136 := by simp; omega
  simp only [finalBlock, List.getD_eq_getElem?_getD, List.getElem?_modify,
    List.getElem?_eq_getElem (show p < (T ++ List.replicate (136 - T.length) 0).length by omega),
    Option.getD_some, padCst]
  by_cases h1 : T.length = p <;> by_cases h2 : 135 = p <;>
    simp [h1, h2, eq_comm (a := p)]

/-- **The inlined final absorb**: where `finalCheck` holds of a block's post-state, and the block
`K` held the `L` bytes `T` then zeros, the state `A` holds `xorBlock` of its bytes and
`finalBlock T`. -/
theorem xorFinal [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    {oA oK L : Nat} (hA : oA + 200 ≤ sz)
    (hc : finalCheck S.mem r oA oK L = true) {T : List UInt8} (hT : T.length = L) (hL : L < 136)
    (hblk : BytesAt env.mem0 (b + BitVec.ofNat 64 oK) (T ++ List.replicate (136 - L) 0)) :
    BytesAt m.dmem (b + BitVec.ofNat 64 oA)
      (xorBlock (bytesOf env.mem0 (b + BitVec.ofNat 64 oA) 200) (finalBlock T)) := by
  have hbase := Env.base_eq (env := env) hb
  intro i hi
  have hi' : i < 200 := by rwa [xorBlock, length_stateBytes] at hi
  rw [getD_eq_getElem' _ hi, Hasher.getD_xorBlock _ _ hi', addr_add, hm.mem r b sz hb (oA + i) (by omega)]
  have hS : (bytesOf env.mem0 (b + BitVec.ofNat 64 oA) 200).getD i 0 = memAt env r (oA + i) := by
    rw [Hasher.getD_bytesOf _ _ hi', addr_add, memAt, hbase]
  by_cases hr : i < 136
  · obtain ⟨v, t, hf, hs⟩ := finalCheck_rate hc hr
    rw [Hasher.ite_pos' hr, memByte, hf]
    dsimp only
    rw [byteOf_eval_of_symByte 64 v t _ hs, hS,
      getD_finalBlock (by omega) hr, hT]
    have hK' : (T ++ List.replicate (136 - L) 0).getD i 0 = memAt env r (oK + i) := by
      have := hblk i (by simp; omega)
      rw [addr_add] at this
      rw [memAt, hbase, this, Option.getD_some, getD_eq_getElem']
    rw [hK']
    simp only [XB.eval, xorAll, UInt8.xor_zero]
    congr 1
    rw [← UInt8.xor_assoc, UInt8.xor_comm (padCst L i), UInt8.xor_assoc,
      UInt8.xor_comm (padCst L i)]
  · rw [Hasher.ite_neg' hr, memByte, finalCheck_rest hc (by omega) hi', hS, memAt, hbase]
    have := hwf.mapped r b sz hb (oA + i) (by omega)
    revert this
    cases env.mem0.get? (b + BitVec.ofNat 64 (oA + i)) <;> simp

end

end NativeRustcArm.SphincsVerifyProof.InlineTh
