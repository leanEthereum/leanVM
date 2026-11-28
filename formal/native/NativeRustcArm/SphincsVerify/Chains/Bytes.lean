module

public import NativeRustcArm.SphincsVerify.Calls
public import NativeRustcArm.SphincsVerify.Rev

/-!
# Bytes in the frame, for the chains

`BytesAt` of concatenations and slices (`BytesAt.append`, `BytesAt.slice`); a symbolic state that also holds a literal write the memory already
has (`Match.withWrite`); the bytes a block's write leaves: of a load (`bytesAt_write_load`), of a
literal (`bytesAt_write_lit`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

public section

/-! ## `BytesAt` -/

theorem addr_add_add (a : BitVec 64) (o i : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (o + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem BytesAt.append {d : DataMem} {a : BitVec 64} {bs cs : List UInt8} (h₁ : BytesAt d a bs)
    (h₂ : BytesAt d (a + BitVec.ofNat 64 bs.length) cs) : BytesAt d a (bs ++ cs) := by
  intro i hi
  by_cases h : i < bs.length
  · rw [List.getElem_append_left h]
    exact h₁ i h
  · rw [List.getElem_append_right (by omega)]
    have := h₂ (i - bs.length) (by simp at hi; omega)
    rwa [addr_add_add, show bs.length + (i - bs.length) = i by omega] at this

theorem BytesAt.slice {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (o n : Nat) : BytesAt d (a + BitVec.ofNat 64 o) ((bs.drop o).take n) := by
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [addr_add_add, h (o + i) (by omega)]
  simp

theorem BytesAt.left {d : DataMem} {a : BitVec 64} {bs cs : List UInt8}
    (h : BytesAt d a (bs ++ cs)) : BytesAt d a bs := fun i hi ↦ by
  rw [h i (by simp; omega), List.getElem_append_left hi]

theorem BytesAt.right {d : DataMem} {a : BitVec 64} {bs cs : List UInt8}
    (h : BytesAt d a (bs ++ cs)) : BytesAt d (a + BitVec.ofNat 64 bs.length) cs := fun i hi ↦ by
  rw [addr_add_add, h _ (by simp; omega), List.getElem_append_right (by omega)]
  simp


/-! ## A literal write the memory has -/

variable [Labels]

/-- **A state with a write the memory already holds**: where `S` has no write, the state with
`v`'s low `n` bytes at `o` in region `r` describes `m` too, when `m` has those bytes there. -/
theorem Match.withWrite {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hS : S.mem = []) {r o n : Nat} {v : Sym} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz))
    (hv : ∀ i < n, m.dmem.get? (b + BitVec.ofNat 64 (o + i)) = some (byteOf (v.eval env) i)) :
    Match env { S with mem := [⟨r, o, n, v⟩] } m where
  regs := hm.regs
  sp := hm.sp
  flags := hm.flags
  regions := hm.regions
  labels := hm.labels
  bounds := hm.bounds
  aliases := hm.aliases
  outside := hm.outside
  mem r' b' n' hb' i hi := by
    have h0 := hm.mem r' b' n' hb' i hi
    rw [hS] at h0
    show _ = memByte env [⟨r, o, n, v⟩] r' b' i
    by_cases hc : r = r' ∧ o ≤ i ∧ i < o + n
    · obtain ⟨rfl, h1, h2⟩ := hc
      rw [hb] at hb'
      cases hb'
      have := hv (i - o) (by omega)
      rw [show o + (i - o) = i by omega] at this
      rw [this]
      simp [memByte, findWrite, h1, h2]
    · rw [h0]
      simp only [memByte, findWrite, hc, ↓reduceIte]

/-! ## The bytes a block writes -/

/-- The newest write covering each of the `n` bytes at `o` in region `r` is `v`'s, from its byte
0 (decided on a literal state). -/
@[expose] def covers (ws : List Write) (r o n : Nat) (v : Sym) : Bool :=
  (List.range n).all fun i ↦ findWrite r (o + i) ws == some (v, i)

omit [Labels] in
theorem findWrite_of_covers {ws : List Write} {r o n : Nat} {v : Sym}
    (h : covers ws r o n v = true) : ∀ i < n, findWrite r (o + i) ws = some (v, i) := by
  intro i hi
  simp only [covers, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi

/-- **A load written back**: where a block's newest write of the `n ≤ 8` bytes at `o` in region
`r` is the load of the `n` bytes at `o'` of region `r'`, and those were `bs`, they are `bs`. -/
theorem bytesAt_write_load {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o n : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hle : o + n ≤ sz) {r' o' : Nat} (hw : covers S.mem r o n (.load r' o' n) = true)
    {bs : List UInt8} (hlen : bs.length = n) (hn : n ≤ 8)
    (h : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 o') bs) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) bs := by
  have := hm.bytesAt_write hb hle (findWrite_of_covers hw)
  intro i hi
  have h1 := this i (by simp; omega)
  simp only [List.getElem_map, List.getElem_range] at h1
  rw [h1]
  show some (byteOf (env.load r' o' n) i) = _
  rw [byteOf_load (by omega) hn, ← addr_add_add, h i hi]
  rfl

/-- **A literal written**: the bytes of the literal `c`. -/
theorem bytesAt_write_lit {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o n : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hle : o + n ≤ sz) {c : Nat} (hw : covers S.mem r o n (.lit c) = true) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) ((List.range n).map (byteOf (BitVec.ofNat 64 c))) :=
  hm.bytesAt_write hb hle (findWrite_of_covers hw)

/-- **A value written**: the bytes of the value. -/
theorem bytesAt_write_val {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o n : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hle : o + n ≤ sz) {v : Sym} (hw : covers S.mem r o n v = true) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) ((List.range n).map (byteOf (v.eval env))) :=
  hm.bytesAt_write hb hle (findWrite_of_covers hw)

end

end NativeRustcArm.SphincsVerifyProof.Chains
