module

public import NativeRustcArm.WotsLeaf.Calls

/-!
# Bytes in memory and the bytes a block writes

`BytesAt` of concatenations and slices (`BytesAt.append`, `BytesAt.slice`, `BytesAt.left`,
`BytesAt.right`), mapped bytes as `bytesOf` reads them (`bytesAt_bytesOf`); a symbolic state with
writes the memory already holds (`Match.withWrites`); the bytes a block's writes leave
(`covers`: of a load `bytesAt_write_load`, of a value `bytesAt_write_val`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustcArm.Sym

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

theorem BytesAt.zero {d : DataMem} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d (a + BitVec.ofNat 64 0) bs) : BytesAt d a bs := by
  simpa using h

/-- Mapped bytes are what `bytesOf` reads. -/
theorem bytesAt_bytesOf {d : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n) :
    BytesAt d a (bytesOf d a n) := by
  intro i hi
  simp only [bytesOf, List.length_map, List.length_range] at hi
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h i hi)
  rw [hv]
  rfl

theorem length_bytesOf (d : DataMem) (a : BitVec 64) (n : Nat) : (bytesOf d a n).length = n := by
  simp [bytesOf]

/-- Bytes at an address are mapped. -/
theorem BytesAt.mapped {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    Mapped d a bs.length := fun i hi ↦ by rw [h i hi]; rfl

/-! ## Writes a symbolic state holds -/

variable [Labels]

/-- **A state with writes the memory already holds**: where `S` has no write, the state with the
writes `ws` describes `m` too, when `m` has each write's bytes. -/
theorem Match.withWrites {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hS : S.mem = []) {ws : List Write}
    (hws : ∀ w ∈ ws, ∀ b sz, env.regions[w.r]? = some (b, sz) → ∀ i < w.n,
      m.dmem.get? (b + BitVec.ofNat 64 (w.off + i)) = some (byteOf (w.v.eval env) i)) :
    Match env { S with mem := ws } m where
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
    show _ = memByte env ws r' b' i
    unfold memByte
    cases hf : findWrite r' i ws with
    | none => exact h0
    | some vt =>
      obtain ⟨v, t⟩ := vt
      have key : ∀ (l : List Write), l ⊆ ws → findWrite r' i l = some (v, t) →
          m.dmem.get? (b' + BitVec.ofNat 64 i) = some (byteOf (v.eval env) t) := by
        intro l
        induction l with
        | nil => intro _ h; cases h
        | cons w l ih =>
          intro hsub h
          rw [findWrite_cons] at h
          by_cases hc : w.r = r' ∧ w.off ≤ i ∧ i < w.off + w.n
          · rw [ite_pos hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have := hws w (hsub List.mem_cons_self) b' n' (hc.1 ▸ hb') (i - w.off) (by omega)
            rwa [show w.off + (i - w.off) = i by omega] at this
          · rw [ite_neg hc] at h
            exact ih (fun x hx ↦ hsub (List.mem_cons_of_mem _ hx)) h
      exact key ws (fun _ h ↦ h) hf

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

/-- **A value written**: the bytes of the value. -/
theorem bytesAt_write_val {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o n : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hle : o + n ≤ sz) {v : Sym} (hw : covers S.mem r o n v = true) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) ((List.range n).map (byteOf (v.eval env))) :=
  hm.bytesAt_write hb hle (findWrite_of_covers hw)

end

end NativeRustcArm.WotsLeafProof
