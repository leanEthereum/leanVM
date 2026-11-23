module

public import NativeRustcArm.SphincsVerify.Frame

/-!
# Calls from the frame

`sphincs_verify` calls `memset`, `memcpy`, `Hasher::update` and `Hasher::finalize` on the frame's
bytes. Their preconditions from the frame's offsets (`Run.memset_pre`, `Run.memcpy_pre`,
`Run.update_pre`, `Run.finalize_pre`, `Run.keccakF_pre`): X0 and X1 the frame's bytes `a` and `b`
(`RegIs`), X2 the
length, the ranges inside the frame and apart where the contract asks. After a call that changed
the frame's bytes `a .. a + n` and the callee's stack (`Run.CallOut`): the frame's invariant
(`Run.frame_of_call`), the frame's bytes apart from `a .. a + n` kept (`Run.bytesAt_of_call`,
`Run.bytesOf_of_call`); each contract's post in that form (`Run.memset_out`, `Run.memcpy_out`,
`Run.update_out`, `Run.finalize_out`, `Run.keccakF_out`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc

public section

/-- The bytes `bytesOf` reads where `BytesAt` holds. -/
theorem bytesOf_of_bytesAt {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    bytesOf d a bs.length = bs := by
  apply List.ext_getElem (by simp [bytesOf])
  intro i h1 h2
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  rw [h i h2]
  rfl

/-- `SameOutside` of a smaller set of changes. -/
theorem SameOutside.mono {d d' : DataMem} {R R' : BitVec 64 → Prop} (h : SameOutside d d' R)
    (hR : ∀ p, R p → R' p) : SameOutside d d' R' := fun p hp ↦ h p fun h' ↦ hp (hR p h')

theorem getXReg_X0 (m : MachineData) : m.regs.getXReg .X0 = m.regs.X0 := rfl
theorem getXReg_X1 (m : MachineData) : m.regs.getXReg .X1 = m.regs.X1 := rfl
theorem getXReg_X2 (m : MachineData) : m.regs.getXReg .X2 = m.regs.X2 := rfl

namespace Run

variable (r : Run) [Labels]

omit [Labels] in
/-- The frame's byte `i` of the bytes at `a`. -/
theorem off_add (a i : Nat) : r.off a + BitVec.ofNat 64 i = r.off (a + i) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- A frame byte outside `a .. a + n` is not in it. -/
theorem not_inRange_off (hpre : r.Pre) {a n o : Nat} (ha : a + n ≤ 29376) (ho : o < 29376)
    (h : o < a ∨ a + n ≤ o) : ¬InRange (r.off a) n (r.off o) := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have h1 := r.off_toNat hpre (a := a) (by omega)
  have h2 := r.off_toNat hpre (a := o) (by omega)
  unfold InRange
  rw [BitVec.toNat_sub, h1, h2]
  omega

/-- A frame byte is not in a callee's stack. -/
theorem not_inRange_below (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {N : Nat}
    (hN : N ≤ finalizeStack) {o : Nat} (ho : o < 29376) :
    ¬InRange (stackBelow m N) N (r.off o) := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have hl := r.stackBelow_toNat hpre hF hN
  have h2 := r.off_toNat hpre (a := o) (by omega)
  rw [finalizeStack_eq] at hN
  unfold InRange
  rw [BitVec.toNat_sub, h2]
  omega

/-- What a call changes: the frame's bytes `a .. a + n` and the callee's `N` bytes of stack. -/
@[expose] def CallOut (m : MachineData) (a n N : Nat) (p : BitVec 64) : Prop :=
  InRange (r.off a) n p ∨ InRange (stackBelow m N) N p

/-- **The frame's invariant after a call** that changed `CallOut`. -/
theorem frame_of_call (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) (hS : Saved m m')
    {a n N : Nat} (ha : a + n ≤ 29280) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : r.Frame m' :=
  hF.of_post hS hout fun _ hp ↦ hp.elim (r.inRange_off hpre ha) (r.inRange_below hpre hF hN)

theorem not_callOut (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a n N : Nat}
    (ha : a + n ≤ 29376) (hN : N ≤ finalizeStack) {o : Nat} (ho : o < 29376)
    (h : o < a ∨ a + n ≤ o) : ¬r.CallOut m a n N (r.off o) :=
  fun hp ↦ hp.elim (r.not_inRange_off hpre ha ho h) (r.not_inRange_below hpre hF hN ho)

/-- **The frame's bytes a call did not change** are kept. -/
theorem bytesAt_of_call (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {a n N : Nat}
    (ha : a + n ≤ 29376) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 29376) (hd : o + bs.length ≤ a ∨ a + n ≤ o)
    (h : BytesAt m.dmem (r.off o) bs) : BytesAt m'.dmem (r.off o) bs :=
  bytesAt_of_sameOutside h hout fun i hi ↦ by
    rw [off_add]
    exact r.not_callOut hpre hF ha hN (by omega) (by omega)

/-- `bytesOf` of the frame's bytes a call did not change. -/
theorem bytesOf_of_call (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {a n N : Nat}
    (ha : a + n ≤ 29376) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) {o k : Nat} (ho : o + k ≤ 29376)
    (hd : o + k ≤ a ∨ a + n ≤ o) : bytesOf m'.dmem (r.off o) k = bytesOf m.dmem (r.off o) k := by
  unfold bytesOf
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [hout _ (by rw [off_add]; exact r.not_callOut hpre hF ha hN (by omega) (by omega))]

/-! ## Preconditions -/

/-- **`memset(a, _, n)`**'s precondition. -/
theorem memset_pre (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a n : Nat}
    (h0 : RegIs m .X0 (r.off a)) (h2 : m.regs.X2.toNat = n) (ha : a + n ≤ 29376) :
    MemsetPre m := by
  unfold MemsetPre
  rw [h2, ← getXReg_X0 m, h0]
  exact r.frame_mapped hpre hF ha

/-- **`memcpy(a, b, n)`**'s precondition. -/
theorem memcpy_pre (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a b n : Nat}
    (h0 : RegIs m .X0 (r.off a)) (h1 : RegIs m .X1 (r.off b)) (h2 : m.regs.X2.toNat = n)
    (ha : a + n ≤ 29376) (hb : b + n ≤ 29376) (hd : a + n ≤ b ∨ b + n ≤ a) : MemcpyPre m := by
  simp only [MemcpyPre]
  rw [h2, ← getXReg_X0 m, h0, ← getXReg_X1 m, h1]
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF ha
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF hb
  exact ⟨m1, m2, w1, w2, r.apart_off hpre ha hb hd⟩

/-- **`Hasher::update(a, b, n)`**'s precondition, the hasher at `a`. -/
theorem update_pre (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a b n : Nat}
    (h0 : RegIs m .X0 (r.off a)) (h1 : RegIs m .X1 (r.off b)) (h2 : m.regs.X2.toNat = n)
    (ha : a + 344 ≤ 29376) (hb : b + n ≤ 29376) (hd : a + 344 ≤ b ∨ b + n ≤ a)
    (hh : ∃ x, Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) x) : UpdatePre m := by
  simp only [UpdatePre]
  rw [h2, ← getXReg_X0 m, h0, ← getXReg_X1 m, h1]
  have hN : updateStack ≤ finalizeStack := by decide
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF ha
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF hb
  exact ⟨r.stackOk hpre hF hN, r.rcAt hpre hF hN, hh, m1, w1, m2, w2, r.apart_off hpre ha hb hd,
    r.apart_off_below hpre hF ha hN, r.apart_off_below hpre hF hb hN, r.apart_rc hpre ha⟩

/-- **`Hasher::finalize(o, a)`**'s precondition, the hasher at `a`, the output at `o`. -/
theorem finalize_pre (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {o a : Nat}
    (h0 : RegIs m .X0 (r.off o)) (h1 : RegIs m .X1 (r.off a)) (ho : o + 32 ≤ 29376)
    (ha : a + 344 ≤ 29376) (hd : o + 32 ≤ a ∨ a + 344 ≤ o)
    (hh : ∃ x, Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) x) : FinalizePre m := by
  simp only [FinalizePre]
  rw [← getXReg_X0 m, h0, ← getXReg_X1 m, h1]
  have hN : finalizeStack ≤ finalizeStack := le_rfl
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF ha
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF ho
  exact ⟨r.stackOk hpre hF hN, r.rcAt hpre hF hN, hh, m1, w1, m2, w2, r.apart_off hpre ho ha hd,
    r.apart_off_below hpre hF ha hN, r.apart_off_below hpre hF ho hN, r.apart_rc hpre ho⟩

/-- **`keccak_f(a)`**'s precondition. -/
theorem keccakF_pre (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a : Nat}
    (h0 : RegIs m .X0 (r.off a)) (ha : a + 200 ≤ 29376) : KeccakFPre m := by
  simp only [KeccakFPre]
  rw [← getXReg_X0 m, h0]
  have hN : keccakFStack ≤ finalizeStack := by decide
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF ha
  exact ⟨r.stackOk hpre hF hN, r.rcAt hpre hF hN, m1, w1, r.apart_off_below hpre hF ha hN,
    r.apart_rc hpre ha⟩

/-! ## Postconditions -/

omit [Labels] in
/-- **After `memset(a, c, n)`**: the `n` bytes `c`, the rest kept. -/
theorem memset_out {m m' : MachineData} {a n : Nat} (h0 : RegIs m .X0 (r.off a))
    (h2 : m.regs.X2.toNat = n) (h : MemsetPost m m') :
    BytesAt m'.dmem (r.off a) (List.replicate n m.regs.X1.toUInt8) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m a n 0) ∧ Saved m m' := by
  simp only [MemsetPost] at h
  rw [h2, ← getXReg_X0 m, h0] at h
  exact ⟨h.2.1, SameOutside.mono h.2.2.1 fun _ hp ↦ Or.inl hp, h.2.2.2⟩

omit [Labels] in
/-- **After `memcpy(a, b, n)`**: the `n` bytes from `b`, the rest kept. -/
theorem memcpy_out {m m' : MachineData} {a b n : Nat} (h0 : RegIs m .X0 (r.off a))
    (h1 : RegIs m .X1 (r.off b)) (h2 : m.regs.X2.toNat = n) (h : MemcpyPost m m') :
    BytesAt m'.dmem (r.off a) (bytesOf m.dmem (r.off b) n) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m a n 0) ∧ Saved m m' := by
  simp only [MemcpyPost] at h
  rw [h2, ← getXReg_X0 m, h0, ← getXReg_X1 m, h1] at h
  exact ⟨h.2.1, SameOutside.mono h.2.2.1 fun _ hp ↦ Or.inl hp, h.2.2.2⟩

omit [Labels] in
/-- **After `Hasher::update(a, b, n)`**: the hasher has absorbed the `n` bytes from `b` too, the
rest kept. -/
theorem update_out {m m' : MachineData} {a b n : Nat} (h0 : RegIs m .X0 (r.off a))
    (h1 : RegIs m .X1 (r.off b)) (h2 : m.regs.X2.toNat = n) (h : UpdatePost m m') :
    (∀ x, Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) x →
      Keccak.HasherHolds (bytesOf m'.dmem (r.off a) 344) (x ++ bytesOf m.dmem (r.off b) n)) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m a 344 updateStack) ∧ Saved m m' := by
  simp only [UpdatePost] at h
  rw [h2, ← getXReg_X0 m, h0, ← getXReg_X1 m, h1] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

omit [Labels] in
/-- **After `Hasher::finalize(o, a)`**: the 32 bytes at `o` the hasher's digest, the rest kept. -/
theorem finalize_out {m m' : MachineData} {o a : Nat} (h0 : RegIs m .X0 (r.off o))
    (h1 : RegIs m .X1 (r.off a)) (h : FinalizePost m m') :
    BytesAt m'.dmem (r.off o) (Keccak.finalize (bytesOf m.dmem (r.off a) 344)) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m o 32 finalizeStack) ∧ Saved m m' := by
  simp only [FinalizePost] at h
  rw [← getXReg_X0 m, h0, ← getXReg_X1 m, h1] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

omit [Labels] in
/-- **After `keccak_f(a)`**: the 200 bytes at `a` permuted, the rest kept. -/
theorem keccakF_out {m m' : MachineData} {a : Nat} (h0 : RegIs m .X0 (r.off a))
    (h : KeccakFPost m m') :
    BytesAt m'.dmem (r.off a) (Keccak.keccakF (bytesOf m.dmem (r.off a) 200)) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m a 200 keccakFStack) ∧ Saved m m' := by
  simp only [KeccakFPost] at h
  rw [← getXReg_X0 m, h0] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

end Run

end

end NativeRustcArm.SphincsVerifyProof
