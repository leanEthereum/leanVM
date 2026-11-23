module

public import NativeRustcX64.WotsLeaf.Frame

/-!
# Calls from the frame

`wots_leaf` calls `memset`, `memcpy`, `Hasher::update`, `Hasher::finalize` and `keccak_f` on the
frame's bytes. Their preconditions at a callee's entry (`Run.CallFrame`) from the frame's offsets
(`Run.memset_pre`, `Run.memcpy_pre`, `Run.update_pre`, `Run.finalize_pre`, `Run.keccakF_pre`): RDI
and RSI the frame's bytes `a` and `b` (`RegIs`), RDX the length, the ranges inside the frame and
apart where the contract asks. After a call that changed the frame's bytes `a .. a + n` and the
callee's stack (`Run.CallOut`): the frame's invariant (`Run.frame_of_call`), the frame's bytes
apart from `a .. a + n` kept (`Run.bytesAt_of_call`, `Run.bytesOf_of_call`); each contract's post
in that form (`Run.memset_out`, `Run.memcpy_out`, `Run.update_out`, `Run.finalize_out`,
`Run.keccakF_out`).
-/

namespace NativeRustcX64.WotsLeafProof

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

namespace Run

variable (r : Run) [Labels]

/-- A frame byte outside `a .. a + n` is not in it. -/
theorem not_inRange_off (hpre : r.Pre) {a n o : Nat} (ha : a + n ≤ 2768) (ho : o < 2768)
    (h : o < a ∨ a + n ≤ o) : ¬InRange (r.off a) n (r.off o) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold InRange
    omega
  have h1 := r.off_toNat hpre (a := a) (by omega)
  have h2 := r.off_toNat hpre (a := o) (by omega)
  unfold InRange
  rw [BitVec.toNat_sub, h1, h2]
  have := r.base_top hpre
  omega

/-- A frame byte is not in a callee's stack or return address. -/
theorem not_inRange_below (hpre : r.Pre) {m : MachineData} (hsp : rspOf m = r.base - 8#64)
    {N : Nat} (hN : N ≤ finalizeStack) {o : Nat} (ho : o < 2768) :
    ¬InRange (stackBelow m N) (N + 8) (r.off o) := by
  have hb := r.base_toNat hpre
  have hl := r.stackBelow_toNat hpre hsp hN
  have h2 := r.off_toNat hpre (a := o) (by omega)
  have := r.base_top hpre
  rw [finalizeStack_eq] at hN
  unfold InRange
  rw [BitVec.toNat_sub, h2]
  omega

/-- What a call changes: the frame's bytes `a .. a + n` and the callee's `N` bytes of stack and
its return address. -/
@[expose] def CallOut (m : MachineData) (a n N : Nat) (p : BitVec 64) : Prop :=
  InRange (r.off a) n p ∨ InRange (stackBelow m N) (N + 8) p

/-- **The frame's invariant after a call** that changed `CallOut`, back at RSP the base. -/
theorem frame_of_call (hpre : r.Pre) {m m' : MachineData} (hF : r.CallFrame m) (hS : Saved m m')
    (hsp : rspOf m' = r.base) {a n N : Nat} (ha : a + n ≤ 2712) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : r.Frame m' :=
  (r.frame_iff m').2 <| hF.of_block hsp hout
    (fun _ hp ↦ hp.elim (r.inRange_off hpre ha) (r.inRange_below hpre hF.rsp hN)) hS.2

theorem not_callOut (hpre : r.Pre) {m : MachineData} (hsp : rspOf m = r.base - 8#64) {a n N : Nat}
    (ha : a + n ≤ 2768) (hN : N ≤ finalizeStack) {o : Nat} (ho : o < 2768)
    (h : o < a ∨ a + n ≤ o) : ¬r.CallOut m a n N (r.off o) :=
  fun hp ↦ hp.elim (r.not_inRange_off hpre ha ho h) (r.not_inRange_below hpre hsp hN ho)

/-- **The frame's bytes a call did not change** are kept. -/
theorem bytesAt_of_call (hpre : r.Pre) {m m' : MachineData} (hsp : rspOf m = r.base - 8#64)
    {a n N : Nat} (ha : a + n ≤ 2768) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 2768) (hd : o + bs.length ≤ a ∨ a + n ≤ o)
    (h : BytesAt m.dmem (r.off o) bs) : BytesAt m'.dmem (r.off o) bs :=
  bytesAt_of_sameOutside h hout fun i hi ↦ by
    rw [off_add]
    exact r.not_callOut hpre hsp ha hN (by omega) (by omega)

/-! ## Preconditions -/

/-- **`memset(a, _, n)`**'s precondition. -/
theorem memset_pre (hpre : r.Pre) {m : MachineData} (hF : r.CallFrame m) {a n : Nat}
    (h0 : RegIs m .rdi (r.off a)) (h2 : (reg m .rdx).toNat = n) (ha : a + n ≤ 2768) :
    MemsetPre m := by
  simp only [MemsetPre]
  rw [h2, show reg m .rdi = r.off a from h0]
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := a) (n := n) (by omega)
  exact ⟨r.stackOk hpre hF (by decide), m1, w1, r.apart_off_ret hpre hF.rsp ha⟩

/-- **`memcpy(a, b, n)`**'s precondition. -/
theorem memcpy_pre (hpre : r.Pre) {m : MachineData} (hF : r.CallFrame m) {a b n : Nat}
    (h0 : RegIs m .rdi (r.off a)) (h1 : RegIs m .rsi (r.off b)) (h2 : (reg m .rdx).toNat = n)
    (ha : a + n ≤ 2768) (hb : b + n ≤ 2768) (hd : a + n ≤ b ∨ b + n ≤ a) : MemcpyPre m := by
  simp only [MemcpyPre]
  rw [h2, show reg m .rdi = r.off a from h0, show reg m .rsi = r.off b from h1]
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := a) (n := n) (by omega)
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF (a := b) (n := n) (by omega)
  exact ⟨r.stackOk hpre hF (by decide), m1, m2, w1, w2, r.apart_off hpre ha hb hd,
    r.apart_off_ret hpre hF.rsp ha⟩

/-- **`Hasher::update(a, b, n)`**'s precondition, the hasher at `a`. -/
theorem update_pre (hpre : r.Pre) {m : MachineData} (hF : r.CallFrame m) {a b n : Nat}
    (h0 : RegIs m .rdi (r.off a)) (h1 : RegIs m .rsi (r.off b)) (h2 : (reg m .rdx).toNat = n)
    (ha : a + 344 ≤ 2768) (hb : b + n ≤ 2768) (hd : a + 344 ≤ b ∨ b + n ≤ a)
    (hh : ∃ x, Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) x) : UpdatePre m := by
  simp only [UpdatePre]
  rw [h2, show reg m .rdi = r.off a from h0, show reg m .rsi = r.off b from h1]
  have hN : updateStack ≤ finalizeStack := by decide
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := a) (n := 344) (by omega)
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF (a := b) (n := n) (by omega)
  refine ⟨r.stackOk hpre hF hN, r.rcAt hpre hF hN, hh, m1, w1, m2, w2, r.apart_off hpre ha hb hd,
    r.apart_off_below hpre hF.rsp ha hN, r.apart_off_below hpre hF.rsp hb hN, r.apart_rc hpre ha, ?_⟩
  apply r.gotAt hpre hF hN (by decide)
  intro l hl p hp
  have hl' : l ∈ ["memcpy", "memset"] := by
    simp only [List.mem_singleton] at hl
    simp [hl]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact r.got_apart_off hpre hl' ha
  · exact r.got_apart_off hpre hl' hb

/-- **`Hasher::update(a, d, n)`**'s precondition, the hasher at `a`, the data `d` an input apart
from the stack area. -/
theorem update_pre_input (hpre : r.Pre) {m : MachineData} (hF : r.CallFrame m) {a n : Nat}
    {d : BitVec 64} (h0 : RegIs m .rdi (r.off a)) (h1 : RegIs m .rsi d)
    (h2 : (reg m .rdx).toNat = n) (ha : a + 344 ≤ 2768) (hdm : Mapped m.dmem d n)
    (hdw : NoWrap d n) (hda : Apart d n (stackBelow r.m0 wotsLeafStack) (wotsLeafStack + 8))
    (hdf : Apart (r.off a) 344 d n) (hdgot : Apart (gotAddr "memcpy") 8 d n)
    (hh : ∃ x, Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) x) : UpdatePre m := by
  simp only [UpdatePre]
  rw [h2, show reg m .rdi = r.off a from h0, show reg m .rsi = d from h1]
  have hN : updateStack ≤ finalizeStack := by decide
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := a) (n := 344) (by omega)
  refine ⟨r.stackOk hpre hF hN, r.rcAt hpre hF hN, hh, m1, w1, hdm, hdw, hdf,
    r.apart_off_below hpre hF.rsp ha hN, r.apart_below hpre hF.rsp hN hda, r.apart_rc hpre ha, ?_⟩
  apply r.gotAt hpre hF hN (by decide)
  intro l hl p hp
  simp only [List.mem_singleton] at hl
  subst l
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact r.got_apart_off hpre (by simp) ha
  · exact hdgot

/-- **`Hasher::finalize(o, a)`**'s precondition, the hasher at `a`, the output at `o`. -/
theorem finalize_pre (hpre : r.Pre) {m : MachineData} (hF : r.CallFrame m) {o a : Nat}
    (h0 : RegIs m .rdi (r.off o)) (h1 : RegIs m .rsi (r.off a)) (ho : o + 32 ≤ 2768)
    (ha : a + 344 ≤ 2768) (hd : o + 32 ≤ a ∨ a + 344 ≤ o)
    (hh : ∃ x, Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) x) : FinalizePre m := by
  simp only [FinalizePre]
  rw [show reg m .rdi = r.off o from h0, show reg m .rsi = r.off a from h1]
  have hN : finalizeStack ≤ finalizeStack := le_rfl
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := a) (n := 344) (by omega)
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF (a := o) (n := 32) (by omega)
  refine ⟨r.stackOk hpre hF hN, r.rcAt hpre hF hN, hh, m1, w1, m2, w2, r.apart_off hpre ho ha hd,
    r.apart_off_below hpre hF.rsp ha hN, r.apart_off_below hpre hF.rsp ho hN, r.apart_rc hpre ho, ?_⟩
  apply r.gotAt hpre hF hN (by decide)
  intro l hl p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact r.got_apart_off hpre hl ho
  · exact r.got_apart_off hpre hl ha

/-- **`keccak_f(a)`**'s precondition. -/
theorem keccakF_pre (hpre : r.Pre) {m : MachineData} (hF : r.CallFrame m) {a : Nat}
    (h0 : RegIs m .rdi (r.off a)) (ha : a + 200 ≤ 2768) : KeccakFPre m := by
  simp only [KeccakFPre]
  rw [show reg m .rdi = r.off a from h0]
  have hN : keccakFStack ≤ finalizeStack := by decide
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := a) (n := 200) (by omega)
  exact ⟨r.stackOk hpre hF hN, r.rcAt hpre hF hN, m1, w1, r.apart_off_below hpre hF.rsp ha hN,
    r.apart_rc hpre ha⟩

/-! ## Postconditions -/

omit [Labels] in
/-- **After `memset(a, c, n)`**: the `n` bytes `c`, the rest kept. -/
theorem memset_out {m m' : MachineData} {a n : Nat} (h0 : RegIs m .rdi (r.off a))
    (h2 : (reg m .rdx).toNat = n) (h : MemsetPost m m') :
    BytesAt m'.dmem (r.off a) (List.replicate n (UInt8.ofNat (reg m .rsi).toNat)) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m a n 0) ∧ Saved m m' := by
  simp only [MemsetPost] at h
  rw [h2, show reg m .rdi = r.off a from h0] at h
  exact ⟨h.2.1, SameOutside.mono h.2.2.1 fun _ hp ↦ Or.inl hp, h.2.2.2⟩

omit [Labels] in
/-- **After `memcpy(a, b, n)`**: the `n` bytes from `b`, the rest kept. -/
theorem memcpy_out {m m' : MachineData} {a n : Nat} {b : BitVec 64} (h0 : RegIs m .rdi (r.off a))
    (h1 : RegIs m .rsi b) (h2 : (reg m .rdx).toNat = n) (h : MemcpyPost m m') :
    BytesAt m'.dmem (r.off a) (bytesOf m.dmem b n) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m a n 0) ∧ Saved m m' := by
  simp only [MemcpyPost] at h
  rw [h2, show reg m .rdi = r.off a from h0, show reg m .rsi = b from h1] at h
  exact ⟨h.2.1, SameOutside.mono h.2.2.1 fun _ hp ↦ Or.inl hp, h.2.2.2⟩

omit [Labels] in
/-- **After `Hasher::update(a, d, n)`**: the hasher has absorbed the `n` bytes from `d` too, the
rest kept. -/
theorem update_out {m m' : MachineData} {a n : Nat} {d : BitVec 64} (h0 : RegIs m .rdi (r.off a))
    (h1 : RegIs m .rsi d) (h2 : (reg m .rdx).toNat = n) (h : UpdatePost m m') :
    (∀ x, Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) x →
      Keccak.HasherHolds (bytesOf m'.dmem (r.off a) 344) (x ++ bytesOf m.dmem d n)) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m a 344 updateStack) ∧ Saved m m' := by
  simp only [UpdatePost] at h
  rw [h2, show reg m .rdi = r.off a from h0, show reg m .rsi = d from h1] at h
  exact ⟨h.2.1, SameOutside.mono h.2.2.1 fun p hp ↦ hp.imp id fun h ↦ by
    unfold InRange at *
    omega, h.2.2.2⟩

omit [Labels] in
/-- **After `Hasher::finalize(o, a)`**: the 32 bytes at `o` the hasher's digest, the rest kept. -/
theorem finalize_out {m m' : MachineData} {o a : Nat} (h0 : RegIs m .rdi (r.off o))
    (h1 : RegIs m .rsi (r.off a)) (h : FinalizePost m m') :
    BytesAt m'.dmem (r.off o) (Keccak.finalize (bytesOf m.dmem (r.off a) 344)) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m o 32 finalizeStack) ∧ Saved m m' := by
  simp only [FinalizePost] at h
  rw [show reg m .rdi = r.off o from h0, show reg m .rsi = r.off a from h1] at h
  exact ⟨h.1, SameOutside.mono h.2.1 fun p hp ↦ hp.imp id fun h ↦ by
    unfold InRange at *
    omega, h.2.2⟩

omit [Labels] in
/-- **After `keccak_f(a)`**: the 200 bytes at `a` permuted, the rest kept. -/
theorem keccakF_out {m m' : MachineData} {a : Nat} (h0 : RegIs m .rdi (r.off a))
    (h : KeccakFPost m m') :
    BytesAt m'.dmem (r.off a) (Keccak.keccakF (bytesOf m.dmem (r.off a) 200)) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m a 200 keccakFStack) ∧ Saved m m' := by
  simp only [KeccakFPost] at h
  rw [show reg m .rdi = r.off a from h0] at h
  exact ⟨h.1, SameOutside.mono h.2.1 fun p hp ↦ hp.imp id fun h ↦ by
    unfold InRange at *
    omega, h.2.2⟩

end Run

end

end NativeRustcX64.WotsLeafProof
