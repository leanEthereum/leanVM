module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Ring.Seq
public import NativeRustcVmX64.Spec.Ring
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# Memory changed only in the stack (x86-64)

A function whose blocks and callees change only its stack (`stackBelow m0 S`, `S` bytes) reads its
arguments' bytes as at the entry (`get_keep`, `slice_keep`, `arr_keep`). The changes of a block in
its frame (`frame_in`), of a callee in the stack below the frame (`callee_in`) are in that stack;
the frame's bytes from an offset are not in a callee's stack (`not_callee`). The argument words on
the stack (`stackArg`) above the return address (`args_toNat`, `args_apart`).
-/

namespace NativeRustcVmX64.Ring

open NativeRustcX64 NativeRustcVmX64.Transcript NativeRustcVm.Transcript

public section

variable {m0 d : MachineData} {S : Nat}

theorem inRange_le {a q : BitVec 64} {n n' : Nat} (h : NativeRustcVm.InRange a n q) (hn : n ≤ n') :
    NativeRustcVm.InRange a n' q := by
  unfold NativeRustcVm.InRange at h ⊢
  omega

/-- **Bytes apart from the stack** are the entry's in a state that changed only the stack. -/
theorem get_keep (hst : StackOk m0 S)
    (hs : SameOutside m0.dmem d.dmem (InRange (stackBelow m0 S) S)) {a : BitVec 64} {n : Nat}
    (ha : Apart a n (stackBelow m0 S) (S + 8)) (hw : NoWrap a n) {i : Nat} (hi : i < n) :
    d.dmem.get? (a + BitVec.ofNat 64 i) = m0.dmem.get? (a + BitVec.ofNat 64 i) :=
  hs _ fun h ↦ NativeRustcVm.Apart.not_inRange_add ha hw (noWrap_stackBelow hst) hi
    (inRange_le h (by omega))

/-- A slice apart from the stack reads as at the entry. -/
theorem slice_keep (hst : StackOk m0 S)
    (hs : SameOutside m0.dmem d.dmem (InRange (stackBelow m0 S) S)) {a n : BitVec 64}
    (h : SliceOk m0 a n S) : slice d a n = slice m0 a n := by
  unfold slice
  rw [NativeRustcVm.ewsOf_congr fun i hi ↦ get_keep hst hs h.2 h.1.2 hi]

/-- An array apart from the stack reads as at the entry. -/
theorem arr_keep (hst : StackOk m0 S)
    (hs : SameOutside m0.dmem d.dmem (InRange (stackBelow m0 S) S)) {a : BitVec 64} {n : Nat}
    (h : ArrOk m0 a n S) : arr d a n = arr m0 a n := by
  unfold arr
  rw [NativeRustcVm.ewsOf_congr fun i hi ↦ get_keep hst hs h.2 h.1.2 hi]

/-- Bytes of the frame (its first `F` bytes) are in the stack. -/
theorem frame_in (hst : StackOk m0 S) {F : Nat} (hF : F ≤ S) {q : BitVec 64}
    (h : InRange (stackBelow m0 F) F q) : InRange (stackBelow m0 S) S q :=
  inRange_frame_stack hst.2.1 hst.1 hF h

/-- A callee's stack below the frame is in the stack. -/
theorem callee_in (hst : StackOk m0 S) {F n' : Nat} (hsp : rspOf d = stackBelow m0 F)
    (hn : F + n' ≤ S) {q : BitVec 64} (h : InRange (stackBelow d n') n' q) :
    InRange (stackBelow m0 S) S q :=
  (inRange_callee hsp hst.2.1 hst.1 hn h).1

/-- The frame's bytes are not in a callee's stack below it. -/
theorem not_callee (hst : StackOk m0 S) {F n' j : Nat} (hsp : rspOf d = stackBelow m0 F)
    (hn : F + n' ≤ S) (hj : j < F + 8) :
    ¬InRange (stackBelow d n') n' (off (stackBelow m0 F) j) := fun h ↦
  (inRange_callee hsp hst.2.1 hst.1 hn h).2
    (inRange_off_self hj (by have := hst.1; have := hst.2.1; omega))

/-- Changes in the frame or a callee's stack are in the stack. -/
theorem same_trans {d₁ d₂ : MachineData} {R : BitVec 64 → Prop}
    (h₁ : SameOutside m0.dmem d₁.dmem (InRange (stackBelow m0 S) S))
    (h₂ : SameOutside d₁.dmem d₂.dmem R) (hR : ∀ q, R q → InRange (stackBelow m0 S) S q) :
    SameOutside m0.dmem d₂.dmem (InRange (stackBelow m0 S) S) :=
  fun q hq ↦ (h₂ q fun h ↦ hq (hR q h)).trans (h₁ q hq)

/-- The argument words' address. -/
theorem args_toNat {k : Nat} (h : ArgsOk m0 k) (hk : 0 < k) :
    (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
  rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl]
  have := h.2
  omega

/-- The argument words are readable. -/
theorem args_readable {k : Nat} (h : ArgsOk m0 k) (hk : 0 < k) :
    Mapped m0.dmem (rspOf m0 + 8#64) (8 * k) ∧ NoWrap (rspOf m0 + 8#64) (8 * k) := by
  refine ⟨h.1, ?_⟩
  unfold NoWrap
  rw [args_toNat h hk]
  have := h.2
  omega

/-- The argument words are above the frame and the return address. -/
theorem args_apart {k F : Nat} (hst : StackOk m0 S) (h : ArgsOk m0 k) (hk : 0 < k) (hF : F ≤ S) :
    Apart (stackBelow m0 F) (F + 8) (rspOf m0 + 8#64) (8 * k) := by
  unfold Apart
  rw [args_toNat h hk, stackBelow_toNat (by have := hst.1; omega)]
  have := hst.1
  omega

/-- Argument word `i`, loaded from the arguments' region. -/
theorem stackArg_eq (i : Nat) :
    stackArg m0 i =
      (NativeRustcVm.wordOf m0.dmem (rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i))).toBitVec := by
  unfold stackArg
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- **Argument word `i`** loaded from the arguments' region (region `1` of `env`) in a state that
changed only the stack. -/
theorem argWord (hst : StackOk m0 S) {k : Nat} (hargs : ArgsOk m0 k) (hk : 0 < k)
    (hs : SameOutside m0.dmem d.dmem (InRange (stackBelow m0 S) S)) {env : Sym.Env}
    (hb : env.base 1 = rspOf m0 + 8#64) (hm : env.mem0 = d.dmem) {i : Nat} (hi : i < k) :
    env.load 1 (8 * i) 8 = stackArg m0 i := by
  rw [load_eq_wordOf, stackArg_eq, hb, hm]
  refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
  rw [NativeRustcVm.addr_add]
  have hx := args_toNat hargs hk
  have ha : Apart (rspOf m0 + 8#64) (8 * k) (stackBelow m0 S) (S + 8) := by
    unfold Apart
    have := hst.1
    rw [hx, stackBelow_toNat hst.1]
    omega
  exact get_keep hst hs ha (args_readable hargs hk).2 (by omega)

/-- **The rest of a range from offset `o`**: mapped, not wrapping, apart from what the range is
apart from. -/
theorem range_rest {dm : DataMem} {a b : BitVec 64} {N M o : Nat} (hm : Mapped dm a N)
    (hw : NoWrap a N) (hap : Apart a N b M) (ho : o ≤ N) :
    Mapped dm (a + BitVec.ofNat 64 o) (N - o) ∧ NoWrap (a + BitVec.ofNat 64 o) (N - o) ∧
      Apart (a + BitVec.ofNat 64 o) (N - o) b M := by
  unfold NoWrap at hw
  unfold Apart at hap
  refine ⟨fun j hj ↦ by rw [NativeRustcVm.addr_add]; exact hm _ (by omega), ?_⟩
  unfold NoWrap Apart
  rcases NativeRustcVm.toNat_add_ofNat_le (a := a) (i := o) (by omega) with h | ⟨h, h'⟩
  · rw [h]; omega
  · rw [h]; omega

end

end NativeRustcVmX64.Ring
