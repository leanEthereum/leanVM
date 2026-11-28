module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Spec.Top

/-!
# Helpers of the x86-64 proofs of `verify.rs` and `leanvm_verify`

Addresses as numbers: an interval is its addresses' numbers (`inR`); a call whose changes are all
below an offset `L` of the frame, under its slots, or above the frame keeps the frame
(`Frame.call_low`); a callee's stack below the frame as numbers (`callee_nat`); bytes kept at
offsets no change touches (`keep_off`). `Disjoint` of two regions (`apart_of_pair`). A `bool` in
AL: `test %al, %al` (`testAl_okAl`), `sete %al` (`sete_okAl`).
-/

namespace NativeRustcVmX64.Top

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript

public section

theorem inR {a q : BitVec 64} {n : Nat} (h : NativeRustcVm.NoWrap a n) :
    NativeRustcVm.InRange a n q ↔ a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + n :=
  inRange_iff' h

theorem apart_of_pair {r r' : NativeRustcVm.Region} (h : NativeRustcVm.Disjoint [r, r']) :
    NativeRustcVm.Apart r.addr r.size r'.addr r'.size := by
  unfold NativeRustcVm.Disjoint at h
  exact (List.pairwise_pair (R := fun r r' : NativeRustcVm.Region ↦
    NativeRustcVm.Apart r.addr r.size r'.addr r'.size)).mp h

/-- Bytes at offsets of `b` that no change touches are kept. -/
theorem keep_off {d d' : DataMem} {b : BitVec 64} {o : Nat} {bs : List UInt8}
    {R : BitVec 64 → Prop} (h : NativeRustcVm.BytesAt d (off b o) bs)
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ j, o ≤ j → j < o + bs.length → ¬ R (off b j)) :
    NativeRustcVm.BytesAt d' (off b o) bs :=
  h.of_sameOutside hs fun i hi ↦ by rw [off_add]; exact hR _ (by omega) (by omega)

/-- An offset of an area no change at offsets `W` touches. -/
theorem not_touch {b : BitVec 64} {N j : Nat} {W : Nat → Prop} (hN : NativeRustcVm.NoWrap b N)
    (hj : j < N) (hW : ¬ W j) : ¬ Touch b N W (off b j) := by
  rintro ⟨j', hj', hW', he⟩
  exact hW (by rw [off_inj hN hj' hj he]; exact hW')

theorem inAny2 {r₁ r₂ : NativeRustcVm.Region} {q : BitVec 64}
    (h : NativeRustcVm.InAny [r₁, r₂] q) : r₁.Holds q ∨ r₂.Holds q := by
  obtain ⟨r, hr, h⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

theorem inAny3 {r₁ r₂ r₃ : NativeRustcVm.Region} {q : BitVec 64}
    (h : NativeRustcVm.InAny [r₁, r₂, r₃] q) : r₁.Holds q ∨ r₂.Holds q ∨ r₃.Holds q := by
  obtain ⟨r, hr, h⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

variable {m0 d d' : MachineData} {F : Nat}

/-- The callee's stack below the frame, as numbers. -/
theorem callee_nat (hsp : rspOf d = stackBelow m0 F) {n' : Nat}
    (hn : F + n' ≤ (rspOf m0).toNat) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow d n') n' q) :
    (rspOf m0).toNat - F - n' ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - F := by
  rw [stackBelow_callee hsp hn] at h
  have h1 := stackBelow_toNat (m := m0) (n := F + n') hn
  rw [inR (by unfold NativeRustcVm.NoWrap; rw [h1]; have := (rspOf m0).isLt; omega), h1] at h
  omega

/-- **A call** keeps the frame where the callee changes only bytes below offset `L` of the frame,
`L` under every slot, or above the frame. -/
theorem Frame.call_low {slots : Slots} {L : Nat} (hf : Frame m0 F slots 0 d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → q.toNat < (stackBelow m0 F).toNat + L ∨
      (stackBelow m0 F).toNat + (F + 8) ≤ q.toNat) (hL : ∀ p ∈ slots, L ≤ p.1)
    (hLF : L ≤ F) (hnw : NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8))
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Frame m0 F slots 8 d' := by
  unfold NativeRustcVm.NoWrap at hnw
  refine Frame.call_slots hf hs hrsp hso (fun p hp i hi h ↦ ?_) (fun j hj h ↦ ?_)
  · have h1 := hR _ h
    have := hL p hp
    have := hle p hp
    rw [toNat_off (by omega)] at h1
    omega
  · have h1 := hR _ h
    rw [toNat_off (by omega)] at h1
    omega

/-- **A call at offset `o`** of the frame keeps it where the callee changes only bytes below
offset `L`, `L` under every slot, or above the frame. -/
theorem Frame.call_low_at {slots : Slots} {L o : Nat} (hf : Frame m0 F slots o d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → q.toNat < (stackBelow m0 F).toNat + L ∨
      (stackBelow m0 F).toNat + (F + 8) ≤ q.toNat) (hL : ∀ p ∈ slots, L ≤ p.1)
    (hLF : L ≤ F) (hnw : NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8))
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Frame m0 F slots (o + 8) d' := by
  unfold NativeRustcVm.NoWrap at hnw
  refine ⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hs.2, fun r hr hsl ↦ ?_⟩
  · rw [hrsp, hf.sp, off_add]
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    refine hso _ fun h ↦ ?_
    have h1 := hR _ h
    have := hL p hp
    have := hle p hp
    rw [toNat_off (by omega)] at h1
    omega
  · rw [hso _ fun h ↦ by
      have h1 := hR _ h
      rw [toNat_off (by omega)] at h1
      omega]
    exact hf.ret j hj
  · exact (hs.1 r hr).trans (hf.regs r hr hsl)

theorem testAl_eq (x : BitVec 64) :
    (CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x x) (BitVec.ofNat 64 0)) =
      decide (x.toNat % 256 = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low_ext, BitVec.and_self]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp [low, BitVec.toNat_setWidth]

/-- `test %al, %al` of a `bool` in AL: zero exactly on `false`. -/
theorem testAl_okAl {m : MachineData} {b : Bool} (h : OkAl m b) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg m .rax) (reg m .rax)) (BitVec.ofNat 64 0) =
      !b := by
  rw [testAl_eq]
  unfold OkAl boolRet at h
  rw [h]
  cases b <;> rfl

/-- `sete %al`: AL the comparison's `bool`. -/
theorem sete_okAl (x : BitVec 64) (c : Bool) :
    (BinOp.apply .merge .W8 x (if c then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)).toNat % 256 =
      (okWord c).toNat := by
  have h := congrArg BitVec.toNat
    (low8_replaceLow x (low .W8 (if c then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)))
  rw [toNat_low, toNat_low] at h
  rw [BinOp.apply, show (256 : Nat) = 2 ^ Width.W8.bits from rfl, h]
  cases c <;> rfl

variable [Labels] in
/-- The read-only data kept where memory changed apart from it, apart from a stack range inside
the first. -/
theorem rodataAt_keep {m d : MachineData} {n n' : Nat} {R : BitVec 64 → Prop} (h : RodataAt m n)
    (hs : NativeRustcVm.SameOutside m.dmem d.dmem R)
    (hR : ∀ p, R p → ∀ t : NativeRustcVm.Data.Item,
      ¬ NativeRustcVm.InRange (rodataAddr t) t.bytes.length p)
    (h1 : (stackBelow m n).toNat ≤ (stackBelow d n').toNat)
    (h2 : (stackBelow d n').toNat + (n' + 8) ≤ (stackBelow m n).toNat + (n + 8)) : RodataAt d n' :=
  fun t ↦ ⟨(h.bytesAt t).of_sameOutside hs fun i hi hp ↦ hR _ hp t
      (inRange_off_self hi (by have := h.noWrap t; unfold NativeRustcVm.NoWrap at this; omega)),
    h.noWrap t, NativeRustcVm.Apart.mono_right (h.apart t) h1 h2⟩

end

end NativeRustcVmX64.Top
