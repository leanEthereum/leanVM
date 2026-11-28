module

public import NativeRustcVmArm.Tables.TableWeights.Places

/-!
# `table_weights`: its inputs through the body

The inputs (the heights, the equality point, the point) are readable and apart from the stack
the function uses (`In`); in every state of the body their words are the entry's (`In.word`), they
are apart from the frame (`In.apart_frame`) and still mapped (`In.mapped`). The point's and the
equality point's coordinates as the entry's words (`ch_eq`, `E_getD`), the factor's limbs
(`fac_c0`, `fac_c1`).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm (wordOf ewOf ewsOf)

@[expose] public section

/-- An input of `len` bytes at `x`: readable, apart from the stack `table_weights` uses. -/
def In (m0 : MachineData) (x : BitVec 64) (len : Nat) : Prop :=
  Readable m0 x len ∧ OffStack m0 x len tableWeightsStack

end

public section

variable {m0 : MachineData}

theorem stackArea_eq : StackArea (fb m0) ewMulStack 240 =
    InRange (stackBelow m0 tableWeightsStack) tableWeightsStack := by
  rw [StackArea, fb_sub, show ewMulStack + 240 = tableWeightsStack by
    unfold tableWeightsStack; omega]

theorem In.not_stack {x : BitVec 64} {len : Nat} (h : In m0 x len)
    (hstk : StackOk m0 tableWeightsStack) {i : Nat} (hi : i < len) :
    ¬StackArea (fb m0) ewMulStack 240 (x + BitVec.ofNat 64 i) := by
  rw [stackArea_eq]
  refine NativeRustcVm.Apart.not_inRange_add h.2 h.1.2 ?_ hi
  have := hstk.2.1
  unfold NativeRustcVm.NoWrap stackBelow
  rw [NativeRustcVm.toNat_sub_ofNat (by rw [UInt64.toNat_toBitVec]; omega),
    UInt64.toNat_toBitVec]
  have := m0.regs.SP.toNat_lt
  omega

/-- **An input's word** in a state of the body: the entry's. -/
theorem In.word {x : BitVec 64} {len : Nat} (h : In m0 x len) (hstk : StackOk m0 tableWeightsStack)
    {m : MachineData} (hf : Frm m0 m) {o : Nat} (ho : o + 8 ≤ len) :
    wordOf m.dmem (x + BitVec.ofNat 64 o) = wordOf m0.dmem (x + BitVec.ofNat 64 o) :=
  NativeRustcVm.wordOf_congr fun i hi => hf.same _ (by
    rw [NativeRustcVm.addr_add_add]; exact h.not_stack hstk (by omega))

theorem In.mapped {x : BitVec 64} {len : Nat} (h : In m0 x len) {m : MachineData}
    (hf : Frm m0 m) : Mapped m.dmem x len := fun i hi => hf.kept _ (h.1.1 i hi)

/-- An input is apart from the frame. -/
theorem In.apart_frame {x : BitVec 64} {len : Nat} (h : In m0 x len)
    (hstk : StackOk m0 tableWeightsStack) : Apart (fb m0) 240 x len := by
  have h2 := h.2
  have := hstk.2.1
  unfold OffStack Apart stackBelow at h2
  unfold Apart
  have e1 : (m0.regs.SP.toBitVec - BitVec.ofNat 64 tableWeightsStack).toNat =
      m0.regs.SP.toNat - tableWeightsStack :=
    NativeRustcVm.toNat_sub_ofNat (by rw [UInt64.toNat_toBitVec]; omega)
  have e2 : (fb m0).toNat = m0.regs.SP.toNat - 240 := fb_toNat hstk
  rw [e1] at h2
  unfold tableWeightsStack at h2 this
  omega

/-- A sub-range of an input is an input. -/
theorem In.sub {x : BitVec 64} {len : Nat} (h : In m0 x len) {o l : Nat} (hl0 : 0 < l)
    (hl : o + l ≤ len) : In m0 (x + BitVec.ofNat 64 o) l := by
  refine ⟨⟨NativeRustcVm.Mapped.sub h.1.1 hl, NativeRustcVm.NoWrap.sub h.1.2 hl⟩, ?_⟩
  have h2 := h.2
  have hn : x.toNat + len ≤ 2 ^ 64 := h.1.2
  unfold OffStack Apart at h2 ⊢
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-! ## The coordinates -/

theorem slice_getD {m : MachineData} {a n : UInt64} {c : Nat} (hc : c < n.toNat) :
    (slice m a n).getD c 0 = ewOf m.dmem (a.toBitVec + BitVec.ofNat 64 (16 * c)) := by
  simp [slice, Array.getD, hc, ewsOf]

theorem ch_eq {c : Nat} (hc : c < n m0) :
    ch m0 c = ewOf m0.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 (16 * c)) :=
  slice_getD hc

theorem E_getD {c : Nat} (hc : c < m0.regs.X3.toNat) :
    (E m0).getD c 0 = ewOf m0.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 (16 * c)) :=
  slice_getD hc

theorem E_getD_none {c : Nat} (hc : ¬c < m0.regs.X3.toNat) : (E m0).getD c 0 = 0 := by
  simp [E, slice, Array.getD, hc]

theorem fac_c0 (c : Nat) :
    (fac m0 c).c0 ^^^ (ch m0 c).c0 = 1 ^^^ ((E m0).getD c 0).c0 := by
  show ((1 : UInt64) ^^^ ((E m0).getD c 0).c0) ^^^ (ch m0 c).c0 ^^^ (ch m0 c).c0 = _
  rw [UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero]

theorem fac_c1 (c : Nat) : (fac m0 c).c1 = ((E m0).getD c 0).c1 ^^^ (ch m0 c).c1 := by
  show ((0 : UInt64) ^^^ ((E m0).getD c 0).c1) ^^^ (ch m0 c).c1 = _
  rw [UInt64.zero_xor]

end

end NativeRustcVmArm.Tables.TableWeights
