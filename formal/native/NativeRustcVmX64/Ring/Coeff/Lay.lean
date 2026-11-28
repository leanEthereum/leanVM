module

public import NativeRustcVmX64.Ring.Coeff.Basic

/-!
# `ring_coefficients`: the entry's facts and each turn's layout (x86-64)

`P`: the entry's facts. `Mem m0 m`: a state whose memory is the entry's but in the stack and
`out`. In such a state, turn `p`'s layout holds (`lay`: the frame below the entry's RSP, the row of
`out` and `f_p`), and `f`'s words are the entry's (`fword`).
-/

namespace NativeRustcVmX64.Ring.Coeff

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Field (Geo inRange_N stackBelow_toNat')

@[expose] public section

/-- The stack `ring_coefficients` uses. -/
abbrev NC : Nat := ringCoefficientsStack

/-- Memory as the entry's but in the stack and `out`. -/
structure Mem (m0 m : MachineData) : Prop where
  same : SameOutside m0.dmem m.dmem (fun q ↦ InRange (stackBelow m0 NC) NC q ∨
    InRange (oA m0) 1024 q)
  kept : Kept m0.dmem m.dmem

end

public section

variable {m0 : MachineData}

theorem nc_eq : NC = 336 := rfl

/-- The entry's facts, unpacked. -/
structure P (m0 : MachineData) : Prop where
  st : StackOk m0 NC
  fm : Mapped m0.dmem (fA m0) 128
  fw : NoWrap (fA m0) 128
  fs : Apart (fA m0) 128 (stackBelow m0 NC) (NC + 8)
  gm : Mapped m0.dmem (gA m0) 128
  gw : NoWrap (gA m0) 128
  gs : Apart (gA m0) 128 (stackBelow m0 NC) (NC + 8)
  om : Mapped m0.dmem (oA m0) 1024
  ow : NoWrap (oA m0) 1024
  os : Apart (oA m0) 1024 (stackBelow m0 NC) (NC + 8)
  of : Apart (oA m0) 1024 (fA m0) 128
  og : Apart (oA m0) 1024 (gA m0) 128

theorem P.intro (h : RingCoefficientsPre m0) : P m0 :=
  ⟨h.1, h.2.1.1.1, h.2.1.1.2, h.2.1.2, h.2.2.1.1.1, h.2.2.1.1.2, h.2.2.1.2, h.2.2.2.1.1.1,
    h.2.2.2.1.1.2, h.2.2.2.1.2, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem P.sN (h : P m0) : NC ≤ (rspOf m0).toNat := h.st.1

theorem P.below (h : P m0) : (stackBelow m0 NC).toNat = (rspOf m0).toNat - NC :=
  stackBelow_toNat' h.sN

theorem Mem.refl : Mem m0 m0 := ⟨fun _ _ ↦ rfl, fun _ h ↦ h⟩

/-- A byte of `f` is outside the stack and `out`. -/
theorem P.f_out (h : P m0) {i : Nat} (hi : i < 128) :
    ¬(InRange (stackBelow m0 NC) NC (fA m0 + BitVec.ofNat 64 i) ∨
      InRange (oA m0) 1024 (fA m0 + BitVec.ofNat 64 i)) := by
  have hfw := h.fw
  have hfs := h.fs
  have hof := h.of
  have how := h.ow
  have hb := h.below
  have hsN := h.sN
  have ht := h.st.2.1
  unfold NoWrap at hfw how
  unfold Apart at hfs hof
  have hq : (fA m0 + BitVec.ofNat 64 i).toNat = (fA m0).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  rintro (h1 | h1)
  · rw [Sym.inRange_iff (by rw [hb]; omega), hq, hb] at h1
    rw [hb] at hfs
    omega
  · rw [Sym.inRange_iff (by omega), hq] at h1
    omega

/-- **`f`'s words** in a state of `Mem`. -/
theorem fword (h : P m0) {m : MachineData} (hM : Mem m0 m) {o : Nat} (ho : o + 8 ≤ 128) :
    NativeRustcVm.wordOf m.dmem (fA m0 + BitVec.ofNat 64 o) =
      NativeRustcVm.wordOf m0.dmem (fA m0 + BitVec.ofNat 64 o) :=
  NativeRustcVm.wordOf_congr fun i hi ↦ by
    rw [addr_add]
    exact hM.same _ (h.f_out (by omega))

theorem fE_c0 (p : Nat) :
    c0 (fE m0 p) = (NativeRustcVm.wordOf m0.dmem (fA m0 + BitVec.ofNat 64 (16 * p))).toBitVec :=
  rfl

theorem fE_c1 (p : Nat) :
    c1 (fE m0 p) =
      (NativeRustcVm.wordOf m0.dmem (fA m0 + BitVec.ofNat 64 (16 * p + 8))).toBitVec := by
  rw [← addr_add]
  rfl

/-- The stack of the entry, for its own registers over a state's memory. -/
theorem own_stackOk (h : P m0) {m : MachineData} (hM : Mem m0 m) : StackOk (own m0 m) NC :=
  ⟨h.st.1, h.st.2.1, fun i hi ↦ hM.kept _ (h.st.2.2 i hi)⟩

/-- **Turn `p`'s layout.** -/
theorem lay (h : P m0) {m : MachineData} (hM : Mem m0 m) {p : Nat} (hp : p < 8) :
    Lay (own m0 m) 176 NC (rsP m0 p) := by
  have hfw := h.fw
  have hfs := h.fs
  have hof := h.of
  have hos := h.os
  have how := h.ow
  unfold NoWrap at hfw how
  unfold Apart at hfs hof hos
  have hr : (oA m0 + BitVec.ofNat 64 (128 * p)).toNat = (oA m0).toNat + 128 * p :=
    toNat_add_ofNat _ _ (by omega)
  have hf : (fA m0 + BitVec.ofNat 64 (16 * p)).toNat = (fA m0).toNat + 16 * p :=
    toNat_add_ofNat _ _ (by omega)
  have hsb : stackBelow (own m0 m) NC = stackBelow m0 NC := rfl
  refine ⟨own_stackOk h hM, by decide, by decide, ⟨⟨fun i hi ↦ ?_, ?_, ?_⟩, ⟨fun i hi ↦ ?_, ?_, ?_⟩,
    trivial⟩, List.pairwise_pair.mpr ?_⟩
  · rw [addr_add]
    exact hM.kept _ (h.om _ (by omega))
  · unfold NoWrap; rw [hr]; omega
  · rw [hsb]; unfold Apart; rw [hr]; omega
  · rw [addr_add]
    exact hM.kept _ (h.fm _ (by omega))
  · unfold NoWrap; rw [hf]; omega
  · rw [hsb]; unfold Apart; rw [hf]; omega
  · unfold Apart; rw [hr, hf]; omega

end

end NativeRustcVmX64.Ring.Coeff
