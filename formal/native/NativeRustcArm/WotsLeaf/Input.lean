module

public import NativeRustcArm.WotsLeaf.Steps

/-!
# The inputs

`wots_leaf`'s inputs (the public parameter, the message, the randomizer, the chain values) and
its output are apart from the stack area (`WotsLeafPre.Input`): in any state of the frame they
hold their bytes at entry (`Run.input_bytes`) and are apart from the frame's bytes
(`Run.apart_input`) and from a callee's stack. `Hasher::update` of an input (`updateInput`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustcArm.Sym

public section

namespace Run

variable (r : Run) [Labels]

theorem pre_out (hpre : r.Pre) : WotsLeafPre.Input r.m0 r.out 75 := hpre.2.2.1
theorem pre_pp (hpre : r.Pre) : WotsLeafPre.Input r.m0 r.m0.regs.X1.toBitVec 16 := hpre.2.2.2.1
theorem pre_msg (hpre : r.Pre) :
    WotsLeafPre.Input r.m0 r.m0.regs.X4.toBitVec r.m0.regs.X5.toNat := hpre.2.2.2.2.1
theorem pre_rnd (hpre : r.Pre) : WotsLeafPre.Input r.m0 r.m0.regs.X6.toBitVec 16 :=
  hpre.2.2.2.2.2.1
theorem pre_values (hpre : r.Pre) : WotsLeafPre.Input r.m0 r.m0.regs.X7.toBitVec (16 * 58) :=
  hpre.2.2.2.2.2.2

omit [Labels] in
/-- A part of an input is an input. -/
theorem Input.sub {b : BitVec 64} {n : Nat} (h : WotsLeafPre.Input r.m0 b n) {o n' : Nat}
    (ho : o + n' ≤ n) (hn : o < n) : WotsLeafPre.Input r.m0 (b + BitVec.ofNat 64 o) n' := by
  obtain ⟨hm, hw, ha⟩ := h
  unfold NoWrap Apart at *
  have hb : (b + BitVec.ofNat 64 o).toNat = b.toNat + o := Sym.toNat_add_ofNat _ _ (by omega)
  refine ⟨fun i hi ↦ ?_, by unfold NoWrap; rw [hb]; omega, by unfold Apart; rw [hb]; omega⟩
  rw [addr_add_add]
  exact hm _ (by omega)

/-- **An input's bytes** in any state of the frame are its bytes at entry. -/
theorem input_bytes (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {b : BitVec 64} {n : Nat}
    (h : WotsLeafPre.Input r.m0 b n) : BytesAt m.dmem b (bytesOf r.m0.dmem b n) := by
  obtain ⟨hm, hw, ha⟩ := h
  have hl := length_bytesOf r.m0.dmem b n
  exact r.bytesAt_entry hpre hF (bytesAt_bytesOf hm) (by rw [hl]; exact ha) (by rw [hl]; exact hw)

omit [Labels] in
/-- An input is mapped in any state keeping the entry's mapped bytes. -/
theorem input_mapped {m : MachineData} (hk : Kept r.m0.dmem m.dmem) {b : BitVec 64} {n : Nat}
    (h : WotsLeafPre.Input r.m0 b n) : Mapped m.dmem b n := fun i hi ↦ hk _ (h.1 i hi)

/-- An input is apart from the frame's bytes. -/
theorem apart_input (hpre : r.Pre) {a n' : Nat} (ha : a + n' ≤ 2752) {b : BitVec 64} {n : Nat}
    (h : WotsLeafPre.Input r.m0 b n) : Apart (r.off a) n' b n := by
  have := r.below_toNat hpre
  have := r.off_toNat hpre (a := a) (by omega)
  have h3 := h.2.2
  unfold Apart at *
  simp only [wotsLeafStack_eq'] at *
  omega

/-- An input is apart from a callee's stack. -/
theorem input_apart_below (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {N : Nat}
    (hN : N ≤ finalizeStack) {b : BitVec 64} {n : Nat} (h : WotsLeafPre.Input r.m0 b n) :
    Apart b n (stackBelow m N) N :=
  r.apart_below hpre hF hN h.2.2

end Run

variable {r : Run} [Labels]

/-- **`Hasher::update(a, b, n)`** of an input `b`, the hasher at the frame's `a` having absorbed
`x`: the input's bytes at entry absorbed. -/
theorem updateInput (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : Keep r L m₁)
    {a n : Nat} {b : BitVec 64} (h0 : Run.RegIs m₁ .X0 (r.off a)) (h1 : Run.RegIs m₁ .X1 b)
    (h2 : m₁.regs.X2.toNat = n) (hin : WotsLeafPre.Input r.m0 b n) (ha : a + 344 ≤ 2656)
    (hL : slotsOff L a 344 = true) {x : List UInt8} (hH : HasherAt r m₁ a x) :
    UpdatePre m₁ ∧ ∀ m₂, UpdatePost m₁ m₂ → Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a 344 ∧
      HasherAt r m₂ a (x ++ bytesOf r.m0.dmem b n) := by
  have hF := hK.1
  have hN : updateStack ≤ finalizeStack := by decide
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := a) (n := 344) (by omega)
  refine ⟨?_, fun m₂ hQ ↦ ?_⟩
  · simp only [UpdatePre]
    rw [h2, ← getXReg_X0 m₁, h0, ← getXReg_X1 m₁, h1]
    exact ⟨r.stackOk hpre hF hN, r.rcAt hpre hF hN, hH.holds_some, m1, w1,
      r.input_mapped hF.2.2.2.2 hin, hin.2.1, r.apart_input hpre (by omega) hin,
      r.apart_off_below hpre hF (by omega) hN, r.input_apart_below hpre hF hN hin,
      r.apart_rc hpre (by omega)⟩
  · have hU := hQ
    simp only [UpdatePost] at hU
    rw [h2, ← getXReg_X0 m₁, h0, ← getXReg_X1 m₁, h1] at hU
    obtain ⟨-, hA, hout, hS⟩ := hU
    have hF₂ := r.frame_of_call hpre hF hS (a := a) (n := 344) (N := updateStack) (by omega) hN hout
    have hA' := hA x hH.holds
    have he : bytesOf m₁.dmem b n = bytesOf r.m0.dmem b n := by
      have := bytesOf_of_bytesAt (r.input_bytes hpre hF hin)
      rwa [length_bytesOf] at this
    rw [he] at hA'
    exact ⟨hK.of_call hpre hS ha hN hout hL, hS, kc_of_call hpre hF (by omega) hN hout,
      ⟨_, bytesAt_bytesOf (r.frame_mapped hpre hF₂ (by omega)).1, hA'⟩⟩

end

end NativeRustcArm.WotsLeafProof
