module

public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontDefs
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontSums
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Arith

/-!
# `verify_layer`'s front: what stays as at the entry

In the front's frame (`FB`) the claim, the claim's bit weights in the scratch, `RMFE_PROJECT` and
`KECCAK_RC` keep their entry's bytes (`claimAt_fb`, `weightsAt_fb`, `proj_fb`, `rc_fb`). The
frame's words `b2` stores (`projWords`). A bit test as `tst` with `1 << c` (`tst_eq`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVm.Layout (Same)
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)

@[expose] public section

/-- `logSteps - 4`, the pack's bits, as `b0` computes it. -/
def packW (m0 : MachineData) : UInt64 := UInt64.ofNat (m0.regs.X1.toNat - 4)

/-- The frame's words `b0` and `b2` store: the step, the instance weights' entries, the scratch,
the layer's weights, the claim's instance weights, the local kernel's second entry, the pack's
bits, the `TState`, the claim. -/
def projWords (m0 : MachineData) : List (Nat × UInt64) :=
  [(128, m0.regs.X2), (144, UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 24)), (120, m0.regs.X4),
    (88, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 51200)),
    (80, UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 16)),
    (96, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107528)), (112, packW m0), (104, m0.regs.X0),
    (136, m0.regs.X3)]

end

public section

theorem projWords_le (m0 : MachineData) : ∀ p ∈ projWords m0, p.1 + 8 ≤ 152 := by
  intro p hp
  simp only [projWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem and_pow_eq_zero (n c : Nat) : n &&& 2 ^ c = 0 ↔ n.testBit c = false := by
  constructor
  · intro h
    have := congrArg (fun x ↦ x.testBit c) h
    simpa [Nat.testBit_and, Nat.testBit_two_pow] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : c = i
    · subst hi; simp [h]
    · simp [hi]

theorem lslv_one {x : BitVec 64} (hx : x.toNat < 64) :
    (BinOp.apply .lslv .W64 (BitVec.ofNat 64 1) x).toNat = 2 ^ x.toNat := by
  sym_simp
  rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hx]
  simp only [BitVec.toNat_ofNat, Nat.one_mod, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hx)

/-- **A bit test**: `tst w, 1 << c` clears Z iff bit `c` of `w` is set. -/
theorem tst_eq (w : UInt64) {c : Nat} (hc : c < 64) (x : BitVec 64) (hx : x.toNat = 2 ^ c) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 w.toBitVec x) (BitVec.ofNat 64 0) =
      !testBitW w c := by
  rw [eq_apply, NativeVm.Equiv.testBitW_eq w hc]
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_and, hx, BitVec.toNat_ofNat,
    Nat.zero_mod, UInt64.toNat_toBitVec]
  cases hb : w.toNat.testBit c
  · simp [(and_pow_eq_zero _ _).mpr hb]
  · have : ¬(w.toNat &&& 2 ^ c = 0) := fun h ↦ by rw [(and_pow_eq_zero _ _).mp h] at hb; cases hb
    simp [this]

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- The claim keeps its bytes in the front. -/
theorem claim_same (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) :
    Same m0.dmem m.dmem (cA m0) 768 := by
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0; have := g.hc; have := g.hcs; have := g.htc
  have := g.hcsc; have := g.ht; have := g.hs
  have hb3 : (base m0 3648).toNat = m0.regs.SP.toNat - 3648 := base_toNat (by omega)
  refine NativeRustcVm.Layout.Same.of_sameOutside hb.same fun j hj hq ↦ ?_
  have hj' : (cA m0).toNat + j < 2 ^ 64 := by omega
  rcases hq with hq | hq | hq
  · rw [stack_eq] at hq
    exact notIn (by rw [hb3]; omega) hj' (by rw [hb3]; omega) hq
  · exact notIn (by simp only [tstateBytes]; omega) hj' (by simp only [tstateBytes]; omega) hq
  · exact notIn (by rw [g.sa (by omega)]; omega) hj' (by rw [g.sa (by omega)]; omega) hq

/-- The claim's bit weights keep their bytes in the front. -/
theorem weights_same (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) :
    Same m0.dmem m.dmem (sA m0 + BitVec.ofNat 64 25600) 25600 := by
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0; have := g.hs; have := g.hss; have := g.htsc; have := g.ht
  have hb3 : (base m0 3648).toNat = m0.regs.SP.toNat - 3648 := base_toNat (by omega)
  have e := g.sa (o := 25600) (by omega)
  refine NativeRustcVm.Layout.Same.of_sameOutside hb.same fun j hj hq ↦ ?_
  have hj' : (sA m0 + BitVec.ofNat 64 25600).toNat + j < 2 ^ 64 := by rw [e]; omega
  rcases hq with hq | hq | hq
  · rw [stack_eq] at hq
    exact notIn (by rw [hb3]; omega) hj' (by rw [hb3, e]; omega) hq
  · exact notIn (by simp only [tstateBytes]; omega) hj' (by simp only [tstateBytes]; rw [e]; omega)
      hq
  · exact notIn (by rw [g.sa (by omega)]; omega) hj'
      (by rw [g.sa (o := 107520) (by omega)]; rw [e]; omega) hq

/-- **The claim** in the front. -/
theorem claimAt_fb (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) :
    ClaimAt m.dmem (cA m0) c := by
  have hs := claim_same h hb
  obtain ⟨h0, h1, h2⟩ := pre_claim h
  exact ⟨NativeRustcVm.Layout.EWAt.of_same h0 hs (by omega),
    NativeRustcVm.Layout.BufEWAt.of_same h1 (hs.sub (o := 16) (k := 264) (by omega)) (by decide),
    NativeRustcVm.Layout.BufEWAt.of_same h2 (hs.sub (o := 280) (k := 488) (by omega))
      (by decide)⟩

/-- **The claim's bit weights** in the front. -/
theorem weightsAt_fb (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) :
    WeightsAt m.dmem (sA m0 + BitVec.ofNat 64 25600) c :=
  ⟨(pre_w h).1, ewsAt_same (pre_w h).2 (weights_same h hb)
    (by rw [Array.length_toList, (pre_w h).1]; decide)⟩

/-- **`RMFE_PROJECT`** in the front. -/
theorem proj_fb (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) :
    NativeRustcVm.WordsAt m.dmem projectAddr rmfeProjectW.toList :=
  NativeRustcVm.Layout.BytesAt.of_same (pre_proj h) (same_rs h (FB.body h hb) (r := projectRegion)
    (by simp))
    (by rw [NativeRustcVm.length_wordsBytes, Array.length_toList, rmfeProjectW_size]
        exact Nat.le_refl _)

/-- **`KECCAK_RC`** in the front. -/
theorem rc_fb (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) :
    NativeRustcVm.WordsAt m.dmem rcAddr LeanVM.Parameters.keccakRC :=
  NativeRustcVm.Layout.BytesAt.of_same (pre_rc h).1 (same_rs h (FB.body h hb) (r := rcRegion)
    (by simp))
    (by rw [NativeRustcVm.length_wordsBytes]; exact Nat.le_refl _)

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
