module

public import NativeRustcVmArm.KeccakGkr.SlotWeights.Defs

/-!
# `slot_weights`: the first segment's loop

`.LSlotWeights_5` (`b6`) to `.LSlotWeights_4` (`b5`): for each bit `j`, row `25 first + j / 64`
(X23, below `64`), the product of segment `first`'s kernel entry (X24, X25) and bit weight `j`
(X28 - 8) by `EW::mul` (`b7`), stored at flat index `1600 first + j` (`b8`); X26 counts `j`, X29
the bytes left (`SegA`, `segA_step`, `segA_loop`).
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.SlotWeights NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

@[expose] public section

/-- The frame's locals the loops read: the count at `8`, the segment kernel's first two entries at
`16` and `32`. -/
structure Loc (m0 : MachineData) (c : KeccakClaimW) (st : MachineData) : Prop where
  cnt : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X5
  s0 : NativeRustcVm.EWAt st.dmem (fbA m0 + BitVec.ofNat 64 16) ((segK m0.regs.X0.toNat c).getD 0 0)
  s1 : NativeRustcVm.EWAt st.dmem (fbA m0 + BitVec.ofNat 64 32) ((segK m0.regs.X0.toNat c).getD 1 0)

/-- The registers both loops keep. -/
structure Keep (m0 st : MachineData) : Prop where
  x19 : st.regs.X19 = m0.regs.X6
  x20 : st.regs.X20 = 1
  x21 : st.regs.X21 = m0.regs.X3
  x22 : st.regs.X22 = m0.regs.X4

/-- **The first segment's loop head** at bit `j`. -/
structure SegA [Labels] (m0 : MachineData) (c : KeccakClaimW) (j : Nat) (st : MachineData) :
    Prop where
  body : Body m0 st
  keep : Keep m0 st
  loc : Loc m0 c st
  j_lt : j < 1600
  x24 : st.regs.X24 = ((segK m0.regs.X0.toNat c).getD 0 0).c0
  x25 : st.regs.X25 = ((segK m0.regs.X0.toNat c).getD 0 0).c1
  x26 : st.regs.X26.toNat = j
  x27 : st.regs.X27.toNat = 25 * m0.regs.X4.toNat
  x28 : st.regs.X28.toBitVec = wA m0 + BitVec.ofNat 64 (8 + 16 * j)
  x29 : st.regs.X29.toNat = 25600 - 16 * j
  rows : ElemsAt st.dmem (rowsA m0)
    (prog m0.regs.X0.toNat c m0.regs.X4.toNat (1600 * m0.regs.X4.toNat + j)) 4096

/-- **A segment's loop done**: the products up to flat index `b`. -/
structure SegDone [Labels] (m0 : MachineData) (c : KeccakClaimW) (b : Nat) (st : MachineData) :
    Prop where
  body : Body m0 st
  keep : Keep m0 st
  loc : Loc m0 c st
  rows : ElemsAt st.dmem (rowsA m0) (prog m0.regs.X0.toNat c m0.regs.X4.toNat b) 4096

end

public section

variable {c : KeccakClaimW} {m0 st st' : MachineData}

theorem pre_areas (hpre : SlotWeightsPre c m0) :
    Areas m0 slotWeightsStack [⟨rowsA m0, rowsBytes⟩]
      [ewsRegion m0.regs.X1.toBitVec c.point.size, ⟨wA m0, weightsBytes⟩] :=
  hpre.2.2.2.2.2.2.2

theorem wsOff (hpre : SlotWeightsPre c m0) :
    WsOff m0 slotWeightsStack [⟨rowsA m0, rowsBytes⟩] :=
  wsOff_of_areas (pre_areas hpre) hpre.1

theorem first_le (hpre : SlotWeightsPre c m0) : m0.regs.X4.toNat ≤ 1 := by
  have h1 : 1 ≤ m0.regs.X5.toNat := hpre.2.2.2.2.2.1
  have h2 : m0.regs.X4.toNat + m0.regs.X5.toNat ≤ 2 := hpre.2.2.2.2.2.2.1
  omega

/-- **A bit weight**, in a body. -/
theorem w_at (hpre : SlotWeightsPre c m0) (hb : Body m0 st) {j : Nat} (hj : j < 1600) :
    NativeRustcVm.EWAt st.dmem (wA m0 + BitVec.ofNat 64 (16 * j)) (c.weights.getD j 0) := by
  obtain ⟨hsz, hw⟩ := hpre.2.2.2.1
  have hj' : j < c.weights.toList.length := by
    rw [Array.length_toList, hsz]; exact hj
  have h := NativeRustcVm.EWsAt.getElem hw hj'
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hj',
    Option.getD_some]
  exact hb.bytesAt (pre_areas hpre) hpre.1 (r := ⟨wA m0, weightsBytes⟩) (by simp)
    (by rw [NativeRustcVm.length_ewBytes]; show 16 * j + 16 ≤ 25600; omega) h

/-- The rows' region is data memory and does not wrap. -/
theorem rows_ok (hpre : SlotWeightsPre c m0) : Region.Ok m0.dmem ⟨rowsA m0, rowsBytes⟩ :=
  Areas.ok (pre_areas hpre) (Or.inl (by simp))

/-- The frame's locals kept by a change apart from them. -/
theorem Loc.keep (h : Loc m0 c st) {R : BitVec 64 → Prop} (hs : SameOutside st.dmem st'.dmem R)
    (hR : ∀ i < 48, ¬R (fbA m0 + BitVec.ofNat 64 (8 + i))) : Loc m0 c st' :=
  ⟨NativeRustcVm.BytesAt.of_sameOutside h.cnt hs fun i hi ↦ by
      rw [NativeRustcVm.length_wordBytes] at hi
      rw [NativeRustcVm.addr_add_add]; exact hR i (by omega),
    NativeRustcVm.BytesAt.of_sameOutside h.s0 hs fun i hi ↦ by
      rw [NativeRustcVm.length_ewBytes] at hi
      rw [NativeRustcVm.addr_add_add, show 16 + i = 8 + (8 + i) by omega]; exact hR _ (by omega),
    NativeRustcVm.BytesAt.of_sameOutside h.s1 hs fun i hi ↦ by
      rw [NativeRustcVm.length_ewBytes] at hi
      rw [NativeRustcVm.addr_add_add, show 32 + i = 8 + (24 + i) by omega]; exact hR _ (by omega)⟩

/-- The locals are not in a callee's stack below the frame. -/
theorem loc_not_callee (hpre : SlotWeightsPre c m0) (hb : Body m0 st) {n : Nat}
    (hn : 176 + n ≤ slotWeightsStack) {i : Nat} (hi : i < 48) :
    ¬InRange (stackBelow st n) n (fbA m0 + BitVec.ofNat 64 (8 + i)) := by
  have hN : slotWeightsStack ≤ m0.regs.SP.toBitVec.toNat := hpre.1.2.1
  unfold stackBelow
  rw [hb.sp]
  exact not_inRange_below (by omega)

/-- The locals are not in the rows. -/
theorem loc_not_rows (hpre : SlotWeightsPre c m0) {o n : Nat} (ho : o + n ≤ rowsBytes) {i : Nat}
    (hi : i < 48) :
    ¬InRange (rowsA m0 + BitVec.ofNat 64 o) n (fbA m0 + BitVec.ofNat 64 (8 + i)) := by
  have hS := hpre.1
  have hrok := rows_ok hpre
  have hap := Areas.apart_stack (pre_areas hpre) (w := ⟨rowsA m0, rowsBytes⟩) (by simp)
  intro hc
  have h1 : InRange (rowsA m0) rowsBytes (fbA m0 + BitVec.ofNat 64 (8 + i)) :=
    inRange_mono hc ho
  have h2 : InRange (stackBelow m0 slotWeightsStack) slotWeightsStack
      (fbA m0 + BitVec.ofNat 64 (8 + i)) := by
    refine local_inStack hS (F := 176) (by decide) (lo := 80) (by decide) ?_
    unfold InRange
    rw [show fbA m0 + BitVec.ofNat 64 (8 + i) - (m0.regs.SP.toBitVec - BitVec.ofNat 64 176) =
      BitVec.ofNat 64 (8 + i) by unfold fbA; bv_omega, BitVec.toNat_ofNat]
    omega
  exact NativeRustcVm.Apart.not_inRange hap hrok.2 (noWrap_stackBelow hS) h1 h2

end

end NativeRustcVmArm.KeccakGkr.SlotWeights
