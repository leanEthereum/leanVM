module

public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.KeccakGkr.SlotWeights.SegA

/-!
# `slot_weights`: the prologue

`b0` saves X19 to X30 in the 176-byte frame, zeroes the segment kernel's four elements at `16`
and calls `eq_kernel` on the point's last `|point| - (logSteps - 4)` coordinates (`ptrS`, `lenS`:
rustc's saturating `logSteps - 4`, `packS`) into them; `b1` checks it succeeded, `b2` saves the
count at `8` and starts the rows' zeroing loop (`prologue`, to `ZeroInv` at row `0`).
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.SlotWeights NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

@[expose] public section

/-- rustc's `logSteps.saturating_sub(4)`. -/
def packS : Sym :=
  .ite (.cmp .ult .W64 (.reg .X0) (.lit 4)) (.lit 0) (.bin .sub .W64 (.reg .X0) (.lit 4))

/-- The address of the point's segment coordinates. -/
def ptrS : Sym :=
  .ite (.cmp .ult .W64 (.reg .X2) packS) (.lit 8)
    (.bin .add .W64 (.reg .X1) (.un (.shift .LSL 4) .W64 packS))

/-- The number of the point's segment coordinates. -/
def lenS : Sym :=
  .ite (.cmp .ult .W64 (.reg .X2) packS) (.lit 0) (.bin .sub .W64 (.reg .X2) packS)

/-- **The zeroing loop's head** at row `r`: the rows before it zero. -/
structure ZeroInv [Labels] (m0 : MachineData) (c : KeccakClaimW) (r : Nat) (st : MachineData) :
    Prop where
  body : Body m0 st
  keep : Keep m0 st
  loc : Loc m0 c st
  r_lt : r < 64
  x8 : st.regs.X8.toNat = 65536 - 1024 * r
  x9 : st.regs.X9.toBitVec = rowsA m0 + BitVec.ofNat 64 (1024 * r)
  rows : ElemsAt st.dmem (rowsA m0) (fun _ ↦ 0) (64 * r)

end

public section

theorem packS_eval [Labels] (env : Env) :
    packS.eval env = BitVec.ofNat 64 ((env.regs .X0).toNat - 4) := by
  have := (env.regs .X0).isLt
  unfold packS
  sym_simp
  apply BitVec.eq_of_toNat_eq
  split <;> rename_i h <;> simp_all [BitVec.ult] <;> omega

theorem ptrS_eval [Labels] (env : Env) (h : (env.regs .X0).toNat - 4 ≤ (env.regs .X2).toNat) :
    ptrS.eval env = env.regs .X1 + BitVec.ofNat 64 (16 * ((env.regs .X0).toNat - 4)) := by
  have := (env.regs .X0).isLt
  have := (env.regs .X2).isLt
  unfold ptrS
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, UnOp.apply, low_W64, ext_W64, shiftW,
    packS_eval]
  rw [ite_eq_right (by simp [BitVec.ult]; omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem lenS_eval [Labels] (env : Env) (h : (env.regs .X0).toNat - 4 ≤ (env.regs .X2).toNat) :
    (lenS.eval env).toNat = (env.regs .X2).toNat - ((env.regs .X0).toNat - 4) := by
  have := (env.regs .X0).isLt
  have := (env.regs .X2).isLt
  unfold lenS
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, packS_eval]
  rw [ite_eq_right (by simp [BitVec.ult]; omega)]
  simp [BitVec.toNat_sub]
  omega

/-- An element of the frame from `o ≥ 16` kept by a block writing below `16`. -/
theorem ew_keep_above {d d' : DataMem} {fb : BitVec 64} {o : Nat} {x : EW}
    (h : NativeRustcVm.EWAt d (fb + BitVec.ofNat 64 o) x) (ho : 16 ≤ o) (ho' : o + 16 < 2 ^ 64)
    (hs : SameOutside d d' (InRange fb 16)) : NativeRustcVm.EWAt d' (fb + BitVec.ofNat 64 o) x :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi ↦ by
    rw [NativeRustcVm.length_ewBytes] at hi
    rw [NativeRustcVm.addr_add_add]
    exact slot_not_local (lo := 16) (o := o + i) (by omega) (by omega)

theorem extract_eq_drop (p : Array EW) (n : Nat) :
    p.extract n p.size = (p.toList.drop n).toArray := by
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract]

variable [NativeRustcArm.Host] {c : KeccakClaimW} {m0 : MachineData} {k : Nat}

/-- **The prologue**: from the entry to the zeroing loop's head at row `0`. -/
theorem prologue (hp : Placed code k) (hpre : SlotWeightsPre c m0)
    (heq : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b3Offset) ∧ ZeroInv m0 c 0 s'.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b0Offset)⟩ := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hNv : slotWeightsStack = 880 := rfl
  have h176 : 176 ≤ slotWeightsStack := by decide
  have hN : slotWeightsStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have hSP := m0.regs.SP.toBitVec.isLt
  obtain ⟨hmap, hnw, hfb⟩ := frame_ok hS h176
  have hfok : Region.Ok m0.dmem ⟨fbA m0, 176⟩ := ⟨hmap, hnw⟩
  have hws := wsOff hpre
  obtain ⟨hlt, hle2⟩ := hpre.2.2.2.2.1
  have hsz : c.point.size = m0.regs.X2.toNat := hpre.2.1
  have hpt : NativeRustcVm.EWsAt m0.dmem m0.regs.X1.toBitVec c.point.toList := hpre.2.2.1
  -- the prologue
  have hmA : Match (Env.ofMachine m0 [(fbA m0, 176)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h176 rfl, trivial⟩
      (by
        show _ = fbA m0 + BitVec.ofInt 64 176
        rw [show BitVec.ofInt 64 176 = BitVec.ofNat 64 176 from rfl, BitVec.sub_add_cancel])
      trivial trivial trivial trivial
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) e0 (wf_one hmap hnw) hmA
    fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    Frame.of_entry hS h176 hm1 rfl (by decide +kernel)
      (fun r hr hn ↦ absurd (all_slots r (by
        simp only [calleeRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl) hn) (by simp))
      (by decide +kernel)
  have hsp1 : s1.data.regs.SP.toBitVec = fbA m0 := hb1.sp
  have hpk : m0.regs.X0.toNat - 4 ≤ m0.regs.X2.toNat := by omega
  have hx0 : s1.data.regs.X0.toBitVec =
      m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * (m0.regs.X0.toNat - 4)) :=
    (hm1.regs .X0 ptrS rfl).trans (ptrS_eval (Env.ofMachine m0 [(fbA m0, 176)]) hpk)
  have hx1 : s1.data.regs.X1.toNat = m0.regs.X2.toNat - (m0.regs.X0.toNat - 4) := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm1.regs .X1 lenS rfl]
    exact lenS_eval (Env.ofMachine m0 [(fbA m0, 176)]) hpk
  have hx2 : s1.data.regs.X2.toBitVec = fbA m0 + BitVec.ofNat 64 16 := hm1.regs .X2 _ rfl
  have hx3 : s1.data.regs.X3.toNat = 4 := by
    show (s1.data.regs.getXReg .X3).toBitVec.toNat = 4
    rw [hm1.regs .X3 _ rfl]; rfl
  -- `eq_kernel` into the frame's four elements
  have hpr : ewsRegion m0.regs.X1.toBitVec c.point.size ∈
      [ewsRegion m0.regs.X1.toBitVec c.point.size, ⟨wA m0, weightsBytes⟩] := by simp
  have hpok := Areas.ok hA (Or.inr hpr)
  have hstk : Apart m0.regs.X1.toBitVec (16 * c.point.size) (stackBelow m0 slotWeightsStack)
      slotWeightsStack := NativeRustcVm.Apart.symm (Areas.stack_rs hA hpr)
  have hseg := sub_ok hpok (o := 16 * (m0.regs.X0.toNat - 4))
    (n := 16 * (m0.regs.X2.toNat - (m0.regs.X0.toNat - 4))) (by show _ ≤ 16 * c.point.size; omega)
  have hsegS : Apart (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * (m0.regs.X0.toNat - 4)))
      (16 * (m0.regs.X2.toNat - (m0.regs.X0.toNat - 4))) (stackBelow m0 slotWeightsStack)
      slotWeightsStack := by
    have := Apart.sub (o := 16 * (m0.regs.X0.toNat - 4))
      (n := 16 * (m0.regs.X2.toNat - (m0.regs.X0.toNat - 4))) (o' := 0) (n' := slotWeightsStack)
      hstk hpok.2 (noWrap_stackBelow hS) (by omega) (by omega) (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hfr := sub_ok hfok (o := 16) (n := 64) (by decide)
  have hfrS : Apart (fbA m0 + BitVec.ofNat 64 16) 64 (stackBelow s1.data eqKernelStack)
      eqKernelStack := by
    unfold Apart stackBelow
    right
    have hN' : 880 ≤ m0.regs.SP.toBitVec.toNat := hNv ▸ hN
    rw [hsp1, toNat_add_ofNat' (by rw [hfb]; omega),
      toNat_sub_ofNat (by rw [hfb]; simp only [eqKernelStack, ewMulStack]; omega), hfb]
    simp only [eqKernelStack, ewMulStack]
    omega
  refine call_then hpc1 heq ⟨hb1.stackOk hS (by decide) (by decide), by rw [hx1]; omega,
    ⟨by rw [hx0, hx1]; exact ⟨Mapped.kept' hseg.1 hb1.kept, hseg.2⟩,
      by rw [hx0, hx1]; exact hb1.apart_callee hS (by decide) hsegS⟩,
    ⟨by rw [hx2, hx3]; exact ⟨Mapped.kept' hfr.1 hb1.kept, hfr.2⟩, by rw [hx2, hx3]; exact hfrS⟩,
    ?_⟩ fun s2 hpc2 hpost2 ↦ ?_
  · rw [hx0, hx1, hx2, hx3]
    have e : fbA m0 + BitVec.ofNat 64 16 =
        stackBelow m0 slotWeightsStack + BitVec.ofNat 64 (slotWeightsStack - 176 + 16) := by
      unfold fbA stackBelow; rw [hNv]; bv_omega
    rw [e]
    exact Apart.sub (o := 16 * (m0.regs.X0.toNat - 4))
      (n := 16 * (m0.regs.X2.toNat - (m0.regs.X0.toNat - 4))) (o' := slotWeightsStack - 176 + 16)
      (n' := 64) hstk hpok.2 (noWrap_stackBelow hS) (by omega) (by rw [hNv]; decide) (by omega)
      (by decide)
  obtain ⟨hpost, hch, hsv2⟩ := hpost2
  rw [hx1, hx3, ite_eq_left (by
    rcases (show m0.regs.X2.toNat - (m0.regs.X0.toNat - 4) = 1 ∨
      m0.regs.X2.toNat - (m0.regs.X0.toNat - 4) = 2 by omega) with h | h <;> rw [h] <;> decide)]
    at hpost
  obtain ⟨hr0, -, hker⟩ := hpost
  have hdrop : NativeRustcVm.EWsAt s1.data.dmem
      (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * (m0.regs.X0.toNat - 4)))
      (c.point.toList.drop (m0.regs.X0.toNat - 4)) :=
    hb1.bytesAt hA hS hpr (by
      show _ + (List.flatMap _ _).length ≤ 16 * c.point.size
      rw [length_flatMap_ewBytes, List.length_drop, Array.length_toList]; omega)
      (NativeRustcVm.EWsAt.drop hpt _)
  have hslice : slice s1.data s1.data.regs.X0 s1.data.regs.X1 =
      c.point.extract (m0.regs.X0.toNat - 4) c.point.size := by
    unfold slice
    rw [hx0, hx1, extract_eq_drop]
    congr 1
    have := NativeRustcVm.ewsOf_of_ewsAt hdrop
    rwa [List.length_drop, Array.length_toList, hsz] at this
  rw [hslice, hx2] at hker
  change NativeRustcVm.EWsAt _ _ (segK m0.regs.X0.toNat c).toList at hker
  have hK : (segK m0.regs.X0.toNat c).size =
      2 ^ (m0.regs.X2.toNat - (m0.regs.X0.toNat - 4)) := by
    rw [segK, NativeVm.Math.Keccak.eqKernel_size, Array.size_extract, hsz, Nat.min_self]
  have hk2 : 2 ≤ (segK m0.regs.X0.toNat c).size := by
    rw [hK]
    rcases (show m0.regs.X2.toNat - (m0.regs.X0.toNat - 4) = 1 ∨
      m0.regs.X2.toNat - (m0.regs.X0.toNat - 4) = 2 by omega) with h | h <;> rw [h] <;> decide
  have hk0 := ewsAt_getD hker (i := 0) (by omega)
  have hk1 := ewsAt_getD hker (i := 1) (by omega)
  rw [NativeRustcVm.addr_add_add] at hk0 hk1
  have hb2 : Body m0 s2.data :=
    hb1.call_local (n := eqKernelStack) (lo := 80) hS (by decide) slots_le (by decide) hws hch
      (fun p h ↦ by
        rcases h with h | h
        · rw [hx2, hx3] at h
          exact Or.inr (Or.inr (inRange_mono h (by decide)))
        · exact Or.inl h) hsv2
  have hs21 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23], s2.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hsv2.1 _ rfl
  -- `b1`: `eq_kernel` succeeded
  have hx0' : (s2.data.regs.getXReg .X0).toBitVec = 1#64 := by
    show s2.data.regs.X0.toBitVec = _
    rw [hr0]; rfl
  refine exec_at (b1_in_code.trans hp.1 (by simp [b1])) e1 (Env.wf_nil _) hpc2 (match_nil _)
    fun s3 hm3 hpc3 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.SlotWeights.b1_length, NativeRustcVmArm.Vm.SlotWeights.b1Length] at hpc3
  sym_simp at hpc3
  simp only [Env.ofMachine_regs, hx0'] at hpc3
  rw [ite_eq_right (by decide)] at hpc3
  have hb3 : Body m0 s3.data :=
    hb2.of_block (match_nil _) hm3 (Env.wf_nil _) rfl all_slots (by decide)
  have k3 := KeccakGkr.Match.regs_keep (match_nil _) hm3 [.X19, .X21, .X22, .X23] (by decide)
  have h20 : (s3.data.regs.getXReg .X20).toBitVec = 1#64 := (hm3.regs .X20 _ rfl).trans hx0'
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  -- `b2`: the count saved, the zeroing loop's start
  have hwfB := wf_one (m := s3.data) (Mapped.kept' hmap hb3.kept) hnw
  have hmB : Match (Env.ofMachine s3.data [(fbA m0, 176)]) bodyS s3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h176 rfl, trivial⟩
      (by rw [hb3.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b2_in_code.trans hp.1 (by simp [b2])) e2 hwfB hpc3 hmB fun s4 hm4 hpc4 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.SlotWeights.b2_length, NativeRustcVmArm.Vm.SlotWeights.b2Length] at hpc4
  have hb4 : Body m0 s4.data :=
    hb3.write_local (lo := 80) hS h176 slots_le (by decide) hws hmB hm4 hwfB rfl all_slots
      (by decide) fun p hw ↦ Or.inr (Written.inRange_le (r := 0) rfl hnw (by decide) (by decide) hw)
  have hso4 : SameOutside s3.data.dmem s4.data.dmem (InRange (fbA m0) 16) := fun p hp ↦
    hm4.sameOutside hwfB p fun hw ↦ hp (Written.inRange_le (r := 0) rfl hnw (by decide) (by decide) hw)
  have k4 := KeccakGkr.Match.regs_keep hmB hm4 [.X19, .X20, .X21, .X22, .X23] (by decide)
  have hreg : ∀ r ∈ [XReg.X19, .X21, .X22, .X23], s4.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    rw [← hs21 r hr, ← k3 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k4 _ (by simp)
  have v19 : s1.data.regs.getXReg .X19 = m0.regs.X6 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl)
  have v21 : s1.data.regs.getXReg .X21 = m0.regs.X3 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have v22 : s1.data.regs.getXReg .X22 = m0.regs.X4 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have v23 : s1.data.regs.getXReg .X23 = m0.regs.X5 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  have hcnt := Sumcheck.Match.wordAt_write hm4 (r := 0) (o := 8) (v := .reg .X23) rfl (by decide)
    (by decide +kernel)
  have e23 : UInt64.ofBitVec ((Sym.reg .X23).eval (Env.ofMachine s3.data [(fbA m0, 176)])) =
      m0.regs.X5 := by
    show UInt64.ofBitVec (s3.data.regs.getXReg .X23).toBitVec = _
    rw [UInt64.ofBitVec_toBitVec, k3 .X23 (by simp), hs21 .X23 (by simp), v23]
  rw [e23] at hcnt
  refine .done _ ⟨by simpa only [b2Offset, b3Offset] using hpc4, ⟨hb4, ⟨?_, ?_, ?_, ?_⟩,
    ⟨hcnt, ew_keep_above (hd3 ▸ hk0) (by decide) (by decide) hso4,
      ew_keep_above (hd3 ▸ hk1) (by decide) (by decide) hso4⟩, by decide, ?_, ?_,
    fun i hi ↦ absurd hi (by omega)⟩⟩
  · show s4.data.regs.getXReg .X19 = _
    rw [hreg .X19 (by simp), v19]
  · apply UInt64.toBitVec_inj.mp
    show (s4.data.regs.getXReg .X20).toBitVec = _
    rw [k4 .X20 (by simp), h20]; rfl
  · show s4.data.regs.getXReg .X21 = _
    rw [hreg .X21 (by simp), v21]
  · show s4.data.regs.getXReg .X22 = _
    rw [hreg .X22 (by simp), v22]
  · show (s4.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [hm4.regs .X8 _ rfl]; rfl
  · show (s4.data.regs.getXReg .X9).toBitVec = _
    rw [hm4.regs .X9 _ rfl]
    show (s3.data.regs.getXReg .X19).toBitVec = _
    rw [k3 .X19 (by simp), hs21 .X19 (by simp), v19, Nat.mul_zero, NativeRustcVm.addr_add_zero]

end

end NativeRustcVmArm.KeccakGkr.SlotWeights
