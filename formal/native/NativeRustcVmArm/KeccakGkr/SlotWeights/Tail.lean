module

public import NativeRustcVmArm.KeccakGkr.SlotWeights.SegAStep
public import NativeRustcVmArm.KeccakGkr.SlotWeights.SegB

/-!
# `slot_weights`: after the first segment

`.LSlotWeights_7` (`b9`) reads the count back: `1`, done; `2` (so `first = 0`), `b11` starts the
second segment's loop at bit `0` (`after_segA`). The epilogue (`b10`) returns `1` (`epilogue`).
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.SlotWeights NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

@[expose] public section

/-- **Both segments done**: the body, X20 the kernel's success, the rows' products. -/
def EndOk [Labels] (m0 : MachineData) (c : KeccakClaimW) (st : MachineData) : Prop :=
  Body m0 st ∧ st.regs.X20 = 1 ∧ ElemsAt st.dmem (rowsA m0)
    (prog m0.regs.X0.toNat c m0.regs.X4.toNat (1600 * (m0.regs.X4.toNat + m0.regs.X5.toNat))) 4096

end

public section

variable [NativeRustcArm.Host] {c : KeccakClaimW} {m0 : MachineData} {k : Nat}

/-- **`b9`, `b11`**: after the first segment, done or the second segment's loop at bit `0`. -/
theorem after_segA (hp : Placed code k) (hpre : SlotWeightsPre c m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b9Offset))
    (hI : SegDone m0 c (1600 * m0.regs.X4.toNat + 1600) s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b10Offset) ∧ EndOk m0 c s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b13Offset) ∧ m0.regs.X5.toNat = 2 ∧ SegB m0 c 0 s'.data)) s := by
  have hS := hpre.1
  have h176 : 176 ≤ slotWeightsStack := by decide
  have h1 : 1 ≤ m0.regs.X5.toNat := hpre.2.2.2.2.2.1
  have h2 : m0.regs.X4.toNat + m0.regs.X5.toNat ≤ 2 := hpre.2.2.2.2.2.2.1
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h176
  have hwf := wf_one (m := s.data) (Mapped.kept' hmap hI.body.kept) hnw
  have hm : Match (Env.ofMachine s.data [(fbA m0, 176)]) bodyS s.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h176 rfl, trivial⟩
      (by rw [hI.body.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b9_in_code.trans hp.1 (by simp [b9])) e9 hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data := hI.body.of_block hm hm1 hwf rfl all_slots (by decide)
  have k1 := KeccakGkr.Match.regs_keep hm hm1 [.X19, .X20, .X21, .X22] (by decide)
  have hd1 : s1.data.dmem = s.data.dmem := hm1.dmem_eq hwf rfl
  have l8 := load_word (env := Env.ofMachine s.data [(fbA m0, 176)]) (r := 0) (off := 8) hI.loc.cnt
  simp only [PcOk, NativeRustcVmArm.Vm.SlotWeights.b9_length, NativeRustcVmArm.Vm.SlotWeights.b9Length] at hpc1
  sym_simp at hpc1
  simp only [l8] at hpc1
  by_cases hc1 : m0.regs.X5.toNat = 1
  · have e : m0.regs.X5.toBitVec = 1#64 := BitVec.eq_of_toNat_eq (by simp [hc1])
    simp only [e, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc1
    refine .done _ (Or.inl ⟨hpc1, hb1, (k1 .X20 (by simp)).trans hI.keep.x20, ?_⟩)
    rw [hd1, hc1, Nat.mul_add, Nat.mul_one]
    exact hI.rows
  · have hc2 : m0.regs.X5.toNat = 2 := by omega
    have hf0 : m0.regs.X4.toNat = 0 := by omega
    have e : (m0.regs.X5.toBitVec == 1#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      simp at this
      omega
    simp only [e, Bool.not_false, ite_true] at hpc1
    -- `b11`
    have hwf1 := wf_one (m := s1.data) (Mapped.kept' hmap hb1.kept) hnw
    have hm1' : Match (Env.ofMachine s1.data [(fbA m0, 176)]) bodyS s1.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h176 rfl, trivial⟩
        (by rw [hb1.sp]; simp [Sym.eval]) trivial trivial trivial trivial
    refine exec_at (b11_in_code.trans hp.1 (by simp [b11])) e11 hwf1
      (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.SlotWeights.b11Offset) NativeRustcVmArm.Vm.SlotWeights.label_9_at)) hm1' fun s2 hm2 hpc2 ↦ ?_
    have hb2 : Body m0 s2.data := hb1.of_block hm1' hm2 hwf1 rfl all_slots (by decide)
    have k2 := KeccakGkr.Match.regs_keep hm1' hm2 [.X19, .X20] (by decide)
    have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf1 rfl
    obtain ⟨w0, w1⟩ := NativeRustcVm.ewAt_iff.mp hI.loc.s1
    rw [NativeRustcVm.addr_add_add] at w1
    rw [← hd1] at w0 w1
    have l0 := load_word (env := Env.ofMachine s1.data [(fbA m0, 176)]) (r := 0) (off := 32) w0
    have l1 := load_word (env := Env.ofMachine s1.data [(fbA m0, 176)]) (r := 0) (off := 32 + 8) w1
    have x21 : s1.data.regs.getXReg .X21 = m0.regs.X3 := (k1 .X21 (by simp)).trans hI.keep.x21
    have x22 : s1.data.regs.getXReg .X22 = m0.regs.X4 := (k1 .X22 (by simp)).trans hI.keep.x22
    refine .done _ (Or.inr ⟨hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.SlotWeights.b13Offset) NativeRustcVmArm.Vm.SlotWeights.label_11_at), hc2, hb2, hf0,
      (k2 .X19 (by simp)).trans ((k1 .X19 (by simp)).trans hI.keep.x19),
      (k2 .X20 (by simp)).trans ((k1 .X20 (by simp)).trans hI.keep.x20), by decide, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩)
    · apply UInt64.toBitVec_inj.mp
      show (s2.data.regs.getXReg .X22).toBitVec = _
      rw [hm2.regs .X22 _ rfl]; exact l0
    · apply UInt64.toBitVec_inj.mp
      show (s2.data.regs.getXReg .X23).toBitVec = _
      rw [hm2.regs .X23 _ rfl]; exact l1
    · show (s2.data.regs.getXReg .X24).toBitVec.toNat = 0
      rw [hm2.regs .X24 _ rfl]; rfl
    · show (s2.data.regs.getXReg .X25).toBitVec.toNat = 25
      rw [hm2.regs .X25 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs]
      rw [x22]
      have : m0.regs.X4.toBitVec = 0#64 := BitVec.eq_of_toNat_eq (by simp [hf0])
      rw [this]
      rfl
    · show (s2.data.regs.getXReg .X21).toBitVec = _
      rw [hm2.regs .X21 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs]
      rw [x21]
    · show (s2.data.regs.getXReg .X26).toBitVec.toNat = _
      rw [hm2.regs .X26 _ rfl]; rfl
    · rw [hd2, hd1, show 1600 + 0 = 1600 * m0.regs.X4.toNat + 1600 by omega]
      exact hI.rows

/-- **The epilogue**: `1` returned, the rows `keccakSlotWeights`. -/
theorem epilogue (hp : Placed code k) (hpre : SlotWeightsPre c m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b10Offset)) (hE : EndOk m0 c s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = retOf m0 ∧ SlotWeightsPost c m0 s'.data) s := by
  obtain ⟨hb, hx20, hrows⟩ := hE
  have hS := hpre.1
  have h176 : 176 ≤ slotWeightsStack := by decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h176
  have hwf := wf_one (m := s.data) (Mapped.kept' hmap hb.kept) hnw
  have hm : Match (Env.ofMachine s.data [(fbA m0, 176)]) bodyS s.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h176 rfl, trivial⟩
      (by rw [hb.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b10_in_code.trans hp.1 (by simp [b10])) e10 hwf hpc hm fun s' hm' hpc' ↦
    .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf
    (List.mem_map.mpr ⟨(88, .X30), by simp [slots], rfl⟩) (by decide +kernel) rfl
  refine ⟨?_, ?_, ?_, fun p hp' ↦ ?_, hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · apply UInt64.toBitVec_inj.mp
    show (s'.data.regs.getXReg .X0).toBitVec = _
    rw [hm'.regs .X0 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs]
    have : (s.data.regs.getXReg .X20).toBitVec = 1#64 := by
      show s.data.regs.X20.toBitVec = _; rw [hx20]; rfl
    rw [this]
    rfl
  · rw [hdm]
    exact rows_final hpre.2.2.2.2.2.2.1 hrows
  · rw [hdm]; exact hb.same p hp'

end

end NativeRustcVmArm.KeccakGkr.SlotWeights
