module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.KeccakGkr.SlotWeights.Step

/-!
# `slot_weights`: a turn of the first segment's loop

From `.LSlotWeights_5` at bit `j`: the row (`b6`), the bit weight and the call of `EW::mul`
(`b7`), the store (`b8`), the counters (`b5`): bit `j + 1`, or the segment done
(`segA_step`, `segA_loop`).
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.SlotWeights NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

public section

variable [NativeRustcArm.Host] {c : KeccakClaimW} {m0 : MachineData} {k : Nat}

/-- **A turn of the first segment's loop**. -/
theorem segA_step (hp : Placed code k) (hpre : SlotWeightsPre c m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b6Offset)) (hI : SegA m0 c j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b6Offset) ∧ SegA m0 c (j + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b9Offset) ∧
        SegDone m0 c (1600 * m0.regs.X4.toNat + 1600) s'.data)) s := by
  have hS := hpre.1
  have hj := hI.j_lt
  have hf := first_le hpre
  have hA := pre_areas hpre
  -- `b6`: the row
  refine exec_at (b6_in_code.trans hp.1 (by simp [b6])) e6 (Env.wf_nil _) hpc (match_nil _)
    fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hI.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl all_slots (by decide)
  have k1 := KeccakGkr.Match.regs_keep (match_nil _) hm1
    [.X19, .X20, .X21, .X22, .X24, .X25, .X26, .X27, .X28, .X29] (by decide)
  have hd1 : s1.data.dmem = s.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have h23 := hm1.regs .X23 _ rfl
  have hx26 : (s.data.regs.getXReg .X26).toBitVec.toNat = j := hI.x26
  have hx27 : (s.data.regs.getXReg .X27).toBitVec.toNat = 25 * m0.regs.X4.toNat := hI.x27
  have hrow : (s.data.regs.getXReg .X27).toBitVec + (s.data.regs.getXReg .X26).toBitVec.ushiftRight 6 =
      BitVec.ofNat 64 (25 * m0.regs.X4.toNat + j / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, hx26, hx27,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  sym_simp at h23
  simp only [Env.ofMachine_regs] at h23
  rw [hrow] at h23
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  simp only [Env.ofMachine_regs, hrow] at hpc1
  have hu : (BitVec.ofNat 64 (25 * m0.regs.X4.toNat + j / 64)).ult 63#64 = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [hu, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false] at hpc1
  -- `b7`: the bit weight, `EW::mul`
  have hwok := Areas.ok hA (r := ⟨wA m0, weightsBytes⟩) (Or.inr (by simp))
  obtain ⟨hwm, hwn⟩ := sub_ok hwok (o := 16 * j) (n := 16) (by show 16 * j + 16 ≤ 25600; omega)
  have hwf2 := wf_one (m := s1.data) (Mapped.kept' hwm hb1.kept) hwn
  have hm2 : Match (Env.ofMachine s1.data [(wA m0 + BitVec.ofNat 64 (16 * j), 16)]) (loadS .X28)
      s1.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s1.data.regs.getXReg .X28).toBitVec =
          (wA m0 + BitVec.ofNat 64 (16 * j)) + BitVec.ofInt 64 8
        rw [k1 .X28 (by simp), show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
          NativeRustcVm.addr_add_add]
        exact hI.x28.trans (by congr 2; omega), trivial⟩ trivial trivial trivial
  refine exec_at (b7_in_code.trans hp.1 (by simp [b7])) e7 hwf2 hpc1 hm2 fun s2 hm2' hpc2 ↦ ?_
  have hb2 : Body m0 s2.data := hb1.of_block hm2 hm2' hwf2 rfl all_slots (by decide)
  have k2 := KeccakGkr.Match.regs_keep hm2 hm2'
    [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29] (by decide)
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hwj := w_at hpre hb1 hj
  rw [← NativeRustcVm.addr_add_zero (wA m0 + _)] at hwj
  obtain ⟨hw0, hw1⟩ := load_ew (env := Env.ofMachine s1.data [(wA m0 + BitVec.ofNat 64 (16 * j), 16)])
    (r := 0) hwj
  have hr0 := hm2'.regs .X0 _ rfl
  have hr1 := hm2'.regs .X1 _ rfl
  have hr2 := hm2'.regs .X2 _ rfl
  have hr3 := hm2'.regs .X3 _ rfl
  refine call_then hpc2 hmul (hb2.stackOk hS (by decide) (by decide)) fun s3 hpc3 hpost3 ↦ ?_
  obtain ⟨hp0, hp1, hsame3, hsv3⟩ := hpost3
  have hb3 : Body m0 s3.data :=
    hb2.call hS (n := ewMulStack) (by decide) slots_le' (wsOff hpre) hsame3 (fun _ h ↦ Or.inl h) hsv3
  have hprod : (⟨s3.data.regs.X0, s3.data.regs.X1⟩ : EW) =
      V m0.regs.X0.toNat c m0.regs.X4.toNat (1600 * m0.regs.X4.toNat + j) := by
    rw [hp0, hp1, V, show (1600 * m0.regs.X4.toNat + j) / 1600 - m0.regs.X4.toNat = 0 by omega,
      show (1600 * m0.regs.X4.toNat + j) % 1600 = j by omega]
    have e0 : s2.data.regs.X0 = ((segK m0.regs.X0.toNat c).getD 0 0).c0 := by
      apply UInt64.toBitVec_inj.mp
      show (s2.data.regs.getXReg .X0).toBitVec = _
      rw [hr0]
      show (s1.data.regs.getXReg .X24).toBitVec = _
      rw [k1 .X24 (by simp)]
      exact congrArg UInt64.toBitVec hI.x24
    have e1 : s2.data.regs.X1 = ((segK m0.regs.X0.toNat c).getD 0 0).c1 := by
      apply UInt64.toBitVec_inj.mp
      show (s2.data.regs.getXReg .X1).toBitVec = _
      rw [hr1]
      show (s1.data.regs.getXReg .X25).toBitVec = _
      rw [k1 .X25 (by simp)]
      exact congrArg UInt64.toBitVec hI.x25
    have e2 : s2.data.regs.X2 = (c.weights.getD j 0).c0 := by
      apply UInt64.toBitVec_inj.mp
      show (s2.data.regs.getXReg .X2).toBitVec = _
      rw [hr2]; exact hw0
    have e3 : s2.data.regs.X3 = (c.weights.getD j 0).c1 := by
      apply UInt64.toBitVec_inj.mp
      show (s2.data.regs.getXReg .X3).toBitVec = _
      rw [hr3]; exact hw1
    rw [e0, e1, e2, e3]
    rfl
  -- `b8`: the store
  have hrok := rows_ok hpre
  have hn : 1600 * m0.regs.X4.toNat + j < 4096 := by omega
  obtain ⟨hrm, hrn⟩ := sub_ok hrok (o := 16 * (1600 * m0.regs.X4.toNat + j)) (n := 16)
    (by show 16 * (1600 * m0.regs.X4.toNat + j) + 16 ≤ 65536; omega)
  have hwf4 := wf_one (m := s3.data) (Mapped.kept' hrm hb3.kept) hrn
  have hk3 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X25, .X26, .X27, .X28, .X29],
      s3.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    have h1 := k1 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hsv3.1 _ rfl).trans ((k2 _ (by simp)).trans h1)
  have hm4 : Match (Env.ofMachine s3.data
      [(rowsA m0 + BitVec.ofNat 64 (16 * (1600 * m0.regs.X4.toNat + j)), 16)]) (storeS .X23 .X26)
      s3.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by
        show (storeAddr .X23 .X26).eval _ = _ + BitVec.ofInt 64 0
        rw [store_addr _ .X23 .X26 (r := 25 * m0.regs.X4.toNat + j / 64) (j := j)
          (n := 1600 * m0.regs.X4.toNat + j)
          (show (s3.data.regs.getXReg .X19).toBitVec = rowsA m0 by
            rw [hk3 .X19 (by simp)]; exact congrArg UInt64.toBitVec hI.keep.x19)
          (show (s3.data.regs.getXReg .X23).toBitVec.toNat = _ by
            rw [hsv3.1 .X23 rfl, k2 .X23 (by simp)]
            show (s1.data.regs.getXReg .X23).toBitVec.toNat = _
            rw [h23, BitVec.toNat_ofNat]; omega)
          (show (s3.data.regs.getXReg .X26).toBitVec.toNat = j by
            rw [hk3 .X26 (by simp)]; exact hx26)
          (by omega)]
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  refine exec_at (b8_in_code.trans hp.1 (by simp [b8])) e8 hwf4 hpc3 hm4 fun s4 hm4' hpc4 ↦ ?_
  have hv := KeccakGkr.Match.ewAt_write2 hm4' (pre := []) rfl rfl nofun (r := 0) rfl (by decide)
  rw [NativeRustcVm.addr_add_zero] at hv
  have hv' : NativeRustcVm.EWAt s4.data.dmem
      (rowsA m0 + BitVec.ofNat 64 (16 * (1600 * m0.regs.X4.toNat + j)))
      (V m0.regs.X0.toNat c m0.regs.X4.toNat (1600 * m0.regs.X4.toNat + j)) := by
    rw [← hprod]
    convert hv using 2 <;> exact (UInt64.ofBitVec_toBitVec _).symm
  have hso : SameOutside s3.data.dmem s4.data.dmem
      (InRange (rowsA m0 + BitVec.ofNat 64 (16 * (1600 * m0.regs.X4.toNat + j))) 16) :=
    NativeRustcVm.SameOutside.mono (hm4'.sameOutside hwf4) fun p h ↦
      Written.inRange (r := 0) rfl hrn (by decide) h
  have hb4 : Body m0 s4.data :=
    hb3.write hS (by decide) slots_le' (wsOff hpre) hm4 hm4' hwf4 rfl all_slots (by decide)
      fun p h ↦ ⟨⟨rowsA m0, rowsBytes⟩, by simp,
        inRange_mono (Written.inRange (r := 0) rfl hrn (by decide) h)
          (by show 16 * (1600 * m0.regs.X4.toNat + j) + 16 ≤ 65536; omega)⟩
  have k4 := KeccakGkr.Match.regs_keep hm4 hm4'
    [.X19, .X20, .X21, .X22, .X24, .X25, .X26, .X27, .X28, .X29] (by decide)
  have hrows2 : ElemsAt s2.data.dmem (rowsA m0)
      (prog m0.regs.X0.toNat c m0.regs.X4.toNat (1600 * m0.regs.X4.toNat + j)) 4096 := by
    rw [hd2, hd1]; exact hI.rows
  have hrows4 : ElemsAt s4.data.dmem (rowsA m0)
      (prog m0.regs.X0.toNat c m0.regs.X4.toNat (1600 * m0.regs.X4.toNat + j + 1)) 4096 := by
    rw [← prog_succ _ _ (by omega)]
    exact store_rows hpre hn (rows_keep_call hpre hb2 (n := ewMulStack) (by decide) hrows2 hsame3)
      hso hv'
  have hloc2 : Loc m0 c s2.data :=
    hI.loc.keep (R := fun _ ↦ False) (fun p _ ↦ by rw [hd2, hd1]) fun _ _ h ↦ h
  have hloc4 : Loc m0 c s4.data :=
    (hloc2.keep hsame3
      fun i hi ↦ loc_not_callee hpre hb2 (by decide) hi).keep hso
      fun i hi ↦ loc_not_rows hpre (by show 16 * (1600 * m0.regs.X4.toNat + j) + 16 ≤ 65536; omega) hi
  have hkeep4 : Keep m0 s4.data :=
    ⟨(k4 .X19 (by simp)).trans ((hk3 .X19 (by simp)).trans hI.keep.x19),
      (k4 .X20 (by simp)).trans ((hk3 .X20 (by simp)).trans hI.keep.x20),
      (k4 .X21 (by simp)).trans ((hk3 .X21 (by simp)).trans hI.keep.x21),
      (k4 .X22 (by simp)).trans ((hk3 .X22 (by simp)).trans hI.keep.x22)⟩
  -- `b5`: the counters
  simp only [PcOk] at hpc4
  refine exec_at (b5_in_code.trans hp.1 (by simp [b5])) e5 (Env.wf_nil _)
    (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.SlotWeights.b5Offset) NativeRustcVmArm.Vm.SlotWeights.label_4_at)) (match_nil _) fun s5 hm5 hpc5 ↦ ?_
  have hb5 : Body m0 s5.data :=
    hb4.of_block (match_nil _) hm5 (Env.wf_nil _) rfl all_slots (by decide)
  have k5 := KeccakGkr.Match.regs_keep (match_nil _) hm5
    [.X19, .X20, .X21, .X22, .X24, .X25, .X27] (by decide)
  have hd5 : s5.data.dmem = s4.data.dmem := hm5.dmem_eq (Env.wf_nil _) rfl
  have hkeep5 : Keep m0 s5.data :=
    ⟨(k5 .X19 (by simp)).trans hkeep4.x19, (k5 .X20 (by simp)).trans hkeep4.x20,
      (k5 .X21 (by simp)).trans hkeep4.x21, (k5 .X22 (by simp)).trans hkeep4.x22⟩
  have hloc5 : Loc m0 c s5.data := hloc4.keep (R := fun _ ↦ False) (fun p _ ↦ by rw [hd5]) fun _ _ h ↦ h
  have hx29 : (s4.data.regs.getXReg .X29).toBitVec.toNat = 25600 - 16 * j := by
    rw [k4 .X29 (by simp), hk3 .X29 (by simp)]; exact hI.x29
  have h26 := hm5.regs .X26 _ rfl
  have h28 := hm5.regs .X28 _ rfl
  have h29 := hm5.regs .X29 _ rfl
  sym_simp at h26 h28 h29
  simp only [Env.ofMachine_regs] at h26 h28 h29
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  simp only [Env.ofMachine_regs] at hpc5
  by_cases hlast : j = 1599
  · subst hlast
    have hc : ((s4.data.regs.getXReg .X29).toBitVec == 16#64) = true := by
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hx29]; rfl
    simp only [hc, ite_true] at hpc5
    exact .done _ (Or.inr ⟨hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.SlotWeights.b9Offset) NativeRustcVmArm.Vm.SlotWeights.label_7_at), hb5, hkeep5, hloc5,
      by rw [hd5]; exact hrows4⟩)
  · have hc : ((s4.data.regs.getXReg .X29).toBitVec == 16#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; rw [hx29] at this
      simp at this; omega
    simp only [hc, Bool.false_eq_true, ite_false, NativeRustcVmArm.Vm.SlotWeights.b5_length, NativeRustcVmArm.Vm.SlotWeights.b5Length] at hpc5
    refine .done _ (Or.inl ⟨hpc5, hb5, hkeep5, hloc5, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [show s5.data.regs.X24 = s5.data.regs.getXReg .X24 from rfl, k5 .X24 (by simp),
        k4 .X24 (by simp), hk3 .X24 (by simp)]; exact hI.x24
    · rw [show s5.data.regs.X25 = s5.data.regs.getXReg .X25 from rfl, k5 .X25 (by simp),
        k4 .X25 (by simp), hk3 .X25 (by simp)]; exact hI.x25
    · show (s5.data.regs.getXReg .X26).toBitVec.toNat = j + 1
      rw [h26, k4 .X26 (by simp), hk3 .X26 (by simp), toNat_add_ofNat' (by rw [hx26]; omega), hx26]
    · show (s5.data.regs.getXReg .X27).toBitVec.toNat = _
      rw [k5 .X27 (by simp), k4 .X27 (by simp), hk3 .X27 (by simp)]; exact hx27
    · show (s5.data.regs.getXReg .X28).toBitVec = _
      rw [h28, k4 .X28 (by simp), hk3 .X28 (by simp),
        show (s.data.regs.getXReg .X28).toBitVec = _ from hI.x28,
        show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add,
        show 8 + 16 * j + 16 = 8 + 16 * (j + 1) by omega]
    · show (s5.data.regs.getXReg .X29).toBitVec.toNat = _
      rw [h29, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hx29]; simp; omega), hx29]
      simp; omega
    · rw [hd5, show 1600 * m0.regs.X4.toNat + (j + 1) = 1600 * m0.regs.X4.toNat + j + 1 by omega]
      exact hrows4

/-- **The first segment's loop**, to its end. -/
theorem segA_loop (hp : Placed code k) (hpre : SlotWeightsPre c m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b6Offset)) (hI : SegA m0 c j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b9Offset) ∧
      SegDone m0 c (1600 * m0.regs.X4.toNat + 1600) s'.data) s :=
  Sym.loop (fun n s ↦ ∃ j, n = 1600 - j ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b6Offset) ∧ SegA m0 c j s.data)
    (fun _ s ⟨j, hn, hpc, hI⟩ ↦ (segA_step hp hpre hmul hpc hI).mono fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨1600 - (j + 1), by have := hI.j_lt; omega, j + 1, rfl, hpc', hI'⟩
      · exact Or.inl h)
    ⟨j, rfl, hpc, hI⟩

end

end NativeRustcVmArm.KeccakGkr.SlotWeights
