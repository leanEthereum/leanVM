module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.KeccakGkr.SlotWeights.Step

/-!
# `slot_weights`: the second segment's loop

When `count = 2` (so `first = 0`): `.LSlotWeights_11` (`b13`) to `.LSlotWeights_10` (`b12`), as
the first segment's loop with segment `1`'s kernel entry (X22, X23), the bit index in X24, the row
base `25` in X25, the bit weights' pointer in X21, the bytes left in X26 (`SegB`, `segB_step`,
`segB_loop`); after the last bit, out to `.LSlotWeights_8`.
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.SlotWeights NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

@[expose] public section

/-- **The second segment's loop head** at bit `j`. -/
structure SegB [Labels] (m0 : MachineData) (c : KeccakClaimW) (j : Nat) (st : MachineData) :
    Prop where
  body : Body m0 st
  first0 : m0.regs.X4.toNat = 0
  x19 : st.regs.X19 = m0.regs.X6
  x20 : st.regs.X20 = 1
  j_lt : j < 1600
  x22 : st.regs.X22 = ((segK m0.regs.X0.toNat c).getD 1 0).c0
  x23 : st.regs.X23 = ((segK m0.regs.X0.toNat c).getD 1 0).c1
  x24 : st.regs.X24.toNat = j
  x25 : st.regs.X25.toNat = 25
  x21 : st.regs.X21.toBitVec = wA m0 + BitVec.ofNat 64 (8 + 16 * j)
  x26 : st.regs.X26.toNat = 25600 - 16 * j
  rows : ElemsAt st.dmem (rowsA m0) (prog m0.regs.X0.toNat c m0.regs.X4.toNat (1600 + j)) 4096

end

public section

variable [NativeRustcArm.Host] {c : KeccakClaimW} {m0 : MachineData} {k : Nat}

/-- **A turn of the second segment's loop**. -/
theorem segB_step (hp : Placed code k) (hpre : SlotWeightsPre c m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b13Offset)) (hI : SegB m0 c j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b13Offset) ∧ SegB m0 c (j + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b10Offset) ∧ Body m0 s'.data ∧ s'.data.regs.X20 = 1 ∧
        ElemsAt s'.data.dmem (rowsA m0) (prog m0.regs.X0.toNat c m0.regs.X4.toNat 3200) 4096)) s := by
  have hS := hpre.1
  have hj := hI.j_lt
  have hf := hI.first0
  have hA := pre_areas hpre
  -- `b13`: the row
  refine exec_at (b13_in_code.trans hp.1 (by simp [b13])) e13 (Env.wf_nil _) hpc (match_nil _)
    fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hI.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl all_slots (by decide)
  have k1 := KeccakGkr.Match.regs_keep (match_nil _) hm1
    [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26] (by decide)
  have hd1 : s1.data.dmem = s.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have h27 := hm1.regs .X27 _ rfl
  have hx24 : (s.data.regs.getXReg .X24).toBitVec.toNat = j := hI.x24
  have hx25 : (s.data.regs.getXReg .X25).toBitVec.toNat = 25 := hI.x25
  have hrow : (s.data.regs.getXReg .X25).toBitVec + (s.data.regs.getXReg .X24).toBitVec.ushiftRight 6 =
      BitVec.ofNat 64 (25 + j / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, hx24, hx25,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  sym_simp at h27
  simp only [Env.ofMachine_regs] at h27
  rw [hrow] at h27
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  simp only [Env.ofMachine_regs, hrow] at hpc1
  have hu : (BitVec.ofNat 64 (25 + j / 64)).ult 63#64 = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [hu, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false] at hpc1
  -- `b14`: the bit weight, `EW::mul`
  have hwok := Areas.ok hA (r := ⟨wA m0, weightsBytes⟩) (Or.inr (by simp))
  obtain ⟨hwm, hwn⟩ := sub_ok hwok (o := 16 * j) (n := 16) (by show 16 * j + 16 ≤ 25600; omega)
  have hwf2 := wf_one (m := s1.data) (Mapped.kept' hwm hb1.kept) hwn
  have hm2 : Match (Env.ofMachine s1.data [(wA m0 + BitVec.ofNat 64 (16 * j), 16)]) (loadS .X21)
      s1.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s1.data.regs.getXReg .X21).toBitVec =
          (wA m0 + BitVec.ofNat 64 (16 * j)) + BitVec.ofInt 64 8
        rw [k1 .X21 (by simp), show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
          NativeRustcVm.addr_add_add]
        exact hI.x21.trans (by congr 2; omega), trivial⟩ trivial trivial trivial
  refine exec_at (b14_in_code.trans hp.1 (by simp [b14])) e14 hwf2 hpc1 hm2 fun s2 hm2' hpc2 ↦ ?_
  have hb2 : Body m0 s2.data := hb1.of_block hm2 hm2' hwf2 rfl all_slots (by decide)
  have k2 := KeccakGkr.Match.regs_keep hm2 hm2'
    [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27] (by decide)
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
      V m0.regs.X0.toNat c m0.regs.X4.toNat (1600 + j) := by
    rw [hp0, hp1, V, hf, show (1600 + j) / 1600 - 0 = 1 by omega,
      show (1600 + j) % 1600 = j by omega]
    have e0 : s2.data.regs.X0 = ((segK m0.regs.X0.toNat c).getD 1 0).c0 := by
      apply UInt64.toBitVec_inj.mp
      show (s2.data.regs.getXReg .X0).toBitVec = _
      rw [hr0]
      show (s1.data.regs.getXReg .X22).toBitVec = _
      rw [k1 .X22 (by simp)]
      exact congrArg UInt64.toBitVec hI.x22
    have e1 : s2.data.regs.X1 = ((segK m0.regs.X0.toNat c).getD 1 0).c1 := by
      apply UInt64.toBitVec_inj.mp
      show (s2.data.regs.getXReg .X1).toBitVec = _
      rw [hr1]
      show (s1.data.regs.getXReg .X23).toBitVec = _
      rw [k1 .X23 (by simp)]
      exact congrArg UInt64.toBitVec hI.x23
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
  -- `b15`: the store
  have hrok := rows_ok hpre
  have hn : 1600 + j < 4096 := by omega
  obtain ⟨hrm, hrn⟩ := sub_ok hrok (o := 16 * (1600 + j)) (n := 16)
    (by show 16 * (1600 + j) + 16 ≤ 65536; omega)
  have hwf4 := wf_one (m := s3.data) (Mapped.kept' hrm hb3.kept) hrn
  have hk3 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26],
      s3.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    have h1 := k1 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hsv3.1 _ rfl).trans ((k2 _ (by simp)).trans h1)
  have hm4 : Match (Env.ofMachine s3.data [(rowsA m0 + BitVec.ofNat 64 (16 * (1600 + j)), 16)])
      (storeS .X27 .X24) s3.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by
        show (storeAddr .X27 .X24).eval _ = _ + BitVec.ofInt 64 0
        rw [store_addr _ .X27 .X24 (r := 25 + j / 64) (j := j) (n := 1600 + j)
          (show (s3.data.regs.getXReg .X19).toBitVec = rowsA m0 by
            rw [hk3 .X19 (by simp)]; exact congrArg UInt64.toBitVec hI.x19)
          (show (s3.data.regs.getXReg .X27).toBitVec.toNat = _ by
            rw [hsv3.1 .X27 rfl, k2 .X27 (by simp)]
            show (s1.data.regs.getXReg .X27).toBitVec.toNat = _
            rw [h27, BitVec.toNat_ofNat]; omega)
          (show (s3.data.regs.getXReg .X24).toBitVec.toNat = j by
            rw [hk3 .X24 (by simp)]; exact hx24)
          (by omega)]
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  refine exec_at (b15_in_code.trans hp.1 (by simp [b15])) e15 hwf4 hpc3 hm4 fun s4 hm4' hpc4 ↦ ?_
  have hv := KeccakGkr.Match.ewAt_write2 hm4' (pre := []) rfl rfl nofun (r := 0) rfl (by decide)
  rw [NativeRustcVm.addr_add_zero] at hv
  have hv' : NativeRustcVm.EWAt s4.data.dmem (rowsA m0 + BitVec.ofNat 64 (16 * (1600 + j)))
      (V m0.regs.X0.toNat c m0.regs.X4.toNat (1600 + j)) := by
    rw [← hprod]
    convert hv using 2 <;> exact (UInt64.ofBitVec_toBitVec _).symm
  have hso : SameOutside s3.data.dmem s4.data.dmem
      (InRange (rowsA m0 + BitVec.ofNat 64 (16 * (1600 + j))) 16) :=
    NativeRustcVm.SameOutside.mono (hm4'.sameOutside hwf4) fun p h ↦
      Written.inRange (r := 0) rfl hrn (by decide) h
  have hb4 : Body m0 s4.data :=
    hb3.write hS (by decide) slots_le' (wsOff hpre) hm4 hm4' hwf4 rfl all_slots (by decide)
      fun p h ↦ ⟨⟨rowsA m0, rowsBytes⟩, by simp,
        inRange_mono (Written.inRange (r := 0) rfl hrn (by decide) h)
          (by show 16 * (1600 + j) + 16 ≤ 65536; omega)⟩
  have k4 := KeccakGkr.Match.regs_keep hm4 hm4'
    [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26] (by decide)
  have hrows2 : ElemsAt s2.data.dmem (rowsA m0)
      (prog m0.regs.X0.toNat c m0.regs.X4.toNat (1600 + j)) 4096 := by
    rw [hd2, hd1]; exact hI.rows
  have hrows4 : ElemsAt s4.data.dmem (rowsA m0)
      (prog m0.regs.X0.toNat c m0.regs.X4.toNat (1600 + j + 1)) 4096 := by
    rw [← prog_succ _ _ (by omega)]
    exact store_rows hpre hn (rows_keep_call hpre hb2 (n := ewMulStack) (by decide) hrows2 hsame3)
      hso hv'
  -- `b12`: the counters
  simp only [PcOk] at hpc4
  refine exec_at (b12_in_code.trans hp.1 (by simp [b12])) e12 (Env.wf_nil _)
    (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.SlotWeights.b12Offset) NativeRustcVmArm.Vm.SlotWeights.label_10_at)) (match_nil _) fun s5 hm5 hpc5 ↦ ?_
  have hb5 : Body m0 s5.data :=
    hb4.of_block (match_nil _) hm5 (Env.wf_nil _) rfl all_slots (by decide)
  have k5 := KeccakGkr.Match.regs_keep (match_nil _) hm5 [.X19, .X20, .X22, .X23, .X25] (by decide)
  have hd5 : s5.data.dmem = s4.data.dmem := hm5.dmem_eq (Env.wf_nil _) rfl
  have hx26 : (s4.data.regs.getXReg .X26).toBitVec.toNat = 25600 - 16 * j := by
    rw [k4 .X26 (by simp), hk3 .X26 (by simp)]; exact hI.x26
  have hx20 : s5.data.regs.X20 = 1 := by
    rw [show s5.data.regs.X20 = s5.data.regs.getXReg .X20 from rfl, k5 .X20 (by simp),
      k4 .X20 (by simp), hk3 .X20 (by simp)]; exact hI.x20
  have h24 := hm5.regs .X24 _ rfl
  have h21 := hm5.regs .X21 _ rfl
  have h26 := hm5.regs .X26 _ rfl
  sym_simp at h24 h21 h26
  simp only [Env.ofMachine_regs] at h24 h21 h26
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  simp only [Env.ofMachine_regs] at hpc5
  by_cases hlast : j = 1599
  · subst hlast
    have hc : ((s4.data.regs.getXReg .X26).toBitVec == 16#64) = true := by
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hx26]; rfl
    simp only [hc, ite_true] at hpc5
    exact .done _ (Or.inr ⟨hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.SlotWeights.b10Offset) NativeRustcVmArm.Vm.SlotWeights.label_8_at), hb5, hx20,
      by rw [hd5]; exact hrows4⟩)
  · have hc : ((s4.data.regs.getXReg .X26).toBitVec == 16#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; rw [hx26] at this
      simp at this; omega
    simp only [hc, Bool.false_eq_true, ite_false, NativeRustcVmArm.Vm.SlotWeights.b12_length, NativeRustcVmArm.Vm.SlotWeights.b12Length] at hpc5
    refine .done _ (Or.inl ⟨hpc5, hb5, hf, ?_, hx20, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [show s5.data.regs.X19 = s5.data.regs.getXReg .X19 from rfl, k5 .X19 (by simp),
        k4 .X19 (by simp), hk3 .X19 (by simp)]; exact hI.x19
    · rw [show s5.data.regs.X22 = s5.data.regs.getXReg .X22 from rfl, k5 .X22 (by simp),
        k4 .X22 (by simp), hk3 .X22 (by simp)]; exact hI.x22
    · rw [show s5.data.regs.X23 = s5.data.regs.getXReg .X23 from rfl, k5 .X23 (by simp),
        k4 .X23 (by simp), hk3 .X23 (by simp)]; exact hI.x23
    · show (s5.data.regs.getXReg .X24).toBitVec.toNat = j + 1
      rw [h24, k4 .X24 (by simp), hk3 .X24 (by simp), toNat_add_ofNat' (by rw [hx24]; omega), hx24]
    · show (s5.data.regs.getXReg .X25).toBitVec.toNat = _
      rw [k5 .X25 (by simp), k4 .X25 (by simp), hk3 .X25 (by simp)]; exact hx25
    · show (s5.data.regs.getXReg .X21).toBitVec = _
      rw [h21, k4 .X21 (by simp), hk3 .X21 (by simp),
        show (s.data.regs.getXReg .X21).toBitVec = _ from hI.x21,
        show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add,
        show 8 + 16 * j + 16 = 8 + 16 * (j + 1) by omega]
    · show (s5.data.regs.getXReg .X26).toBitVec.toNat = _
      rw [h26, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hx26]; simp; omega), hx26]
      simp; omega
    · rw [hd5, show 1600 + (j + 1) = 1600 + j + 1 by omega]
      exact hrows4

/-- **The second segment's loop**, to its end. -/
theorem segB_loop (hp : Placed code k) (hpre : SlotWeightsPre c m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b13Offset)) (hI : SegB m0 c j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b10Offset) ∧ Body m0 s'.data ∧
      s'.data.regs.X20 = 1 ∧
      ElemsAt s'.data.dmem (rowsA m0) (prog m0.regs.X0.toNat c m0.regs.X4.toNat 3200) 4096) s :=
  Sym.loop (fun n s ↦ ∃ j, n = 1600 - j ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b13Offset) ∧ SegB m0 c j s.data)
    (fun _ s ⟨j, hn, hpc, hI⟩ ↦ (segB_step hp hpre hmul hpc hI).mono fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨1600 - (j + 1), by have := hI.j_lt; omega, j + 1, rfl, hpc', hI'⟩
      · exact Or.inl h)
    ⟨j, rfl, hpc, hI⟩

end

end NativeRustcVmArm.KeccakGkr.SlotWeights
