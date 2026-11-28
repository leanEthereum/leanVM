module

public import NativeRustcVmArm.Code.Vm.RingWeight.Names
public import NativeRustcVmArm.Ring.Weight.Entry
public import NativeRustcVmArm.Ring.Weight.Exit

/-!
# `ring_weight` with `r` empty: the coefficients' sum

Every product is its coefficient: `b2` clears four lanes, `b3` adds four coefficients to them
per turn (`SumI`: the lanes' sum is the first `4 t` coefficients'), `b4` adds the lanes into X21,
X23 and jumps to the epilogue.
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight

@[expose] public section

/-- The first `j` coefficients' sum. -/
def sumC (m0 : MachineData) (j : Nat) : EW := ((cL m0).toList.take j).foldl (· + ·) 0

/-- **The sum, turn `t`**: the lanes (X12, X2), (X14, X8), (X15, X10), (X16, X11) add up to the
first `4 t` coefficients, X13 at the next four. -/
structure SumI (m0 : MachineData) (t : Nat) (m : MachineData) : Prop where
  fr : WFr m0 m
  lt : t < 16
  x9 : (m.regs.getXReg .X9).toBitVec.toNat = 2 ^ 64 - 64 + 4 * t
  x13 : (m.regs.getXReg .X13).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 (64 * t + 32)
  lo : m.regs.getXReg .X12 ^^^ m.regs.getXReg .X14 ^^^ m.regs.getXReg .X15 ^^^
    m.regs.getXReg .X16 = (sumC m0 (4 * t)).c0
  hi : m.regs.getXReg .X2 ^^^ m.regs.getXReg .X8 ^^^ m.regs.getXReg .X10 ^^^
    m.regs.getXReg .X11 = (sumC m0 (4 * t)).c1

end

public section

variable {m0 : MachineData}

theorem add_c0 (x y : EW) : (x + y).c0 = x.c0 ^^^ y.c0 := rfl
theorem add_c1 (x y : EW) : (x + y).c1 = x.c1 ^^^ y.c1 := rfl

theorem sumC_succ {j : Nat} (hj : j < 64) : sumC m0 (j + 1) = sumC m0 j + (cL m0).getD j 0 := by
  unfold sumC
  rw [List.take_add_one, List.foldl_append,
    List.getElem?_eq_getElem (by simp [size_cL (m0 := m0)]; omega)]
  simp [Array.getD, size_cL (m0 := m0), hj]

theorem rL_nil (h0 : nR m0 = 0) : rL m0 = #[] := by
  simp [slice, NativeRustcVm.ewsOf, h0]

theorem ringWeight_nil (h0 : nR m0 = 0) : ringWeight (rL m0) (qL m0) (cL m0) = sumC m0 64 := by
  rw [ringWeight_eq, size_cL, rL_nil h0, accW_nil (by rw [size_cL])]
  rfl

theorem uxor_toBitVec (a b : UInt64) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

section
variable [Labels]

/-- A coefficient's limbs, loaded from a window of the coefficients. -/
theorem coef_loads (h : RingWeightPre m0) {m : MachineData} (hfr : WFr m0 m) {o j : Nat}
    (hj : j < 64) (hoj : o ≤ 16 * j) (n : Nat) :
    (Sym.load 0 (16 * j - o) 8).eval
        (Env.ofMachine m [(m0.regs.X5.toBitVec + BitVec.ofNat 64 o, n)]) =
        ((cL m0).getD j 0).c0.toBitVec ∧
      (Sym.load 0 (16 * j - o + 8) 8).eval
        (Env.ofMachine m [(m0.regs.X5.toBitVec + BitVec.ofNat 64 o, n)]) =
        ((cL m0).getD j 0).c1.toBitVec := by
  rw [load_c0 rfl, load_c1 rfl, addr_eq (z := 16 * j) (by omega), elem_c h hfr hj]
  exact ⟨rfl, rfl⟩

end

variable [Host] {k : Nat}

/-- **The lanes cleared** (`b2`): the sum's first turn. -/
theorem stepB2 (hp : Placed code k) {m : MachineData} (hB : Base m0 m) (h0 : nR m0 = 0)
    {R : MachineState → Prop}
    (cont : ∀ m', SumI m0 0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b3Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b2Offset)⟩ := by
  refine exec_then (hb b2_in_code (by simp [b2]) hp) run_b2 (Env.wf_nil m) (match_nil m)
    fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  refine at_pc hpc ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b2Offset + b2.length = k + NativeRustcVmArm.Vm.RingWeight.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b2_next]]
  have hx2 : m.regs.getXReg .X2 = 0 := by
    rw [hB.x2]; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_zero]; exact h0
  have z : ∀ r ∈ [XReg.X2, .X8, .X10, .X11, .X12, .X14, .X15, .X16], st.data.regs.getXReg r = 0 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (reg_of hm1 (w := m.regs.getXReg .X2) rfl rfl).trans hx2
  refine cont st.data ⟨regs_fr hB.fr hm1 rfl rfl, by decide, ?_, ?_, ?_, ?_⟩
  · rw [reg_bv hm1 rfl rfl]
    simp only [Sym.eval, Env.ofMachine_regs, hx2]
    rfl
  · refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, Env.ofMachine_regs, add_bv, hB.x8, hB.x20, h0]
    simp
  · rw [z .X12 (by simp), z .X14 (by simp), z .X15 (by simp), z .X16 (by simp)]
    rfl
  · rw [z .X2 (by simp), z .X8 (by simp), z .X10 (by simp), z .X11 (by simp)]
    rfl

/-- **A turn of the sum** (`b3`): the next turn, or the lanes done at `b4`. -/
theorem stepB3 (hp : Placed code k) (h : RingWeightPre m0) {t : Nat} {m : MachineData}
    (hI : SumI m0 t m) {R : MachineState → Prop}
    (hnext : ∀ m', SumI m0 (t + 1) m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b3Offset)⟩)
    (hdone : ∀ m', WFr m0 m' →
      m'.regs.getXReg .X12 ^^^ m'.regs.getXReg .X14 ^^^ m'.regs.getXReg .X15 ^^^
        m'.regs.getXReg .X16 = (sumC m0 64).c0 →
      m'.regs.getXReg .X2 ^^^ m'.regs.getXReg .X8 ^^^ m'.regs.getXReg .X10 ^^^
        m'.regs.getXReg .X11 = (sumC m0 64).c1 →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b4Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b3Offset)⟩ := by
  have hlt := hI.lt
  have hfr := hI.fr
  have hc := h.2.2.2.2.1
  have hcc : coeffCount = 64 := rfl
  let rs : List (BitVec 64 × Nat) := [(m0.regs.X5.toBitVec + BitVec.ofNat 64 (64 * t), 64)]
  have hwf : (Env.ofMachine m rs).WF :=
    win_wf1 (arg_win hfr hc.1 (by rw [hcc]; omega) (by decide))
  have hm : Match (Env.ofMachine m rs) sumS m :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show _ = m0.regs.X5.toBitVec + BitVec.ofNat 64 (64 * t) + BitVec.ofInt 64 (32 : Nat)
        rw [hI.x13, ofInt_lit, addr_eq rfl], trivial⟩
      trivial trivial trivial
  refine exec_then (hb b3_in_code (by simp [b3]) hp) run_b3 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : WFr m0 st.data := hfr.ofBlock hm hm1 hwf rfl rfl rfl fun r hr ↦ by simp at hr
  have L : ∀ u < 4, (Sym.load 0 (16 * u) 8).eval (Env.ofMachine m rs) =
        ((cL m0).getD (4 * t + u) 0).c0.toBitVec ∧
      (Sym.load 0 (16 * u + 8) 8).eval (Env.ofMachine m rs) =
        ((cL m0).getD (4 * t + u) 0).c1.toBitVec := fun u hu ↦ by
    have := coef_loads h hfr (o := 64 * t) (j := 4 * t + u) (by omega) (by omega) 64
    rwa [show 16 * (4 * t + u) - 64 * t = 16 * u by omega] at this
  have e12 : st.data.regs.getXReg .X12 = ((cL m0).getD (4 * t) 0).c0 ^^^ m.regs.getXReg .X12 :=
    reg_of hm1 rfl (eor_eval (L 0 (by decide)).1 rfl)
  have e2 : st.data.regs.getXReg .X2 = ((cL m0).getD (4 * t) 0).c1 ^^^ m.regs.getXReg .X2 :=
    reg_of hm1 rfl (eor_eval (L 0 (by decide)).2 rfl)
  have e14 : st.data.regs.getXReg .X14 = ((cL m0).getD (4 * t + 1) 0).c0 ^^^ m.regs.getXReg .X14 :=
    reg_of hm1 rfl (eor_eval (L 1 (by decide)).1 rfl)
  have e8 : st.data.regs.getXReg .X8 = ((cL m0).getD (4 * t + 1) 0).c1 ^^^ m.regs.getXReg .X8 :=
    reg_of hm1 rfl (eor_eval (L 1 (by decide)).2 rfl)
  have e15 : st.data.regs.getXReg .X15 = ((cL m0).getD (4 * t + 2) 0).c0 ^^^ m.regs.getXReg .X15 :=
    reg_of hm1 rfl (eor_eval (L 2 (by decide)).1 rfl)
  have e10 : st.data.regs.getXReg .X10 = ((cL m0).getD (4 * t + 2) 0).c1 ^^^ m.regs.getXReg .X10 :=
    reg_of hm1 rfl (eor_eval (L 2 (by decide)).2 rfl)
  have e16 : st.data.regs.getXReg .X16 = ((cL m0).getD (4 * t + 3) 0).c0 ^^^ m.regs.getXReg .X16 :=
    reg_of hm1 rfl (eor_eval (L 3 (by decide)).1 rfl)
  have e11 : st.data.regs.getXReg .X11 = ((cL m0).getD (4 * t + 3) 0).c1 ^^^ m.regs.getXReg .X11 :=
    reg_of hm1 rfl (eor_eval (L 3 (by decide)).2 rfl)
  have hs : sumC m0 (4 * (t + 1)) = sumC m0 (4 * t) + (cL m0).getD (4 * t) 0 +
      (cL m0).getD (4 * t + 1) 0 + (cL m0).getD (4 * t + 2) 0 + (cL m0).getD (4 * t + 3) 0 := by
    rw [show 4 * (t + 1) = 4 * t + 3 + 1 by omega, sumC_succ (by omega), sumC_succ (by omega),
      sumC_succ (by omega), sumC_succ (by omega)]
  have hlo : st.data.regs.getXReg .X12 ^^^ st.data.regs.getXReg .X14 ^^^
      st.data.regs.getXReg .X15 ^^^ st.data.regs.getXReg .X16 = (sumC m0 (4 * (t + 1))).c0 := by
    rw [e12, e14, e15, e16, hs]
    simp only [add_c0, ← hI.lo]
    ac_rfl
  have hhi : st.data.regs.getXReg .X2 ^^^ st.data.regs.getXReg .X8 ^^^
      st.data.regs.getXReg .X10 ^^^ st.data.regs.getXReg .X11 = (sumC m0 (4 * (t + 1))).c1 := by
    rw [e2, e8, e10, e11, hs]
    simp only [add_c1, ← hI.hi]
    ac_rfl
  have h9 : ((m.regs.getXReg .X9).toBitVec + BitVec.ofNat 64 4).toNat = (2 ^ 64 - 60 + 4 * t) % 2 ^ 64 := by
    rw [BitVec.toNat_add, hI.x9, BitVec.toNat_ofNat]
    omega
  simp only [PcOk] at hpc
  sym_simp at hpc
  have hc' := NativeRustcVmArm.Arrays.pc_ne hpc
  by_cases hl : t + 1 < 16
  · rw [Nat.mod_eq_of_lt (by omega)] at h9
    have hpc' := hc'.1 (fun e ↦ by
      rw [Env.ofMachine_regs] at e
      have := congrArg BitVec.toNat e
      rw [h9] at this
      simp at this)
    refine at_pc hpc' ?_
    rw [show Labels.label NativeRustcVmArm.Vm.RingWeight.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b3Offset) from hp.label (j := NativeRustcVmArm.Vm.RingWeight.b3Offset) NativeRustcVmArm.Vm.RingWeight.label_3_at]
    refine hnext st.data ⟨hfr1, hl, ?_, ?_, hlo, hhi⟩
    · rw [reg_bv hm1 rfl rfl]
      simp only [Sym.eval, add_bv, Env.ofMachine_regs]
      rw [h9]
      omega
    · refine reg_bv hm1 rfl ?_
      show m0.regs.X5.toBitVec + BitVec.ofNat 64 (64 * t) + BitVec.ofInt 64 (96 : Nat) = _
      rw [ofInt_lit, addr_eq (z := 64 * (t + 1) + 32) (by omega)]
  · have ht : t = 15 := by omega
    subst ht
    have hpc' := hc'.2 (by
      apply BitVec.eq_of_toNat_eq
      rw [Env.ofMachine_regs, h9]
      rfl)
    refine at_pc hpc' ?_
    rw [show k + NativeRustcVmArm.Vm.RingWeight.b3Offset + b3.length = k + NativeRustcVmArm.Vm.RingWeight.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b3_next]]
    exact hdone st.data hfr1 hlo hhi

/-- **The lanes added** (`b4`): at the epilogue with the coefficients' sum. -/
theorem stepB4 (hp : Placed code k) (h0 : nR m0 = 0) {m : MachineData} (hfr : WFr m0 m)
    (hlo : m.regs.getXReg .X12 ^^^ m.regs.getXReg .X14 ^^^ m.regs.getXReg .X15 ^^^
      m.regs.getXReg .X16 = (sumC m0 64).c0)
    (hhi : m.regs.getXReg .X2 ^^^ m.regs.getXReg .X8 ^^^ m.regs.getXReg .X10 ^^^
      m.regs.getXReg .X11 = (sumC m0 64).c1) {R : MachineState → Prop}
    (cont : ∀ m', Done m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b26Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b4Offset)⟩ := by
  refine exec_then (hb b4_in_code (by simp [b4]) hp) run_b4 (Env.wf_nil m) (match_nil m)
    fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  refine at_pc hpc ?_
  rw [show Labels.label NativeRustcVmArm.Vm.RingWeight.label_22 = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b26Offset) from hp.label (j := NativeRustcVmArm.Vm.RingWeight.b26Offset) NativeRustcVmArm.Vm.RingWeight.label_22_at]
  refine cont st.data ⟨regs_fr hfr hm1 rfl rfl, ?_⟩
  rw [ringWeight_nil h0]
  have e21 : st.data.regs.getXReg .X21 = (sumC m0 64).c0 := by
    refine reg_of hm1 rfl ?_
    simp only [Sym.eval, eor_bv, Env.ofMachine_regs]
    rw [← hlo]
    show _ = (m.regs.getXReg .X12 ^^^ m.regs.getXReg .X14 ^^^ m.regs.getXReg .X15 ^^^
      m.regs.getXReg .X16).toBitVec
    simp only [uxor_toBitVec]
    ac_rfl
  have e23 : st.data.regs.getXReg .X23 = (sumC m0 64).c1 := by
    refine reg_of hm1 rfl ?_
    simp only [Sym.eval, eor_bv, Env.ofMachine_regs]
    rw [← hhi]
    show _ = (m.regs.getXReg .X2 ^^^ m.regs.getXReg .X8 ^^^ m.regs.getXReg .X10 ^^^
      m.regs.getXReg .X11).toBitVec
    simp only [uxor_toBitVec]
    ac_rfl
  rw [e21, e23]

/-- **`r` empty**: from `b2` to the epilogue. -/
theorem stepSum (hp : Placed code k) (h : RingWeightPre m0) {m : MachineData} (hB : Base m0 m)
    (h0 : nR m0 = 0) {R : MachineState → Prop}
    (cont : ∀ m', Done m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b26Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b2Offset)⟩ := by
  refine stepB2 hp hB h0 fun m1 hI ↦ ?_
  refine Sym.loop (I := fun n st ↦ ∃ t, n = 16 - t ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b3Offset) ∧
    SumI m0 t st.data) (fun n st ⟨t, hn, hpc, hI⟩ ↦ ?_) ⟨0, rfl, rfl, hI⟩
  refine at_pc hpc (stepB3 hp h hI (fun m' hI' ↦ .done _ (.inr ⟨16 - (t + 1),
    by have := hI.lt; omega, t + 1, rfl, rfl, hI'⟩)) fun m' hfr hlo hhi ↦ ?_)
  exact (stepB4 hp h0 hfr hlo hhi cont).mono fun _ h ↦ .inl h

end

end NativeRustcVmArm.Ring.Weight
