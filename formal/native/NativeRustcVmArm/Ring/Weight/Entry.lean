module

public import NativeRustcVmArm.Ring.Weight.Step

/-!
# `ring_weight`: the prologue

`b0` saves the registers, zeroes the powers, keeps `out`'s address at frame byte `8` and
branches on `|r| = 1`; the state it leaves (`Base`: the arguments' registers, `16 |r|` in X8,
the powers' address in X9, the coefficients' in X20) holds until the products (`Base.after`).
The first powers copied from `r` (`CopyAt`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight

@[expose] public section

/-- **Until the products**: the frame, the arguments' registers, `16 |r|` in X8, the powers'
address in X9, the coefficients' in X20. -/
structure Base (m0 m : MachineData) : Prop where
  fr : WFr m0 m
  x1 : m.regs.getXReg .X1 = m0.regs.X1
  x2 : m.regs.getXReg .X2 = m0.regs.X2
  x3 : m.regs.getXReg .X3 = m0.regs.X3
  x4 : m.regs.getXReg .X4 = m0.regs.X4
  x8 : (m.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 (16 * nR m0)
  x9 : (m.regs.getXReg .X9).toBitVec = fb m0 + BitVec.ofNat 64 16
  x20 : m.regs.getXReg .X20 = m0.regs.X5

/-- The registers `Base` names, each its own atom in `S`. -/
def baseKeep (S : SState) : Bool :=
  [XReg.X1, .X2, .X3, .X4, .X8, .X9, .X20].all fun r ↦ S.reg r == some (.reg r)

/-- The first `c` powers are `r`'s. -/
def CopyAt (m0 : MachineData) (d : DataMem) (c : Nat) : Prop :=
  ∀ j < c, NativeRustcVm.EWAt d (slotA m0 j) ((rL m0).getD j 0)

end

public section

variable {m0 : MachineData}

theorem mem_low {S : SState} {F : Nat}
    (h : S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ F)) = true) :
    ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F := by
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h

theorem eq_lit {x : BitVec 64} {c : Nat} (hc : c < 2 ^ 64) :
    (x == BitVec.ofNat 64 c) = true ↔ x.toNat = c := by
  rw [beq_iff_eq]
  constructor
  · rintro rfl; simp; omega
  · intro hx; apply BitVec.eq_of_toNat_eq; simp; omega

section
variable [Labels]

/-- **`Base` after a block** that keeps its registers. -/
theorem Base.after {env : Env} {S S' : SState} {m m' : MachineData} (hB : Base m0 m)
    (hm : Match env S m) (hm' : Match env S' m') (h0 : baseKeep S = true)
    (h1 : baseKeep S' = true) (hfr : WFr m0 m') : Base m0 m' := by
  have k0 := List.all_eq_true.mp h0
  have k1 := List.all_eq_true.mp h1
  have e : ∀ r ∈ [XReg.X1, .X2, .X3, .X4, .X8, .X9, .X20],
      m'.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    Match.reg_eq hm hm' (beq_iff_eq.mp (k0 r hr)) (beq_iff_eq.mp (k1 r hr))
  exact ⟨hfr, (e .X1 (by simp)).trans hB.x1, (e .X2 (by simp)).trans hB.x2,
    (e .X3 (by simp)).trans hB.x3, (e .X4 (by simp)).trans hB.x4,
    by rw [e .X8 (by simp)]; exact hB.x8, by rw [e .X9 (by simp)]; exact hB.x9,
    (e .X20 (by simp)).trans hB.x20⟩

end

variable [Host] {k : Nat}

/-- **The prologue** (`b0`): `Base`, at `b5` when `|r| = 1`, else at `b1`. -/
theorem stepEntry (hp : Placed code k) (h : RingWeightPre m0) {R : MachineState → Prop}
    (cont : ∀ st : MachineState, Base m0 st.data →
      st.pc = Host.addrOf (k + if nR m0 = 1 then NativeRustcVmArm.Vm.RingWeight.b5Offset else NativeRustcVmArm.Vm.RingWeight.b1Offset) → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b0Offset)⟩ := by
  have hfw := fbw h
  have hwf : (Env.ofMachine m0 [(fb m0, 688)]).WF :=
    Env.wf_of ⟨⟨frame_mapped h.1 (by decide), hfw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m0 [(fb m0, 688)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), trivial⟩
      (by
        show m0.regs.SP.toBitVec = fb m0 + BitVec.ofInt 64 (688 : Nat)
        rw [BitVec.ofInt_natCast, base_add_eq])
      trivial trivial trivial trivial
  refine exec_then (hb b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : WFr m0 st.data :=
    Fr.ofPrologue (rs := []) (hN h) (by decide) hm1 hwf rfl (by decide +kernel) slots_le
      (mem_low (by decide +kernel)) fun r hr ↦ by simp at hr
  have hB : Base m0 st.data := by
    refine ⟨hfr1, reg_of hm1 (v := .reg .X1) rfl rfl, reg_of hm1 (v := .reg .X2) rfl rfl,
      reg_of hm1 (v := .reg .X3) rfl rfl, reg_of hm1 (v := .reg .X4) rfl rfl, ?_, ?_,
      reg_of hm1 (v := .reg .X5) rfl rfl⟩
    · refine reg_bv hm1 rfl ?_
      simp only [Sym.eval, Env.ofMachine_regs]
      exact NativeRustcVmArm.Arrays.lsl4 _
    · exact reg_bv hm1 rfl rfl
  refine cont st hB ?_
  simp only [PcOk] at hpc
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b0Offset + b0.length = k + NativeRustcVmArm.Vm.RingWeight.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b0_next]] at hpc
  have hc := NativeRustcVmArm.Arrays.pc_cond hpc
  have he : (SBool.cmp .eq .W64 (.reg .X2) (.lit 1)).eval (Env.ofMachine m0 [(fb m0, 688)]) = true ↔
      nR m0 = 1 := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Env.ofMachine_regs, Sym.low_W64]
    exact eq_lit (by decide)
  by_cases h1 : nR m0 = 1
  · rw [ite_eq_left h1, hc.1 (he.mpr h1)]
    exact hp.label (j := NativeRustcVmArm.Vm.RingWeight.b5Offset) NativeRustcVmArm.Vm.RingWeight.label_5_at
  · rw [ite_eq_right h1, hc.2 (fun e ↦ h1 (he.mp e))]

/-- **`|r| = 0`?** (`b1`): at `b2` if so, else at `b6`. -/
theorem stepB1 (hp : Placed code k) {m : MachineData} (hB : Base m0 m) {R : MachineState → Prop}
    (cont : ∀ st : MachineState, Base m0 st.data →
      st.pc = Host.addrOf (k + if nR m0 = 0 then NativeRustcVmArm.Vm.RingWeight.b2Offset else NativeRustcVmArm.Vm.RingWeight.b6Offset) → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b1Offset)⟩ := by
  refine exec_then (hb b1_in_code (by simp [b1]) hp) run_b1 (Env.wf_nil m) (match_nil m)
    fun st hm1 hpc ↦ ?_
  refine cont st (hB.after (match_nil m) hm1 (by decide) (by decide)
    (regs_fr hB.fr hm1 rfl rfl)) ?_
  simp only [PcOk] at hpc
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b1Offset + b1.length = k + NativeRustcVmArm.Vm.RingWeight.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b1_next]] at hpc
  have hc := NativeRustcVmArm.Arrays.pc_cond hpc
  have he : (SBool.not (SBool.cmp .eq .W64 (.reg .X2) (.lit 0))).eval (Env.ofMachine m []) = true ↔
      nR m0 ≠ 0 := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Env.ofMachine_regs, Sym.low_W64, hB.x2,
      Bool.not_eq_true', Bool.eq_false_iff, ne_eq]
    exact not_congr (eq_lit (by decide))
  by_cases h0 : nR m0 = 0
  · rw [ite_eq_left h0, hc.2 (fun e ↦ he.mp e h0)]
  · rw [ite_eq_right h0, hc.1 (he.mpr h0)]
    exact hp.label (j := NativeRustcVmArm.Vm.RingWeight.b6Offset) NativeRustcVmArm.Vm.RingWeight.label_6_at

end

end NativeRustcVmArm.Ring.Weight
