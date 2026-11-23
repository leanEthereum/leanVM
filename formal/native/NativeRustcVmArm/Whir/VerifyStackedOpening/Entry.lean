module

public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.Count

/-!
# `verify_stacked_opening`: the prologue, the counting loop

`entry_step`: `b0` saves the registers and reads the claims' count; none: `b9`; else `b1` to the
loop's head with no claim counted. `cnt_step`: one claim counted, to the head or, after the last,
to `b5`.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt ColumnClaimAt PlacementWAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **From the entry**: no claim (`b9`), or the counting loop's head. -/
theorem entry_step (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0) {R : MachineState → Prop}
    (cont0 : ∀ st, Base cs m0 st → cs.size = 0 →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b9Offset)⟩)
    (cont1 : ∀ st, CntInv layout cs m0 0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b0Offset)⟩ := by
  have hstk := h.wt.1
  have hS := h.hS
  have hcin := (h.ins _ mem_cl).1
  simp only at hcin
  have hc := h.cl
  have hn160 : cs.size ≤ 160 := hc.len_le
  let env0 := Env.ofMachine m0 [(base m0 512, 512), (m0.regs.X5.toBitVec, 8)]
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨Ring.frame_mapped hstk (by rw [stack_eq]; decide), base_noWrap (by omega)⟩,
      ⟨fun i hi ↦ hcin.1.1 i (by show i < 97288; omega),
        NativeRustcVm.NoWrap.mono hcin.1.2 (by show 8 ≤ 97288; omega)⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        show Apart (base m0 512) 512 m0.regs.X5.toBitVec 8
        have := Ring.apart_frame (F := 512) h.hN (by rw [stack_eq]; decide) hcin.2
        have hcb : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
        rw [hcb] at this
        unfold Apart at this ⊢
        omega))
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by rw [stack_eq]; decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by simp [Sym.eval, base]) ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk0 run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : VFr m0 st1.data :=
    Fr.ofPrologue h.hN (by rw [stack_eq]; decide) hm1 hwf0 rfl (by decide) slots_le (by decide)
      (by simp)
  have hn : env0.load 1 0 8 = cs.size.toUInt64.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt m0.dmem (m0.regs.X5.toBitVec + BitVec.ofNat 64 0) _
    rw [NativeRustcVm.addr_add_zero]
    exact hc.len
  have hult : (cs.size.toUInt64.toBitVec).ult (BitVec.ofNat 64 161) = true := by
    rw [toBitVec_ult_ofNat (by decide), natCast_toUInt64_toNat (by omega)]
    simp
    omega
  have hb1 : Base cs m0 st1.data := by
    refine ⟨hfr1, (rv hm1 (r := .X20) rfl).trans rfl, reg_of hm1 rfl (by simp [Sym.eval]; rfl),
      (rv hm1 (r := .X22) rfl).trans rfl, (rv hm1 (r := .X24) rfl).trans rfl,
      (rv hm1 (r := .X26) rfl).trans rfl, ?_, ?_, (rv hm1 (r := .X0) rfl).trans rfl,
      (rv hm1 (r := .X2) rfl).trans rfl, (rv hm1 (r := .X4) rfl).trans rfl,
      NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf0) fun q hq ↦
        written_r0 hwf0 rfl (by decide) hq⟩
    · refine (hm1.regs .X28 _ rfl).trans ?_
      sym_simp
      rw [hn, hult]
      rfl
    · refine (rv hm1 (r := .X29) rfl).trans ?_
      sym_simp
      rw [hn, hult]
      rfl
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hn, hult] at hpc1
  by_cases hz : cs.size = 0
  · have hc0 : (cs.size.toUInt64.toBitVec == 0#64) = true := by rw [hz]; rfl
    simp only [hc0, ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b9Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b9Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_8_at]
      at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1
    subst hpc1
    exact cont0 d1 hb1 hz
  · have hc0 : (cs.size.toUInt64.toBitVec == 0#64) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro he
      have := congrArg BitVec.toNat he
      rw [UInt64.toNat_toBitVec, natCast_toUInt64_toNat (by omega)] at this
      exact hz this
    simp only [hc0, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine hfr1.regsBlock hk1 run_b1 hpc1 rfl rfl rfl fun st2 hf2 hd2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_3_at]
      at hpc2
    obtain ⟨d2, pc2⟩ := st2
    simp only at hpc2
    subst hpc2
    refine cont1 d2 ⟨hb1.keep hf2 hd2 fun r hr ↦ ?_, Nat.pos_of_ne_zero hz,
      (rv hm2 (r := .X8) rfl).trans rfl, ?_, ?_, ?_⟩
    · simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (rv hm2 rfl).trans rfl
    · refine (hm2.regs .X9 _ rfl).trans ?_
      sym_simp
      show (st1.data.regs.getXReg .X22).toBitVec + BitVec.ofNat 64 120 = _
      rw [hb1.x22]
    · refine (hm2.regs .X10 _ rfl).trans ?_
      show (st1.data.regs.getXReg .X28).toBitVec = _
      rw [hb1.x28]
    · refine (rv hm2 (r := .X11) rfl).trans ?_
      show st1.data.regs.getXReg .X29 = _
      rw [hb1.x29, Nat.sub_zero]

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
