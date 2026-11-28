module

public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Layout.PlacementsOf.Loop1

/-!
# `placements_of`: the prologue and the first loop (`b0` to `b7`)

`b0` saves the registers, opens the frame and zeroes `block_cols`, `b1` zeroes `block_sizes`,
`b2` starts the first loop at `.L2` with nothing stacked (`entry`). The loop (`loop1`) runs
`turn1` and `l1` over the `158` columns, out at `.L6` (`b8`).
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

variable [Host] {k : Nat}

/-- **The prologue** `b0`-`b2`: two arrays zeroed, at `.L2` with nothing stacked. -/
theorem entry (hp : Placed code k) (hms : Spec (Labels.label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    {m0 : MachineData} (hF : Facts m0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b4Offset) ∧ I1 m0 0 0 st.data)
      ⟨m0, Host.addrOf k⟩ := by
  obtain ⟨hwf, hm⟩ := Arrays.entry_match hF.stack (F := 5136) (by decide) (by decide)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hw, hmem, hregs⟩ := Arrays.after_eq run_b0 ▸ b0_frame
  have hb1 : Bd m0 st1.data := Arrays.Body.of_entry hF.stack (by decide) hm1 rfl hw hregs hmem
  have g0 := hm1.regs .X0 _ rfl
  have g2 := hm1.regs .X2 _ rfl
  have g19 := hm1.regs .X19 _ rfl
  have g20 := hm1.regs .X20 _ rfl
  have g21 := hm1.regs .X21 _ rfl
  have g25 := hm1.regs .X25 _ rfl
  sym_simp at g0 g2 g19 g20 g21 g25
  refine memset_call hms hF hpc1 hb1 (o := 0) (n := 1264) (by omega)
    (by rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl, g0]; rfl)
    (by show (st1.data.regs.getXReg .X2).toBitVec.toNat = _; rw [g2]; rfl)
    fun st2 hpc2 hb2 hsv2 _ ↦ ?_
  -- `b1`: `block_sizes` zeroed
  refine regs_step (infix_of b1_in_code (by simp [b1]) hp) run_b1 (rk run_b1) hb2
    (pc_of hpc2 rfl) fun st3 hm3 hpc3 hb3 _ hr3 ↦ ?_
  have g0' := hm3.regs .X0 _ rfl
  have g2' := hm3.regs .X2 _ rfl
  have g26 := hm3.regs .X26 _ rfl
  sym_simp at g0' g2' g26
  have hsp2 : st2.data.regs.SP.toBitVec = fb m0 := hb2.sp
  refine memset_call hms hF hpc3 hb3 (o := 1264) (n := 1264) (by omega)
    (by
      rw [show st3.data.regs.X0 = st3.data.regs.getXReg .X0 from rfl, g0']
      show st2.data.regs.SP.toBitVec + _ = _
      rw [hsp2])
    (by show (st3.data.regs.getXReg .X2).toBitVec.toNat = _; rw [g2']; rfl)
    fun st4 hpc4 hb4 hsv4 _ ↦ ?_
  -- `b2`: to `.L2`
  refine regs_step (infix_of b2_in_code (by simp [b2]) hp) run_b2 (rk run_b2) hb4
    (pc_of hpc4 rfl) fun st5 hm5 hpc5 hb5 _ hr5 ↦ ?_
  have g8 := hm5.regs .X8 _ rfl
  have g22 := hm5.regs .X22 _ rfl
  have g23 := hm5.regs .X23 _ rfl
  have g24 := hm5.regs .X24 _ rfl
  sym_simp at g8 g22 g23 g24
  simp only [PcOk] at hpc5
  refine .done _ ⟨hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b4Offset) NativeRustcVmArm.Vm.PlacementsOf.label_2_at), hb5, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, fun q hq ↦ absurd hq (by simp [below]), fun q hq ↦ absurd hq (by simp [below])⟩
  · show (st5.data.regs.getXReg .X8).toBitVec.toNat = _; rw [g8]; rfl
  · show (st5.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [hr5 .X21 rfl, hsv4 .X21 rfl, hr3 .X21 rfl, hsv2 .X21 rfl, g21]; rfl
  · show (st5.data.regs.getXReg .X22).toBitVec.toNat = _; rw [g22]; rfl
  · apply UInt64.toBitVec_inj.mp
    show (st5.data.regs.getXReg .X19).toBitVec = _
    rw [hr5 .X19 rfl, hsv4 .X19 rfl, hr3 .X19 rfl, hsv2 .X19 rfl]; exact g19
  · apply UInt64.toBitVec_inj.mp
    show (st5.data.regs.getXReg .X20).toBitVec = _
    rw [hr5 .X20 rfl, hsv4 .X20 rfl, hr3 .X20 rfl, hsv2 .X20 rfl]; exact g20
  · show (st5.data.regs.getXReg .X23).toBitVec = _; rw [g23]; rfl
  · show (st5.data.regs.getXReg .X24).toBitVec = _; rw [g24]; rfl
  · show (st5.data.regs.getXReg .X25).toBitVec = _
    rw [hr5 .X25 rfl, hsv4 .X25 rfl, hr3 .X25 rfl, hsv2 .X25 rfl, g25, Layout.ofInt_zero,
      BitVec.add_zero]; rfl
  · show (st5.data.regs.getXReg .X26).toBitVec = _
    rw [hr5 .X26 rfl, hsv4 .X26 rfl, g26]
    show st2.data.regs.SP.toBitVec + _ = _
    rw [hsp2]

/-- **The first loop**, from `.L2` at column `c` to `.L6` with every column tested. -/
theorem loop1 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b4Offset)) (hI : I1 m0 c c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b8Offset) ∧ I1 m0 158 158 s.data)
      st := by
  refine Sym.loop (fun n s ↦ ∃ c, c < 158 ∧ 158 - c = n ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b4Offset) ∧
      I1 m0 c c s.data) (fun n s ⟨c, hc, hn, hpc, hI⟩ ↦ ?_) ⟨c, hc, rfl, hpc, hI⟩
  refine Eventually.bind (turn1 hp hF hc hpc hI) fun s1 ⟨hpc1, hI1⟩ ↦ ?_
  refine Eventually.mono (l1 hp hc hpc1 hI1) fun s2 h ↦ ?_
  rcases h with ⟨hlt, hpc2, hI2⟩ | ⟨_, hpc2, hI2⟩
  · exact Or.inr ⟨158 - (c + 1), by omega, c + 1, hlt, rfl, hpc2, hI2⟩
  · exact Or.inl ⟨hpc2, hI2⟩

end

end NativeRustcVmArm.Layout.PlacementsOf
