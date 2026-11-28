module

public import NativeRustcVmArm.Code.Vm.BuildLayout.Names
public import NativeRustcVmArm.Layout.BuildLayout.Base

/-!
# `build_layout`: the size checks (`b2` to `b8`)

After `bit_length(n)`: the bytecode's bit length at least `5` and the memory's log-size in
`1 … 30` (`b2`), each row count at most `2 ^ 30` (`b3` to `b8`), the bytecode's log-size at most
`30` (`b8`). A failed check returns `0` (`fail`); else the row counts are in X28 to X23 and the
log-sizes in X19, X20 (`checks`).
-/

namespace NativeRustcVmArm.Layout.BuildLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BuildLayout
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier
open NativeRustcVm (WordAt WordsAt addr_add_add addr_add_zero toNat_add_ofNat wordOf)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

/-- Row count `t`, a word of the entry's memory. -/
abbrev rowW (m0 : MachineData) (t : Nat) : UInt64 := wordOf m0.dmem (rp m0 + BitVec.ofNat 64 (8 * t))

variable [Host] {k : Nat}

theorem frame_rows_wf {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0) {st : MachineData}
    (hb : Bd m0 st) : (Env.ofMachine st [(fb m0, 1360), (rp m0, 48)]).WF := by
  have hfr := Arrays.frame_ok hF.stack (F := 1360) (by decide)
  exact Env.wf_of ⟨⟨fun i hi ↦ hb.kept _ (hfr.1 i hi), hfr.2.1⟩,
    ⟨fun i hi ↦ hb.kept _ (hF.rr.1 i hi), hF.rr.2⟩, trivial⟩
    (List.pairwise_pair.mpr (Layout.apart_frame hF.stack (by decide) hF.ro))

/-- Row count `t` loaded in a body. -/
theorem row_load {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0) {st : MachineData}
    (hb : Bd m0 st) {t : Nat} (ht : t < 6) :
    (Env.ofMachine st [(fb m0, 1360), (rp m0, 48)]).load 1 (8 * t) 8 = (rowW m0 t).toBitVec := by
  rw [Arrays.load8_eq]
  show (wordOf st.dmem (rp m0 + BitVec.ofNat 64 (8 * t))).toBitVec = _
  rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ by
    rw [addr_add_add]
    exact Arrays.same_of_apart hb.same hF.stack hF.rr.2 hF.ro hF.ap hF.lr.2 _ (by omega)]

omit [Host] in
theorem rows_getD (m0 : MachineData) {t : Nat} (ht : t < 6) :
    (rowsOf m0).getD t 0 = (rowW m0 t).toNat :=
  Layout.natsOf_getD m0 m0.regs.X2 ht

/-- **The checks.** -/
theorem checks (hp : Placed code k) {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b2Offset)) (hbd : Bd m0 st.data)
    (h19 : st.data.regs.getXReg .X19 = m0.regs.X1) (h21 : st.data.regs.getXReg .X21 = m0.regs.X2)
    (h22 : st.data.regs.getXReg .X22 = m0.regs.X3) {bl : Nat}
    (hx0 : st.data.regs.X0.toNat = bl) (hbl1 : 1 ≤ bl)
    (hnone : ¬(5 ≤ bl ∧ 1 ≤ m0.regs.X1.toNat ∧ m0.regs.X1.toNat ≤ 30 ∧
      (∀ t < 6, (rowW m0 t).toNat ≤ 2 ^ 30) ∧ bl - 5 ≤ 30) →
      buildLayout bc m0.regs.X1.toNat (rowsOf m0) = none)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b9Offset) → Bd m0 st'.data →
      st'.data.regs.getXReg .X22 = m0.regs.X3 → st'.data.regs.getXReg .X19 = m0.regs.X1 →
      (st'.data.regs.getXReg .X20).toNat = bl - 5 →
      st'.data.regs.getXReg .X28 = rowW m0 0 → st'.data.regs.getXReg .X27 = rowW m0 1 →
      st'.data.regs.getXReg .X26 = rowW m0 2 → st'.data.regs.getXReg .X25 = rowW m0 3 →
      st'.data.regs.getXReg .X24 = rowW m0 4 → st'.data.regs.getXReg .X23 = rowW m0 5 →
      5 ≤ bl → bl - 5 ≤ 30 → 1 ≤ m0.regs.X1.toNat → m0.regs.X1.toNat ≤ 30 →
      (∀ t < 6, (rowW m0 t).toNat ≤ 2 ^ 30) →
      Eventually (step1 Host.exe) (Post bc m0) st') :
    Eventually (step1 Host.exe) (Post bc m0) st := by
  have hS := hF.stack
  have hwf := frame_rows_wf hF hbd
  have hm : Match (Env.ofMachine st.data [(fb m0, 1360), (rp m0, 48)]) rowsS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Arrays.frame_aligned hS (by decide) rfl, rfl, nofun, trivial⟩
      (by show _ = fb m0 + BitVec.ofInt 64 0; rw [Layout.ofInt_zero, BitVec.add_zero]; exact hbd.sp)
      ⟨by show _ = rp m0 + BitVec.ofInt 64 0; rw [Layout.ofInt_zero, BitVec.add_zero]
          exact congrArg UInt64.toBitVec h21, trivial⟩ trivial trivial trivial
  have ld := fun {t : Nat} (ht : t < 6) ↦ row_load hF hbd ht
  have L11 : Labels.label NativeRustcVmArm.Vm.BuildLayout.label_11 = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b20Offset) := hp.label (j := NativeRustcVmArm.Vm.BuildLayout.b20Offset) NativeRustcVmArm.Vm.BuildLayout.label_11_at
  have kb : ∀ {S' : SState} {st' : MachineData},
      Match (Env.ofMachine st.data [(fb m0, 1360), (rp m0, 48)]) S' st' →
      keepsAll rowsS S' keptRegs = true → Bd m0 st' := fun hm' hk ↦
    hbd.of_block hm hm' hwf rfl hk
  have mem : ∀ {S : SState} {l : List SState}, S ∈ S :: l := List.mem_cons_self
  let env := Env.ofMachine st.data [(fb m0, 1360), (rp m0, 48)]
  have l0 : env.load 1 0 8 = (rowW m0 0).toBitVec := ld (t := 0) (by decide)
  have l1 : env.load 1 8 8 = (rowW m0 1).toBitVec := ld (t := 1) (by decide)
  have l2 : env.load 1 16 8 = (rowW m0 2).toBitVec := ld (t := 2) (by decide)
  have l3 : env.load 1 24 8 = (rowW m0 3).toBitVec := ld (t := 3) (by decide)
  have l4 : env.load 1 32 8 = (rowW m0 4).toBitVec := ld (t := 4) (by decide)
  have l5 : env.load 1 40 8 = (rowW m0 5).toBitVec := ld (t := 5) (by decide)
  have hy : (env.regs .X19).toNat = m0.regs.X1.toNat := by
    rw [Env.ofMachine_regs, h19]; rfl
  have nult : ∀ (x : UInt64), (x.toBitVec.toNat < (1073741825#64).toNat) ↔ x.toNat ≤ 2 ^ 30 := by
    intro x; show x.toNat < 1073741825 ↔ _; omega
  -- `b2`
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf hpc hm fun s2 hm2 hpc2 ↦ ?_
  have hb2 := kb hm2 (Arrays.after_eq run_b2 ▸ chk_all _ mem)
  simp only [PcOk] at hpc2
  sym_simp at hpc2
  obtain ⟨f2, t2⟩ := Arrays.pc_cond hpc2
  have c2 := cond2 (env.regs .X0) (env.regs .X19) bl hx0 hbl1
  rw [hy] at c2
  by_cases g2 : 5 ≤ bl ∧ 1 ≤ m0.regs.X1.toNat ∧ m0.regs.X1.toNat ≤ 30
  swap
  · exact fail hp hF ((f2 (c2.mpr g2)).trans L11) hb2 (hnone fun h ↦ g2 ⟨h.1, h.2.1, h.2.2.1⟩)
  have hpc2' := pc_of (t2 fun h ↦ c2.mp h g2) (show k + NativeRustcVmArm.Vm.BuildLayout.b2Offset + b2.length = k + NativeRustcVmArm.Vm.BuildLayout.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b2_next])
  -- `b3`
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (Arrays.exec_after run_b2 run_b3) hwf hpc2'
    hm2 fun s3 hm3 hpc3 ↦ ?_
  have hb3 := kb hm3 (Arrays.after_eq run_b3 ▸ chk_all _ (List.mem_cons_of_mem _ mem))
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  rw [l0] at hpc3
  obtain ⟨f3, t3⟩ := Arrays.pc_cond hpc3
  by_cases g3 : (rowW m0 0).toNat ≤ 2 ^ 30
  swap
  · exact fail hp hF ((f3 ((cond3 _).mpr g3)).trans L11) hb3 (hnone fun h ↦ g3 (h.2.2.2.1 0 (by decide)))
  have hpc3' := pc_of (t3 fun h ↦ (cond3 _).mp h g3) (show k + NativeRustcVmArm.Vm.BuildLayout.b3Offset + b3.length = k + NativeRustcVmArm.Vm.BuildLayout.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b3_next])
  -- `b4`
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) (Arrays.exec_after run_b3 run_b4) hwf hpc3'
    hm3 fun s4 hm4 hpc4 ↦ ?_
  have hb4 := kb hm4 (Arrays.after_eq run_b4 ▸ chk_all _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem)))
  simp only [PcOk] at hpc4
  sym_simp at hpc4
  rw [l1] at hpc4
  obtain ⟨f4, t4⟩ := Layout.pc_nult hpc4
  by_cases g4 : (rowW m0 1).toNat ≤ 2 ^ 30
  swap
  · exact fail hp hF ((f4 (by rw [nult]; exact g4)).trans L11) hb4
      (hnone fun h ↦ g4 (h.2.2.2.1 1 (by decide)))
  have hpc4' := pc_of (t4 ((nult _).mpr g4)) (show k + NativeRustcVmArm.Vm.BuildLayout.b4Offset + b4.length = k + NativeRustcVmArm.Vm.BuildLayout.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b4_next])
  -- `b5`
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (Arrays.exec_after run_b4 run_b5) hwf hpc4'
    hm4 fun s5 hm5 hpc5 ↦ ?_
  have hb5 := kb hm5 (Arrays.after_eq run_b5 ▸ chk_all _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem))))
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  rw [l2] at hpc5
  obtain ⟨f5, t5⟩ := Layout.pc_nult hpc5
  by_cases g5 : (rowW m0 2).toNat ≤ 2 ^ 30
  swap
  · exact fail hp hF ((f5 (by rw [nult]; exact g5)).trans L11) hb5
      (hnone fun h ↦ g5 (h.2.2.2.1 2 (by decide)))
  have hpc5' := pc_of (t5 ((nult _).mpr g5)) (show k + NativeRustcVmArm.Vm.BuildLayout.b5Offset + b5.length = k + NativeRustcVmArm.Vm.BuildLayout.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b5_next])
  -- `b6`
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) (Arrays.exec_after run_b5 run_b6) hwf hpc5'
    hm5 fun s6 hm6 hpc6 ↦ ?_
  have hb6 := kb hm6 (Arrays.after_eq run_b6 ▸ chk_all _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem)))))
  simp only [PcOk] at hpc6
  sym_simp at hpc6
  rw [l3] at hpc6
  obtain ⟨f6, t6⟩ := Layout.pc_nult hpc6
  by_cases g6 : (rowW m0 3).toNat ≤ 2 ^ 30
  swap
  · exact fail hp hF ((f6 (by rw [nult]; exact g6)).trans L11) hb6
      (hnone fun h ↦ g6 (h.2.2.2.1 3 (by decide)))
  have hpc6' := pc_of (t6 ((nult _).mpr g6)) (show k + NativeRustcVmArm.Vm.BuildLayout.b6Offset + b6.length = k + NativeRustcVmArm.Vm.BuildLayout.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b6_next])
  -- `b7`
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (Arrays.exec_after run_b6 run_b7) hwf hpc6'
    hm6 fun s7 hm7 hpc7 ↦ ?_
  have hb7 := kb hm7 (Arrays.after_eq run_b7 ▸ chk_all _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ mem))))))
  simp only [PcOk] at hpc7
  sym_simp at hpc7
  rw [l4] at hpc7
  obtain ⟨f7, t7⟩ := Layout.pc_nult hpc7
  by_cases g7 : (rowW m0 4).toNat ≤ 2 ^ 30
  swap
  · exact fail hp hF ((f7 (by rw [nult]; exact g7)).trans L11) hb7
      (hnone fun h ↦ g7 (h.2.2.2.1 4 (by decide)))
  have hpc7' := pc_of (t7 ((nult _).mpr g7)) (show k + NativeRustcVmArm.Vm.BuildLayout.b7Offset + b7.length = k + NativeRustcVmArm.Vm.BuildLayout.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b7_next])
  -- `b8`
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (Arrays.exec_after run_b7 run_b8) hwf hpc7'
    hm7 fun s8 hm8 hpc8 ↦ ?_
  have hb8 := kb hm8 (Arrays.after_eq run_b8 ▸ chk_keeps.1)
  simp only [PcOk] at hpc8
  sym_simp at hpc8
  rw [l5] at hpc8
  obtain ⟨f8, t8⟩ := Arrays.pc_cond hpc8
  have c8 := cond8 (env.regs .X0) (rowW m0 5).toBitVec bl hx0 g2.1
  by_cases g8 : bl - 5 ≤ 30 ∧ (rowW m0 5).toNat ≤ 2 ^ 30
  swap
  · exact fail hp hF ((f8 (c8.mpr g8)).trans L11) hb8
      (hnone fun h ↦ g8 ⟨h.2.2.2.2, h.2.2.2.1 5 (by decide)⟩)
  have hpc8' := pc_of (t8 fun h ↦ c8.mp h g8) (show k + NativeRustcVmArm.Vm.BuildLayout.b8Offset + b8.length = k + NativeRustcVmArm.Vm.BuildLayout.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b8_next])
  have hk8 := Arrays.regs_eq_of hm hm8 [.X19, .X22] (Arrays.after_eq run_b8 ▸ chk_keeps.2)
  have x28 : s8.data.regs.getXReg .X28 = rowW m0 0 :=
    UInt64.toBitVec_inj.mp ((hm8.regs .X28 _ rfl).trans l0)
  have x27 : s8.data.regs.getXReg .X27 = rowW m0 1 :=
    UInt64.toBitVec_inj.mp ((hm8.regs .X27 _ rfl).trans l1)
  have x26 : s8.data.regs.getXReg .X26 = rowW m0 2 :=
    UInt64.toBitVec_inj.mp ((hm8.regs .X26 _ rfl).trans l2)
  have x25 : s8.data.regs.getXReg .X25 = rowW m0 3 :=
    UInt64.toBitVec_inj.mp ((hm8.regs .X25 _ rfl).trans l3)
  have x24 : s8.data.regs.getXReg .X24 = rowW m0 4 :=
    UInt64.toBitVec_inj.mp ((hm8.regs .X24 _ rfl).trans l4)
  have x23 : s8.data.regs.getXReg .X23 = rowW m0 5 :=
    UInt64.toBitVec_inj.mp ((hm8.regs .X23 _ rfl).trans l5)
  refine cont s8 hpc8' hb8 ((hk8 .X22 (by simp)).trans h22) ((hk8 .X19 (by simp)).trans h19) ?_
    x28 x27 x26 x25 x24 x23
    g2.1 g8.1 g2.2.1 g2.2.2 ?_
  · have := hm8.regs .X20 _ rfl
    sym_simp at this
    show (s8.data.regs.getXReg .X20).toBitVec.toNat = _
    rw [this, BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]; show 5 % 2 ^ 64 ≤ st.data.regs.X0.toNat; omega)]
    show st.data.regs.X0.toNat - 5 % 2 ^ 64 = _
    omega
  · intro t ht
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g3, g4, g5, g6, g7, g8.2]

end

end NativeRustcVmArm.Layout.BuildLayout
