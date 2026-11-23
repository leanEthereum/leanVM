module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.BuildLayout.Names
public import NativeRustcVmArm.Code.Vm.ColumnKappas.Names
public import NativeRustcVmArm.Code.Vm.PlacementsOf.Names
public import NativeRustcVmArm.Layout.BuildLayout.Checks
public import NativeRustcVmArm.Layout.BuildLayout.Finish

/-!
# `build_layout`

**`buildLayout_spec`**: rustc's `build_layout(bytecode_len, log_memory, table_rows, layout)`,
placed anywhere in the program, meets `BuildLayoutPre`/`BuildLayoutPost` given the contracts of
`bit_length`, `column_kappas` and `placements_of`. `b0` tests the bytecode's length a power of two
(`b19` returns `0`); the prologue (`b1`) saves X19-X30 and calls `bit_length`; the checks
(`checks`), the stores (`stores`), `column_kappas` (`kappas`), `placements_of` and the return
(`finish`) follow. The model's `buildLayout` is `layoutF` exactly when the code's checks pass
(`model_some`, `model_none`, from `NativeVm.Math.Layout.buildLayout_eq`).
-/

namespace NativeRustcVmArm.Layout.BuildLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BuildLayout
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

/-! ## The model -/

theorem rowsOf_size (m0 : MachineData) : (rowsOf m0).size = 6 := by simp [natsOf, nTables]

theorem rows_all (m0 : MachineData) :
    (rowsOf m0).all (· ≤ 2 ^ 30) = true ↔ ∀ t < 6, (rowW m0 t).toNat ≤ 2 ^ 30 := by
  rw [Array.all_eq_true]
  constructor
  · intro h t ht
    have := h t (by rw [rowsOf_size]; exact ht)
    rw [getElem_getD (by rw [rowsOf_size]; exact ht), rows_getD m0 ht] at this
    simpa using this
  · intro h t ht
    rw [rowsOf_size] at ht
    rw [getElem_getD (by rw [rowsOf_size]; exact ht), rows_getD m0 ht]
    simpa using h t ht

/-- The code's checks. -/
abbrev Chk (m0 : MachineData) : Prop :=
  5 ≤ bitLength m0.regs.X0.toNat ∧ 1 ≤ m0.regs.X1.toNat ∧ m0.regs.X1.toNat ≤ 30 ∧
    (∀ t < 6, (rowW m0 t).toNat ≤ 2 ^ 30) ∧ bitLength m0.regs.X0.toNat - 5 ≤ 30

/-- The length a power of two. -/
abbrev Pow2 (n : Nat) : Prop := 0 < n ∧ n &&& (n - 1) = 0

theorem busBits_eq : busBits = 4 := rfl

theorem model_some {bc : Array UInt64} {m0 : MachineData} (hsz : m0.regs.X0.toNat = bc.size)
    (hp2 : Pow2 m0.regs.X0.toNat) (hc : Chk m0) :
    buildLayout bc m0.regs.X1.toNat (rowsOf m0) =
      some (layoutF bc m0.regs.X1.toNat (bitLength m0.regs.X0.toNat - 5) (rowsOf m0)) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc
  rw [buildLayout_eq, ite_true_of ⟨by rw [← hsz]; exact hp2, by rw [busBits_eq, ← hsz]; omega, c2, c3,
    (rows_all m0).mpr c4, by rw [busBits_eq, ← hsz]; omega, rowsOf_size m0⟩, ← hsz, busBits_eq,
    show bitLength m0.regs.X0.toNat - 1 - 4 = bitLength m0.regs.X0.toNat - 5 by omega]

theorem model_none {bc : Array UInt64} {m0 : MachineData} (hsz : m0.regs.X0.toNat = bc.size)
    (hc : ¬(Pow2 m0.regs.X0.toNat ∧ Chk m0)) :
    buildLayout bc m0.regs.X1.toNat (rowsOf m0) = none := by
  rw [buildLayout_eq, ite_false_of]
  rintro ⟨c0, c1, c2, c3, c4, c5, -⟩
  rw [← hsz] at c0 c1 c5
  rw [busBits_eq] at c1 c5
  exact hc ⟨c0, by omega, c2, c3, (rows_all m0).mp c4, by omega⟩

/-- The words `b9` to `b14` stored, as the model's. -/
theorem ws_conv {d : Mem 64} {a : BitVec 64} {x19 x20 x24 x25 x26 x27 x28 : UInt64} {lm lb : Nat}
    {rows : Array Nat} (e19 : x19.toNat = lm) (e20 : x20.toNat = lb)
    (e24 : x24.toNat = rows.getD 4 0) (e25 : x25.toNat = rows.getD 3 0)
    (e26 : x26.toNat = rows.getD 2 0) (e27 : x27.toNat = rows.getD 1 0)
    (e28 : x28.toNat = rows.getD 0 0)
    (h : Ws d a [(56, hw x24), (104, x24), (48, hw x25), (96, x25), (40, hw x26), (88, x26),
      (32, hw x27), (80, x27), (24, hw x28), (72, x28), (0, x19), (8, x20)]) :
    Ws d a (wsL lm lb rows) := by
  have q4 : hw x24 = hgt rows 4 := by simp only [hw, hgt, e24]
  have q3 : hw x25 = hgt rows 3 := by simp only [hw, hgt, e25]
  have q2 : hw x26 = hgt rows 2 := by simp only [hw, hgt, e26]
  have q1 : hw x27 = hgt rows 1 := by simp only [hw, hgt, e27]
  have q0 : hw x28 = hgt rows 0 := by simp only [hw, hgt, e28]
  rw [q4, q3, q2, q1, q0, u64_eq e24, u64_eq e25, u64_eq e26, u64_eq e27, u64_eq e28, u64_eq e19,
    u64_eq e20] at h
  exact h

theorem bitLength_pos {n : Nat} (h : 0 < n) : 1 ≤ bitLength n := by
  unfold bitLength; split <;> omega

variable [Host] {k : Nat}

/-- **`build_layout` meets its contract.** -/
theorem buildLayout_spec (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hck : Spec (Labels.label NativeRustcVmArm.Vm.ColumnKappas.entryLabel) ColumnKappasPre ColumnKappasPost)
    (hpl : Spec (Labels.label NativeRustcVmArm.Vm.PlacementsOf.entryLabel) PlacementsOfPre PlacementsOfPost)
    {bc : Array UInt64} :
    Spec (Labels.label NativeRustcVmArm.Vm.BuildLayout.entryLabel) (BuildLayoutPre bc) (BuildLayoutPost bc) := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  have hS := hF.stack
  have hsz := hF.size
  obtain ⟨hwf, hm⟩ := Arrays.entry_match hS (F := 1360) (by decide) (by decide)
  rw [show Labels.label NativeRustcVmArm.Vm.BuildLayout.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.BuildLayout.entryOffset) NativeRustcVmArm.Vm.BuildLayout.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st0 hm0 hpc0 ↦ ?_
  simp only [PcOk] at hpc0
  sym_simp at hpc0
  obtain ⟨f0, t0⟩ := Arrays.pc_cond hpc0
  have c0 := pow2_test ((Arrays.frameEnv m0 m0 1360).regs .X0)
  by_cases hpow : Pow2 m0.regs.X0.toNat
  swap
  · -- not a power of two: `b19` returns `0`
    have hpc1 := (f0 (c0.mpr hpow)).trans (hp.label (j := NativeRustcVmArm.Vm.BuildLayout.b19Offset) NativeRustcVmArm.Vm.BuildLayout.label_10_at)
    refine exec_at (infix_of b19_in_code (by simp [b19]) hp) (Arrays.exec_after run_b0 run_b19) hwf
      hpc1 hm0 fun st1 hm1 hpc2 ↦ .done _ ?_
    have hnone := model_none (bc := bc) hsz fun h ↦ hpow h.1
    have hdm := hm1.dmem_eq hwf (Arrays.after_eq run_b19 ▸ b19_keeps).2
    refine ⟨?_, ?_, fun L hL ↦ absurd hL (by rw [hnone]; nofun), ?_,
      Match.saved hm hm1 hwf rfl (Arrays.after_eq run_b19 ▸ b19_keeps).1⟩
    · simp only [PcOk] at hpc2; exact hpc2.trans (retOf_of_x30 hm1 rfl rfl)
    · rw [hnone]; exact UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)
    · exact NativeRustcVm.SameOutside.of_eq hdm _
  -- the prologue and `bit_length(n)`
  have hpc1 := pc_of (t0 fun h ↦ c0.mp h hpow) (show k + NativeRustcVmArm.Vm.BuildLayout.b0Offset + b0.length = k + NativeRustcVmArm.Vm.BuildLayout.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b0_next])
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (Arrays.exec_after run_b0 run_b1) hwf hpc1
    hm0 fun st1 hm1 hpc2 ↦ ?_
  obtain ⟨hw, hmem, hregs⟩ := Arrays.after_eq run_b1 ▸ b1_frame
  have hb1 : Bd m0 st1.data := Arrays.Body.of_entry hS (by decide) hm1 rfl hw hregs hmem
  have e0 : st1.data.regs.getXReg .X0 = m0.regs.getXReg .X0 := Match.reg_eq hm hm1 rfl rfl
  have e19 : st1.data.regs.getXReg .X19 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl)
  have e21 : st1.data.regs.getXReg .X21 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have e22 : st1.data.regs.getXReg .X22 = m0.regs.X3 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  refine call_then hpc2 hbl trivial fun st2 hpc3 hpost ↦ ?_
  have hb2 : Bd m0 st2.data := Body.of_call_stack (G := 96) hb1 hpost.2.1
    (fun p hp ↦ absurd hp (by unfold InRange bitLengthStack; omega)) hpost.2.2 slots_top (by decide)
    hF.sp
  have hx0 : st2.data.regs.X0.toNat = bitLength m0.regs.X0.toNat := by
    rw [hpost.1]; exact congrArg (fun x : UInt64 ↦ bitLength x.toNat) e0
  -- the checks
  refine checks hp hF (pc_of hpc3 rfl) hb2 ((hpost.2.2.1 .X19 rfl).trans e19)
    ((hpost.2.2.1 .X21 rfl).trans e21) ((hpost.2.2.1 .X22 rfl).trans e22) hx0
    (bitLength_pos hpow.1) (fun h ↦ model_none hsz fun hc ↦ h hc.2)
    fun s hpc hb h22 h19 h20 x28 x27 x26 x25 x24 x23 g5 g30 gl1 gl30 gr ↦ ?_
  have hr : ∀ t < 6, (rowsOf m0).getD t 0 ≤ 2 ^ 30 := fun t ht ↦ by
    rw [rows_getD m0 ht]; exact gr t ht
  have hres := model_some hsz hpow ⟨g5, gl1, gl30, gr, g30⟩
  -- the stores, `column_kappas`, `placements_of`, the return
  refine stores hp hbl hF hpc hb h22 fun s6 hpc6 hb6 h22' h21' hk6 hx6 hW6 ↦ ?_
  have r : ∀ {x : UInt64} {t : Nat}, x = rowW m0 t → t < 6 → x.toNat = (rowsOf m0).getD t 0 :=
    fun h ht ↦ by rw [h, rows_getD m0 ht]
  refine kappas hp hck hF (rowsOf_size m0) hr hpc6 hb6 h22' h21'
    (by rw [hk6 .X19 (by simp), h19]) (by rw [hk6 .X20 (by simp)]; exact h20)
    (by rw [hk6 .X23 (by simp)]; exact u64_eq (r x23 (by decide)))
    (by rw [hx6, r x23 (by decide)])
    (ws_conv (by rw [h19]) h20 (r x24 (by decide)) (r x25 (by decide)) (r x26 (by decide))
      (r x27 (by decide)) (r x28 (by decide)) hW6)
    fun s7 hpc7 hb7 h22'' h21'' hW7 hK7 ↦ ?_
  exact finish hp hpl hF (rowsOf_size m0) gl30 g30 hr hres hpc7 hb7 h22'' h21'' hW7 hK7

end

end NativeRustcVmArm.Layout.BuildLayout
