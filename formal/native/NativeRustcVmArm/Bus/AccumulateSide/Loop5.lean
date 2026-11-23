module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Bus.AccumulateSide.Loop4

/-!
# `accumulate_side`: the table loop's backedge

`b37` accumulates the padding term, decrements the remaining block count, and either starts the next turn or leaves the loop.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

@[expose] def L37kept : List (Sym × Nat) :=
  [(.reg .X20, 12), (.reg .X26, 13), (.reg .X27, 198), (.reg .X28, 199),
    (.load 0 136 8, 190), (.load 0 144 8, 191)] ++ DLf0

@[expose] def L37new : List (Sym × Nat) :=
  [(.reg .X12, 197), (.reg .X21, 193), (.reg .X22, 192), (.reg .X29, 200)]

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

private theorem holds_next {rs : List (BitVec 64 × Nat)} {m : MachineData} {j : Nat}
    (h : Holds rs (TT SL m0 L rows bl Fm j) (shiftD DL) m) :
    Holds rs (TT SL m0 L rows bl Fm (j + 1)) DL m := by
  intro p hp
  have h' := h (p.1, shiftI p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  refine h'.trans ?_
  simp only [DL, DLr, DLf, DLf0, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false,
    or_assoc] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- **`b37`**: finish one table block and choose the next PC. -/
theorem turn37 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L37 m) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm (j + 1)) DL m2 → KeepF m0 m m2 →
      Eventually (step1 Host.exe) R ⟨m2, if j + 1 < bl.length then Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset)
        else Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b38Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b37Offset)⟩ := by
  have h51 := bl_size h
  have hH0 := St.lift (D := L37) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b37_in_code.trans hp.1 (by simp [b37])) run_b37 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := L37kept) (E := L37new) (by decide) (by decide)
    (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [L37new, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl
    · rw [tval_reg_of hm' rfl]
      rfl
    · change st.regs.getXReg .X21 = _
      rw [reg_eor hH0 hm' rfl (i := 113) (j := 93) (by decide) (by decide)]
      change (pterm SL m0 (BA L rows bl) j).c1 ^^^ (sta SL m0 (BA L rows bl) Fm j).2.c1 =
        (sta SL m0 (BA L rows bl) Fm (j + 1)).2.c1
      simp only [sta, stAt_succ, stepT, add_c1]
      exact UInt64.xor_comm _ _
    · change st.regs.getXReg .X22 = _
      rw [reg_eor hH0 hm' rfl (i := 112) (j := 92) (by decide) (by decide)]
      change (pterm SL m0 (BA L rows bl) j).c0 ^^^ (sta SL m0 (BA L rows bl) Fm j).2.c0 =
        (sta SL m0 (BA L rows bl) Fm (j + 1)).2.c0
      simp only [sta, stAt_succ, stepT, add_c0]
      exact UInt64.xor_comm _ _
    · rw [tval_reg_of hm' rfl]
      change UInt64.ofBitVec (BinOp.apply .sub .W64
        ((Sym.reg .X29).eval (Env.ofMachine m [(base m0 F, F + 0)])) (BitVec.ofNat 64 1)) = _
      rw [Holds.evc hH0 (i := 100) (by decide)]
      apply UInt64.toBitVec_inj.mp
      change BinOp.apply .sub .W64 (((BA L rows bl).size - j).toUInt64.toBitVec) (BitVec.ofNat 64 1) =
        ((BA L rows bl).size - (j + 1)).toUInt64.toBitVec
      rw [BA_size]
      apply BitVec.eq_of_toNat_eq
      have ha : (UInt64.ofNat (bl.length - j)).toBitVec.toNat = bl.length - j :=
        UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
      have hb : (UInt64.ofNat (bl.length - (j + 1))).toBitVec.toNat = bl.length - (j + 1) :=
        UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat,
        Nat.toUInt64, ha, hb]
      omega
  · have hd : Holds _ (TT SL m0 L rows bl Fm j) (shiftD DL) st.data :=
      Holds.sub hst'.hd (by decide)
    have hnext := holds_next hd
    have he : SBool.eval (Env.ofMachine m [(base m0 F, F + 0)])
        (.cmp .eq .W64 (.reg .X29) (.lit 1)) = decide (bl.length - j = 1) := by
      have he := cmp_eq_lit _ (Holds.evc hH0 (s := .reg .X29) (i := 100) (by decide))
        (by decide : 1 < 2 ^ 64)
      change SBool.eval _ _ = decide (((BA L rows bl).size - j).toUInt64.toNat = 1) at he
      rw [BA_size, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)] at he
      exact he
    have hc : SBool.eval (Env.ofMachine m [(base m0 F, F + 0)])
        (.not (.cmp .eq .W64 (.reg .X29) (.lit 1))) = decide (j + 1 < bl.length) := by
      change Bool.not (SBool.eval _ (.cmp .eq .W64 (.reg .X29) (.lit 1))) = _
      rw [he]
      by_cases hn : j + 1 < bl.length
      · simp [hn, show bl.length - j ≠ 1 by omega]
      · simp [hn, show bl.length - j = 1 by omega]
    simp only [PcOk, hc] at hpc
    rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b27Offset) NativeRustcVmArm.Vm.AccumulateSide.label_17_at,
      show k + NativeRustcVmArm.Vm.AccumulateSide.b37Offset + b37.length = k + NativeRustcVmArm.Vm.AccumulateSide.b38Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b37_next]] at hpc
    have hp' : st.pc = if j + 1 < bl.length then Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset) else Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b38Offset) := by
      simpa only [decide_eq_true_eq] using hpc
    exact Gkr.at_pc hp' (cont st.data ⟨hst'.fr, hnext⟩ fun G hG ↦
      forms_wrOk h (.inl rfl) hm' hwf (by decide) hG)

end

end NativeRustcVmArm.Bus.AccumulateSide
