module

public import NativeRustcVmArm.Code.Vm.InsD.Names
public import NativeRustcVmArm.Wire.InsD.Shift

/-!
# `ins_d` meets its contract

`insD_spec`: the scan (`b1`, `b2`, `SInv`) finds the first element at least `x`: `x` itself, the
count back (`b4`, `b5`); else `x` at the end (`b3`) or, after the shift (`b6`, `six_spec`), in
place. The elements are those of the words `L` the array holds (`exists_wordsAt`), any list the
caller gives being theirs (`post_of`).
-/

namespace NativeRustcVmArm.Wire.InsD

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmArm.Vm.InsD

public section

variable [Host] {k : Nat} {m : MachineData} {L : List UInt64}

section
variable (hp : Placed code k)
  (hok : NativeRustcVm.Mapped m.dmem (arr m) 2048 ∧ NativeRustcVm.NoWrap (arr m) 2048)
  (hL : L.length = m.regs.X1.toNat) (hn : L.length < 256) (hW : WordsAt m.dmem (arr m) L)
  {g : UInt64} (hW' : WordsAt m.dmem (arr m) (L ++ [g]))
include hp hok hL hn hW hW'

/-- **`x` at the end** (`b3`): every element below it. -/
theorem end_spec {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsD.b3Offset)) (hk : Kp m st.data)
    (hd : st.data.dmem = m.dmem) (hb : Below m L L.length) :
    Eventually (step1 Host.exe) (Post m) st := by
  have hwf := env1_wf hok hk hn
  have hx1 : (st.data.regs.getXReg .X1).toNat = L.length := by rw [hk.x1]; exact hL.symm
  have hm : Match (env1 m st.data L.length) endS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by rw [elem_reg]; exact elem_alias hk hn rfl hx1, trivial⟩
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf hpc hm fun st' hm' hpc' ↦ ?_
  refine .done _ (finish (g := g) hok hL hn hW hk (le_refl _) hb
    (fun h ↦ absurd h (Nat.lt_irrefl _)) ?_ hwf hm hm' rfl rfl ⟨rfl, rfl⟩ (by decide) hpc')
  rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp), hd]
  exact hW'

/-- **A step of the scan** (`b1`, then `b2` or `b4`): on past element `i`, or `x` found, or the
end, or the shift. -/
theorem scan_step {i : Nat} {st : MachineState} (hI : SInv m L k i st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ Post m st' ∨ ∃ n' < L.length - i, ∃ i', n' = L.length - i' ∧ SInv m L k i' st') st := by
  have hi : i < 256 := by have := hI.lt; omega
  have hwf := env1_wf hok hI.kp hi
  have hm : Match (env1 m st.data i) scanS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by rw [elem_reg]; exact elem_alias hI.kp hi rfl hI.x8, trivial⟩
  have hiL : i < L.length := hI.lt
  have hLi : WordAt st.data.dmem (pos m i) L[i] := by
    rw [hI.d]; exact hW.getElem hiL
  have hld : (env1 m st.data i).load 0 0 8 = L[i].toBitVec := load_pos rfl hLi
  have hx2 : ((Sym.reg .X2).eval (env1 m st.data i)).toNat = xv m := by
    show (st.data.regs.getXReg .X2).toNat = _; rw [hI.kp.x2]; rfl
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf hI.pc hm fun s1 hm1 hpc1 ↦ ?_
  have hc1 : (SBool.cmp .ult .W64 (.load 0 0 8) (.reg .X2)).not.eval (env1 m st.data i) =
      decide (xv m ≤ L[i].toNat) := by
    simp only [SBool.eval, ult_apply]
    rw [hx2]; simp only [Sym.eval, hld, UInt64.toNat_toBitVec]
    by_cases h : L[i].toNat < xv m
    · simp [h]
    · simp [h]; omega
  simp only [PcOk, hc1] at hpc1
  by_cases hlt : L[i].toNat < xv m
  · -- `b2`: on
    simp only [decide_eq_false (show ¬xv m ≤ L[i].toNat by omega), Bool.false_eq_true,
      ↓reduceIte] at hpc1
    have r2 := run_b2
    rw [after_eq run_b1] at r2
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) r2 hwf hpc1 hm1 fun s2 hm2 hpc2 ↦ ?_
    have hd2 : s2.data.dmem = st.data.dmem := hm2.dmem_eq hwf rfl
    have hkp : Kp m s2.data := hI.kp.block hm hm2 hwf rfl (by decide) (by decide)
      (by rw [hd2]; exact NativeRustcVm.SameOutside.refl _ _)
    have h8 : (s2.data.regs.getXReg .X8).toNat = i + 1 := by
      show (s2.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [hm2.regs .X8 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [toNat_add_one (by show (st.data.regs.getXReg .X8).toNat < 256; rw [hI.x8]; exact hi)]
      exact congrArg (· + 1) hI.x8
    have hb : Below m L (i + 1) := fun j hj hjn ↦ by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact hI.below j h hjn
      · exact hlt
    have hc2 : (SBool.cmp .eq .W64 (.reg .X1) (.bin .add .W64 (.reg .X8) (.lit 1))).not.eval
        (env1 m st.data i) = decide (i + 1 ≠ L.length) := by
      simp only [SBool.eval, eq_apply]
      have e1 : ((Sym.reg .X1).eval (env1 m st.data i)).toNat = L.length := by
        show (st.data.regs.getXReg .X1).toNat = _; rw [hI.kp.x1]; exact hL.symm
      have e8 : ((Sym.bin .add .W64 (.reg .X8) (.lit 1)).eval (env1 m st.data i)).toNat = i + 1 := by
        simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
        rw [toNat_add_one (by show (st.data.regs.getXReg .X8).toNat < 256; rw [hI.x8]; exact hi)]
        exact congrArg (· + 1) hI.x8
      rw [e1, e8]
      by_cases h : i + 1 = L.length
      · simp [h]
      · simp [h]; omega
    simp only [PcOk, hc2] at hpc2
    by_cases he : i + 1 = L.length
    · simp only [he, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
      refine Eventually.mono (end_spec hp hok hL hn hW hW' (hpc2.trans (congrArg Host.addrOf rfl))
        hkp (hd2.trans hI.d) (he ▸ hb)) fun _ h ↦ .inl h
    · simp only [ne_eq, he, not_false_eq_true, decide_true, ↓reduceIte, lbl hp (j := 3) rfl] at hpc2
      exact .done _ (.inr ⟨_, by omega, i + 1, rfl,
        ⟨hpc2, hkp, hd2.trans hI.d, h8, by omega, hb⟩⟩)
  · -- `b4`: found or the shift
    simp only [decide_eq_true (show xv m ≤ L[i].toNat by omega), ↓reduceIte,
      lbl hp (j := 15) rfl] at hpc1
    have r4 := run_b4
    rw [after_eq run_b1] at r4
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) r4 hwf hpc1 hm1 fun s4 hm4 hpc4 ↦ ?_
    have hd4 : s4.data.dmem = st.data.dmem := hm4.dmem_eq hwf rfl
    have hc4 : (SBool.cmp .eq .W64 (.load 0 0 8) (.reg .X2)).not.eval (env1 m st.data i) =
        decide (L[i].toNat ≠ xv m) := by
      simp only [SBool.eval, eq_apply]
      rw [hx2]; simp only [Sym.eval, hld, UInt64.toNat_toBitVec]
      by_cases h : L[i].toNat = xv m <;> simp [h]
    simp only [PcOk, hc4] at hpc4
    by_cases hne : L[i].toNat = xv m
    · -- `b5`: `x` is there
      simp only [hne, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
      have r5 := run_b5
      rw [after_eq run_b4] at r5
      refine exec_at (infix_of b5_in_code (by simp [b5]) hp) r5 hwf hpc4 hm4 fun s5 hm5 hpc5 ↦ ?_
      have hd5 : s5.data.dmem = st.data.dmem := hm5.dmem_eq hwf rfl
      have h30 : s5.data.regs.getXReg .X30 = m.regs.getXReg .X30 :=
        (Match.reg_eq hm hm5 (v := .reg .X30) rfl rfl).trans hI.kp.x30
      have hself : insD (lst L) (xv m) = lst L :=
        insD_self _ _ i (by simpa using hI.lt) (fun j hj ↦ by simpa using hI.below j hj (by omega))
          (by simpa using hne)
      simp only [PcOk] at hpc5
      refine .done _ (.inl ⟨by rw [hpc5, retOf, retOf, show s5.data.regs.X30 = m.regs.X30 from h30], ?_⟩)
      refine post_of hL hW (hI.kp.sv.trans (Match.saved hm hm5 hwf rfl (by decide)))
        (by rw [hd5, hI.d]; exact NativeRustcVm.SameOutside.refl _ _) ?_ ?_
      · rw [hself]
        show (s5.data.regs.getXReg .X0).toBitVec.toNat = _
        rw [hm5.regs .X0 (.reg .X1) rfl]
        show (st.data.regs.getXReg .X1).toNat = _
        rw [hI.kp.x1]; simp [lst, hL]; rfl
      · rw [hself, hd5, hI.d, map_toUInt64_toNat]; exact hW
    · -- the shift
      simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, lbl hp (j := 19) rfl] at hpc4
      have hkp : Kp m s4.data := hI.kp.block hm hm4 hwf rfl (by decide) (by decide)
        (by rw [hd4]; exact NativeRustcVm.SameOutside.refl _ _)
      have h8 : (s4.data.regs.getXReg .X8).toNat = i := by
        rw [Match.reg_eq hm hm4 (v := .reg .X8) rfl rfl]; exact hI.x8
      exact Eventually.mono (six_spec hp hok hL hn hW hW'
        ⟨hpc4, hkp, hd4.trans hI.d, h8, le_of_lt hI.lt, hI.below, fun _ ↦ by omega⟩) fun _ h ↦ .inl h

/-- **From the entry** (`b0`): the scan, or straight to the shift when the list is empty. -/
theorem entry_spec : Eventually (step1 Host.exe) (Post m) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.InsD.b0Offset)⟩ := by
  have hwf := Env.wf_nil m
  have hm := match_nil m
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hd : s1.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have hkp : Kp m s1.data := (Kp.refl m).block hm hm1 hwf rfl (by decide) (by decide)
    (by rw [hd]; exact NativeRustcVm.SameOutside.refl _ _)
  have h8 : (s1.data.regs.getXReg .X8).toNat = 0 := by
    show (s1.data.regs.getXReg .X8).toBitVec.toNat = 0
    rw [hm1.regs .X8 (.lit 0) rfl]; rfl
  have hc : (SBool.cmp .eq .W64 (.reg .X1) (.lit 0)).eval (Env.ofMachine m []) =
      decide (L.length = 0) := by
    simp only [SBool.eval, eq_apply]
    have e1 : ((Sym.reg .X1).eval (Env.ofMachine m [])).toNat = L.length := hL.symm
    rw [e1]; rfl
  simp only [PcOk, hc] at hpc1
  have hb0 : Below m L 0 := fun _ h ↦ absurd h (Nat.not_lt_zero _)
  by_cases h0 : L.length = 0
  · simp only [h0, decide_true, ↓reduceIte, lbl hp (j := 19) rfl] at hpc1
    exact six_spec hp hok hL hn hW hW' ⟨hpc1, hkp, hd, h8, Nat.zero_le _, hb0, fun h ↦ by omega⟩
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  refine Sym.loop (fun n st ↦ ∃ i, n = L.length - i ∧ SInv m L k i st)
    (fun n st ⟨i, hn', hI⟩ ↦ ?_) ⟨0, rfl, hpc1.trans (congrArg Host.addrOf rfl), hkp, hd, h8,
      by omega, hb0⟩
  subst hn'
  exact scan_step hp hok hL hn hW hW' hI

end

/-- **`ins_d` meets its contract.** -/
theorem insD_spec (hp : Placed code k) : Spec (Labels.label NativeRustcVmArm.Vm.InsD.entryLabel) InsDPre InsDPost := by
  intro m ⟨_, hn, hok⟩
  have hok' : NativeRustcVm.Mapped m.dmem (arr m) 2048 ∧ NativeRustcVm.NoWrap (arr m) 2048 := hok
  obtain ⟨L, hL, hW⟩ := exists_wordsAt m.regs.X1.toNat (arr m)
    (hok'.1.mono (by omega))
  obtain ⟨g, hg⟩ := exists_wordAt (hok'.1.sub (o := 8 * m.regs.X1.toNat) (m := 8) (by omega))
  have hW' : WordsAt m.dmem (arr m) (L ++ [g]) :=
    NativeRustcVm.wordsAt_append_iff.mpr ⟨hW, by rw [hL, NativeRustcVm.wordsAt_singleton_iff]; exact hg⟩
  rw [lbl hp (j := 0) (l := NativeRustcVmArm.Vm.InsD.entryLabel) rfl]
  exact entry_spec hp hok' hL (by omega) hW hW'

end

end NativeRustcVmArm.Wire.InsD
