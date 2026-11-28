module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Count

/-!
# `verify_stacked_opening`: the counting loop (x86-64)

From the head `NativeRustcVmX64.Vm.VerifyStackedOpening.label_7` (`b9`, `Head j`): `b9` reads claim `2j`'s column; at most
`157`, `b10` its `present` bit and claim `2j + 1`'s column, else `NativeRustcVmX64.Vm.VerifyStackedOpening.label_9` (`b13`)
a zero bit and that column; at most `157`, `NativeRustcVmX64.Vm.VerifyStackedOpening.label_5` (`b7`) claim `2j + 1`'s bit,
else `NativeRustcVmX64.Vm.VerifyStackedOpening.label_10` (`b14`, after `b11`) a zero bit: `NativeRustcVmX64.Vm.VerifyStackedOpening.label_6`
(`b8`, `Mid j`, `pair_mid`). `b8` adds both and goes on to the head or, after the last pair, to
`NativeRustcVmX64.Vm.VerifyStackedOpening.label_11` (`b15`, `AtB15`) (`mid_step`); `count_loop`.
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

@[expose] public section

/-- **After the pairs**, at `NativeRustcVmX64.Vm.VerifyStackedOpening.label_11`. -/
structure AtB15 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 st : MachineData) : Prop where
  cb : CB a s cs m0 st
  rax : reg st .rax = off (layA m0) 120
  rcx : (reg st .rcx).toNat = 2 * (cs.size / 2)
  rbx : (reg st .rbx).toNat = placedOf layout cs (2 * (cs.size / 2))

end

public section

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {cs : Array ColumnClaimW}
  {m0 : MachineData}

/-- The loop's blocks from their literal state. -/
theorem Head.m_cnt {j : Nat} {st : MachineData} (hh : Head a s layout cs m0 j st)
    {ret : BitVec 64} : Match (cntEnv m0 st j ret) cntS st :=
  match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hh.cb.ok.fr.rsp_eval, trivial⟩ trivial trivial
    ⟨by show reg st .rax = _; rw [hh.rax]; rfl,
      by show reg st .rsi = _
         rw [hh.rsi, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩

/-- The loop's blocks from their literal state with a column at most `157` in R9. -/
theorem Head.m_cntB {j : Nat} {st : MachineData} (hh : Head a s layout cs m0 j st)
    (h9 : (reg st .r9).toNat ≤ 157) {ret : BitVec 64} : Match (cntEnv m0 st j ret) cntBS st :=
  match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hh.cb.ok.fr.rsp_eval, trivial⟩ trivial
    ⟨by show ((t3 (.reg .r9)).eval _).toNat < 472
        rw [toNat_t3 _ (by show (reg st .r9).toNat < _; omega)]; show 3 * (reg st .r9).toNat < 472
        omega, trivial⟩
    ⟨by show reg st .rax = _; rw [hh.rax]; rfl,
      by show reg st .rsi = _
         rw [hh.rsi, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩

/-- The frame alone. -/
theorem Ok.m_reg {st : MachineData} (hok : Ok m0 st 8) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : Match (frameEnv m0 st 512 [] vars ret) regS st :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hok.fr.rsp_eval, trivial⟩ trivial trivial trivial

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

section
variable (h : Parts a s layout target coefficients point slices cs z value m0)
  (hp : Placed code k)
include h hp

/-- `b14`: claim `2j + 1` not counted. -/
theorem at_b14 {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b14Offset))
    (hh : Head a s layout cs m0 j st.data)
    (h11 : (reg st.data .r11).toNat = bitAt layout cs (2 * j))
    (hB : 157 < (cs[2 * j + 1]'(by have := hh.hj; omega)).column) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b8Offset) → Mid a s layout cs m0 j st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hh.cb.ok
  refine h.run hp b14_in_code (List.cons_ne_nil _ _) hpc hok (hok.cnt_wf h hh.hj) hh.m_cnt run_b14
    (o := 8) (by decide +kernel) (by decide) fun st1 hok1 _ hm1 hpc1 ↦ ?_
  have hk : keeps (cbRegs ++ headRegs ++ [.r11]) (after b14 cntS) = true := by
    rw [after_eq run_b14]; decide
  have hk' : ∀ r ∈ cbRegs ++ headRegs ++ [.r11], reg st1.data r = reg st.data r :=
    fun r hr ↦ kept_reg hm1 (after_eq run_b14 ▸ hk) hr
  have hd := hm1.dmem_eq (hok.cnt_wf h hh.hj) rfl
  simp only [PcOk] at hpc1
  rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_6_at] at hpc1
  refine cont st1 hpc1 ⟨hh.keep hok1 hd fun r hr ↦ hk' r (List.mem_append_left _ hr), ?_, ?_⟩
  · rw [hk' .r11 (by simp)]; exact h11
  · rw [show reg st1.data .r9 = 0#64 from hm1.regs .r9 _ rfl,
      hok.bit_eq h (by have := hh.hj; omega)]
    split
    · omega
    · rfl

/-- `b7`: claim `2j + 1` counted by its `present` bit. -/
theorem at_b7 {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b7Offset))
    (hh : Head a s layout cs m0 j st.data)
    (h11 : (reg st.data .r11).toNat = bitAt layout cs (2 * j))
    (h9 : (reg st.data .r9).toNat = (cs[2 * j + 1]'(by have := hh.hj; omega)).column)
    (hB : (cs[2 * j + 1]'(by have := hh.hj; omega)).column ≤ 157) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b8Offset) → Mid a s layout cs m0 j st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hh.cb.ok
  refine h.run hp b7_in_code (List.cons_ne_nil _ _) hpc hok (hok.cnt_wf h hh.hj)
    (hh.m_cntB (by omega)) run_b7 (o := 8) (by decide +kernel) (by decide)
    fun st1 hok1 _ hm1 hpc1 ↦ ?_
  have hk : keeps (cbRegs ++ headRegs ++ [.r11]) (after b7 cntBS) = true := by
    rw [after_eq run_b7]; decide
  have hk' : ∀ r ∈ cbRegs ++ headRegs ++ [.r11], reg st1.data r = reg st.data r :=
    fun r hr ↦ kept_reg hm1 (after_eq run_b7 ▸ hk) hr
  have hd := hm1.dmem_eq (hok.cnt_wf h hh.hj) rfl
  simp only [PcOk] at hpc1
  refine cont st1 (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b7_next))
    ⟨hh.keep hok1 hd fun r hr ↦ hk' r (List.mem_append_left _ hr), ?_, ?_⟩
  · rw [hk' .r11 (by simp)]; exact h11
  · rw [show reg st1.data .r9 = _ from hm1.regs .r9 _ rfl]
    exact hok.bit_val h (by have := hh.hj; omega) hB (.reg .r9) h9

/-- **A pair's bits**: from the head, `b9` and `b10` or `b13`, then `b7` or `b14` (`b11`). -/
theorem pair_mid {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b9Offset))
    (hh : Head a s layout cs m0 j st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b8Offset) → Mid a s layout cs m0 j st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hh.cb.ok
  have hj := hh.hj
  have hi0 : 2 * j < cs.size := by omega
  have hi1 : 2 * j + 1 < cs.size := by omega
  refine h.run hp b9_in_code (List.cons_ne_nil _ _) hpc hok (hok.cnt_wf h hj) hh.m_cnt run_b9
    (o := 8) (by decide +kernel) (by decide) fun st1 hok1 _ hm1 hpc1 ↦ ?_
  have hk : keeps (cbRegs ++ headRegs) (after b9 cntS) = true := by
    rw [after_eq run_b9]; decide
  have hh1 := hh.keep hok1 (hm1.dmem_eq (hok.cnt_wf h hj) rfl)
    fun r hr ↦ kept_reg hm1 (after_eq run_b9 ▸ hk) hr
  have hc0 := hok.col_eval h hi0 (e := 0) rfl (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b9Offset + b9.length)).toBitVec
    (off' := 0) rfl
  have h9 : (reg st1.data .r9).toNat = cs[2 * j].column := by
    rw [show reg st1.data .r9 = _ from hm1.regs .r9 _ rfl]; exact hc0
  simp only [PcOk] at hpc1
  rw [eval_gt157, hc0] at hpc1
  by_cases hc : 157 < cs[2 * j].column
  · -- `b13`: claim `2j` not counted.
    simp only [hc, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_9_at] at hpc1
    have hok1 := hh1.cb.ok
    refine h.run hp b13_in_code (List.cons_ne_nil _ _) hpc1 hok1 (hok1.cnt_wf h hj) hh1.m_cnt
      run_b13 (o := 8) (by decide +kernel) (by decide) fun st2 hok2 _ hm2 hpc2 ↦ ?_
    have hk2 : keeps (cbRegs ++ headRegs) (after b13 cntS) = true := by
      rw [after_eq run_b13]; decide
    have hh2 := hh1.keep hok2 (hm2.dmem_eq (hok1.cnt_wf h hj) rfl)
      fun r hr ↦ kept_reg hm2 (after_eq run_b13 ▸ hk2) hr
    have hc1 := hok1.col_eval h hi1 (e := 1) rfl (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b13Offset + b13.length)).toBitVec
      (off' := 608) rfl
    have h11 : (reg st2.data .r11).toNat = bitAt layout cs (2 * j) := by
      rw [show reg st2.data .r11 = 0#64 from hm2.regs .r11 _ rfl, hok.bit_eq h hi0]
      split
      · omega
      · rfl
    have h9' : (reg st2.data .r9).toNat = cs[2 * j + 1].column := by
      rw [show reg st2.data .r9 = _ from hm2.regs .r9 _ rfl]; exact hc1
    simp only [PcOk] at hpc2
    rw [eval_le157, hc1] at hpc2
    by_cases hc' : cs[2 * j + 1].column ≤ 157
    · simp only [hc', decide_true, ↓reduceIte] at hpc2
      rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_5_at] at hpc2
      exact at_b7 h hp hpc2 hh2 h11 h9' hc' cont
    · simp only [hc', decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
      exact at_b14 h hp (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b13_next)) hh2 h11
        (by omega) cont
  · -- `b10`: claim `2j` counted by its `present` bit.
    simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hok1 := hh1.cb.ok
    refine h.run hp b10_in_code (List.cons_ne_nil _ _)
      (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b9_next)) hok1 (hok1.cnt_wf h hj)
      (hh1.m_cntB (by omega)) run_b10 (o := 8) (by decide +kernel) (by decide)
      fun st2 hok2 _ hm2 hpc2 ↦ ?_
    have hk2 : keeps (cbRegs ++ headRegs) (after b10 cntBS) = true := by
      rw [after_eq run_b10]; decide
    have hh2 := hh1.keep hok2 (hm2.dmem_eq (hok1.cnt_wf h hj) rfl)
      fun r hr ↦ kept_reg hm2 (after_eq run_b10 ▸ hk2) hr
    have hc1 := hok1.col_eval h hi1 (e := 1) rfl (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b10Offset + b10.length)).toBitVec
      (off' := 608) rfl
    have h11 : (reg st2.data .r11).toNat = bitAt layout cs (2 * j) := by
      rw [show reg st2.data .r11 = _ from hm2.regs .r11 _ rfl]
      exact hok1.bit_val h hi0 (by omega) (.reg .r9) h9
    have h9' : (reg st2.data .r9).toNat = cs[2 * j + 1].column := by
      rw [show reg st2.data .r9 = _ from hm2.regs .r9 _ rfl]; exact hc1
    simp only [PcOk] at hpc2
    rw [eval_le157, hc1] at hpc2
    by_cases hc' : cs[2 * j + 1].column ≤ 157
    · simp only [hc', decide_true, ↓reduceIte] at hpc2
      rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_5_at] at hpc2
      exact at_b7 h hp hpc2 hh2 h11 h9' hc' cont
    · simp only [hc', decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
      -- `b11`: to `b14`.
      have hok2 := hh2.cb.ok
      refine h.run hp b11_in_code (List.cons_ne_nil _ _)
        (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b10_next)) hok2 (hok2.cnt_wf h hj) hh2.m_cnt
        run_b11 (o := 8) (by decide +kernel) (by decide) fun st3 hok3 _ hm3 hpc3 ↦ ?_
      have hk3 : keeps (cbRegs ++ headRegs ++ [.r11]) (after b11 cntS) = true := by
        rw [after_eq run_b11]; decide
      have hk3' : ∀ r ∈ cbRegs ++ headRegs ++ [.r11], reg st3.data r = reg st2.data r :=
        fun r hr ↦ kept_reg hm3 (after_eq run_b11 ▸ hk3) hr
      have hh3 := hh2.keep hok3 (hm3.dmem_eq (hok2.cnt_wf h hj) rfl)
        fun r hr ↦ hk3' r (List.mem_append_left _ hr)
      simp only [PcOk] at hpc3
      rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_10_at] at hpc3
      exact at_b14 h hp hpc3 hh3 (by rw [hk3' .r11 (by simp)]; exact h11) (by omega) cont

/-- **`b8`**: the pair's bits added; the next pair, or `NativeRustcVmX64.Vm.VerifyStackedOpening.label_11` after the
last. -/
theorem mid_step {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b8Offset))
    (hm : Mid a s layout cs m0 j st.data) {R : MachineState → Prop}
    (cont1 : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b9Offset) → Head a s layout cs m0 (j + 1) st'.data →
      Eventually (step1 Host.exe) R st')
    (cont2 : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b15Offset) → AtB15 a s layout cs m0 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hh := hm.hd
  have hok := hh.cb.ok
  have hj := hh.hj
  have hn := h.n_le
  refine h.run hp b8_in_code (List.cons_ne_nil _ _) hpc hok (hok.cnt_wf h hj) hh.m_cnt run_b8
    (o := 8) (by decide +kernel) (by decide) fun st1 hok1 _ hm1 hpc1 ↦ ?_
  have hk : keeps (cbRegs ++ [.rax, .rdx]) (after b8 cntS) = true := by
    rw [after_eq run_b8]; decide
  have hk' : ∀ r ∈ cbRegs ++ [.rax, .rdx], reg st1.data r = reg st.data r :=
    fun r hr ↦ kept_reg hm1 (after_eq run_b8 ▸ hk) hr
  have hd := hm1.dmem_eq (hok.cnt_wf h hj) rfl
  have hcb := hh.cb.keep hok1 hd fun r hr ↦ hk' r (List.mem_append_left _ hr)
  have hb0 : bitAt layout cs (2 * j) ≤ 1 := by rw [bitAt_eq (by omega)]; split <;> omega
  have hb1 : bitAt layout cs (2 * j + 1) ≤ 1 := by rw [bitAt_eq (by omega)]; split <;> omega
  have hpl := placedOf_le_self (layout := layout) (cs := cs) (2 * j)
  have hrbx : (reg st1.data .rbx).toNat = placedOf layout cs (2 * (j + 1)) := by
    rw [show reg st1.data .rbx = _ from hm1.regs .rbx _ rfl, eval_add64, eval_add64]
    show (reg st.data .r9 + (reg st.data .r11 + reg st.data .rbx)).toNat = _
    have e9 := hm.r9
    have e11 := hm.r11
    have ebx := hh.rbx
    rw [toNat_add_small (by rw [toNat_add_small (by omega)]; omega), toNat_add_small (by omega),
      hm.r9, hm.r11, hh.rbx, show 2 * (j + 1) = 2 * j + 1 + 1 by omega, placedOf_succ',
      placedOf_succ']
    omega
  have hrcx : (reg st1.data .rcx).toNat = 2 * j + 2 := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ rfl, eval_add64]
    show (BitVec.ofNat 64 2 + reg st.data .rcx).toNat = _
    rw [toNat_add_small (by rw [hh.rcx]; simp; omega), hh.rcx]
    simp; omega
  have hrsi : reg st1.data .rsi = off (clA m0) (8 + 608 * (2 * (j + 1))) := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ rfl, eval_add64]
    show BitVec.ofNat 64 1216 + reg st.data .rsi = _
    rw [hh.rsi, BitVec.add_comm, off_add, show 8 + 608 * (2 * j) + 1216 = 8 + 608 * (2 * (j + 1)) by
      omega]
  simp only [PcOk] at hpc1
  rw [eval_eq64] at hpc1
  have hcond : ((Sym.reg .rdx).eval (cntEnv m0 st.data j
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b8Offset + b8.length)).toBitVec)).toNat =
      ((Sym.bin .add .W64 (.lit 2) (.reg .rcx)).eval (cntEnv m0 st.data j
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b8Offset + b8.length)).toBitVec)).toNat ↔ 2 * (cs.size / 2) = 2 * j + 2 := by
    rw [eval_add64]
    show (reg st.data .rdx).toNat = (BitVec.ofNat 64 2 + reg st.data .rcx).toNat ↔ _
    rw [toNat_add_small (by rw [hh.rcx]; simp; omega), hh.rcx, hh.rdx]
    simp
    omega
  by_cases he : 2 * (cs.size / 2) = 2 * j + 2
  · simp only [hcond.mpr he, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_11_at] at hpc1
    refine cont2 st1 hpc1 ⟨hcb, (hk' .rax (by simp)).trans hh.rax, by omega, ?_⟩
    rw [hrbx]; congr 1; omega
  · have hne : ¬ (((Sym.reg .rdx).eval (cntEnv m0 st.data j
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b8Offset + b8.length)).toBitVec)).toNat =
        ((Sym.bin .add .W64 (.lit 2) (.reg .rcx)).eval (cntEnv m0 st.data j
          (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b8Offset + b8.length)).toBitVec)).toNat) := fun e ↦ he (hcond.mp e)
    simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine cont1 st1 (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b8_next))
      ⟨hcb, by omega, (hk' .rax (by simp)).trans hh.rax, (hk' .rdx (by simp)) ▸ hh.rdx, by omega,
        hrsi, hrbx⟩

/-- **The counting loop**: from the head before pair `j`, to `NativeRustcVmX64.Vm.VerifyStackedOpening.label_11`. -/
theorem count_loop {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b15Offset) → AtB15 a s layout cs m0 st'.data →
      Eventually (step1 Host.exe) R st') :
    ∀ d j (st : MachineState), cs.size / 2 - j = d → st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b9Offset) →
      Head a s layout cs m0 j st.data → Eventually (step1 Host.exe) R st := by
  intro d
  induction d with
  | zero => intro j st hd _ hh; have := hh.hj; omega
  | succ d ih =>
    intro j st hd hpc hh
    exact pair_mid h hp hpc hh fun st1 hpc1 hm ↦ mid_step h hp hpc1 hm
      (fun st2 hpc2 hh2 ↦ ih (j + 1) st2 (by omega) hpc2 hh2) cont

end

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
