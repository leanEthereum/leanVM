module

public import NativeRustcVmArm.Bus.BusLayout.Place

/-!
# `bus_layout`: a table block's placement pushed

`push_tb`: `b17` reads the tables' count at `936` (below `51`, so the branch to the panic is not
taken); `b18` stores the placement at `944 + 16 (j - nf)` and the count plus one.
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)

public section

variable [Host] {k : Nat}

/-- **A table placement pushed** (`b17`, `b18`). -/
theorem push_tb (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b17Offset)) (hI : PInv L bl m0 j st.data)
    (h13 : st.data.regs.getXReg .X13 = ((S L bl m0).getD j 0).toUInt64)
    (h12 : st.data.regs.getXReg .X12 = ((O L bl m0).1.getD j 0).toUInt64) (hj : nf m0 ≤ j) :
    Eventually (step1 Host.exe) (fun st' ↦
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b13Offset) ∧ PMid L bl m0 j st'.data) st := by
  have hS := hpre.1
  have hN : busLayoutStack ≤ m0.regs.SP.toNat := hS.2.1
  have hF : 1840 ≤ busLayoutStack := by decide
  have hF' : 1840 ≤ m0.regs.SP.toNat := by omega
  have hnf3 : nf m0 ≤ 3 := hpre.2.1
  have hn := pre_n hpre
  have hlt := hI.lt
  have hbl51 : bl.length ≤ 51 := hpre.2.2.2.2.2.1
  -- `b17`: the tables' count.
  have hwf := Bus.wf_frame (F := 1840) hS hF hI.fr.kept
  have hm := Bus.match_frame (m := st.data) hS hF rfl hI.fr.sp
  have hld : (Env.ofMachine st.data [(fb m0, 1840)]).load 0 936 8 =
      (j - nf m0).toUInt64.toBitVec := load_word hI.part.tlen
  have hcnt : (j - nf m0).toUInt64.toNat = j - nf m0 :=
    UInt64.toNat_ofNat_of_lt' (lt_of_lt_of_le (show j - nf m0 < 54 by omega) (by decide))
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) run_b17 hwf hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hI.fr hm hm1 hwf rfl rfl rfl (ofBlock_keep (by decide))
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have K1 : Bus.KeepRegs [.X8, .X9, .X10, .X11, .X12, .X13, .X19, .X20, .X21, .X22, .X23]
      st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
  have hx14 : (st1.data.regs.getXReg .X14).toNat = j - nf m0 := by
    rw [← UInt64.toNat_toBitVec, hm1.regs .X14 _ rfl]
    show ((Env.ofMachine st.data [(fb m0, 1840)]).load 0 936 8).toNat = _
    rw [hld, UInt64.toNat_toBitVec, hcnt]
  have hpc1' := (pc_of_cond hpc1).2 (by
    sym_simp
    rw [hld, ult_toNat, UInt64.toNat_toBitVec, hcnt, BitVec.toNat_ofNat]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq]
    have : bl.length ≤ 51 := hpre.2.2.2.2.2.1
    omega)
  -- `b18`: the placement at `944 + 16 (j - nf)`, the count plus one.
  have hwf2 := Bus.wf_frame (F := 1840) hS hF hfr1.kept
  have hm2 : Match (Env.ofMachine st1.data [(fb m0, 1840)]) sT st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Bus.base_aligned hS hF rfl, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]; rw [hfr1.sp]; simp)
      ⟨by show (st1.data.regs.getXReg .X11).toBitVec = _; rw [K1 .X11 (by simp), hI.x11]; rfl,
        trivial⟩ trivial
      ⟨by
        show (st1.data.regs.getXReg .X14).toBitVec.toNat < 51
        have : bl.length ≤ 51 := hpre.2.2.2.2.2.1
        rw [UInt64.toNat_toBitVec, hx14]; omega, trivial⟩ trivial
  refine exec_at (infix_of b18_in_code (by simp [b18]) hp) run_b18 hwf2 hpc1' hm2
    fun st2 hm2' hpc2 ↦ ?_
  have hall := b18_mem
  have hlo := b18_lo
  have hhi := b18_hi
  have hct := b18_count
  rw [Bus.after_eq run_b18] at hall hlo hhi hct
  have hfr2 : Frm m0 st2.data :=
    frm_block hN hfr1 hm2 hm2' hwf2 rfl (ofBlock_keep (by decide)) (by decide) hall
  have K2 : Bus.KeepRegs [.X8, .X9, .X10, .X11, .X19, .X20, .X21, .X22, .X23] st1.data st2.data :=
    KeepRegs.of_block' hm2 hm2' rfl
  have hX14 := eval_reg_eq (rs := [(fb m0, 1840)]) hx14 (by omega)
  have hko : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 936 → WordAt st.data.dmem (fa m0 o) w →
      WordAt st2.data.dmem (fa m0 o) w :=
    fun ho h ↦ keep_out hm2' hwf2 rfl hF' (by decide) (by decide) hall (by omega) (.inl ho)
      (by rw [Env.ofMachine_mem0, hd1]; exact h)
  have hmem : (Env.ofMachine st1.data [(fb m0, 1840)]).mem0 = st.data.dmem := hd1
  have hpart : Part st2.data.dmem L bl m0 (j + 1) := by
    obtain ⟨hdep, -, hfw, htb⟩ := hI.part
    refine ⟨hko (by omega) hdep, ?_, fun j' hj' ↦ ?_, fun j' hj' ↦ ?_⟩
    · have h := Bus.wordAt_write hm2' (r := 0) (o := 936) rfl (by omega) hct
      rw [show UInt64.ofBitVec ((Sym.bin .add .W64 (.reg .X14) (.lit 1)).eval
          (Env.ofMachine st1.data [(fb m0, 1840)])) = (j + 1 - nf m0).toUInt64 by
        apply UInt64.toNat_inj.mp
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt'
          (lt_of_lt_of_le (show j + 1 - nf m0 < 55 by omega) (by decide))]
        show ((Sym.bin .add .W64 (.reg .X14) (.lit 1)).eval
          (Env.ofMachine st1.data [(fb m0, 1840)])).toNat = _
        sym_simp
        rw [Env.ofMachine_regs, BitVec.toNat_add, UInt64.toNat_toBitVec, hx14, BitVec.toNat_ofNat]
        omega] at h
      exact h
    · have hj'' : j' < nf m0 := by omega
      exact pa_move (hfw j' (by omega)) (hko (by omega)) (hko (by omega))
    · by_cases hjj : j' = j - nf m0
      · subst hjj
        rw [show nf m0 + (j - nf m0) = j by omega]
        refine pa_mk (pre_P_ok hpre j).1 (pre_P_ok hpre j).2 ?_ ?_
        · have h := slot_new hm2' rfl (by omega) (hlo (j - nf m0) (by omega)) hX14
          rw [show UInt64.ofBitVec ((Sym.reg .X13).eval (Env.ofMachine st1.data [(fb m0, 1840)])) =
            ((S L bl m0).getD j 0).toUInt64 by
              show UInt64.ofBitVec (st1.data.regs.getXReg .X13).toBitVec = _
              rw [K1 .X13 (by simp), h13]] at h
          exact h
        · have h := slot_new hm2' rfl (by omega) (hhi (j - nf m0) (by omega)) hX14
          rw [show UInt64.ofBitVec ((Sym.reg .X12).eval (Env.ofMachine st1.data [(fb m0, 1840)])) =
            ((O L bl m0).1.getD j 0).toUInt64 by
              show UInt64.ofBitVec (st1.data.regs.getXReg .X12).toBitVec = _
              rw [K1 .X12 (by simp), h12]] at h
          exact h
      · have hne : (Sym.reg .X14).eval (Env.ofMachine st1.data [(fb m0, 1840)]) ≠
            BitVec.ofNat 64 j' := by
          rw [hX14]; exact ofNat_ne (by omega) (by omega) (Ne.symm hjj)
        refine pa_move (htb j' (by omega)) (fun h ↦ ?_) (fun h ↦ ?_)
        · exact slot_keep hm2' rfl (by omega) (hlo j' (by omega)) hne (by rw [hmem]; exact h)
        · exact slot_keep hm2' rfl (by omega) (hhi j' (by omega)) hne (by rw [hmem]; exact h)
  simp only [PcOk] at hpc2
  rw [lbl_10 hp] at hpc2
  refine .done _ ⟨hpc2, hfr2, hI.lt, fun j' hj' ↦ hko (by omega) (hI.sizes j' hj'),
    fun j' hj' ↦ hko (by omega) (hI.offs j' hj'), hpart, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [K2 .X19 (by simp), K1 .X19 (by simp), hI.x19]
  · rw [K2 .X8 (by simp), K1 .X8 (by simp), hI.x8]
  · rw [K2 .X9 (by simp), K1 .X9 (by simp), hI.x9]; omega
  · rw [K2 .X10 (by simp), K1 .X10 (by simp), hI.x10]
  · rw [K2 .X11 (by simp), K1 .X11 (by simp), hI.x11]
  · rw [K2 .X20 (by simp), K1 .X20 (by simp), hI.x20]
  · rw [K2 .X21 (by simp), K1 .X21 (by simp), hI.x21]
  · rw [K2 .X22 (by simp), K1 .X22 (by simp), hI.x22]
  · rw [K2 .X23 (by simp), K1 .X23 (by simp), hI.x23]

end

end NativeRustcVmArm.Bus.BusLayout
