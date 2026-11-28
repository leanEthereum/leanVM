module

public import NativeRustcVmArm.Bus.BusLayout.Keep

/-!
# `bus_layout`: the placements' loop

A turn from `.LBusLayout_11` (`place_step`): `b14` reads size and offset `j`; a framework block's
placement (`j < nf`) is pushed by `b15`, `b16` (`push_fw`), a table block's by `b17`, `b18`
(`push_tb`, the tables' count at `936`); `b13` (`b13_step`) leaves for `.LBusLayout_17` after the
last (`PEnd`), else back to the head.
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)

public section

/-- At `.LBusLayout_10` (`b13`), placement `j` pushed. -/
structure PMid (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) (j : Nat)
    (st : MachineData) : Prop where
  fr : Frm m0 st
  lt : j < nf m0 + bl.length
  sizes : SizesAt st.dmem L bl m0 (nf m0 + bl.length)
  offs : OffsAt st.dmem L bl m0
  part : Part st.dmem L bl m0 (j + 1)
  x19 : st.regs.getXReg .X19 = m0.regs.X0
  x8 : (st.regs.getXReg .X8).toNat = j
  x9 : (st.regs.getXReg .X9).toNat = min (j + 1) (nf m0)
  x10 : (st.regs.getXReg .X10).toBitVec = fa m0 888
  x11 : (st.regs.getXReg .X11).toBitVec = fa m0 944
  x20 : (st.regs.getXReg .X20).toNat = nf m0
  x21 : (st.regs.getXReg .X21).toNat = nf m0 + bl.length
  x22 : (st.regs.getXReg .X22).toBitVec = fa m0 440
  x23 : (st.regs.getXReg .X23).toBitVec = fa m0 8

theorem eval_reg_eq [Labels] {m : MachineData} {rs : List (BitVec 64 × Nat)} {r : XReg} {n : Nat}
    (h : (m.regs.getXReg r).toNat = n) (hn : n < 2 ^ 64) :
    (Sym.reg r).eval (Env.ofMachine m rs) = BitVec.ofNat 64 n := by
  show (m.regs.getXReg r).toBitVec = _
  apply BitVec.eq_of_toNat_eq
  rw [UInt64.toNat_toBitVec, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he ↦ by
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

variable [Host] {k : Nat}

/-- **`b13`**: the next index; out after the last placement. -/
theorem b13_step (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b13Offset))
    (hI : PMid L bl m0 j st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b20Offset) ∧ PEnd L bl m0 st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b14Offset) ∧ PInv L bl m0 (j + 1) st'.data)) st := by
  have hlt := hI.lt
  have hn := pre_n hpre
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13 (Env.wf_nil _) hpc
    (match_nil _) fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hI.fr (match_nil _) hm1 (Env.wf_nil _) rfl rfl rfl
    (ofBlock_keep (by decide))
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have K : Bus.KeepRegs [.X9, .X10, .X11, .X19, .X20, .X21, .X22, .X23] st.data st1.data :=
    Bus.KeepRegs.of_block hm1 rfl
  have hx8 : (st1.data.regs.getXReg .X8).toNat = j + 1 := by
    rw [← UInt64.toNat_toBitVec, hm1.regs .X8 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, BitVec.toNat_add, UInt64.toNat_toBitVec, hI.x8, BitVec.toNat_ofNat]
    omega
  have hc : (SBool.cmp .eq .W64 (.reg .X21) (.bin .add .W64 (.reg .X8) (.lit 1))).eval
      (Env.ofMachine st.data []) = decide (j + 1 = nf m0 + bl.length) := by
    sym_simp
    rw [beq_toNat, Env.ofMachine_regs, Env.ofMachine_regs, BitVec.toNat_add, UInt64.toNat_toBitVec,
      UInt64.toNat_toBitVec, hI.x21, hI.x8, BitVec.toNat_ofNat]
    exact decide_eq_decide.mpr (by omega)
  obtain ⟨hpcT, hpcF⟩ := pc_of_cond hpc1
  by_cases hend : j + 1 = nf m0 + bl.length
  · have hpc' := hpcT (by rw [hc]; exact decide_eq_true hend)
    rw [lbl_17 hp] at hpc'
    refine .done _ (Or.inl ⟨hpc', hfr1, by rw [hd1, ← hend]; exact hI.part, ?_, ?_⟩)
    · rw [K .X19 (by simp), hI.x19]
    · rw [K .X9 (by simp), hI.x9]; omega
  · have hpc' := hpcF (by rw [hc]; exact decide_eq_false hend)
    refine .done _ (Or.inr ⟨hpc', hfr1, by omega, by rw [hd1]; exact hI.sizes,
      by rw [hd1]; exact hI.offs, by rw [hd1]; exact hI.part, ?_, hx8, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [K .X19 (by simp), hI.x19]
    · rw [K .X9 (by simp), hI.x9]
    · rw [K .X10 (by simp), hI.x10]
    · rw [K .X11 (by simp), hI.x11]
    · rw [K .X20 (by simp), hI.x20]
    · rw [K .X21 (by simp), hI.x21]
    · rw [K .X22 (by simp), hI.x22]
    · rw [K .X23 (by simp), hI.x23]

/-- **A framework placement pushed** (`b15`, `b16`). -/
theorem push_fw (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b15Offset)) (hI : PInv L bl m0 j st.data)
    (h13 : st.data.regs.getXReg .X13 = ((S L bl m0).getD j 0).toUInt64)
    (h12 : st.data.regs.getXReg .X12 = ((O L bl m0).1.getD j 0).toUInt64) (hj : j < nf m0) :
    Eventually (step1 Host.exe) (fun st' ↦
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b13Offset) ∧ PMid L bl m0 j st'.data) st := by
  have hS := hpre.1
  have hN : busLayoutStack ≤ m0.regs.SP.toNat := hS.2.1
  have hF : 1840 ≤ busLayoutStack := by decide
  have hF' : 1840 ≤ m0.regs.SP.toNat := by omega
  have hnf3 : nf m0 ≤ 3 := hpre.2.1
  have hn := pre_n hpre
  -- `b15`: below three framework blocks.
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 (Env.wf_nil _) hpc
    (match_nil _) fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hI.fr (match_nil _) hm1 (Env.wf_nil _) rfl rfl rfl
    (ofBlock_keep (by decide))
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have K1 : Bus.KeepRegs [.X8, .X9, .X10, .X11, .X12, .X13, .X19, .X20, .X21, .X22, .X23]
      st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
  have hpc1' := (pc_of_cond hpc1).2 (by
    show (!(SBool.cmp .ult .W64 (.reg .X9) (.lit 3)).eval _) = false
    rw [eval_ult_lit _ _ _ .X9 (by decide), hI.x9]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq]
    omega)
  -- `b16`: the placement's words at `888 + 16 j`.
  have hwf2 := Bus.wf_frame (F := 1840) hS hF hfr1.kept
  have hx9 : (st1.data.regs.getXReg .X9).toNat = j := by rw [K1 .X9 (by simp), hI.x9]; omega
  have hm2 : Match (Env.ofMachine st1.data [(fb m0, 1840)]) sF16 st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Bus.base_aligned hS hF rfl, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]; rw [hfr1.sp]; simp)
      ⟨by show (st1.data.regs.getXReg .X10).toBitVec = _; rw [K1 .X10 (by simp), hI.x10]; rfl,
        trivial⟩ trivial
      ⟨by show (st1.data.regs.getXReg .X9).toBitVec.toNat < 3; rw [UInt64.toNat_toBitVec, hx9]; omega,
        trivial⟩ trivial
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf2 hpc1' hm2
    fun st2 hm2' hpc2 ↦ ?_
  have hall := b16_mem
  have hlo := b16_lo
  have hhi := b16_hi
  rw [Bus.after_eq run_b16] at hall hlo hhi
  have hfr2 : Frm m0 st2.data :=
    frm_block hN hfr1 hm2 hm2' hwf2 rfl (ofBlock_keep (by decide)) (by decide) hall
  have K2 : Bus.KeepRegs [.X8, .X10, .X11, .X19, .X20, .X21, .X22, .X23] st1.data st2.data :=
    KeepRegs.of_block' hm2 hm2' rfl
  have hX9 := eval_reg_eq (rs := [(fb m0, 1840)]) hx9 (by omega)
  have hko : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 888 ∨ 936 ≤ o → o + 8 ≤ 1840 →
      WordAt st.data.dmem (fa m0 o) w → WordAt st2.data.dmem (fa m0 o) w :=
    fun ho ho' h ↦ keep_out hm2' hwf2 rfl hF' (by decide) (by decide) hall ho' ho
      (by rw [Env.ofMachine_mem0, hd1]; exact h)
  have hmem : (Env.ofMachine st1.data [(fb m0, 1840)]).mem0 = st.data.dmem := hd1
  have hpart : Part st2.data.dmem L bl m0 (j + 1) := by
    obtain ⟨hdep, htl, hfw, -⟩ := hI.part
    refine ⟨hko (by omega) (by omega) hdep, ?_, fun j' hj' ↦ ?_, fun j' hj' ↦ by omega⟩
    · rw [show j + 1 - nf m0 = j - nf m0 by omega]; exact hko (.inr le_rfl) (by omega) htl
    · by_cases hjj : j' = j
      · subst hjj
        refine pa_mk (pre_P_ok hpre j').1 (pre_P_ok hpre j').2 ?_ ?_
        · have h := slot_new hm2' rfl (by omega) (hlo j' (by omega)) hX9
          rw [show UInt64.ofBitVec ((Sym.reg .X13).eval (Env.ofMachine st1.data [(fb m0, 1840)])) =
            ((S L bl m0).getD j' 0).toUInt64 by
              show UInt64.ofBitVec (st1.data.regs.getXReg .X13).toBitVec = _
              rw [K1 .X13 (by simp), h13]] at h
          exact h
        · have h := slot_new hm2' rfl (by omega) (hhi j' (by omega)) hX9
          rw [show UInt64.ofBitVec ((Sym.reg .X12).eval (Env.ofMachine st1.data [(fb m0, 1840)])) =
            ((O L bl m0).1.getD j' 0).toUInt64 by
              show UInt64.ofBitVec (st1.data.regs.getXReg .X12).toBitVec = _
              rw [K1 .X12 (by simp), h12]] at h
          exact h
      · have hne : (Sym.reg .X9).eval (Env.ofMachine st1.data [(fb m0, 1840)]) ≠
            BitVec.ofNat 64 j' := by
          rw [hX9]; exact ofNat_ne (by omega) (by omega) (Ne.symm hjj)
        refine pa_move (hfw j' (by omega)) (fun h ↦ ?_) (fun h ↦ ?_)
        · exact slot_keep hm2' rfl (by omega) (hlo j' (by omega)) hne (by rw [hmem]; exact h)
        · exact slot_keep hm2' rfl (by omega) (hhi j' (by omega)) hne (by rw [hmem]; exact h)
  simp only [PcOk] at hpc2
  rw [lbl_10 hp] at hpc2
  refine .done _ ⟨hpc2, hfr2, hI.lt, fun j' hj' ↦ hko (.inl (by omega)) (by omega) (hI.sizes j' hj'),
    fun j' hj' ↦ hko (.inl (by omega)) (by omega) (hI.offs j' hj'), hpart, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [K2 .X19 (by simp), K1 .X19 (by simp), hI.x19]
  · rw [K2 .X8 (by simp), K1 .X8 (by simp), hI.x8]
  · rw [← UInt64.toNat_toBitVec, hm2'.regs .X9 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, BitVec.toNat_add, UInt64.toNat_toBitVec, hx9, BitVec.toNat_ofNat]
    omega
  · rw [K2 .X10 (by simp), K1 .X10 (by simp), hI.x10]
  · rw [K2 .X11 (by simp), K1 .X11 (by simp), hI.x11]
  · rw [K2 .X20 (by simp), K1 .X20 (by simp), hI.x20]
  · rw [K2 .X21 (by simp), K1 .X21 (by simp), hI.x21]
  · rw [K2 .X22 (by simp), K1 .X22 (by simp), hI.x22]
  · rw [K2 .X23 (by simp), K1 .X23 (by simp), hI.x23]

end

end NativeRustcVmArm.Bus.BusLayout
