module

public import NativeRustcVmArm.Bus.BusLayout.Sizes

/-!
# `bus_layout`: the blocks' heights

A turn of the loop `.LBusLayout_6` (`loop_step`): `b7` reads block `i`'s owner at X23 (below `6`,
so the branch to `b6` is taken); `b6` reads the owner's log-height from the layout (region 1) and
stores it as size `nf + i` (the slot store at `8 + 8 (nf + i)` of the frame, `var 0 = nf + i`),
then leaves for `.LBusLayout_8` after the last block (`Done`), else back to the head.
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)
open NativeRustcVm.Transcript (off)

public section

/-- The height `b6` reads: region 1's word at X10's slot. -/
abbrev hV : Sym := .loadx 1 0 (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X10)) 8

/-- `b6`'s slot store: size `j` is the height where `var 0 = j`, else unchanged. -/
theorem b6_slots : ∀ j < 54, ∀ t < 8, findWrite 0 (8 + 8 * j + t) (Bus.after b6 sL).mem =
    some (.ite (.cmp .eq .W64 (.var 0) (.lit j)) hV (.load 0 (8 + 8 * j) 8), t) := by
  rw [Bus.after_eq run_b6]; decide +kernel

/-- `b6` writes the sizes only. -/
theorem b6_mem : ((Bus.after b6 sL).mem.all fun w ↦
    w.r == 0 && decide (8 ≤ w.off) && decide (w.off + w.n ≤ 440)) = true := by
  rw [Bus.after_eq run_b6]; decide +kernel

/-- `b6`'s environment: the frame, the layout's heights; `var 0` the size's index `j`. -/
abbrev envL (st m0 : MachineData) (j : Nat) : Env :=
  Env.ofMachine st [(fb m0, 1840), (m0.regs.X5.toBitVec + BitVec.ofNat 64 24, 48)]
    fun _ ↦ BitVec.ofNat 64 j

variable [Host] {k : Nat}

/-- **A turn of the heights' loop**: block `i`'s height stored; out after the last block. -/
theorem loop_step (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b7Offset)) (hI : LInv L bl m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Done L bl m0 k st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b7Offset) ∧ LInv L bl m0 (i + 1) st'.data)) st := by
  have hpre' := hpre
  obtain ⟨hS, hnf, -, -, -, hbl, -, hown, -, hBok, -, hLok, -, -, -, -⟩ := hpre
  have hN : busLayoutStack ≤ m0.regs.SP.toNat := hS.2.1
  have hF : 1840 ≤ busLayoutStack := by decide
  have hlt := hI.lt
  have hn54 := pre_n hpre'
  have hBnw := hBok.1.2
  unfold NoWrap at hBnw
  -- `b7`: block `i`'s owner.
  have hbt : (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i)).toNat =
      m0.regs.X3.toNat + 16 * i := NativeRustcVm.toNat_add_ofNat (by
        show m0.regs.X3.toBitVec.toNat + 16 * i < 2 ^ 64; omega)
  have hwf1 : (Env.ofMachine st.data [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i), 16)]).WF :=
    Env.wf_of ⟨⟨fun t ht ↦ by
        rw [NativeRustcVm.addr_add_add]; exact hI.fr.kept _ (hBok.1.1 _ (by omega)),
      by unfold NoWrap; rw [hbt]; show m0.regs.X3.toBitVec.toNat + 16 * i + 16 ≤ 2 ^ 64; omega⟩,
      trivial⟩ (List.pairwise_singleton _ _)
  have hm1 : Match (Env.ofMachine st.data [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i), 16)])
      sB st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [hI.x23]; simp, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf1 hpc hm1
    fun st1 hm1' hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1'.dmem_eq hwf1 rfl
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hI.fr hm1 hm1' hwf1 rfl rfl rfl
    (ofBlock_keep (by decide))
  have K1 : Bus.KeepRegs [.X8, .X9, .X19, .X20, .X21, .X22, .X24, .X25, .X26] st.data st1.data :=
    Bus.KeepRegs.of_block hm1' rfl
  have hown6 : bl[i].owner < 6 := hown _ (List.getElem_mem hlt)
  have hld : (Env.ofMachine st.data [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i), 16)]).load
      0 0 8 = bl[i].owner.toUInt64.toBitVec := by
    rw [load_eq_wordOf]
    show (wordOf st.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i) +
      BitVec.ofNat 64 0)).toBitVec = _
    rw [add_zero', owner_word hpre' hI.fr hlt]
  have hx10 : (st1.data.regs.getXReg .X10).toNat = bl[i].owner := by
    rw [← UInt64.toNat_toBitVec, hm1'.regs .X10 _ rfl]
    show (Env.load _ 0 0 8).toNat = _
    rw [hld, UInt64.toNat_toBitVec, Nat.toUInt64_eq,
      UInt64.toNat_ofNat_of_lt' (lt_of_lt_of_le hown6 (by decide))]
  have hpc1' := (pc_of_cond hpc1).1 (by
    sym_simp
    rw [hld]
    simp only [ult_toNat, beq_toNat, UInt64.toNat_toBitVec, Nat.toUInt64_eq,
      UInt64.toNat_ofNat_of_lt' (lt_of_lt_of_le hown6 (by decide)), BitVec.toNat_ofNat]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega)
  rw [lbl_5 hp] at hpc1'
  -- `b6`: the height, stored as size `nf + i`.
  have hLb : (m0.regs.X5.toBitVec + BitVec.ofNat 64 24).toNat = m0.regs.X5.toNat + 24 :=
    NativeRustcVm.toNat_add_ofNat (by
      have := hLok.1.2; unfold NoWrap layoutBytes at this
      show m0.regs.X5.toBitVec.toNat + 24 < 2 ^ 64; omega)
  have hwf2 : (envL st1.data m0 (nf m0 + i)).WF :=
    Bus.wf_two (fun t ht ↦ hfr1.kept _ ((Bus.frame_mapped hS hF).1 t ht))
      (Bus.frame_mapped hS hF).2
      (fun t ht ↦ by
        rw [NativeRustcVm.addr_add_add]
        exact hfr1.kept _ (hLok.1.1 _ (by unfold layoutBytes; omega)))
      (by
        have := hLok.1.2; unfold NoWrap layoutBytes at this
        unfold NoWrap; rw [hLb]; show m0.regs.X5.toBitVec.toNat + 24 + 48 ≤ 2 ^ 64; omega)
      (by
        have hA := apart_frame hN hF hLok.2
        unfold Apart at hA ⊢
        unfold layoutBytes at hA
        rw [hLb]
        simp only [UInt64.toNat_toBitVec] at hA
        omega)
      _
  have hm2 : Match (envL st1.data m0 (nf m0 + i)) sL st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Bus.base_aligned hS hF rfl, rfl, nofun, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]; rw [hfr1.sp]; simp)
      ⟨by
        simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [K1 .X26 (by simp), hI.regs.x26]; rfl,
       by
        simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.map_some, Option.getD_some]
        rw [K1 .X9 (by simp), hI.x9]; simp,
       by
        simp only [Sym.eval]
        apply BitVec.eq_of_toNat_eq
        rw [shl_toNat, UInt64.toNat_toBitVec, K1 .X8 (by simp), hI.x8]
        show _ = (BitVec.ofNat 64 (nf m0 + i)).toNat * 2 ^ 3 % 2 ^ 64
        rw [BitVec.toNat_ofNat]
        omega, trivial⟩
      trivial
      ⟨by show (BitVec.ofNat 64 (nf m0 + i)).toNat < 54; rw [BitVec.toNat_ofNat]; omega,
       by simp only [Sym.eval, Env.ofMachine_regs, UInt64.toNat_toBitVec]; omega, trivial⟩
      trivial
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf2 hpc1' hm2
    fun st2 hm2' hpc2 ↦ ?_
  have hall := b6_mem
  rw [Bus.after_eq run_b6] at hall
  have hW : ∀ w ∈ (Bus.after b6 sL).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 440 := by
    rw [Bus.after_eq run_b6]
    intro w hw'
    have := List.all_eq_true.mp hall w hw'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  rw [Bus.after_eq run_b6] at hW
  have hfr2 : Frm m0 st2.data := by
    refine Fr.ofBlockW hfr1 hm2 hm2' hwf2 rfl rfl (ofBlock_keep (by decide)) rfl (by decide) hN
      slots_le fun w hw' ↦ .inl ⟨(hW w hw').1, by have := hW w hw'; omega, fun p hp ↦ ?_⟩
    have := hW w hw'
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (left; simp; omega)
  have K2 : Bus.KeepRegs [.X9, .X19, .X20, .X21, .X23, .X24, .X25, .X26] st1.data st2.data :=
    KeepRegs.of_block' hm2 hm2' rfl
  have K : Bus.KeepRegs [.X9, .X19, .X20, .X21, .X24, .X25, .X26] st.data st2.data := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (K2 _ (by simp)).trans (K1 _ (by simp))
  have hregs : Regs m0 st2.data :=
    hI.regs.keep fun r hr ↦ K r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hslots := b6_slots
  rw [Bus.after_eq run_b6] at hslots
  have hsizes : SizesAt st2.data.dmem L bl m0 (nf m0 + i + 1) := by
    unfold SizesAt
    intro j hj
    have h := slot_word hm2' (r := 0) (o := 8 + 8 * j) rfl (by omega) (hslots j (by omega))
    have hv : (envL st1.data m0 (nf m0 + i)).vars 0 = BitVec.ofNat 64 (nf m0 + i) := rfl
    simp only [Sym.eval, hv] at h
    by_cases hji : j = nf m0 + i
    · subst hji
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at h
      have hh := height_word hpre' hfr1 (o := bl[i].owner) hown6
      rw [S_getD_bl hlt]
      show WordAt _ (fb m0 + BitVec.ofNat 64 (8 + 8 * (nf m0 + i))) _
      convert h using 1
      show _ = UInt64.ofBitVec (Env.load _ 1 (0 + _) 8)
      rw [load_eq_wordOf, memExt3, Env.ofMachine_regs, UInt64.toNat_toBitVec, hx10]
      rw [← hh]
      show _ = UInt64.ofBitVec (wordOf st1.data.dmem
        (m0.regs.X5.toBitVec + BitVec.ofNat 64 24 + BitVec.ofNat 64 (0 + _))).toBitVec
      rw [show 0 + bl[i].owner * 8 % 2 ^ 64 = 8 * bl[i].owner by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by
        intro he
        have := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat] at this
        omega))] at h
      have hold := hI.sizes j (by omega)
      rw [← hd1] at hold
      rw [load_word (env := envL st1.data m0 (nf m0 + i)) (r := 0) hold] at h
      exact h
  have h22 := hm2'.regs .X22 _ rfl
  have h8 := hm2'.regs .X8 _ rfl
  have h23 := hm1'.regs .X23 _ rfl
  have hx22 : (st1.data.regs.getXReg .X22).toNat = bl.length - i := by
    rw [K1 .X22 (by simp), hI.x22]
  obtain ⟨hpcT, hpcF⟩ := pc_of_cond hpc2
  by_cases hend : i + 1 = bl.length
  · have hpc2 := hpcT (by rw [eval_eq_lit _ _ _ .X22 (by decide), hx22]; simp; omega)
    rw [lbl_8 hp] at hpc2
    refine .done _ (Or.inl ⟨hpc2, hfr2, hregs, ?_, ?_⟩)
    · rw [K .X21 (by simp), hI.x21]
    · rw [← hend]; exact hsizes
  · have hpc2 := hpcF (by rw [eval_eq_lit _ _ _ .X22 (by decide), hx22]; simp; omega)
    refine .done _ (Or.inr ⟨hpc2, hfr2, hregs, by omega, hsizes, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [K .X21 (by simp), hI.x21]
    · rw [← UInt64.toNat_toBitVec, h22]
      sym_simp
      rw [Env.ofMachine_regs, BitVec.toNat_sub, UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, hx22]
      change (2 ^ 64 - 1 + (bl.length - i)) % 2 ^ 64 = _
      omega
    · rw [K2 .X23 (by simp), h23]
      simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]
      rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add]
      rfl
    · rw [← UInt64.toNat_toBitVec, h8]
      sym_simp
      rw [BitVec.toNat_add]
      show ((BitVec.ofNat 64 (nf m0 + i) <<< 3).toNat + (8#64).toNat) % 2 ^ 64 = _
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    · rw [K .X9 (by simp), hI.x9]

end

end NativeRustcVmArm.Bus.BusLayout
