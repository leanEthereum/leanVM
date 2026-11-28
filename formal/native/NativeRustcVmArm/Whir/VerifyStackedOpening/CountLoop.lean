module

public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.Entry

/-!
# `verify_stacked_opening`: a step of the counting loop

`cnt_step`: at the loop's head before claim `i`, `b3` reads its column; below `158`, `b2` adds
its placement's `present` bit, else `b4` adds nothing; then the head before claim `i + 1`, or `b5`
after the last claim with every placed claim counted (`AtB5`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt ColumnClaimAt PlacementWAt)

@[expose] public section

/-- **At `b5`**: every claim counted. -/
structure AtB5 (layout : LayoutW) (cs : Array ColumnClaimW) (m0 st : MachineData) : Prop where
  base : Base cs m0 st
  pos : 0 < cs.size
  x8 : st.regs.getXReg .X8 = (placedOf layout cs cs.size).toUInt64

end

public section

/-- A scaled index, as the executor computes it. -/
theorem idx_eval' [Labels] {env : Env} {x : Sym} (hn : (x.eval env).toNat < 2 ^ 61) :
    ((Sym.un (.memExtend ⟨.UXTX, .E3⟩) .W64 x).eval env).toNat = 8 * (x.eval env).toNat := by
  simp only [Sym.eval, UnOp.apply]
  simp [BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq, BitVec.toNat_ofInt]
  omega

/-- Three times a column, as the executor computes it. -/
theorem t3_eval [Labels] {env : Env} {r : XReg} {c : Nat} (h : env.regs r = BitVec.ofNat 64 c)
    (hc : c < 2 ^ 62) : ((t3 r).eval env).toNat = 3 * c := by
  simp only [t3, Sym.eval, BinOp.apply, UnOp.apply, h, Sym.low_W64, Sym.ext_W64, shiftW]
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **A step of the counting loop.** -/
theorem cnt_step (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0) {i : Nat}
    {st : MachineData} (hc : CntInv layout cs m0 i st) {R : MachineState → Prop}
    (cont : ∀ st', CntInv layout cs m0 (i + 1) st' →
      Eventually (step1 Host.exe) R ⟨st', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset)⟩)
    (fin : ∀ st', AtB5 layout cs m0 st' →
      Eventually (step1 Host.exe) R ⟨st', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b5Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset)⟩ := by
  have hb := hc.base
  have hi := hc.hi
  have hn160 : cs.size ≤ 160 := h.cl.len_le
  have hcl := h.in_ok hb.fr mem_cl
  simp only at hcl
  have hcb : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
  rw [hcb] at hcl
  obtain ⟨ca, hca⟩ : ∃ ca, ca = m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i) := ⟨_, rfl⟩
  have hoff : 8 + 608 * i + 608 ≤ 97288 := by omega
  -- `b3`
  let env3 := Env.ofMachine st [(ca, 608)]
  have hwf3 : env3.WF :=
    Env.wf_of ⟨⟨fun j hj ↦ by
        rw [hca, NativeRustcVm.addr_add_add]; exact hcl.1 _ (by omega),
      by rw [hca]; exact NativeRustcVm.NoWrap.sub hcl.2.1 hoff⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm3 : Match env3 claimS st :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by show (st.regs.getXReg .X10).toBitVec = _; rw [hc.x10, hca]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  have hcol : env3.load 0 0 8 = cs[i].column.toUInt64.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt st.dmem (ca + BitVec.ofNat 64 0) _
    rw [NativeRustcVm.addr_add_zero, hca]
    exact h.column_word hb.fr hi
  have hclt := (h.cl.claims i hi).column_lt
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk3 run_b3 hwf3 hm3 fun st3 hm3' hpc3 ↦ ?_
  have hd3 : st3.data.dmem = st.dmem := hm3'.dmem_eq hwf3 rfl
  have hf3 : VFr m0 st3.data := Fr.ofBlock hb.fr hm3 hm3' hwf3 rfl rfl rfl (by simp)
  have k3 : ∀ r, (after b3 claimS).reg r = some (.reg r) →
      st3.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦
    (rv hm3' (by rw [← after_eq run_b3]; exact hr)).trans rfl
  have hb3 : Base cs m0 st3.data := hb.keep hf3 hd3 fun r hr ↦ k3 r (by
    rw [after_eq run_b3]
    simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have e3x12 : st3.data.regs.getXReg .X12 = cs[i].column.toUInt64 :=
    (rv hm3' (r := .X12) rfl).trans (by show UInt64.ofBitVec (env3.load 0 0 8) = _; rw [hcol])
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  rw [hcol] at hpc3
  have hcolN : cs[i].column.toUInt64.toNat = cs[i].column := natCast_toUInt64_toNat hclt
  -- the common end: `x11 - 1`, `x10 + 608`, the count
  have tail : ∀ (st4 : MachineState), Base cs m0 st4.data →
      st4.data.regs.getXReg .X8 = (placedOf layout cs (i + 1)).toUInt64 →
      (st4.data.regs.getXReg .X9).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 120 →
      (st4.data.regs.getXReg .X10).toBitVec =
        m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * (i + 1)) →
      st4.data.regs.getXReg .X11 = (cs.size - (i + 1)).toUInt64 →
      (st4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset) ∧ i + 1 < cs.size ∨
        st4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b5Offset) ∧ i + 1 = cs.size) →
      Eventually (step1 Host.exe) R st4 := by
    intro st4 hb4 e8 e9 e10 e11 hpc
    obtain ⟨d4, pc4⟩ := st4
    rcases hpc with ⟨hp4, hlt⟩ | ⟨hp4, heq⟩ <;> simp only at hp4 <;> subst hp4
    · exact cont d4 ⟨hb4, hlt, e8, e9, e10, e11⟩
    · exact fin d4 ⟨hb4, by omega, by rw [e8, heq]⟩
  have hx11 : (st.regs.getXReg .X11).toBitVec = BitVec.ofNat 64 (cs.size - i) := by
    rw [hc.x11]; rfl
  have hlast : ((st.regs.getXReg .X11).toBitVec == BitVec.ofNat 64 1) =
      decide (i + 1 = cs.size) := by
    rw [hx11]
    by_cases he : i + 1 = cs.size
    · simp only [he, decide_true]
      rw [show cs.size - i = 1 by omega]
      exact beq_self_eq_true _
    · simp only [he, decide_false]
      apply beq_eq_false_iff_ne.mpr
      intro hq
      have := congrArg BitVec.toNat hq
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
  have hsub : ∀ (x : UInt64), x = (cs.size - i).toUInt64 →
      UInt64.ofBitVec (x.toBitVec - BitVec.ofNat 64 1) = (cs.size - (i + 1)).toUInt64 := by
    intro x hx
    subst hx
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec,
      natCast_toUInt64_toNat (show cs.size - i < 2 ^ 64 by omega),
      natCast_toUInt64_toNat (show cs.size - (i + 1) < 2 ^ 64 by omega), BitVec.toNat_ofNat]
    omega
  have hadd : (st.regs.getXReg .X10).toBitVec + BitVec.ofNat 64 608 =
      m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * (i + 1)) := by
    rw [hc.x10, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 8 + 608 * i + 608 = 8 + 608 * (i + 1) by omega]
  by_cases hle : cs[i].column ≤ 157
  · -- `b2`: the placement's `present` bit
    have hc1 : ((cs[i].column.toUInt64.toBitVec.ult (BitVec.ofNat 64 157)) ||
        (cs[i].column.toUInt64.toBitVec == BitVec.ofNat 64 157)) = true := by
      rw [toBitVec_ult_ofNat (by decide), hcolN]
      by_cases hl157 : cs[i].column < 157
      · simp [hl157]
      · have : cs[i].column = 157 := by omega
        rw [this]
        rfl
    simp only [hc1, ↓reduceIte] at hpc3
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b2Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b2Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_2_at]
      at hpc3
    have hlin := h.in_ok hf3 mem_lay
    simp only at hlin
    have hlb : NativeRustcVm.Layout.layoutBytes = 3912 := rfl
    rw [hlb] at hlin
    let env2 := Env.ofMachine st3.data [(m0.regs.X1.toBitVec, 3912)]
    have hwf2 : env2.WF :=
      Env.wf_of ⟨⟨hlin.1, hlin.2.1⟩, trivial⟩ (List.pairwise_singleton _ _)
    have hx12 : env2.regs .X12 = BitVec.ofNat 64 cs[i].column := by
      show (st3.data.regs.getXReg .X12).toBitVec = _
      rw [e3x12]
      rfl
    have hm2 : Match env2 placeS st3.data :=
      match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
        ⟨by
          show (st3.data.regs.getXReg .X9).toBitVec = _
          rw [k3 .X9 rfl, hc.x9]; simp [Sym.eval], trivial⟩ trivial
        ⟨by show ((t3 .X12).eval env2).toNat < 472; rw [t3_eval hx12 (by omega)]; omega, trivial⟩
        trivial
    have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk2 run_b2 hwf2 hpc3 hm2 fun st2 hm2' hpc2 ↦ ?_
    have hd2 : st2.data.dmem = st3.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hf2 : VFr m0 st2.data := Fr.ofBlock hf3 hm2 hm2' hwf2 rfl rfl rfl (by simp)
    have k2 : ∀ r, (after b2 placeS).reg r = some (.reg r) →
        st2.data.regs.getXReg r = st3.data.regs.getXReg r := fun r hr ↦
      (rv hm2' (by rw [← after_eq run_b2]; exact hr)).trans rfl
    have hb2 : Base cs m0 st2.data := hb3.keep hf2 hd2 fun r hr ↦ k2 r (by
      rw [after_eq run_b2]
      simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    -- the placement word
    have hidx : ((Sym.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (t3 .X12)).eval env2).toNat =
        24 * cs[i].column := by
      rw [idx_eval' (by rw [t3_eval hx12 (by omega)]; omega), t3_eval hx12 (by omega)]
      omega
    have hw : env2.load 0 (120 + 24 * cs[i].column) 8 =
        (NativeRustcVm.wordOf m0.dmem
          (off m0.regs.X1.toBitVec (120 + 24 * cs[i].column))).toBitVec := by
      rw [Ring.load_eq_wordOf]
      exact congrArg UInt64.toBitVec (h.place_word hf3 (by omega))
    have hsome := onStack_isSome h.lay cs[i]
    simp only [show decide (cs[i].column < 158) = true from decide_eq_true (by omega),
      Bool.true_and] at hsome
    have hidx2 : (BitVec.ofInt 64 (BitVec.apply_mem_extend (env2.regs .X12 + env2.regs .X12 <<< 1)
        ⟨.UXTX, .E3⟩)).toNat = 24 * cs[i].column := by
      have := hidx
      simp only [Sym.eval, UnOp.apply, t3, BinOp.apply, Sym.low_W64, Sym.ext_W64, shiftW] at this
      exact this
    have hx8 : env2.regs .X8 = (st.regs.getXReg .X8).toBitVec := by
      show (st3.data.regs.getXReg .X8).toBitVec = _
      rw [k3 .X8 rfl]
    have hx11 : env2.regs .X11 = (st.regs.getXReg .X11).toBitVec := by
      show (st3.data.regs.getXReg .X11).toBitVec = _
      rw [k3 .X11 rfl]
    have hx10 : env2.regs .X10 = (st.regs.getXReg .X10).toBitVec := by
      show (st3.data.regs.getXReg .X10).toBitVec = _
      rw [hm3'.regs .X10 _ rfl, hc.x10]
      show ca + BitVec.ofInt 64 0 = _
      rw [hca]
      simp
    have hp160 : placedOf layout cs i ≤ 160 := (placedOf_le_self i).trans (by omega)
    have e8 : st2.data.regs.getXReg .X8 = (placedOf layout cs (i + 1)).toUInt64 := by
      apply UInt64.toBitVec_inj.mp
      refine (hm2'.regs .X8 _ rfl).trans ?_
      sym_simp
      rw [hidx2, hw, hx8, hc.x8, placedOf_succ hi, hsome]
      by_cases hz :
        NativeRustcVm.wordOf m0.dmem (off m0.regs.X1.toBitVec (120 + 24 * cs[i].column)) = 0
      · simp only [hz, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true, Nat.add_zero]
        exact BitVec.zero_add _
      · have : (NativeRustcVm.wordOf m0.dmem
            (off m0.regs.X1.toBitVec (120 + 24 * cs[i].column))).toBitVec ≠ 0#64 := fun he ↦
          hz (UInt64.toBitVec_inj.mp he)
        have hne : (NativeRustcVm.wordOf m0.dmem
            (off m0.regs.X1.toBitVec (120 + 24 * cs[i].column)) != 0) = true := by
          simpa using hz
        simp only [beq_eq_false_iff_ne.mpr this, Bool.false_eq_true, ↓reduceIte, hne]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, UInt64.toNat_toBitVec,
          natCast_toUInt64_toNat (show placedOf layout cs i < 2 ^ 64 by omega),
          natCast_toUInt64_toNat (show placedOf layout cs i + 1 < 2 ^ 64 by omega)]
        simp
        omega
    simp only [PcOk] at hpc2
    sym_simp at hpc2
    rw [hx11, hlast] at hpc2
    refine tail st2 hb2 e8 ?_ ?_ ?_ ?_
    · exact (hm2'.regs .X9 _ rfl).trans (by show m0.regs.X1.toBitVec + BitVec.ofInt 64 120 = _; rfl)
    · refine (hm2'.regs .X10 _ rfl).trans ?_
      sym_simp
      rw [hx10, hadd]
    · refine (rv hm2' (r := .X11) rfl).trans ?_
      sym_simp
      rw [hx11]
      exact hsub _ hc.x11
    · by_cases he : i + 1 = cs.size
      · simp only [he, decide_true, ↓reduceIte] at hpc2
        rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b5Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b5Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_5_at]
          at hpc2
        exact .inr ⟨hpc2, he⟩
      · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
        exact .inl ⟨hpc2, by omega⟩
  · -- `b4`: not placed
    have hc1 : ((cs[i].column.toUInt64.toBitVec.ult (BitVec.ofNat 64 157)) ||
        (cs[i].column.toUInt64.toBitVec == BitVec.ofNat 64 157)) = false := by
      rw [toBitVec_ult_ofNat (by decide), hcolN]
      have h1 : ¬cs[i].column < 157 := by omega
      have h2 : cs[i].column.toUInt64.toBitVec ≠ BitVec.ofNat 64 157 := fun he ↦ by
        have := congrArg BitVec.toNat he
        rw [UInt64.toNat_toBitVec, hcolN] at this
        simp at this
        omega
      simp [h1, h2]
    simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hpc3
    have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine hf3.regsBlock hk4 run_b4 hpc3 rfl rfl rfl fun st4 hf4 hd4 hm4 hpc4 ↦ ?_
    have hb4 : Base cs m0 st4.data := hb3.keep hf4 hd4 fun r hr ↦ by
      simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (rv hm4 rfl).trans rfl
    have hns : (cs[i].onStack layout).isSome = false := by
      rw [onStack_isSome h.lay cs[i]]
      simp only [show decide (cs[i].column < 158) = false from decide_eq_false (by omega),
        Bool.false_and]
    have hx11 : (st3.data.regs.getXReg .X11).toBitVec = (st.regs.getXReg .X11).toBitVec := by
      rw [k3 .X11 rfl]
    simp only [PcOk] at hpc4
    sym_simp at hpc4
    simp only [Env.ofMachine_regs, hx11, hlast] at hpc4
    refine tail st4 hb4 ?_ ?_ ?_ ?_ ?_
    · refine (rv hm4 (r := .X8) rfl).trans ?_
      sym_simp
      show st3.data.regs.getXReg .X8 = _
      rw [k3 .X8 rfl, hc.x8, placedOf_succ hi, hns]
      rfl
    · rw [(rv hm4 (r := .X9) rfl).trans (show st3.data.regs.getXReg .X9 = _ from k3 .X9 rfl)]
      exact hc.x9
    · refine (hm4.regs .X10 _ rfl).trans ?_
      sym_simp
      show (st3.data.regs.getXReg .X10).toBitVec + BitVec.ofNat 64 608 = _
      rw [hm3'.regs .X10 _ rfl, ← hadd, hc.x10]
      show ca + BitVec.ofInt 64 0 + _ = _
      rw [hca]
      simp
    · refine (rv hm4 (r := .X11) rfl).trans ?_
      sym_simp
      show UInt64.ofBitVec ((st3.data.regs.getXReg .X11).toBitVec - BitVec.ofNat 64 1) = _
      rw [hx11]
      exact hsub _ hc.x11
    · by_cases he : i + 1 = cs.size
      · simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
        exact .inr ⟨hpc4, he⟩
      · simp only [he, decide_false, Bool.not_false, ↓reduceIte] at hpc4
        rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b3Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_3_at]
          at hpc4
        exact .inl ⟨hpc4, by omega⟩

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
