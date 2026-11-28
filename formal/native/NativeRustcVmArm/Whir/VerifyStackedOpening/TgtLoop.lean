module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.First

/-!
# `verify_stacked_opening`: a step of the target's loop

`tgt_step`: at `.LVerifyStackedOpening_17` (`b22`) before claim `i`: `b22` reads its column, `b23`
its placement's `present` word; placed, `b24` (a scale left), `b18` reads the next scale, `b19`
the claim's value and calls `EW::mul`, `b20` adds the product; then (and for a claim not placed)
`b21` steps to the next claim or, after the last, to `.LVerifyStackedOpening_21` (`b26`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **`b21`**: to the next claim or past the last. -/
theorem tgt_tail (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0) {i : Nat}
    (hi : i < cs.size) {R : MachineState → Prop}
    (cont : ∀ st, Tgt a s layout target cs value m0 (i + 1) st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b22Offset)⟩)
    (fin : ∀ st, AtB26 a s layout target cs value m0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset)⟩)
    {st : MachineData} (hc : Common a s layout cs m0 st)
    (x28 : (st.regs.getXReg .X28).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i))
    (x29 : st.regs.getXReg .X29 = (608 * (cs.size - i)).toUInt64)
    (x20 : (st.regs.getXReg .X20).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 120)
    (x19 : (st.regs.getXReg .X19).toBitVec =
      scA m0 + BitVec.ofNat 64 (8 + 16 * (1 + placedOf layout cs (i + 1))))
    (x21 : (st.regs.getXReg .X21).toBitVec = scA m0 + BitVec.ofNat 64 (8 + 16 * cntOf layout cs))
    (acc : (⟨st.regs.getXReg .X27, st.regs.getXReg .X26⟩ : EW) =
      dotL ((scalesOf s layout cs).toList.take (1 + placedOf layout cs (i + 1)))
        ((valsOf layout target cs value).take (1 + placedOf layout cs (i + 1)))) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b21Offset)⟩ := by
  have hcs160 : cs.size ≤ 160 := h.cl.len_le
  have hk21 : b21.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b21Offset) := b21_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hc.fr.regsBlock (st := ⟨st, _⟩) hk21 run_b21 rfl rfl rfl rfl
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  have k1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27],
      st1.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (rv hm1 rfl).trans rfl
  have hc1 : Common a s layout cs m0 st1.data := hc.same hf1 hd1 fun r hr ↦ k1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp)
  have hx29 : (Env.ofMachine st []).regs .X29 = (608 * (cs.size - i)).toUInt64.toBitVec := by
    show (st.regs.getXReg .X29).toBitVec = _; rw [x29]
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hx29] at hpc1
  have e29 : st1.data.regs.getXReg .X29 = (608 * (cs.size - (i + 1))).toUInt64 := by
    refine (rv hm1 (r := .X29) rfl).trans ?_
    sym_simp
    rw [hx29]
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec,
      natCast_toUInt64_toNat (show 608 * (cs.size - i) < 2 ^ 64 by omega),
      natCast_toUInt64_toNat (show 608 * (cs.size - (i + 1)) < 2 ^ 64 by omega), BitVec.toNat_ofNat]
    omega
  have e28 : (st1.data.regs.getXReg .X28).toBitVec =
      m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * (i + 1)) := by
    refine (hm1.regs .X28 _ rfl).trans ?_
    sym_simp
    show (st.regs.getXReg .X28).toBitVec + BitVec.ofNat 64 608 = _
    rw [x28, BitVec.add_assoc, ← BitVec.ofNat_add, show 8 + 608 * i + 608 = 8 + 608 * (i + 1) by
      omega]
  by_cases hl : i + 1 = cs.size
  · have hc : ((608 * (cs.size - i)).toUInt64.toBitVec == BitVec.ofNat 64 608) = true := by
      rw [show cs.size - i = 1 by omega]; rfl
    simp only [hc, ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_21 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_21_at]
      at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1
    subst hpc1
    refine fin d1 ⟨hc1, ?_, ?_, ?_⟩
    · rw [k1 .X19 (by simp), x19, hl]
    · rw [k1 .X21 (by simp), x21]
    · rw [k1 .X27 (by simp), k1 .X26 (by simp), acc, hl]
  · have hc : ((608 * (cs.size - i)).toUInt64.toBitVec == BitVec.ofNat 64 608) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro he
      have := congrArg BitVec.toNat he
      rw [UInt64.toNat_toBitVec, natCast_toUInt64_toNat (by omega)] at this
      simp at this
      omega
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hb21 : b21.length = NativeRustcVmArm.Vm.VerifyStackedOpening.b21Length := NativeRustcVmArm.Vm.VerifyStackedOpening.b21_length
    rw [hb21] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1
    subst hpc1
    exact cont d1 ⟨hc1, by omega, e28, e29, by rw [k1 .X20 (by simp), x20],
      by rw [k1 .X19 (by simp), x19], by rw [k1 .X21 (by simp), x21],
      by rw [k1 .X27 (by simp), k1 .X26 (by simp), acc]⟩

/-- **A step of the target's loop.** -/
theorem tgt_step (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i : Nat} {st : MachineData}
    (ht : Tgt a s layout target cs value m0 i st) {R : MachineState → Prop}
    (cont : ∀ st, Tgt a s layout target cs value m0 (i + 1) st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b22Offset)⟩)
    (fin : ∀ st, AtB26 a s layout target cs value m0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b22Offset)⟩ := by
  have hc := ht.com
  have hi := ht.hi
  have hcs160 : cs.size ≤ 160 := h.cl.len_le
  have hPt : placedOf layout cs cs.size ≤ 160 := (placedOf_le_self _).trans hcs160
  have hPi : placedOf layout cs i ≤ placedOf layout cs cs.size := placedOf_le i
  have hcl := h.in_ok hc.fr mem_cl
  simp only at hcl
  have hcb : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
  rw [hcb] at hcl
  obtain ⟨ca, hca⟩ : ∃ ca, ca = m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i) := ⟨_, rfl⟩
  have hoff : 8 + 608 * i + 608 ≤ 97288 := by omega
  have hcaw : NoWrap ca 608 := by rw [hca]; exact NativeRustcVm.NoWrap.sub hcl.2.1 hoff
  have hcam : ∀ (d : MachineData), VFr m0 d → NativeRustcVm.Mapped d.dmem ca 608 :=
    fun d hf j hj ↦ by
      rw [hca, NativeRustcVm.addr_add_add]
      exact hf.kept _ ((h.ins _ mem_cl).1.1.1 _ (by show _ < 97288; omega))
  -- `b22`: the column
  let env := Env.ofMachine st [(ca, 608)]
  have hwf : env.WF := Env.wf_of ⟨⟨hcam st hc.fr, hcaw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env claim2S st :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by show (st.regs.getXReg .X28).toBitVec = _; rw [ht.x28, hca]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  have hcol : env.load 0 0 8 = cs[i].column.toUInt64.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt st.dmem (ca + BitVec.ofNat 64 0) _
    rw [NativeRustcVm.addr_add_zero, hca]
    exact h.column_word hc.fr hi
  have hclt := (h.cl.claims i hi).column_lt
  have hcolN : cs[i].column.toUInt64.toNat = cs[i].column := natCast_toUInt64_toNat hclt
  have hk22 : b22.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b22Offset) := b22_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk22 run_b22 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have k1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X29],
      st1.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (rv hm1 rfl).trans rfl
  have e1x28 : (st1.data.regs.getXReg .X28).toBitVec =
      m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i) := by
    rw [hm1.regs .X28 _ rfl, ← hca]
    show ca + BitVec.ofInt 64 0 = ca
    simp
  have hc1 : Common a s layout cs m0 st1.data :=
    hc.blk hm hm1 hwf rfl rfl (by decide)
  have e1x8 : st1.data.regs.getXReg .X8 = cs[i].column.toUInt64 :=
    (rv hm1 (r := .X8) rfl).trans (by show UInt64.ofBitVec (env.load 0 0 8) = _; rw [hcol])
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hcol, toBitVec_ult_ofNat (by decide), hcolN] at hpc1
  -- not placed: to `b21` with the same sums
  have notPlaced : ∀ (d : MachineData), Common a s layout cs m0 d →
      (∀ r ∈ [XReg.X19, .X20, .X21, .X26, .X27, .X29], d.regs.getXReg r = st.regs.getXReg r) →
      (d.regs.getXReg .X28).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i) →
      (cs[i].onStack layout).isSome = false →
      Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b21Offset)⟩ := by
    intro d hcd hkd hx28 hns
    have hP1 : placedOf layout cs (i + 1) = placedOf layout cs i := by
      rw [placedOf_succ hi, hns]; rfl
    exact tgt_tail hp h hi cont fin hcd hx28
      (by rw [hkd .X29 (by simp)]; exact ht.x29) (by rw [hkd .X20 (by simp)]; exact ht.x20)
      (by rw [hkd .X19 (by simp), hP1]; exact ht.x19) (by rw [hkd .X21 (by simp)]; exact ht.x21)
      (by rw [hkd .X27 (by simp), hkd .X26 (by simp), hP1]; exact ht.acc)
  by_cases hle : cs[i].column ≤ 157
  swap
  · -- column out of range
    have hc1' : (!decide (cs[i].column < 157) &&
        !(cs[i].column.toUInt64.toBitVec == BitVec.ofNat 64 157)) = true := by
      have h1 : ¬cs[i].column < 157 := by omega
      have h2 : cs[i].column.toUInt64.toBitVec ≠ BitVec.ofNat 64 157 := fun he ↦ by
        have := congrArg BitVec.toNat he
        rw [UInt64.toNat_toBitVec, hcolN] at this
        simp at this
        omega
      simp [h1, h2]
    simp only [hc1', ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_16 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b21Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b21Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_16_at]
      at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1
    subst hpc1
    refine notPlaced d1 hc1 (fun r hr ↦ k1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)) e1x28 ?_
    rw [onStack_isSome h.lay cs[i]]
    simp only [show decide (cs[i].column < 158) = false from decide_eq_false (by omega),
      Bool.false_and]
  have hc1' : (!decide (cs[i].column < 157) &&
      !(cs[i].column.toUInt64.toBitVec == BitVec.ofNat 64 157)) = false := by
    by_cases hl157 : cs[i].column < 157
    · simp [hl157]
    · have : cs[i].column = 157 := by omega
      rw [this]
      rfl
  simp only [hc1', Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b23`: the placement word
  have hlin := h.in_ok hc1.fr mem_lay
  simp only at hlin
  have hlb : NativeRustcVm.Layout.layoutBytes = 3912 := rfl
  rw [hlb] at hlin
  let env2 := Env.ofMachine st1.data [(m0.regs.X1.toBitVec, 3912)]
  have hwf2 : env2.WF := Env.wf_of ⟨⟨hlin.1, hlin.2.1⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hx8 : env2.regs .X8 = BitVec.ofNat 64 cs[i].column := by
    show (st1.data.regs.getXReg .X8).toBitVec = _
    rw [e1x8]
    rfl
  have hm2 : Match env2 place2S st1.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by
        show (st1.data.regs.getXReg .X20).toBitVec = _
        rw [k1 .X20 (by simp), ht.x20]; rfl, trivial⟩ trivial
      ⟨by show ((t3 .X8).eval env2).toNat < 472; rw [t3_eval hx8 (by omega)]; omega, trivial⟩
      trivial
  have hk23 : b23.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b23Offset) := b23_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk23 run_b23 hwf2 hpc1 hm2 fun st2 hm2' hpc2 ↦ ?_
  have k2 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      st2.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (rv hm2' rfl).trans rfl
  have e2x20 : (st2.data.regs.getXReg .X20).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 120 :=
    (hm2'.regs .X20 _ rfl).trans rfl
  have hc2 : Common a s layout cs m0 st2.data := hc1.blk hm2 hm2' hwf2 rfl rfl (by decide)
  have hidx : ((Sym.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (t3 .X8)).eval env2).toNat =
      24 * cs[i].column := by
    rw [idx_eval' (by rw [t3_eval hx8 (by omega)]; omega), t3_eval hx8 (by omega)]
    omega
  have hidx2 : (BitVec.ofInt 64 (BitVec.apply_mem_extend (env2.regs .X8 + env2.regs .X8 <<< 1)
      ⟨.UXTX, .E3⟩)).toNat = 24 * cs[i].column := by
    have := hidx
    simp only [Sym.eval, UnOp.apply, t3, BinOp.apply, Sym.low_W64, Sym.ext_W64, shiftW] at this
    exact this
  have hw : env2.load 0 (120 + 24 * cs[i].column) 8 =
      (NativeRustcVm.wordOf m0.dmem
        (off m0.regs.X1.toBitVec (120 + 24 * cs[i].column))).toBitVec := by
    rw [Ring.load_eq_wordOf]
    exact congrArg UInt64.toBitVec (h.place_word hc1.fr (by omega))
  have hsome := onStack_isSome h.lay cs[i]
  simp only [show decide (cs[i].column < 158) = true from decide_eq_true (by omega),
    Bool.true_and] at hsome
  simp only [PcOk] at hpc2
  sym_simp at hpc2
  rw [hidx2, hw] at hpc2
  by_cases hz : NativeRustcVm.wordOf m0.dmem (off m0.regs.X1.toBitVec (120 + 24 * cs[i].column)) = 0
  · have hc : ((NativeRustcVm.wordOf m0.dmem
        (off m0.regs.X1.toBitVec (120 + 24 * cs[i].column))).toBitVec == 0#64) = true := by
      rw [hz]; rfl
    simp only [hc, ↓reduceIte] at hpc2
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_16 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b21Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b21Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_16_at]
      at hpc2
    obtain ⟨d2, pc2⟩ := st2
    simp only at hpc2
    subst hpc2
    refine notPlaced d2 hc2 (fun r hr ↦ ?_) ?_ (by rw [hsome, hz]; rfl)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [k2 .X19 (by simp), k1 .X19 (by simp)]
      · exact UInt64.toBitVec_inj.mp (e2x20.trans ht.x20.symm)
      · rw [k2 .X21 (by simp), k1 .X21 (by simp)]
      · rw [k2 .X26 (by simp), k1 .X26 (by simp)]
      · rw [k2 .X27 (by simp), k1 .X27 (by simp)]
      · rw [k2 .X29 (by simp), k1 .X29 (by simp)]
    · rw [k2 .X28 (by simp)]; exact e1x28
  have hc : ((NativeRustcVm.wordOf m0.dmem
      (off m0.regs.X1.toBitVec (120 + 24 * cs[i].column))).toBitVec == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    exact fun he ↦ hz (UInt64.toBitVec_inj.mp he)
  simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc2
  have hpl : (cs[i].onStack layout).isSome = true := by
    rw [hsome]; simpa using hz
  obtain ⟨p, hpd⟩ : ∃ p, p = placedOf layout cs i := ⟨_, rfl⟩
  have hP1 : placedOf layout cs (i + 1) = p + 1 := by rw [placedOf_succ hi, hpl, hpd]; rfl
  have hpt : p + 1 ≤ placedOf layout cs cs.size := hP1 ▸ placedOf_le (i + 1)
  have hscb : scalesBytes = 2600 := rfl
  have hnw := h.sc_nw
  rw [hscb] at hnw
  have hsc : ∀ o, o < 2600 → (scA m0 + BitVec.ofNat 64 o).toNat = (scA m0).toNat + o := fun o ho ↦
    NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)
  -- `b24`: a scale left
  have hk24 : b24.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b24Offset) := b24_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hc2.fr.regsBlock hk24 run_b24 hpc2 rfl rfl rfl fun st3 hf3 hd3 hm3 hpc3 ↦ ?_
  have k3 : ∀ r, st3.data.regs.getXReg r = st2.data.regs.getXReg r := fun r ↦
    (rv hm3 (v := .reg r) (by cases r <;> rfl)).trans rfl
  have hc3 : Common a s layout cs m0 st3.data := hc2.same hf3 hd3 fun r _ ↦ k3 r
  have hx19 : (st2.data.regs.getXReg .X19).toBitVec =
      scA m0 + BitVec.ofNat 64 (8 + 16 * (1 + p)) := by
    rw [k2 .X19 (by simp), k1 .X19 (by simp), ht.x19, hpd]
  have hx21 : (st2.data.regs.getXReg .X21).toBitVec =
      scA m0 + BitVec.ofNat 64 (8 + 16 * cntOf layout cs) := by
    rw [k2 .X21 (by simp), k1 .X21 (by simp), ht.x21]
  have hne : ((st2.data.regs.getXReg .X19).toBitVec == (st2.data.regs.getXReg .X21).toBitVec) =
      false := by
    rw [hx19, hx21]
    apply beq_eq_false_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    rw [hsc _ (by omega), BitVec.toNat_add, BitVec.toNat_ofNat] at this
    unfold cntOf at this
    unfold NoWrap at hnw
    have h1 : 8 + 16 * (placedOf layout cs cs.size + 2) < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h1] at this
    omega
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  simp only [Env.ofMachine_regs, hne, Bool.not_false, ↓reduceIte] at hpc3
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_14 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b18Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b18Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_14_at]
    at hpc3
  -- `b18`: the scale
  obtain ⟨sa, hsad⟩ : ∃ sa, sa = scA m0 + BitVec.ofNat 64 (8 + 16 * (1 + p)) := ⟨_, rfl⟩
  have hsaN : sa.toNat = (scA m0).toNat + (8 + 16 * (1 + p)) := by rw [hsad]; exact hsc _ (by omega)
  let env4 := Env.ofMachine st3.data [(sa, 16)]
  have hwf4 : env4.WF :=
    Env.wf_of ⟨⟨fun j hj ↦ by
        rw [hsad, NativeRustcVm.addr_add_add]
        exact hc3.fr.kept _ (h.so.1.1 _ (by rw [hscb]; omega)),
      by show sa.toNat + 16 ≤ 2 ^ 64; rw [hsaN]; unfold NoWrap at hnw; omega⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm4 : Match env4 scale2S st3.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by show (st3.data.regs.getXReg .X19).toBitVec = _; rw [k3, hx19, hsad]; simp [Sym.eval],
        trivial⟩ trivial trivial trivial
  have hlen : 1 + p < (scalesOf s layout cs).toList.length := by
    rw [Array.length_toList, size_scalesOf]; unfold cntOf; omega
  have hsce := NativeRustcVm.ewAt_iff.mp (NativeRustcVm.ewsAt_getElem hc3.scs hlen)
  rw [NativeRustcVm.addr_add_add, show 8 + 16 * (1 + p) = 8 + 16 * (1 + p) from rfl, ← hsad]
    at hsce
  have hl0 : env4.load 0 0 8 = (scalesOf s layout cs).toList[1 + p].c0.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt st3.data.dmem (sa + BitVec.ofNat 64 0) _
    rw [NativeRustcVm.addr_add_zero]; exact hsce.1
  have hl8 : env4.load 0 8 8 = (scalesOf s layout cs).toList[1 + p].c1.toBitVec :=
    Ring.load_word hsce.2
  have hk18 : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b18Offset) := b18_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk18 run_b18 hwf4 hpc3 hm4 fun st4 hm4' hpc4 ↦ ?_
  have hc4 : Common a s layout cs m0 st4.data := hc3.blk hm4 hm4' hwf4 rfl rfl (by decide)
  have k4 : ∀ r ∈ [XReg.X20, .X21, .X26, .X27, .X28, .X29],
      st4.data.regs.getXReg r = st3.data.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (rv hm4' rfl).trans rfl
  have e4x19 : (st4.data.regs.getXReg .X19).toBitVec =
      scA m0 + BitVec.ofNat 64 (8 + 16 * (1 + (p + 1))) := by
    refine (hm4'.regs .X19 _ rfl).trans ?_
    show sa + BitVec.ofInt 64 16 = _
    rw [hsad, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    congr 2
  have e4x0 : st4.data.regs.X0 = (scalesOf s layout cs).toList[1 + p].c0 :=
    (rv hm4' (r := .X0) rfl).trans (by show UInt64.ofBitVec (env4.load 0 0 8) = _; rw [hl0])
  have e4x1 : st4.data.regs.X1 = (scalesOf s layout cs).toList[1 + p].c1 :=
    (rv hm4' (r := .X1) rfl).trans (by show UInt64.ofBitVec (env4.load 0 8 8) = _; rw [hl8])
  simp only [PcOk] at hpc4
  have hb18 : b18.length = NativeRustcVmArm.Vm.VerifyStackedOpening.b18Length := NativeRustcVmArm.Vm.VerifyStackedOpening.b18_length
  rw [hb18] at hpc4
  -- `b19`: the claim's value, `EW::mul`
  let env5 := Env.ofMachine st4.data [(ca, 608)]
  have hwf5 : env5.WF :=
    Env.wf_of ⟨⟨hcam _ hc4.fr, hcaw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm5 : Match env5 claim2S st4.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by
        show (st4.data.regs.getXReg .X28).toBitVec = _
        rw [k4 .X28 (by simp), k3, k2 .X28 (by simp), e1x28, hca]
        simp [Sym.eval], trivial⟩
      trivial trivial trivial
  have hsame := h.same_in hc4.fr mem_cl
  simp only at hsame
  rw [hcb] at hsame
  have hv : NativeRustcVm.EWAt m0.dmem (m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i) +
      BitVec.ofNat 64 592) cs[i].value := (h.cl.claims i hi).value
  rw [NativeRustcVm.addr_add_add] at hv
  have hval := NativeRustcVm.ewAt_iff.mp (NativeRustcVm.Layout.EWAt.of_same hv
    (hsame.sub (o := 8 + 608 * i + 592) (k := 16) (by omega)) le_rfl)
  have hv0 : env5.load 0 592 8 = cs[i].value.c0.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt st4.data.dmem (ca + BitVec.ofNat 64 592) _
    rw [hca, NativeRustcVm.addr_add_add]; exact hval.1
  have hv8 : env5.load 0 600 8 = cs[i].value.c1.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt st4.data.dmem (ca + BitVec.ofNat 64 600) _
    rw [hca, NativeRustcVm.addr_add_add]
    have := hval.2
    rwa [NativeRustcVm.addr_add_add] at this
  have hk19 : b19.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b19Offset) := b19_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk19 run_b19 hwf5 hpc4 hm5 fun st5 hm5' hpc5 ↦ ?_
  have hc5 : Common a s layout cs m0 st5.data := hc4.blk hm5 hm5' hwf5 rfl rfl (by decide)
  have e5x28 : (st5.data.regs.getXReg .X28).toBitVec =
      m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i) := by
    rw [hm5'.regs .X28 _ rfl, ← hca]
    show ca + BitVec.ofInt 64 0 = ca
    simp
  have k5 : ∀ r ∈ [XReg.X19, .X20, .X21, .X26, .X27, .X29],
      st5.data.regs.getXReg r = st4.data.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (rv hm5' rfl).trans rfl
  have e5 : (⟨st5.data.regs.X0, st5.data.regs.X1⟩ : EW) = (scalesOf s layout cs).toList[1 + p] := by
    rw [show st5.data.regs.X0 = st4.data.regs.X0 from (rv hm5' (r := .X0) rfl).trans rfl,
      show st5.data.regs.X1 = st4.data.regs.X1 from (rv hm5' (r := .X1) rfl).trans rfl, e4x0, e4x1]
  have e5' : (⟨st5.data.regs.X2, st5.data.regs.X3⟩ : EW) = cs[i].value := by
    rw [show st5.data.regs.X2 = UInt64.ofBitVec (env5.load 0 592 8) from
        (rv hm5' (r := .X2) rfl).trans rfl,
      show st5.data.regs.X3 = UInt64.ofBitVec (env5.load 0 600 8) from
        (rv hm5' (r := .X3) rfl).trans rfl, hv0, hv8]
  refine mul_call h hmul hc5.fr hpc5 fun m6 hf6 h0 h1 hcs6 hs6 hk6 ↦ ?_
  have hc6 := hc5.call h hf6 (by rw [stack_eq]; decide) hs6 hk6 hcs6
  rw [e5, e5'] at h0 h1
  -- `b20`: added
  have hk20 : b20.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b20Offset) := b20_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hf6.regsBlock (st := ⟨m6, _⟩) hk20 run_b20 rfl rfl rfl rfl
    fun st7 hf7 hd7 hm7 hpc7 ↦ ?_
  simp only [PcOk] at hpc7
  obtain ⟨d7, pc7⟩ := st7
  simp only at hpc7
  subst hpc7
  have k7 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X28, .X29],
      d7.regs.getXReg r = m6.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (rv hm7 rfl).trans rfl
  have hc7 : Common a s layout cs m0 d7 := hc6.same hf7 hd7 fun r hr ↦ k7 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp)
  have kk : ∀ r ∈ [XReg.X19, .X20, .X21, .X26, .X27, .X29], calleeSaved r = true →
      m6.regs.getXReg r = st4.data.regs.getXReg r := fun r hr hcr ↦ by
    rw [hcs6 r hcr, k5 r hr]
  have hb : b20.length = NativeRustcVmArm.Vm.VerifyStackedOpening.b20Length := NativeRustcVmArm.Vm.VerifyStackedOpening.b20_length
  rw [hb]
  have hlv : 1 + p < (valsOf layout target cs value).length := by
    rw [length_valsOf]; omega
  have hvv : (valsOf layout target cs value)[1 + p] = cs[i].value := by
    have := vals_placed (layout := layout) hi hpl target value
    rw [← hpd, Nat.add_comm p 1, List.getElem?_eq_getElem hlv] at this
    exact Option.some.inj this
  refine tgt_tail hp h hi cont fin hc7 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [k7 .X28 (by simp), hcs6 .X28 rfl]; exact e5x28
  · rw [k7 .X29 (by simp), kk .X29 (by simp) rfl, k4 .X29 (by simp), k3, k2 .X29 (by simp),
      k1 .X29 (by simp)]; exact ht.x29
  · rw [k7 .X20 (by simp), kk .X20 (by simp) rfl, k4 .X20 (by simp), k3]; exact e2x20
  · rw [k7 .X19 (by simp), kk .X19 (by simp) rfl, hP1]; exact e4x19
  · rw [k7 .X21 (by simp), kk .X21 (by simp) rfl, k4 .X21 (by simp), k3]; exact hx21
  · have hacc' := ht.acc
    rw [← hpd] at hacc'
    have e27 : d7.regs.getXReg .X27 = m6.regs.X0 ^^^ m6.regs.getXReg .X27 :=
      (rv hm7 (r := .X27) rfl).trans (by sym_simp; rfl)
    have e26 : d7.regs.getXReg .X26 = m6.regs.X1 ^^^ m6.regs.getXReg .X26 :=
      (rv hm7 (r := .X26) rfl).trans (by sym_simp; rfl)
    rw [e27, e26, kk .X27 (by simp) rfl, kk .X26 (by simp) rfl, k4 .X27 (by simp),
      k4 .X26 (by simp), k3 .X27, k3 .X26, k2 .X27 (by simp), k2 .X26 (by simp),
      k1 .X27 (by simp), k1 .X26 (by simp), hP1,
      show 1 + (p + 1) = (1 + p) + 1 by omega, dotL_take_succ hlen hlv, ← hacc', h0, h1,
      hvv]
    show (⟨_, _⟩ : EW) = ⟨_ ^^^ _, _ ^^^ _⟩
    rw [UInt64.xor_comm (st.regs.getXReg .X27), UInt64.xor_comm (st.regs.getXReg .X26)]
    rfl

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
