module

public import NativeRustcVmArm.Whir.LanesOf.Ret

/-!
# `lanes_of` at level `0`: the row reversed, the loops

A turn (`rv_step`, `b9`) writes four lanes, the row's words from the end; after the turns (`RvEnd`)
`b10` ends with `Some(len)` when they covered the row, else the tail: `b11` (`rv_tail`), a turn
(`rv1_step`, `b12`, `b13`) writes one lane.
-/

namespace NativeRustcVmArm.Whir.LanesOf

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.LanesOf

/-- After `b9`'s turns. -/
@[expose] public def RvEnd (m0 st : MachineData) : Prop :=
  Body m0 (revL m0) (4 * qOf m0) st ∧ st.regs.X2.toNat = lenOf m0 ∧
    st.regs.X11.toNat = lenOf m0 ∧ st.regs.X12.toNat = 4 * qOf m0 ∧
    st.regs.X8.toBitVec = outOf m0 + BitVec.ofNat 64 (64 * qOf m0) ∧
    st.regs.X10.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * (lenOf m0 - 4 * qOf m0)) ∧
    st.regs.X9.toNat = 16 * lenOf m0 ∧ lenOf m0 < 65

public section

variable [Host] {k : Nat}

/-- **A four-lane turn** (`b9`). -/
theorem rv_step (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0) {j : Nat}
    {st : MachineData} (hL : RvLoop m0 j st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (RvEnd m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b10Offset)) ∨
        (RvLoop m0 (j + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b9Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b9Offset)⟩ := by
  have hb := hL.body
  have hj := hL.hj
  have hn := hL.hn
  unfold qOf at hj
  have hnw : NativeRustcVm.NoWrap (outOf m0) 1024 := (pre_parts hpre).2.1.1.2
  let o := lenOf m0 - 4 - 4 * j
  have hwf : (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * o), 32),
      (outOf m0 + BitVec.ofNat 64 (16 * (4 * j)), 64)]).WF :=
    wf_two hpre hb.fr (by omega) (by omega) (by omega) (by omega)
  have hm : Match (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * o), 32),
      (outOf m0 + BitVec.ofNat 64 (16 * (4 * j)), 64)]) revS st :=
    match_ofMachine
      ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by
        show st.regs.X14.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * o) + BitVec.ofNat 64 16
        rw [hL.x14, addr_add, show 8 * o + 16 = 8 * lenOf m0 - 16 - 32 * j by omega],
       by
        show st.regs.X13.toBitVec = outOf m0 + BitVec.ofNat 64 (16 * (4 * j)) + BitVec.ofNat 64 32
        rw [hL.x13, addr_add, show 16 * (4 * j) + 32 = 64 * j + 32 by omega], trivial⟩
      trivial trivial trivial
  refine exec_then (inf hp b9_in_code (by simp [b9])) run_b9 hwf hm fun s hm' hpc ↦ ?_
  have hk := after_eq run_b9 ▸ b9_keeps
  have hfr := hb.fr.of_lanes hpre hm hm' hwf rfl hk.1 (c := 4 * j) rfl le_rfl hk.2 (by omega)
  have hsame := same_region hm' hwf (r := 1) rfl hk.2
  have w0 := Match.ewAt_write hm' (r := 1) (o := 0) rfl (by decide) (v0 := .load 0 24 8)
    (v1 := .lit 0) (by decide) (by decide)
  have w1 := Match.ewAt_write hm' (r := 1) (o := 16) rfl (by decide) (v0 := .load 0 16 8)
    (v1 := .lit 0) (by decide) (by decide)
  have w2 := Match.ewAt_write hm' (r := 1) (o := 32) rfl (by decide) (v0 := .load 0 8 8)
    (v1 := .lit 0) (by decide) (by decide)
  have w3 := Match.ewAt_write hm' (r := 1) (o := 48) rfl (by decide) (v0 := .load 0 0 8)
    (v1 := .lit 0) (by decide) (by decide)
  rw [load_eval hpre hb.fr (t := 3) rfl (by omega), addr_add, revL_of (c := 4 * j + 0) (by omega),
    show 16 * (4 * j) + 0 = 16 * (4 * j + 0) by omega] at w0
  rw [load_eval hpre hb.fr (t := 2) rfl (by omega), addr_add, revL_of (c := 4 * j + 1) (by omega),
    show 16 * (4 * j) + 16 = 16 * (4 * j + 1) by omega] at w1
  rw [load_eval hpre hb.fr (t := 1) rfl (by omega), addr_add, revL_of (c := 4 * j + 2) (by omega),
    show 16 * (4 * j) + 32 = 16 * (4 * j + 2) by omega] at w2
  rw [load_eval hpre hb.fr (t := 0) rfl (by omega), addr_add, revL_of (c := 4 * j + 3) (by omega),
    show 16 * (4 * j) + 48 = 16 * (4 * j + 3) by omega] at w3
  have hl : Lanes m0 (revL m0) (4 * j + 4) s.data :=
    hb.lanes.extend (w := 4) hnw (by omega) hsame fun t ht ↦
      match t, ht with
      | 0, _ => w0
      | 1, _ => w1
      | 2, _ => w2
      | 3, _ => w3
  have hb' : Body m0 (revL m0) (4 * j + 4) s.data :=
    ⟨hfr, hl, (reg_kept hm' (r := .X1) rfl).trans hb.x1, (reg_kept hm' (r := .X3) rfl).trans hb.x3,
      (reg_kept hm' (r := .X30) rfl).trans hb.x30⟩
  have h15 : (st.regs.getXReg .X15).toBitVec.toNat = 4 * qOf m0 - 4 * j := hL.x15
  have kp : ∀ r ∈ [XReg.X2, .X8, .X9, .X10, .X11, .X12], s.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact reg_kept hm' rfl
  have hc : ((SBool.cmp .eq .W64 (.bin .sub .W64 (.reg .X15) (.lit 4)) (.lit 0)).not.eval
      (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * o), 32),
        (outOf m0 + BitVec.ofNat 64 (16 * (4 * j)), 64)])) = decide (j + 1 ≠ qOf m0) := by
    sym_simp
    rw [Env.ofMachine_regs, bv_beq_toNat, toNat_sub_ofNat (by rw [h15]; unfold qOf; omega), h15,
      toNat_ofNat_lt (by decide)]
    by_cases h : j + 1 = qOf m0
    · simp [h]; omega
    · simp [h]; unfold qOf at h ⊢; omega
  by_cases hlast : j + 1 = qOf m0
  · have hpc' := pc_fall hpc (by rw [hc]; simp [hlast])
    refine .done _ (.inl ⟨⟨by rw [← hlast]; exact hb', ?_, ?_, ?_, ?_, ?_, ?_, hn⟩, hpc'⟩)
    · rw [show s.data.regs.X2 = st.regs.X2 from kp .X2 (by simp)]; exact hL.x2
    · rw [show s.data.regs.X11 = st.regs.X11 from kp .X11 (by simp)]; exact hL.x11
    · rw [show s.data.regs.X12 = st.regs.X12 from kp .X12 (by simp)]; exact hL.x12
    · rw [show s.data.regs.X8 = st.regs.X8 from kp .X8 (by simp)]; exact hL.x8
    · rw [show s.data.regs.X10 = st.regs.X10 from kp .X10 (by simp)]; exact hL.x10
    · rw [show s.data.regs.X9 = st.regs.X9 from kp .X9 (by simp)]; exact hL.x9
  · have hpc' := pc_taken hpc (by rw [hc]; simp [hlast])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b9Offset) NativeRustcVmArm.Vm.LanesOf.label_9_at] at hpc'
    refine .done _ (.inr ⟨⟨by rw [show 4 * (j + 1) = 4 * j + 4 by omega]; exact hb', ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, by unfold qOf at hlast ⊢; omega, hn⟩, hpc'⟩)
    · rw [show s.data.regs.X2 = st.regs.X2 from kp .X2 (by simp)]; exact hL.x2
    · rw [show s.data.regs.X11 = st.regs.X11 from kp .X11 (by simp)]; exact hL.x11
    · rw [show s.data.regs.X12 = st.regs.X12 from kp .X12 (by simp)]; exact hL.x12
    · have h := hm'.regs .X15 _ rfl
      sym_simp at h
      rw [Env.ofMachine_regs] at h
      refine toNat_of_eq h ?_
      rw [toNat_sub_ofNat (by rw [h15]; unfold qOf; omega), h15]
      omega
    · have h := hm'.regs .X14 _ rfl
      simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some] at h
      rw [add_ofInt_neg _ (n := 8 * o) (z := -16) (c := 16) (by omega)
        (by unfold qOf at hlast; omega)] at h
      rw [show 8 * lenOf m0 - 16 - 32 * (j + 1) = 8 * o - 16 by unfold qOf at hlast; omega]
      exact h
    · have h : (s.data.regs.getXReg .X13).toBitVec =
          outOf m0 + BitVec.ofNat 64 (16 * (4 * j)) + BitVec.ofInt 64 96 := hm'.regs .X13 _ rfl
      rw [show BitVec.ofInt 64 96 = BitVec.ofNat 64 96 from rfl, addr_add,
        show 16 * (4 * j) + 96 = 64 * (j + 1) + 32 by omega] at h
      exact h
    · rw [show s.data.regs.X8 = st.regs.X8 from kp .X8 (by simp)]; exact hL.x8
    · rw [show s.data.regs.X10 = st.regs.X10 from kp .X10 (by simp)]; exact hL.x10
    · rw [show s.data.regs.X9 = st.regs.X9 from kp .X9 (by simp)]; exact hL.x9

/-- **A one-lane turn** (`b12`, `b13`). -/
theorem rv1_step (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0) {i : Nat}
    {st : MachineData} (hL : Rv1Loop m0 i st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Done m0 (revL m0) (lenOf m0) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b14Offset)) ∨
        (Rv1Loop m0 (i + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b12Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b12Offset)⟩ := by
  have hb := hL.body
  have hi := hL.hi
  have hn := hL.hn
  have hnw : NativeRustcVm.NoWrap (outOf m0) 1024 := (pre_parts hpre).2.1.1.2
  have hrw : (rowOf m0).toNat + 8 * lenOf m0 ≤ 2 ^ 64 := (pre_parts hpre).1.1.2
  have hnw' : (outOf m0).toNat + 1024 ≤ 2 ^ 64 := hnw
  let o := lenOf m0 - 1 - i
  have hwf : (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * o), 8),
      (outOf m0 + BitVec.ofNat 64 (16 * i), 16)]).WF :=
    wf_two hpre hb.fr (by omega) (by omega) (by omega) (by omega)
  have hm : Match (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * o), 8),
      (outOf m0 + BitVec.ofNat 64 (16 * i), 16)]) rev1S st :=
    match_ofMachine
      ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by
        show st.regs.X11.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * o) + BitVec.ofInt 64 0
        rw [hL.x11, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero],
       by
        show st.regs.X8.toBitVec = outOf m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 0
        rw [hL.x8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
      trivial trivial trivial
  refine exec_then (inf hp b12_in_code (by simp [b12])) run_b12 hwf hm fun s hm' hpc ↦ ?_
  have hk := after_eq run_b12 ▸ b12_keeps
  have hfr := hb.fr.of_lanes hpre hm hm' hwf rfl hk.1 (c := i) rfl le_rfl hk.2 (by omega)
  have hsame := same_region hm' hwf (r := 1) rfl hk.2
  have w0 := Match.ewAt_write hm' (r := 1) (o := 0) rfl (by decide) (v0 := .load 0 0 8)
    (v1 := .lit 0) (by decide) (by decide)
  rw [load_eval hpre hb.fr (t := 0) rfl (by omega), NativeRustcVm.addr_add_zero,
    revL_of (c := i + 0) (by omega), show 16 * i = 16 * (i + 0) by omega] at w0
  have hl : Lanes m0 (revL m0) (i + 1) s.data :=
    hb.lanes.extend (w := 1) hnw (by omega) hsame fun t ht ↦
      match t, ht with
      | 0, _ => w0
  have hb' : Body m0 (revL m0) (i + 1) s.data :=
    ⟨hfr, hl, (reg_kept hm' (r := .X1) rfl).trans hb.x1, (reg_kept hm' (r := .X3) rfl).trans hb.x3,
      (reg_kept hm' (r := .X30) rfl).trans hb.x30⟩
  have x0 : s.data.regs.X0 = 1 := (reg_kept hm' (r := .X0) rfl).trans hL.x0
  have x2 : s.data.regs.X2 = st.regs.X2 := reg_kept hm' (r := .X2) rfl
  have x9 : s.data.regs.X9 = st.regs.X9 := reg_kept hm' (r := .X9) rfl
  have x10 : s.data.regs.X10 = st.regs.X10 := reg_kept hm' (r := .X10) rfl
  have hc : (SBool.cmp .eq .W64 (.ptr 1 16) (.reg .X9)).eval
      (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * o), 8),
        (outOf m0 + BitVec.ofNat 64 (16 * i), 16)]) = decide (i + 1 = lenOf m0) := by
    sym_simp
    rw [Env.ofMachine_regs, bv_beq_toNat]
    show decide ((outOf m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 16).toNat =
      st.regs.X9.toBitVec.toNat) = _
    rw [hL.x9, addr_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    by_cases h : i + 1 = lenOf m0
    · simp [h]; omega
    · simp [h]; omega
  by_cases hlast : i + 1 = lenOf m0
  · have hpc' := pc_taken hpc (by rw [hc]; simp [hlast])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b14Offset) NativeRustcVmArm.Vm.LanesOf.label_14_at] at hpc'
    refine .done _ (.inl ⟨⟨by rw [← hlast]; exact hb', x0, by rw [x2]; exact hL.x2⟩, hpc'⟩)
  have hpc' := pc_fall hpc (by rw [hc]; simp [hlast])
  refine goto hpc' ?_
  -- `b13`
  refine exec_then (inf hp b13_in_code (by simp [b13])) run_b13 (Env.wf_nil _) (match_nil _)
    fun s2 hm2 hpc2 ↦ ?_
  have hk2 := after_eq run_b13 ▸ b13_keeps
  have hb2 := hb'.of_regsS hm2 hk2.1 hk2.2 rfl rfl rfl
  have hc2 : ((SBool.cmp .eq .W64 (.reg .X10) (.reg .X1)).not.eval (Env.ofMachine s.data [])) =
      true := by
    sym_simp
    rw [Env.ofMachine_regs, Env.ofMachine_regs, bv_beq_toNat]
    show (!decide (s.data.regs.X10.toBitVec.toNat = s.data.regs.X1.toBitVec.toNat)) = true
    rw [x10, hL.x10, show s.data.regs.X1 = m0.regs.X1 from hb'.x1,
      toNat_add_ofNat' (by omega)]
    simp only [rowOf]
    simp
    omega
  have hpc2' := pc_taken hpc2 hc2
  rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b12Offset) NativeRustcVmArm.Vm.LanesOf.label_12_at] at hpc2'
  have x11 : (s.data.regs.getXReg .X11).toBitVec =
      rowOf m0 + BitVec.ofNat 64 (8 * (lenOf m0 - 1 - (i + 1))) := by
    have h := hm'.regs .X11 _ rfl
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some] at h
    rw [add_ofInt_neg _ (n := 8 * o) (z := -8) (c := 8) (by omega) (by omega)] at h
    rw [h, show 8 * o - 8 = 8 * (lenOf m0 - 1 - (i + 1)) by omega]
  refine .done _ (.inr ⟨⟨hb2, (reg_kept hm2 (r := .X0) rfl).trans x0, ?_, ?_, ?_, ?_, ?_,
    by omega, hn⟩, hpc2'⟩)
  · rw [show s2.data.regs.X2 = s.data.regs.X2 from reg_kept hm2 (r := .X2) rfl, x2]; exact hL.x2
  · have h := hm2.regs .X8 _ rfl
    show (s2.data.regs.getXReg .X8).toBitVec = _
    rw [h]
    show (s.data.regs.getXReg .X12).toBitVec = _
    have h12 : (s.data.regs.getXReg .X12).toBitVec =
        outOf m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 16 := hm'.regs .X12 _ rfl
    rw [h12, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, addr_add,
      show 16 * i + 16 = 16 * (i + 1) by omega]
  · rw [show s2.data.regs.X9 = s.data.regs.X9 from reg_kept hm2 (r := .X9) rfl, x9]; exact hL.x9
  · have h := hm2.regs .X10 _ rfl
    show (s2.data.regs.getXReg .X10).toBitVec = _
    rw [h]
    exact x11
  · show (s2.data.regs.getXReg .X11).toBitVec = _
    rw [reg_kept hm2 (r := .X11) rfl]
    exact x11

/-- **The tail's head** (`b11`): from lane `e`. -/
theorem rv_tail (hp : Placed code k) {m0 : MachineData} {e : Nat} {st : MachineData}
    (hT : RvTail m0 e st) :
    Eventually (step1 Host.exe) (fun s ↦ Rv1Loop m0 e s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b12Offset))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b11Offset)⟩ := by
  have he := hT.he
  have hn := hT.hn
  refine exec_then (inf hp b11_in_code (by simp [b11])) run_b11 (Env.wf_nil _) (match_nil _)
    fun s hm hpc ↦ .done _ ⟨?_, hpc⟩
  have hk := after_eq run_b11 ▸ b11_keeps
  have x10 : ∀ r ∈ [XReg.X10, .X11], (s.data.regs.getXReg r).toBitVec =
      rowOf m0 + BitVec.ofNat 64 (8 * (lenOf m0 - 1 - e)) := by
    intro r hr
    have h : (s.data.regs.getXReg r).toBitVec = st.regs.X10.toBitVec - BitVec.ofNat 64 8 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · have h := hm.regs .X10 _ rfl; sym_simp at h; exact h
      · have h := hm.regs .X11 _ rfl; sym_simp at h; exact h
    rw [h, hT.x10, sub_ofNat _ (by omega), show 8 * (lenOf m0 - e) - 8 = 8 * (lenOf m0 - 1 - e) by
      omega]
  refine ⟨hT.body.of_regsS hm hk.1 hk.2 rfl rfl rfl, UInt64.toBitVec_inj.mp (hm.regs .X0 _ rfl),
    by rw [show s.data.regs.X2 = st.regs.X2 from reg_kept hm (r := .X2) rfl]; exact hT.x2, ?_, ?_,
    x10 .X10 (by simp), x10 .X11 (by simp), he, hn⟩
  · show (s.data.regs.getXReg .X8).toBitVec = _
    rw [reg_kept hm (r := .X8) rfl]
    exact hT.x8
  · have h := hm.regs .X9 _ rfl
    sym_simp at h
    show (s.data.regs.getXReg .X9).toBitVec = _
    rw [h, Env.ofMachine_regs, Env.ofMachine_regs]
    show st.regs.X3.toBitVec + st.regs.X9.toBitVec = m0.regs.X3.toBitVec + _
    rw [hT.body.x3, show st.regs.X9.toBitVec = BitVec.ofNat 64 (16 * lenOf m0) from
      BitVec.eq_of_toNat_eq (by rw [toNat_ofNat_lt (by omega)]; exact hT.x9)]

end

end NativeRustcVmArm.Whir.LanesOf
