module

public import NativeRustcVmArm.Whir.LanesOf.Ret

/-!
# `lanes_of` at a later level: the row's pairs

`index ≠ 0`, `n = len / 2` lanes. `b1`: `None` for `len ≥ 130`; `b2`: `Some(0)` for `n = 0`; `b3`,
`b4`: one lane, the tail from lane `0`; `b16`: the turns' head. A turn (`cp_step`, `b17`) copies two
lanes, `b18` ends with `Some(n)` for an even `n`, else the tail: `b20` (`cp_tail`), a turn
(`cp1_step`, `b21`) copies one lane, `b22` to the end `b14`.
-/

namespace NativeRustcVmArm.Whir.LanesOf

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.LanesOf

/-- After `b17`'s turns. -/
@[expose] public def CpEnd (m0 st : MachineData) : Prop :=
  Body m0 (pairL m0) (2 * (nOf m0 / 2)) st ∧ st.regs.X2.toNat = nOf m0 ∧
    st.regs.X8.toNat = 2 * (nOf m0 / 2) ∧ lenOf m0 < 130

public section

variable [Host] {k : Nat}

/-- **A two-lane turn** (`b17`). -/
theorem cp_step (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0) {j : Nat}
    {st : MachineData} (hL : CpLoop m0 j st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (CpEnd m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b18Offset)) ∨
        (CpLoop m0 (j + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b17Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b17Offset)⟩ := by
  have hb := hL.body
  have hj := hL.hj
  have hn := hL.hn
  unfold nOf at hj
  have hnw : NativeRustcVm.NoWrap (outOf m0) 1024 := (pre_parts hpre).2.1.1.2
  have hwf : (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * (4 * j)), 32),
      (outOf m0 + BitVec.ofNat 64 (16 * (2 * j)), 32)]).WF :=
    wf_two hpre hb.fr (by omega) (by omega) (by omega) (by omega)
  have hm : Match (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * (4 * j)), 32),
      (outOf m0 + BitVec.ofNat 64 (16 * (2 * j)), 32)]) cpS st :=
    match_ofMachine
      ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by
        show st.regs.X10.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * (4 * j)) + BitVec.ofNat 64 16
        rw [hL.x10, addr_add, show 8 * (4 * j) + 16 = 32 * j + 16 by omega],
       by
        show st.regs.X9.toBitVec = outOf m0 + BitVec.ofNat 64 (16 * (2 * j)) + BitVec.ofNat 64 16
        rw [hL.x9, addr_add, show 16 * (2 * j) + 16 = 32 * j + 16 by omega], trivial⟩
      trivial trivial trivial
  refine exec_then (inf hp b17_in_code (by simp [b17])) run_b17 hwf hm fun s hm' hpc ↦ ?_
  have hk := after_eq run_b17 ▸ b17_keeps
  have hfr := hb.fr.of_lanes hpre hm hm' hwf rfl hk.1 (c := 2 * j) rfl le_rfl hk.2 (by omega)
  have hsame := same_region hm' hwf (r := 1) rfl hk.2
  -- the two lanes
  have w0 := Match.ewAt_write hm' (r := 1) (o := 0) rfl (by decide) (v0 := .load 0 0 8)
    (v1 := .load 0 8 8) (by decide) (by decide)
  have w1 := Match.ewAt_write hm' (r := 1) (o := 16) rfl (by decide) (v0 := .load 0 16 8)
    (v1 := .load 0 24 8) (by decide) (by decide)
  rw [load_eval hpre hb.fr (t := 0) rfl (by omega), load_eval hpre hb.fr (t := 1) rfl (by omega),
    addr_add, show 4 * j + 0 = 2 * (2 * j + 0) by omega,
    show 4 * j + 1 = 2 * (2 * j + 0) + 1 by omega,
    show 16 * (2 * j) + 0 = 16 * (2 * j + 0) by omega] at w0
  rw [load_eval hpre hb.fr (t := 2) rfl (by omega), load_eval hpre hb.fr (t := 3) rfl (by omega),
    addr_add, show 4 * j + 2 = 2 * (2 * j + 1) by omega,
    show 4 * j + 3 = 2 * (2 * j + 1) + 1 by omega,
    show 16 * (2 * j) + 16 = 16 * (2 * j + 1) by omega] at w1
  have hl : Lanes m0 (pairL m0) (2 * j + 2) s.data :=
    hb.lanes.extend (w := 2) hnw (by omega) hsame fun t ht ↦
      match t, ht with
      | 0, _ => w0
      | 1, _ => w1
  have hb' : Body m0 (pairL m0) (2 * j + 2) s.data :=
    ⟨hfr, hl, (reg_kept hm' (r := .X1) rfl).trans hb.x1, (reg_kept hm' (r := .X3) rfl).trans hb.x3,
      (reg_kept hm' (r := .X30) rfl).trans hb.x30⟩
  -- the registers
  have h11 : (st.regs.getXReg .X11).toBitVec.toNat = 2 * (nOf m0 / 2) - 2 * j := hL.x11
  have x2 : s.data.regs.X2 = st.regs.X2 := reg_kept hm' (r := .X2) rfl
  have x8 : s.data.regs.X8 = st.regs.X8 := reg_kept hm' (r := .X8) rfl
  have x11 : s.data.regs.X11.toNat = 2 * (nOf m0 / 2) - 2 * (j + 1) := by
    have h := hm'.regs .X11 _ rfl
    sym_simp at h
    rw [Env.ofMachine_regs] at h
    refine toNat_of_eq h ?_
    rw [toNat_sub_ofNat (by rw [h11]; unfold nOf; omega), h11]
    omega
  have x9 : s.data.regs.X9.toBitVec = outOf m0 + BitVec.ofNat 64 (32 * (j + 1) + 16) := by
    have h : (s.data.regs.getXReg .X9).toBitVec =
        outOf m0 + BitVec.ofNat 64 (16 * (2 * j)) + BitVec.ofInt 64 48 := hm'.regs .X9 _ rfl
    rw [show BitVec.ofInt 64 48 = BitVec.ofNat 64 48 from rfl, addr_add,
      show 16 * (2 * j) + 48 = 32 * (j + 1) + 16 by omega] at h
    exact h
  have x10 : s.data.regs.X10.toBitVec = rowOf m0 + BitVec.ofNat 64 (32 * (j + 1) + 16) := by
    have h : (s.data.regs.getXReg .X10).toBitVec =
        rowOf m0 + BitVec.ofNat 64 (8 * (4 * j)) + BitVec.ofInt 64 48 := hm'.regs .X10 _ rfl
    rw [show BitVec.ofInt 64 48 = BitVec.ofNat 64 48 from rfl, addr_add,
      show 8 * (4 * j) + 48 = 32 * (j + 1) + 16 by omega] at h
    exact h
  by_cases hlast : j + 1 = nOf m0 / 2
  · -- the turns' end
    have hpc' := pc_fall hpc (by
      sym_simp
      rw [Env.ofMachine_regs, bv_beq_toNat, h11, toNat_ofNat_lt (by decide)]
      simp
      omega)
    refine .done _ (.inl ⟨⟨by rw [← hlast]; exact hb', by rw [x2]; exact hL.x2,
      by rw [x8]; exact hL.x8, hn⟩, hpc'⟩)
  · have hpc' := pc_taken hpc (by
      sym_simp
      rw [Env.ofMachine_regs, bv_beq_toNat, h11, toNat_ofNat_lt (by decide)]
      simp
      omega)
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b17Offset) NativeRustcVmArm.Vm.LanesOf.label_17_at] at hpc'
    refine .done _ (.inr ⟨⟨by rw [show 2 * (j + 1) = 2 * j + 2 by omega]; exact hb',
      by rw [x2]; exact hL.x2, by rw [x8]; exact hL.x8, x11, x9, x10,
      by unfold nOf at hlast ⊢; omega, hn⟩,
      hpc'⟩)

/-- **A one-lane turn** (`b21`), then `b22` to the end. -/
theorem cp1_step (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0) {i : Nat}
    {st : MachineData} (hL : Cp1Loop m0 i st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Done m0 (pairL m0) (nOf m0) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b14Offset)) ∨
        (Cp1Loop m0 (i + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b21Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b21Offset)⟩ := by
  have hb := hL.body
  have hi := hL.hi
  have hn := hL.hn
  have hnw : NativeRustcVm.NoWrap (outOf m0) 1024 := (pre_parts hpre).2.1.1.2
  have hi' : 2 * i + 1 < lenOf m0 := by unfold nOf at hi; omega
  have hwf : (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * (2 * i)), 16),
      (outOf m0 + BitVec.ofNat 64 (16 * i), 16)]).WF :=
    wf_two hpre hb.fr (by omega) (by unfold nOf at hi; omega) (by omega) (by omega)
  have hm : Match (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * (2 * i)), 16),
      (outOf m0 + BitVec.ofNat 64 (16 * i), 16)]) cp1S st :=
    match_ofMachine
      ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by
        show st.regs.X9.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * (2 * i)) + BitVec.ofNat 64 8
        rw [hL.x9, addr_add, show 8 * (2 * i) + 8 = 16 * i + 8 by omega],
       by
        show st.regs.X10.toBitVec = outOf m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8
        rw [hL.x10, addr_add], trivial⟩
      trivial trivial trivial
  refine exec_then (inf hp b21_in_code (by simp [b21])) run_b21 hwf hm fun s hm' hpc ↦ ?_
  have hk := after_eq run_b21 ▸ b21_keeps
  have hfr := hb.fr.of_lanes hpre hm hm' hwf rfl hk.1 (c := i) rfl le_rfl hk.2 (by unfold nOf at hi; omega)
  have hsame := same_region hm' hwf (r := 1) rfl hk.2
  have w0 := Match.ewAt_write hm' (r := 1) (o := 0) rfl (by decide) (v0 := .load 0 0 8)
    (v1 := .load 0 8 8) (by decide) (by decide)
  rw [load_eval hpre hb.fr (t := 0) rfl (by omega), load_eval hpre hb.fr (t := 1) rfl (by omega),
    NativeRustcVm.addr_add_zero, show 2 * i + 0 = 2 * i by omega,
    show 16 * i = 16 * (i + 0) by omega] at w0
  have hl : Lanes m0 (pairL m0) (i + 1) s.data :=
    hb.lanes.extend (w := 1) hnw (by unfold nOf at hi; omega) hsame fun t ht ↦
      match t, ht with
      | 0, _ => w0
  have hb' : Body m0 (pairL m0) (i + 1) s.data :=
    ⟨hfr, hl, (reg_kept hm' (r := .X1) rfl).trans hb.x1, (reg_kept hm' (r := .X3) rfl).trans hb.x3,
      (reg_kept hm' (r := .X30) rfl).trans hb.x30⟩
  have h8 : (st.regs.getXReg .X8).toBitVec.toNat = nOf m0 - i := hL.x8
  have x0 : s.data.regs.X0 = 1 := (reg_kept hm' (r := .X0) rfl).trans hL.x0
  have x2 : s.data.regs.X2 = st.regs.X2 := reg_kept hm' (r := .X2) rfl
  have hc : ((SBool.cmp .eq .W64 (.reg .X8) (.lit 1)).not.eval
      (Env.ofMachine st [(rowOf m0 + BitVec.ofNat 64 (8 * (2 * i)), 16),
        (outOf m0 + BitVec.ofNat 64 (16 * i), 16)])) = decide (i + 1 ≠ nOf m0) := by
    sym_simp
    rw [Env.ofMachine_regs, bv_beq_toNat, h8, toNat_ofNat_lt (by decide)]
    by_cases h : i + 1 = nOf m0 <;> simp [h] <;> omega
  by_cases hlast : i + 1 = nOf m0
  · have hpc' := pc_fall hpc (by rw [hc]; simp [hlast])
    refine goto hpc' (exec_then (inf hp b22_in_code (by simp [b22])) run_b22 (Env.wf_nil _)
      (match_nil _) fun s2 hm2 hpc2 ↦ .done _ (.inl ⟨⟨?_, ?_, ?_⟩, ?_⟩))
    · have hk2 := after_eq run_b22 ▸ b22_keeps
      rw [← hlast]
      exact hb'.of_regsS hm2 hk2.1 hk2.2 rfl rfl rfl
    · exact (reg_kept hm2 (r := .X0) rfl).trans x0
    · rw [show s2.data.regs.X2 = s.data.regs.X2 from reg_kept hm2 (r := .X2) rfl, x2]
      exact hL.x2
    · simp only [PcOk] at hpc2
      rw [hpc2, hp.label (j := NativeRustcVmArm.Vm.LanesOf.b14Offset) NativeRustcVmArm.Vm.LanesOf.label_14_at]
  · have hpc' := pc_taken hpc (by rw [hc]; simp [hlast])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b21Offset) NativeRustcVmArm.Vm.LanesOf.label_21_at] at hpc'
    refine .done _ (.inr ⟨⟨hb', x0, by rw [x2]; exact hL.x2, ?_, ?_, ?_, by omega, hn⟩, hpc'⟩)
    · have h := hm'.regs .X8 _ rfl
      sym_simp at h
      rw [Env.ofMachine_regs] at h
      refine toNat_of_eq h ?_
      rw [toNat_sub_ofNat (by rw [h8]; omega), h8]
      omega
    · have h : (s.data.regs.getXReg .X9).toBitVec =
          rowOf m0 + BitVec.ofNat 64 (8 * (2 * i)) + BitVec.ofInt 64 24 := hm'.regs .X9 _ rfl
      rw [show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, addr_add,
        show 8 * (2 * i) + 24 = 16 * (i + 1) + 8 by omega] at h
      exact h
    · have h : (s.data.regs.getXReg .X10).toBitVec =
          outOf m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 24 := hm'.regs .X10 _ rfl
      rw [show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, addr_add,
        show 16 * i + 24 = 16 * (i + 1) + 8 by omega] at h
      exact h

/-- **The tail's head** (`b20`): from lane `e`. -/
theorem cp_tail (hp : Placed code k) {m0 : MachineData} {e : Nat} {st : MachineData}
    (hT : CpTail m0 e st) :
    Eventually (step1 Host.exe) (fun s ↦ Cp1Loop m0 e s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b21Offset))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b20Offset)⟩ := by
  have he := hT.he
  have hn := hT.hn
  have hn64 : nOf m0 < 65 := by unfold nOf; omega
  refine exec_then (inf hp b20_in_code (by simp [b20])) run_b20 (Env.wf_nil _) (match_nil _)
    fun s hm hpc ↦ .done _ ⟨?_, hpc⟩
  have hk := after_eq run_b20 ▸ b20_keeps
  have h8 : (st.regs.getXReg .X8).toBitVec.toNat = e := hT.x8
  have h2 : (st.regs.getXReg .X2).toBitVec.toNat = nOf m0 := hT.x2
  have ho : (BitVec.ofNat 64 8 ||| (st.regs.getXReg .X8).toBitVec <<< 4) =
      BitVec.ofNat 64 (16 * e + 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [orr_lsl4 _ (by rw [h8]; omega), h8, toNat_ofNat_lt (by omega)]
  refine ⟨hT.body.of_regsS hm hk.1 hk.2 rfl rfl rfl, UInt64.toBitVec_inj.mp (hm.regs .X0 _ rfl),
    by rw [show s.data.regs.X2 = st.regs.X2 from reg_kept hm (r := .X2) rfl]; exact hT.x2,
    ?_, ?_, ?_, he, hn⟩
  · have h := hm.regs .X8 _ rfl
    sym_simp at h
    rw [Env.ofMachine_regs, Env.ofMachine_regs] at h
    refine toNat_of_eq h ?_
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h8, h2]; omega), h8, h2]
  · have h := hm.regs .X9 _ rfl
    sym_simp at h
    rw [Env.ofMachine_regs, Env.ofMachine_regs, ho] at h
    show (s.data.regs.getXReg .X9).toBitVec = _
    rw [h]
    show st.regs.X1.toBitVec + _ = m0.regs.X1.toBitVec + _
    rw [hT.body.x1]
  · have h := hm.regs .X10 _ rfl
    sym_simp at h
    rw [Env.ofMachine_regs, Env.ofMachine_regs, ho] at h
    show (s.data.regs.getXReg .X10).toBitVec = _
    rw [h]
    show st.regs.X3.toBitVec + _ = m0.regs.X3.toBitVec + _
    rw [hT.body.x3]

end

end NativeRustcVmArm.Whir.LanesOf
