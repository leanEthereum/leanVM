module

public import NativeRustcVmArm.Wire.WriteOpenings.B.Defs
public import NativeRustcVmArm.Wire.WriteOpenings.A.Scan

/-!
# `write_openings` without levels nor leaf words (`h = 0`, `lw = 0`)

From the queries' loop head (`HeadZ`, `b39`): the query's word stored (`headZ_step`); the
positions scanned (`scanZ_loop`, `b40`, `b41`) to the query's (`b43`), or past the last, a
rejection (`b42`); then the next query or the epilogue (`b43`, `b44`): `queryZ_loop`.
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

@[expose] public section

/-- The registers of the queries' loop without words, after query `j`'s head. -/
structure RZ (R : Run) (j : Nat) (m : MachineData) : Prop where
  x0 : rv m .X0 = BitVec.ofNat 64 1
  x1 : rv m .X1 = BitVec.ofNat 64 (8 * R.np)
  x2 : rv m .X2 = R.qa + BitVec.ofNat 64 (8 * (j + 1))
  x3 : rv m .X3 = R.oa 24
  x5 : rv m .X5 = R.qa + BitVec.ofNat 64 (8 * R.nq)
  x8 : rv m .X8 = BitVec.ofNat 64 1544
  x9 : rv m .X9 = BitVec.ofNat 64 (j + 1)
  x19 : rv m .X19 = R.pa

/-- `RZ`'s registers. -/
abbrev rzRegs : List XReg := [.X0, .X1, .X2, .X3, .X5, .X8, .X9, .X19]

section
variable [Host]

/-- **The queries' loop head** without words (`b39`) at query `j`. -/
structure HeadZ (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b39Offset
  fr : Frm R st.data
  x0 : rv st.data .X0 = BitVec.ofNat 64 1
  x1 : rv st.data .X1 = BitVec.ofNat 64 (8 * R.np)
  x2 : rv st.data .X2 = R.qa + BitVec.ofNat 64 (8 * j)
  x3 : rv st.data .X3 = R.oa 24
  x5 : rv st.data .X5 = R.qa + BitVec.ofNat 64 (8 * R.nq)
  x8 : rv st.data .X8 = BitVec.ofNat 64 1544
  x9 : rv st.data .X9 = BitVec.ofNat 64 j
  x19 : rv st.data .X19 = R.pa
  lt : j < R.nq
  hz : R.h = 0
  lw0 : R.lw = 0
  done : R.Done st.data.dmem j

/-- **The positions' scan** (`b40`) of query `j` at position `i`. -/
structure ScanZ (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b40Offset
  fr : Frm R st.data
  rz : RZ R j st.data
  x10 : rv st.data .X10 = BitVec.ofNat 64 i
  x11 : rv st.data .X11 = (R.qw j).toBitVec
  x12 : rv st.data .X12 = BitVec.ofNat 64 (8 * (R.np - i))
  lt : j < R.nq
  ilt : i < R.np
  hz : R.h = 0
  lw0 : R.lw = 0
  miss : ∀ i' < i, R.pw i' ≠ R.qw j
  mem : Begun R j st.data.dmem

end

end

public section

variable {R : Run} {j : Nat} {m m' : MachineData}

theorem RZ.keep (h : RZ R j m)
    (hk : ∀ r ∈ rzRegs, m'.regs.getXReg r = m.regs.getXReg r) : RZ R j m' :=
  ⟨by rw [hk .X0 (by simp)]; exact h.x0, by rw [hk .X1 (by simp)]; exact h.x1,
    by rw [hk .X2 (by simp)]; exact h.x2, by rw [hk .X3 (by simp)]; exact h.x3,
    by rw [hk .X5 (by simp)]; exact h.x5, by rw [hk .X8 (by simp)]; exact h.x8,
    by rw [hk .X9 (by simp)]; exact h.x9, by rw [hk .X19 (by simp)]; exact h.x19⟩

variable [Host]

/-- **The query's word stored** (`b39`). -/
theorem headZ_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : HeadZ R j st) :
    Eventually (step1 Host.exe) (ScanZ R j 0) st := by
  have hj := H.lt
  have hnq := G.nq256
  have hob := ob_le (j := j) (by omega)
  have hin1 : Inside (R.qa + BitVec.ofNat 64 (8 * j)) 8 (R.big 2) :=
    inside_off (G.noWrap (by omega)) (by show 8 * j + 8 ≤ 8 * R.nq; omega) (by omega)
  have hin2 : Inside (R.oa (ob j)) 8 (R.big 7) :=
    inside_off G.outNw (by show ob j + 8 ≤ phaseBytes; omega) (by omega)
  have hwf := G.wf2 H.fr.kept (i := 2) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin1 hin2
  have hm : Match (envOf R st.data [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (ob j), 8)])
      (qS (mulAddr .X3 .X9 .X8)) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [H.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x2, base1, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], by
        simp only [mulAddr, Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64,
          Env.ofMachine_regs, memExt0]
        rw [H.x3, H.x9, H.x8, base2, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero, ofNat_mul, NativeRustcVm.addr_add_add]
        show R.out + _ = R.out + _
        congr 2
        unfold ob
        omega, trivial⟩
  refine run_block G hp b39_in_code (by simp [b39]) run_b39 H.fr H.pc hwf hm rfl
    (G.writesOk_out (r := 2) (by omega) rfl hin2 (by decide)) fun s1 hfr1 hm1 hpc1 ↦ .done _ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem (InRange (R.oa (ob j)) 8) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 2) (o := 0) (n := 8) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hqw : wordOf st.data.dmem (R.qa + BitVec.ofNat 64 (8 * j)) = R.qw j :=
    G.wordOf_keep H.fr (i := 2) (by omega) (by omega) hin1
  have hw := copied hm1 (r := 2) (o := 0) (sz := 8) (r' := 1) (o' := 0) rfl (by omega) (by decide)
  simp only [Env.ofMachine_mem0, base1, NativeRustcVm.addr_add_zero] at hw
  rw [hqw] at hw
  have hk1 := regs_keep hm hm1 (rs := [.X0, .X1, .X3, .X5, .X8, .X19]) (by decide)
  refine ⟨hpc1.trans (congrArg Host.addrOf rfl), hfr1, ⟨by rw [hk1 .X0 (by simp)]; exact H.x0,
    by rw [hk1 .X1 (by simp)]; exact H.x1, ?_, by rw [hk1 .X3 (by simp)]; exact H.x3,
    by rw [hk1 .X5 (by simp)]; exact H.x5, by rw [hk1 .X8 (by simp)]; exact H.x8, ?_,
    by rw [hk1 .X19 (by simp)]; exact H.x19⟩, ?_, ?_, ?_, hj, G.np0, H.hz, H.lw0,
    fun _ h ↦ absurd h (Nat.not_lt_zero _),
    G.done_keep hs (by omega) (by omega) H.done (le_refl _), hw⟩
  · rw [hm1.regs .X2 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [H.x2]
    exact addr_add (by omega)
  · rw [hm1.regs .X9 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [H.x9, ofNat_add]
  · rw [hm1.regs .X10 _ rfl]; rfl
  · rw [hm1.regs .X11 _ rfl]
    simp only [Sym.eval]
    rw [envLoad rfl 0, NativeRustcVm.addr_add_zero, hqw]
  · rw [hm1.regs .X12 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [H.x1, Nat.sub_zero]

/-- **Query `j` found** (`b43`, `b44`): the next query, or the epilogue. -/
theorem b43_step (hp : Placed code R.k) (G : Geo R) {i : Nat} {st : MachineState}
    (hpc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b43Offset) (hfr : Frm R st.data) (rz : RZ R j st.data) (hj : j < R.nq)
    (hz : R.h = 0) (hlw0 : R.lw = 0) (hpos : R.pos (R.qw j) = some i)
    (hmem : Begun R j st.data.dmem) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ HeadZ R (j + 1) st') st := by
  have hwf := G.wf0 hfr.kept
  have hm := frMatch G hfr
  refine run_block G hp b43_in_code (by simp [b43]) run_b43 hfr hpc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have rz1 : RZ R j s1.data := rz.keep (regs_keep hm hm1 (by decide))
  have hdone : R.Done s1.data.dmem (j + 1) := by
    rw [hd1]; exact done_succ hz hmem hpos (by rw [hlw0]; exact leaf_zero)
  have hc : (SBool.cmp .eq .W64 (.reg .X2) (.reg .X5)).not.eval (envOf R st.data []) =
      decide (j + 1 ≠ R.nq) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [rz.x2, rz.x5, qa_cmp G hj]
    simp only [ne_eq, decide_not]
  simp only [PcOk, hc] at hpc1
  by_cases hend : j + 1 = R.nq
  · simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc1
    have hwf2 := G.wf0 hfr1.kept
    have hm2 := frMatch G hfr1
    refine run_block G hp b44_in_code (by simp [b44]) run_b44 hfr1
      (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
      fun s2 hfr2 hm2' hpc2 ↦ ?_
    have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hx0 : s2.data.regs.X0 = 1 := by
      apply UInt64.toBitVec_inj.mp
      rw [show s2.data.regs.X0 = s2.data.regs.getXReg .X0 from rfl,
        Match.reg_eq hm2 hm2' (v := .reg .X0) rfl rfl, rz1.x0]
      rfl
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b46Offset) NativeRustcVmArm.Vm.WriteOpenings.label_39_at] at hpc2
    refine Eventually.mono (end_spec hp G ⟨hpc2, hfr2, .inl ⟨hx0, ?_⟩⟩) fun _ h ↦ .inl h
    rw [hd2, ← hend]
    exact hdone
  · simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b39Offset) NativeRustcVmArm.Vm.WriteOpenings.label_34_at]
      at hpc1
    exact .done _ (.inr ⟨hpc1, hfr1, rz1.x0, rz1.x1, rz1.x2, rz1.x3, rz1.x5, rz1.x8, rz1.x9,
      rz1.x19, by omega, hz, hlw0, hdone⟩)

/-- **The positions' scan** (`b40`, `b41`, `b42`): the next query or the epilogue, or a
rejection. -/
theorem scanZ_loop (hp : Placed code R.k) (G : Geo R) {i : Nat} {st : MachineState}
    (H : ScanZ R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ HeadZ R (j + 1) st') st := by
  refine Sym.loop (fun n st ↦ ∃ i, n = R.np - i ∧ ScanZ R j i st) (fun n st ⟨i, hn, H⟩ ↦ ?_)
    ⟨i, rfl, H⟩
  have hi := H.ilt
  have hnp := G.np256
  have hin : Inside (R.pa + BitVec.ofNat 64 (8 * i)) 8 (R.big 3) :=
    inside_off (G.noWrap (by omega)) (by show 8 * i + 8 ≤ 8 * R.np; omega) (by omega)
  have hwf := G.wf1 H.fr.kept (by omega) (by omega) hin
  have hm : Match (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)])
      (pS (idxAddr .X19 .X10)) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, trivial⟩ (by rw [H.fr.sp]; simp [Sym.eval])
      trivial trivial trivial ⟨by
        simp only [idxAddr, Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64,
          Env.ofMachine_regs, memExt3]
        rw [H.rz.x19, H.x10, ofNat_toNat (by omega), base1,
          show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine run_block G hp b40_in_code (by simp [b40]) run_b40 H.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hpwi : (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)]).load 1 0 8 =
      (R.pw i).toBitVec := by
    rw [envLoad rfl 0, NativeRustcVm.addr_add_zero, G.wordOf_keep H.fr (by omega) (by omega) hin]
    rfl
  have hc : (SBool.cmp .eq .W64 (.load 1 0 8) (.reg .X11)).eval
      (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)]) = decide (R.pw i = R.qw j) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [hpwi, H.x11]
    by_cases h : R.pw i = R.qw j
    · rw [h, decide_eq_true rfl, decide_eq_true rfl]
    · rw [decide_eq_false h, decide_eq_false fun h' ↦ h (UInt64.toBitVec_inj.mp
        (BitVec.eq_of_toNat_eq h'))]
  simp only [PcOk, hc] at hpc1
  have hk1 := regs_keep hm hm1 (rs := .X10 :: .X11 :: .X12 :: rzRegs) (by decide)
  have rz1 : RZ R j s1.data :=
    H.rz.keep fun r hr ↦ hk1 r (by simp only [List.mem_cons] at hr ⊢; tauto)
  by_cases he : R.pw i = R.qw j
  · simp only [he, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b43Offset) NativeRustcVmArm.Vm.WriteOpenings.label_37_at] at hpc1
    refine Eventually.mono (b43_step hp G hpc1 hfr1 rz1 H.lt H.hz H.lw0 (pos_some hi he H.miss)
      (by rw [hd1]; exact H.mem)) fun _ h ↦ .inl h
  simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hwf2 := G.wf0 hfr1.kept
  have hm2 := frMatch G hfr1
  refine run_block G hp b41_in_code (by simp [b41]) run_b41 hfr1
    (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
    fun s2 hfr2 hm2' hpc2 ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hk2 := regs_keep hm2 hm2' (rs := .X11 :: rzRegs) (by decide)
  have x12 : rv s1.data .X12 = BitVec.ofNat 64 (8 * (R.np - i)) := by
    rw [hk1 .X12 (by simp)]; exact H.x12
  have hc2 : (SBool.cmp .eq .W64 (.reg .X12) (.lit 8)).not.eval (envOf R s1.data []) =
      decide (i + 1 ≠ R.np) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [x12, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    by_cases h : i + 1 = R.np
    · rw [decide_eq_true (by omega : 8 * (R.np - i) = 8),
        decide_eq_false (by omega : ¬i + 1 ≠ R.np)]; rfl
    · rw [decide_eq_false (by omega : ¬8 * (R.np - i) = 8),
        decide_eq_true (by omega : i + 1 ≠ R.np)]; rfl
  simp only [PcOk, hc2] at hpc2
  have miss : ∀ i' < i + 1, R.pw i' ≠ R.qw j := fun i' hi' ↦ by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
    · exact H.miss i' h
    · exact he
  by_cases hl : i + 1 = R.np
  · simp only [hl, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc2
    have hwf3 := G.wf0 hfr2.kept
    refine run_block G hp b42_in_code (by simp [b42]) run_b42 hfr2
      (hpc2.trans (congrArg Host.addrOf rfl)) hwf3 (frMatch G hfr2) rfl
      (writesOk_frame (by decide)) fun s3 hfr3 _ hpc3 ↦ ?_
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b45Offset) NativeRustcVmArm.Vm.WriteOpenings.label_38_at] at hpc3
    exact Eventually.mono (fail_spec hp G hpc3 hfr3 (bad_of_none H.lt fun i' hi' ↦
      miss i' (by omega))) fun _ h ↦ .inl (.inl h)
  simp only [ne_eq, hl, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b40Offset) NativeRustcVmArm.Vm.WriteOpenings.label_35_at]
    at hpc2
  refine .done _ (.inr ⟨R.np - (i + 1), by omega, i + 1, rfl, hpc2, hfr2,
    rz1.keep fun r hr ↦ hk2 r (List.mem_cons_of_mem _ hr), ?_,
    by rw [hk2 .X11 (by simp), hk1 .X11 (by simp)]; exact H.x11, ?_, H.lt, by omega, H.hz,
    H.lw0, miss, by rw [hd2, hd1]; exact H.mem⟩)
  · rw [hm2'.regs .X10 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hk1 .X10 (by simp), H.x10, ofNat_add]
  · rw [hm2'.regs .X12 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [x12, ofNat_sub (by omega)]
    congr 1
    omega

/-- **The queries' loop** without words, from query `j`: the epilogue. -/
theorem queryZ_loop (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : HeadZ R j st) :
    Eventually (step1 Host.exe) (Post R) st := by
  refine Sym.loop (fun n st ↦ ∃ j, n = R.nq - j ∧ HeadZ R j st) (fun n st ⟨j, hn, H⟩ ↦ ?_)
    ⟨j, rfl, H⟩
  have hj := H.lt
  refine eventually_trans _ _ _ _ (headZ_step hp G H) fun s1 h1 ↦ ?_
  refine Eventually.mono (scanZ_loop hp G h1) fun s2 h2 ↦ ?_
  rcases h2 with h2 | h2
  · exact .inl h2
  · exact .inr ⟨R.nq - (j + 1), by omega, j + 1, rfl, h2⟩

end

end NativeRustcVmArm.Wire.WriteOpenings
