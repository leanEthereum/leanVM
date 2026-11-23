module

public import NativeRustcVmArm.Wire.WriteOpenings.B.Defs
public import NativeRustcVmArm.Wire.WriteOpenings.A.Scan

/-!
# `write_openings`' query and its position (`h = 0`, a leaf)

From the queries' loop head (`HeadB`): the query's word stored at its opening (`headB_step`,
`b25`); the positions scanned (`scanB_loop`, `b26`, `b27`) to the query's (`FoundB`), or past the
last, a rejection (`b28`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} {j : Nat} [Host]

/-- **The query's word stored** (`b25`). -/
theorem headB_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : HeadB R j st) :
    Eventually (step1 Host.exe) (ScanB R j 0) st := by
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
      (qS (mulAddr .X3 .X11 .X12)) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [H.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x2, base1, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], by
        simp only [mulAddr, Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64,
          Env.ofMachine_regs, memExt0]
        rw [H.x3, H.x11, H.x12, base2, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero, ofNat_mul, NativeRustcVm.addr_add_add]
        show R.out + _ = R.out + _
        congr 2
        unfold ob
        omega, trivial⟩
  refine run_block G hp b25_in_code (by simp [b25]) run_b25 H.fr H.pc hwf hm rfl
    (G.writesOk_out (r := 2) (by omega) rfl hin2 (by decide)) fun s1 hfr1 hm1 hpc1 ↦ .done _ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem (InRange (R.oa (ob j)) 8) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 2) (o := 0) (n := 8) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hqw : wordOf st.data.dmem (R.qa + BitVec.ofNat 64 (8 * j)) = R.qw j :=
    G.wordOf_keep H.fr (i := 2) (by omega) (by omega) hin1
  have hw := copied hm1 (r := 2) (o := 0) (sz := 8) (r' := 1) (o' := 0) rfl (by omega) (by decide)
  simp only [Env.ofMachine_mem0, base1, NativeRustcVm.addr_add_zero] at hw
  rw [hqw] at hw
  have hk1 := regs_keep hm hm1 (rs := [.X1, .X3, .X4, .X5, .X8, .X9, .X10, .X12, .X19, .X21])
    (by decide)
  refine ⟨hpc1.trans (congrArg Host.addrOf rfl), hfr1, ⟨by rw [hk1 .X1 (by simp)]; exact H.x1,
    ?_, by rw [hk1 .X3 (by simp)]; exact H.x3, by rw [hk1 .X4 (by simp)]; exact H.x4,
    by rw [hk1 .X5 (by simp)]; exact H.x5, by rw [hk1 .X8 (by simp)]; exact H.x8,
    by rw [hk1 .X9 (by simp)]; exact H.x9, by rw [hk1 .X10 (by simp)]; exact H.x10, ?_,
    by rw [hk1 .X12 (by simp)]; exact H.x12, by rw [hk1 .X19 (by simp)]; exact H.x19,
    by rw [hk1 .X21 (by simp)]; exact H.x21⟩, ?_, ?_, ?_, ?_, ?_, hj, G.np0, H.hz, H.lw0,
    fun _ h ↦ absurd h (Nat.not_lt_zero _),
    G.done_keep hs (by omega) (by omega) H.done (le_refl _), hw⟩
  · rw [hm1.regs .X2 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [H.x2]
    exact addr_add (by omega)
  · rw [hm1.regs .X11 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [H.x11, ofNat_add]
  · rw [hm1.regs .X13 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [H.x4, Nat.mul_zero, NativeRustcVm.addr_add_zero]
  · rw [hm1.regs .X14 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [H.x4]
  · rw [hm1.regs .X15 _ rfl]; rfl
  · rw [hm1.regs .X16 _ rfl]
    simp only [Sym.eval]
    rw [envLoad rfl 0, NativeRustcVm.addr_add_zero, hqw]
  · rw [hm1.regs .X17 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [H.x1, Nat.sub_zero]

/-- **The positions' scan** (`b26`, `b27`, `b28`): the query's position, or a rejection. -/
theorem scanB_loop (hp : Placed code R.k) (G : Geo R) {i : Nat} {st : MachineState}
    (H : ScanB R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ ∃ i, FoundB R j i st') st := by
  refine Sym.loop (fun n st ↦ ∃ i, n = R.np - i ∧ ScanB R j i st) (fun n st ⟨i, hn, H⟩ ↦ ?_)
    ⟨i, rfl, H⟩
  have hi := H.ilt
  have hnp := G.np256
  have hin : Inside (R.pa + BitVec.ofNat 64 (8 * i)) 8 (R.big 3) :=
    inside_off (G.noWrap (by omega)) (by show 8 * i + 8 ≤ 8 * R.np; omega) (by omega)
  have hwf := G.wf1 H.fr.kept (by omega) (by omega) hin
  have hm : Match (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)])
      (pS (idxAddr .X19 .X15)) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, trivial⟩ (by rw [H.fr.sp]; simp [Sym.eval])
      trivial trivial trivial ⟨by
        simp only [idxAddr, Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64,
          Env.ofMachine_regs, memExt3]
        rw [H.rb.x19, H.x15, ofNat_toNat (by omega), base1,
          show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine run_block G hp b26_in_code (by simp [b26]) run_b26 H.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hpwi : (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)]).load 1 0 8 =
      (R.pw i).toBitVec := by
    rw [envLoad rfl 0, NativeRustcVm.addr_add_zero, G.wordOf_keep H.fr (by omega) (by omega) hin]
    rfl
  have hc : (SBool.cmp .eq .W64 (.load 1 0 8) (.reg .X16)).eval
      (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)]) = decide (R.pw i = R.qw j) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [hpwi, H.x16]
    by_cases h : R.pw i = R.qw j
    · rw [h, decide_eq_true rfl, decide_eq_true rfl]
    · rw [decide_eq_false h, decide_eq_false fun h' ↦ h (UInt64.toBitVec_inj.mp
        (BitVec.eq_of_toNat_eq h'))]
  simp only [PcOk, hc] at hpc1
  have hk1 := regs_keep hm hm1 (rs := .X13 :: .X14 :: .X15 :: .X16 :: .X17 :: rbRegs) (by decide)
  have rb1 : RB R j s1.data :=
    H.rb.keep fun r hr ↦ hk1 r (by simp only [List.mem_cons] at hr ⊢; tauto)
  by_cases he : R.pw i = R.qw j
  · simp only [he, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b29Offset) NativeRustcVmArm.Vm.WriteOpenings.label_25_at] at hpc1
    refine .done _ (.inl (.inr ⟨i, hpc1, hfr1, rb1, by rw [hk1 .X13 (by simp)]; exact H.x13,
      by rw [hk1 .X14 (by simp)]; exact H.x14, H.lt, hi, H.hz, H.lw0, pos_some hi he H.miss,
      by rw [hd1]; exact H.mem⟩))
  simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hwf2 := G.wf0 hfr1.kept
  have hm2 := frMatch G hfr1
  refine run_block G hp b27_in_code (by simp [b27]) run_b27 hfr1
    (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
    fun s2 hfr2 hm2' hpc2 ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hk2 := regs_keep hm2 hm2' (rs := .X16 :: rbRegs) (by decide)
  have x17 : rv s1.data .X17 = BitVec.ofNat 64 (8 * (R.np - i)) := by
    rw [hk1 .X17 (by simp)]; exact H.x17
  have hc2 : (SBool.cmp .eq .W64 (.reg .X17) (.lit 8)).not.eval (envOf R s1.data []) =
      decide (i + 1 ≠ R.np) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [x17, ofNat_toNat (by omega), ofNat_toNat (by omega)]
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
    refine run_block G hp b28_in_code (by simp [b28]) run_b28 hfr2
      (hpc2.trans (congrArg Host.addrOf rfl)) hwf3 (frMatch G hfr2) rfl
      (writesOk_frame (by decide)) fun s3 hfr3 _ hpc3 ↦ ?_
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b45Offset) NativeRustcVmArm.Vm.WriteOpenings.label_38_at] at hpc3
    exact Eventually.mono (fail_spec hp G hpc3 hfr3 (bad_of_none H.lt fun i' hi' ↦
      miss i' (by omega))) fun _ h ↦ .inl (.inl h)
  simp only [ne_eq, hl, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b26Offset) NativeRustcVmArm.Vm.WriteOpenings.label_23_at]
    at hpc2
  refine .done _ (.inr ⟨R.np - (i + 1), by omega, i + 1, rfl, hpc2, hfr2,
    rb1.keep fun r hr ↦ hk2 r (List.mem_cons_of_mem _ hr), ?_, ?_, ?_,
    by rw [hk2 .X16 (by simp), hk1 .X16 (by simp)]; exact H.x16, ?_, H.lt, by omega, H.hz,
    H.lw0, miss, by rw [hd2, hd1]; exact H.mem⟩)
  · rw [hm2'.regs .X13 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hk1 .X13 (by simp), H.x13]
    exact addr_add (by omega)
  · rw [hm2'.regs .X14 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hk1 .X14 (by simp), H.x14]
    exact addr_add (by omega)
  · rw [hm2'.regs .X15 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hk1 .X15 (by simp), H.x15, ofNat_add]
  · rw [hm2'.regs .X17 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [x17, ofNat_sub (by omega)]
    congr 1
    omega

end

end NativeRustcVmArm.Wire.WriteOpenings
