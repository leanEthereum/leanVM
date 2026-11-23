module

public import NativeRustcVmArm.Wire.WriteOpenings.A.Defs

/-!
# `write_openings`' query and its position (`h > 0`)

From the queries' loop head (`HeadA`): the query's word stored at its opening (`head_step`,
`b2`); the positions scanned (`scan_loop`, `b3`, `b4`) to the query's (`FoundA`, `b6`), or past
the last, a rejection (`b5`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

@[expose] public section

/-- **Query `j` found at position `i`** (`b6`). -/
structure FoundA [Host] (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b6Offset
  fr : Frm R st.data
  cs : Cs R st.data
  cr : Cr R j st.data
  args : Args R st.data
  x2 : rv st.data .X2 = R.qa + BitVec.ofNat 64 (8 * (j + 1))
  x8 : rv st.data .X8 = R.lv + BitVec.ofNat 64 (512 * i)
  x9 : rv st.data .X9 = R.lv + BitVec.ofNat 64 (512 * i + 16)
  x13 : rv st.data .X13 = BitVec.ofNat 64 (j + 1)
  x25 : rv st.data .X25 = (R.qw j).toBitVec
  lt : j < R.nq
  ilt : i < R.np
  h0 : 0 < R.h
  pos : R.pos (R.qw j) = some i
  mem : Begun R j st.data.dmem

end

public section

theorem ofNat_mul (a b : Nat) :
    BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_mod]

variable {R : Run} {j : Nat} [Host]

/-- **The query's word stored** (`b2`). -/
theorem head_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : HeadA R j st) :
    Eventually (step1 Host.exe) (ScanA R j 0) st := by
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
      (qS (mulAddr .X3 .X9 .X11)) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [H.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        simp only [Sym.eval, Env.ofMachine_regs]
        rw [H.x2, base1, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], by
        simp only [mulAddr, Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64,
          Env.ofMachine_regs, memExt0]
        rw [H.args.x3, H.x9, H.x11, base2, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero, ofNat_mul, NativeRustcVm.addr_add_add]
        show R.out + _ = R.out + _
        congr 2
        unfold ob
        omega, trivial⟩
  refine run_block G hp b2_in_code (by simp [b2]) run_b2 H.fr H.pc hwf hm rfl
    (G.writesOk_out (r := 2) (by omega) rfl hin2 (by decide)) fun s1 hfr1 hm1 hpc1 ↦ .done _ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem (InRange (R.oa (ob j)) 8) := by
    have := Match.sameOutside_in hm1 hwf (r0 := 2) (o := 0) (n := 8) rfl (by omega) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hqw : wordOf st.data.dmem (R.qa + BitVec.ofNat 64 (8 * j)) = R.qw j :=
    G.wordOf_keep H.fr (i := 2) (by omega) (by omega) hin1
  have hw := copied hm1 (r := 2) (o := 0) (sz := 8) (r' := 1) (o' := 0) rfl (by omega) (by decide)
  simp only [Env.ofMachine_mem0, base1, NativeRustcVm.addr_add_zero] at hw
  rw [hqw] at hw
  refine ⟨hpc1.trans (congrArg Host.addrOf rfl), hfr1, H.cs.keep (regs_keep hm hm1 (by decide)),
    H.cr.keep (regs_keep hm hm1 (by decide)), H.args.keep (regs_keep hm hm1 (by decide)), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, hj, G.np0, H.h0, fun _ h ↦ absurd h (Nat.not_lt_zero _),
    G.done_keep hs (by omega) (by omega) H.done (le_refl _), hw⟩
  · rw [hm1.regs .X2 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [H.x2]
    exact addr_add (by omega)
  · rw [hm1.regs .X8 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [H.args.x4, Nat.mul_zero, NativeRustcVm.addr_add_zero]
  · rw [hm1.regs .X9 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [H.args.x4]
  · rw [hm1.regs .X10 _ rfl]; rfl
  · rw [hm1.regs .X11 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [H.args.x1, Nat.sub_zero]
  · rw [hm1.regs .X13 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [H.x9, ofNat_add]
  · rw [hm1.regs .X25 _ rfl]
    simp only [Sym.eval]
    rw [envLoad rfl 0, NativeRustcVm.addr_add_zero, hqw]

/-- **The positions' scan** (`b3`, `b4`, `b5`): the query's position, or a rejection. -/
theorem scan_loop (hp : Placed code R.k) (G : Geo R) {i : Nat} {st : MachineState}
    (H : ScanA R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ ∃ i, FoundA R j i st') st := by
  refine Sym.loop (fun n st ↦ ∃ i, n = R.np - i ∧ ScanA R j i st) (fun n st ⟨i, hn, H⟩ ↦ ?_)
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
        rw [H.cs.x19, H.x10, ofNat_toNat (by omega), base1, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero], trivial⟩
  refine run_block G hp b3_in_code (by simp [b3]) run_b3 H.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hpwi : (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)]).load 1 0 8 =
      (R.pw i).toBitVec := by
    rw [envLoad rfl 0, NativeRustcVm.addr_add_zero, G.wordOf_keep H.fr (by omega) (by omega) hin]
    rfl
  have hc : (SBool.cmp .eq .W64 (.load 1 0 8) (.reg .X25)).eval
      (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)]) = decide (R.pw i = R.qw j) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [hpwi, H.x25]
    by_cases h : R.pw i = R.qw j
    · rw [h, decide_eq_true rfl, decide_eq_true rfl]
    · rw [decide_eq_false h, decide_eq_false fun h' ↦ h (UInt64.toBitVec_inj.mp
        (BitVec.eq_of_toNat_eq h'))]
  simp only [PcOk, hc] at hpc1
  have hk1 := regs_keep hm hm1 (rs := [.X2, .X8, .X9, .X10, .X11, .X13, .X25]) (by decide)
  by_cases he : R.pw i = R.qw j
  · simp only [he, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b6Offset) NativeRustcVmArm.Vm.WriteOpenings.label_5_at] at hpc1
    refine .done _ (.inl (.inr ⟨i, hpc1, hfr1, H.cs.keep (regs_keep hm hm1 (by decide)),
      H.cr.keep (regs_keep hm hm1 (by decide)), H.args.keep (regs_keep hm hm1 (by decide)),
      by rw [hk1 .X2 (by simp)]; exact H.x2, by rw [hk1 .X8 (by simp)]; exact H.x8,
      by rw [hk1 .X9 (by simp)]; exact H.x9,
      by rw [hk1 .X13 (by simp)]; exact H.x13, by rw [hk1 .X25 (by simp)]; exact H.x25, H.lt, hi,
      H.h0, pos_some hi he H.miss, by rw [hd1]; exact H.mem⟩))
  simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hwf2 := G.wf0 hfr1.kept
  have hm2 := frMatch G hfr1
  refine run_block G hp b4_in_code (by simp [b4]) run_b4 hfr1
    (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
    fun s2 hfr2 hm2' hpc2 ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hk2 := regs_keep hm2 hm2' (rs := [.X2, .X13, .X25]) (by decide)
  have x11 : rv s1.data .X11 = BitVec.ofNat 64 (8 * (R.np - i)) := by
    rw [hk1 .X11 (by simp)]; exact H.x11
  have hc2 : (SBool.cmp .eq .W64 (.reg .X11) (.lit 8)).not.eval (envOf R s1.data []) =
      decide (i + 1 ≠ R.np) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [x11, ofNat_toNat (by omega), ofNat_toNat (by omega)]
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
    refine run_block G hp b5_in_code (by simp [b5]) run_b5 hfr2
      (hpc2.trans (congrArg Host.addrOf rfl)) hwf3 (frMatch G hfr2) rfl
      (writesOk_frame (by decide)) fun s3 hfr3 _ hpc3 ↦ ?_
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b45Offset) NativeRustcVmArm.Vm.WriteOpenings.label_38_at] at hpc3
    exact Eventually.mono (fail_spec hp G hpc3 hfr3 (bad_of_none H.lt fun i' hi' ↦
      miss i' (by omega))) fun _ h ↦ .inl (.inl h)
  simp only [ne_eq, hl, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b3Offset) NativeRustcVmArm.Vm.WriteOpenings.label_3_at]
    at hpc2
  refine .done _ (.inr ⟨R.np - (i + 1), by omega, i + 1, rfl, hpc2, hfr2,
    (H.cs.keep (regs_keep hm hm1 (by decide))).keep (regs_keep hm2 hm2' (by decide)),
    (H.cr.keep (regs_keep hm hm1 (by decide))).keep (regs_keep hm2 hm2' (by decide)),
    (H.args.keep (regs_keep hm hm1 (by decide))).keep (regs_keep hm2 hm2' (by decide)),
    by rw [hk2 .X2 (by simp), hk1 .X2 (by simp)]; exact H.x2, ?_, ?_, ?_, ?_,
    by rw [hk2 .X13 (by simp), hk1 .X13 (by simp)]; exact H.x13,
    by rw [hk2 .X25 (by simp), hk1 .X25 (by simp)]; exact H.x25, H.lt, by omega, H.h0, miss,
    by rw [hd2, hd1]; exact H.mem⟩)
  · rw [hm2'.regs .X8 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hk1 .X8 (by simp), H.x8]
    exact addr_add (by omega)
  · rw [hm2'.regs .X9 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hk1 .X9 (by simp), H.x9]
    exact addr_add (by omega)
  · rw [hm2'.regs .X10 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hk1 .X10 (by simp), H.x10, ofNat_add]
  · rw [hm2'.regs .X11 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [x11, ofNat_sub (by omega)]
    congr 1
    omega

end

end NativeRustcVmArm.Wire.WriteOpenings
