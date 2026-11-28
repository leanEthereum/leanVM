module

public import NativeRustcVmX64.Wire.WriteOpenings.A.Defs

/-!
# `write_openings`' query and its position (`h > 0`, x86-64)

From the queries' loop head (`HeadA`): the query's word stored at its opening (`head_step`,
`b2`); the positions scanned (`scan_loop`, `b3`, `b4`) to the query's (`FoundA`, `b7`), or past
the last, a rejection (`b5`).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

public section

variable {R : Run} {j : Nat} [Host]

/-- **The query's word stored** (`b2`). -/
theorem head_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : HeadA R j st) :
    Eventually (step1 Host.exe) (ScanA R j 0) st := by
  have hj := H.lt
  have hnq := G.nq256
  have hnp := G.np256
  have hob := ob_le (j := j) (by omega)
  have hob' : 24 + 1544 * j + 1544 ≤ phaseBytes := hob
  have hin2 := G.q_in hj
  have hin3 : Inside (R.oa (1544 * j)) 32 (R.big 7) := G.o_in (by unfold ob at hob; omega) (by omega)
  have hwf := G.wf2 H.F.fr.kept (i := 2) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin2 hin3 (ret := 0)
  have hm : Match (envOf R st.data [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (1544 * j), 32)] 0)
      (qS .rsi) st.data :=
    match_fS H.F.fr (csz := [8, 32])
      (cs := [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (1544 * j), 32)]) ⟨rfl, rfl, trivial⟩
      ⟨al0 (by
        show reg st.data .rdi = R.qa + BitVec.ofNat 64 (8 * j)
        exact H.rg.get (by simp)), al0 (by
        show (ix .rbp .rsi 1544).eval _ = R.oa (1544 * j)
        rw [ix_eval, H.rg.get (v := R.out) (by simp), H.rg.get (v := BitVec.ofNat 64 j) (by simp),
          ixs_ofNat]), trivial⟩
  refine blkW G hp b2_in_code (by simp [b2]) run_b2 H.F H.pc hwf hm nofun (o := 8) (by decide +kernel)
    (ro := 3) rfl (lo := 24) (a := R.oa (ob j)) (n := 8) (addr_add (by unfold ob; omega))
    (G.o_in (by omega) (by omega)) (by decide +kernel) fun st1 F1 hm1 hpc1 hs ↦ .done _ ?_
  have hqw : wordOf st.data.dmem (R.qa + BitVec.ofNat 64 (8 * j)) = R.qw j :=
    G.rd H.F.chg (i := 2) (by omega) (by omega) hin2
  have hl2 : (envOf R st.data [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (1544 * j), 32)] 0).load
      2 0 8 = (R.qw j).toBitVec := by
    rw [load_eq_wordOf]
    show (wordOf st.data.dmem (R.qa + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, hqw]
  have hw := copied hm1 (r := 3) (o := 24) (sz := 32) (b := R.oa (1544 * j)) rfl (by omega)
    (r' := 2) (o' := 0) (by decide +kernel)
  rw [addr_add (show 1544 * j + 24 = ob j by unfold ob; omega)] at hw
  have hw' : WordAt st1.data.dmem (R.oa (ob j)) (R.qw j) := by
    have e : wordOf (envOf R st.data [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (1544 * j), 32)]
        0).mem0 ((envOf R st.data [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (1544 * j), 32)]
        0).base 2 + BitVec.ofNat 64 0) = R.qw j := by
      show wordOf st.data.dmem (R.qa + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 0) = _
      rw [NativeRustcVm.addr_add_zero, hqw]
    rw [e] at hw
    exact hw
  have hk := fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := [32, 88, 96, 40, 16]) (by decide +kernel) (by decide +kernel)
  refine ⟨pc_fall hpc1, F1, hj, H.h0, G.np0, fun _ h ↦ absurd h (Nat.not_lt_zero _),
    ⟨G.done_keep (o := ob j) (n := 8) hs (by omega) (by omega) H.done (le_refl _), hw'⟩, H.w.keep hk,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := fw_write hm1 (o := 104) (by omega) (v := .bin .add .W64 (.reg .rsi) (.lit 1))
      (by decide +kernel)
    rwa [show (Sym.bin .add .W64 (.reg .rsi) (.lit 1)).eval (envOf R st.data
        [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (1544 * j), 32)] 0) = BitVec.ofNat 64 (j + 1) by
      simp only [Sym.eval, add_eval, envRegs]
      rw [H.rg.get (v := BitVec.ofNat 64 j) (by simp), ofNat_add]] at this
  · keep_regs hm1 H.rg
    · refine (hm1.regs .rdi _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [H.rg.get (v := R.qa + BitVec.ofNat 64 (8 * j)) (by simp)]
      exact lit_add (by omega)
    · refine (hm1.regs .r10 _ rfl).trans ?_
      exact fw_load (H.w.get (by simp))
    · refine (hm1.regs .r15 _ rfl).trans hl2
  · exact (hm1.regs .rsi _ rfl).trans rfl
  · refine (hm1.regs .rax _ rfl).trans ?_
    simp only [Sym.eval, envRegs]
    rw [H.rg.get (v := R.lv) (by simp), Nat.mul_zero, NativeRustcVm.addr_add_zero]
  · refine (hm1.regs .r8 _ rfl).trans ?_
    simp only [Sym.eval, envRegs]
    rw [H.rg.get (v := BitVec.ofNat 64 (8 * R.np)) (by simp), Nat.sub_zero]
  · refine kreg hm1 rfl ?_
    rw [H.rg.get (v := R.lv + BitVec.ofNat 64 24) (by simp)]

/-- **The positions' scan** (`b3`, `b4`, `b5`): the query's position, or a rejection. -/
theorem scan_loop (hp : Placed code R.k) (G : Geo R) {i : Nat} {st : MachineState}
    (H : ScanA R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ ∃ i, FoundA R j i st') st := by
  refine Sym.loop (fun n st ↦ ∃ i, n = R.np - i ∧ ScanA R j i st) (fun n st ⟨i, hn, H⟩ ↦ ?_)
    ⟨i, rfl, H⟩
  have hi := H.ilt
  have hnp := G.np256
  have hin := G.p_in hi
  have hwf := G.wf1 H.F.fr.kept (i := 3) (by omega) (by omega) hin (ret := 0)
  have hm : Match (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)] 0) (pS .rsi) st.data :=
    match_fS H.F.fr (csz := [8]) (cs := [(R.pa + BitVec.ofNat 64 (8 * i), 8)]) ⟨rfl, trivial⟩
      ⟨al0 (by
        show (ix .rdx .rsi 8).eval _ = R.pa + BitVec.ofNat 64 (8 * i)
        rw [ix_eval, H.rg.get (v := R.pa) (by simp), H.rsi, ixs_ofNat]), trivial⟩
  refine blk hp b3_in_code (by simp [b3]) run_b3 H.F H.pc hwf hm nofun (o := 8) (by decide +kernel) (by decide +kernel)
    fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hpw : (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)] 0).load 2 0 8 =
      (R.pw i).toBitVec := by
    rw [load_eq_wordOf]
    show (wordOf st.data.dmem (R.pa + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, G.rd H.F.chg (i := 3) (by omega) (by omega) hin]
    rfl
  have hpc1' := pc_cond hpc1 (b := decide (R.pw i = R.qw j)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, envRegs]
    rw [hpw, H.rg.get (v := (R.qw j).toBitVec) (by simp), beq_word])
  have hk1 : Regs s1.data (sA R j) := H.rg.keep hm1 (by kdec)
  have hk1' : Regs s1.data [(.rsi, BitVec.ofNat 64 i), (.rax, R.lv + BitVec.ofNat 64 (512 * i)),
      (.r8, BitVec.ofNat 64 (8 * (R.np - i))), (.r9, R.lv + BitVec.ofNat 64 (512 * i + 24))] :=
    Regs.keep (l := [(.rsi, _), (.rax, _), (.r8, _), (.r9, _)])
      (Regs.cons H.rsi (Regs.cons H.rax (Regs.cons H.r8 (Regs.cons H.r9 (Regs.nil _))))) hm1
      (by kdec)
  have hw1 := H.w.keep (FwK.of_eq hd1 _)
  have hw104 : R.FW s1.data.dmem 104 (BitVec.ofNat 64 (j + 1)) := hd1 ▸ H.w104
  have hmem1 : R.Begun j s1.data.dmem := hd1 ▸ H.mem
  by_cases he : R.pw i = R.qw j
  · rw [decide_eq_true he, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_5_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    exact .done _ (.inl (.inr ⟨i, hpc1', F1, H.lt, H.h0, hi, pos_some hi he H.miss, hmem1, hw1,
      hw104, hk1, hk1'.get (by simp), hk1'.get (by simp)⟩))
  rw [decide_eq_false he] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b4_in_code (by simp [b4]) run_b4 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  have hr8 : (BitVec.ofNat 64 18446744073709551608 + BitVec.ofNat 64 (8 * (R.np - i))) =
      BitVec.ofNat 64 (8 * (R.np - (i + 1))) := by
    rw [show R.np - i = R.np - (i + 1) + 1 by omega]
    exact (dec8 _).trans (by congr 2)
  have hpc2' := pc_cond hpc2 (b := decide (i + 1 ≠ R.np)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, add_eval, envRegs]
    rw [hk1'.get (v := BitVec.ofNat 64 (8 * (R.np - i))) (by simp), hr8, beq_ofNat (by omega)
      (by omega)]
    by_cases h : i + 1 = R.np
    · rw [decide_eq_false (by omega : ¬i + 1 ≠ R.np)]
      simp [show R.np - (i + 1) = 0 by omega]
    · rw [decide_eq_true h]
      simp [show R.np - (i + 1) ≠ 0 by omega])
  have miss : ∀ i' < i + 1, R.pw i' ≠ R.qw j := fun i' hi' ↦ by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
    · exact H.miss i' h
    · exact he
  by_cases hl : i + 1 = R.np
  · rw [decide_eq_false (by omega)] at hpc2'
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc2'
    have hwf3 := G.wf0 F2.fr.kept (ret := 0)
    refine blk hp b5_in_code (by simp [b5]) run_b5 F2 (hpc2'.trans (congrArg Host.addrOf rfl))
      hwf3 (frMatch F2.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s3 F3 _ hpc3 _ ↦ ?_
    have := pc_jump hpc3
    rw [hp.label NativeRustcVmX64.Vm.WriteOpenings.label_45_at] at this
    exact Eventually.mono (fail_spec hp G this F3 (bad_of_none H.lt fun i' hi' ↦
      miss i' (by omega))) fun _ h ↦ .inl (.inl h)
  rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_3_at] at hpc2'
  simp only [↓reduceIte] at hpc2'
  have hk2 : Regs s2.data (sA R j) := hk1.keep hm2 (by kdec)
  refine .done _ (.inr ⟨R.np - (i + 1), by omega, i + 1, rfl, hpc2', F2, H.lt, H.h0, by omega,
    miss, hd2 ▸ hmem1, hw1.keep (FwK.of_eq hd2 _), hd2 ▸ hw104, hk2, ?_, ?_, ?_, ?_⟩)
  · refine (hm2.regs .rsi _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [hk1'.get (v := BitVec.ofNat 64 i) (by simp), ofNat_add]
  · refine (hm2.regs .rax _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [hk1'.get (v := R.lv + BitVec.ofNat 64 (512 * i)) (by simp)]
    exact lit_add (by omega)
  · refine (hm2.regs .r8 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [hk1'.get (v := BitVec.ofNat 64 (8 * (R.np - i))) (by simp), hr8]
  · refine (hm2.regs .r9 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [hk1'.get (v := R.lv + BitVec.ofNat 64 (512 * i + 24)) (by simp)]
    exact lit_add (by omega)

end

end NativeRustcVmX64.Wire.WriteOpenings
