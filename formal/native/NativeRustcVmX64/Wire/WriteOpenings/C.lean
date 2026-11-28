module

public import NativeRustcVmX64.Wire.WriteOpenings.Step
public import NativeRustcVmX64.Transcript.Arith

/-!
# `write_openings` without levels and leaves (`h = 0`, `lw = 0`, x86-64)

rustc unrolled the queries' loop by two. From the head at query `j` (`HeadC`, `b42`): the query's
word stored, the positions scanned (`ScanC`, `b43`, `b44`) to the query's (`b46`): past the last
query the epilogue (`AtEnd`), else the next query's word stored (`b47`), scanned (`Scan2`, `b48`,
`b49`) to its position (`b51`): the head at query `j + 2` or the epilogue. A query at no position:
a rejection (`b45`, `b50`). `C_run`: the whole path from `b25`.
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVmX64.Transcript (Frame merge_one_mod)
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

@[expose] public section

/-- The registers at the head. -/
abbrev hC (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  [(.rdi, R.qa + BitVec.ofNat 64 (8 * j)), (.r9, BitVec.ofNat 64 j), (.rbp, R.out),
    (.rcx, BitVec.ofNat 64 (8 * R.np)), (.rdx, R.pa), (.r14, R.qe)]

/-- The registers through the first scan. -/
abbrev sC (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  hC R j ++ [(.rsi, R.qa + BitVec.ofNat 64 (8 * (j + 1))), (.rax, (R.qw j).toBitVec),
    (.r10, BitVec.ofNat 64 (1544 * j))]

/-- The registers through the second scan. -/
abbrev s2C (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  hC R (j + 2) ++ [(.rsi, (R.qw (j + 1)).toBitVec)]

/-- Decides a `keepAll` over path C's registers. -/
macro "kdecC" : tactic => `(tactic| (simp only [hC, sC, s2C, List.map_append, List.map_cons,
  List.map_nil, List.cons_append, List.nil_append]; decide +kernel))

variable [Host]

/-- **The head** (`b42`) at query `j`. -/
structure HeadC (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 241
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : R.h = 0
  lw0 : R.lw = 0
  done : R.Done st.data.dmem j
  rg : Regs st.data (hC R j)

/-- **The first scan** (`b43`) of query `j` at position `i`. -/
structure ScanC (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 249
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : R.h = 0
  lw0 : R.lw = 0
  ilt : i < R.np
  miss : ∀ i' < i, R.pw i' ≠ R.qw j
  mem : R.Begun j st.data.dmem
  rg : Regs st.data (sC R j)
  r8 : reg st.data .r8 = BitVec.ofNat 64 i
  r11 : reg st.data .r11 = BitVec.ofNat 64 (8 * (R.np - i))

/-- **Query `j` found** (`b46`). -/
structure FoundC (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 256
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : R.h = 0
  lw0 : R.lw = 0
  done : R.Done st.data.dmem (j + 1)
  rg : Regs st.data (sC R j)

/-- **The second scan** (`b48`) of query `j + 1` at position `i`. -/
structure Scan2 (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 267
  F : Fr R 8 st.data
  lt : j + 1 < R.nq
  h0 : R.h = 0
  lw0 : R.lw = 0
  al : boolRet st.data = 1
  ilt : i < R.np
  miss : ∀ i' < i, R.pw i' ≠ R.qw (j + 1)
  mem : R.Begun (j + 1) st.data.dmem
  rg : Regs st.data (s2C R j)
  r10 : reg st.data .r10 = BitVec.ofNat 64 i
  r8 : reg st.data .r8 = BitVec.ofNat 64 (8 * (R.np - i))

/-- **Query `j + 1` found** (`b51`). -/
structure Found2 (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 274
  F : Fr R 8 st.data
  lt : j + 1 < R.nq
  h0 : R.h = 0
  lw0 : R.lw = 0
  al : boolRet st.data = 1
  done : R.Done st.data.dmem (j + 2)
  rg : Regs st.data (hC R (j + 2))

end

public section

variable {R : Run} {j : Nat}

/-- **Opening `j` written** without levels and leaves: its word and position. -/
theorem done_succ0 {d : Mem 64} (hlw : R.lw = 0) (hh : R.h = 0) (hb : R.Begun j d) {i : Nat}
    (hpos : R.pos (R.qw j) = some i) : R.Done d (j + 1) :=
  ⟨hb.1.1, fun j' hj' ↦ by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | rfl
    · exact hb.1.2 j' h
    · exact ⟨i, hpos, hb.2, by rw [hlw]; exact leaf_zero, by rw [hh]; exact path_zero⟩⟩

variable [Host]

/-- **A query's word stored** (`b42`). -/
theorem headC_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : HeadC R j st) :
    Eventually (step1 Host.exe) (ScanC R j 0) st := by
  have hj := H.lt
  have hnq := G.nq256
  have hnp := G.np256
  have hob := ob_le (j := j) (by omega)
  have hob' : 24 + 1544 * j + 1544 ≤ phaseBytes := hob
  have hin2 := G.q_in hj
  have hin3 : Inside (R.oa (1544 * j)) 32 (R.big 7) := G.o_in (by omega) (by omega)
  have hwf := G.wf2 H.F.fr.kept (i := 2) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin2 hin3 (ret := 0)
  have hm : Match (envOf R st.data [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (1544 * j), 32)] 0)
      (qS .r9) st.data :=
    match_fS H.F.fr (csz := [8, 32])
      (cs := [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (1544 * j), 32)]) ⟨rfl, rfl, trivial⟩
      ⟨al0 (by
        show reg st.data .rdi = R.qa + BitVec.ofNat 64 (8 * j)
        exact H.rg.get (by simp)), al0 (by
        show (ix .rbp .r9 1544).eval _ = R.oa (1544 * j)
        rw [ix_eval, H.rg.get (v := R.out) (by simp), H.rg.get (v := BitVec.ofNat 64 j) (by simp),
          ixs_ofNat]), trivial⟩
  refine blkW G hp b42_in_code (by simp [b42]) run_b42 H.F H.pc hwf hm nofun (o := 8) (by decide +kernel)
    (ro := 3) rfl (lo := 24) (a := R.oa (ob j)) (n := 8) (addr_add (by unfold ob; omega))
    (G.o_in (by omega) (by omega)) (by decide +kernel) fun st1 F1 hm1 hpc1 hs ↦ .done _ ?_
  have hqw : wordOf st.data.dmem (R.qa + BitVec.ofNat 64 (8 * j)) = R.qw j :=
    G.rd H.F.chg (i := 2) (by omega) (by omega) hin2
  have hl2 : (envOf R st.data [(R.qa + BitVec.ofNat 64 (8 * j), 8), (R.oa (1544 * j), 32)] 0).load
      2 0 8 = (R.qw j).toBitVec := by
    rw [load_eq_wordOf]
    show (wordOf st.data.dmem (R.qa + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, hqw]
  have hw' : WordAt st1.data.dmem (R.oa (ob j)) (R.qw j) :=
    word_at (stored_load hm1 (r := 3) (o := 24) (sz := 32) rfl (by omega) (r' := 2) (o' := 0)
      (by decide +kernel) hl2) (by unfold ob; omega)
  refine ⟨pc_fall hpc1, F1, hj, H.h0, H.lw0, G.np0, fun _ h ↦ absurd h (Nat.not_lt_zero _),
    ⟨G.done_keep (o := ob j) (n := 8) hs (by omega) (by omega) H.done (le_refl _), hw'⟩, ?_,
    hm1.regs .r8 _ rfl, ?_⟩
  · refine Regs.append (H.rg.keep hm1 (by kdecC)) (Regs.cons ?_ (Regs.cons
      ((hm1.regs .rax _ rfl).trans hl2) (Regs.cons ?_ (Regs.nil _))))
    · refine (hm1.regs .rsi _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [H.rg.get (v := R.qa + BitVec.ofNat 64 (8 * j)) (by simp)]
      exact addr_add (by omega)
    · refine (hm1.regs .r10 _ rfl).trans ?_
      simp only [Sym.eval, mul_eval, envRegs]
      rw [H.rg.get (v := BitVec.ofNat 64 j) (by simp), ofNat_mul, Nat.mul_comm]
  · rw [Nat.sub_zero]
    exact kregV hm1 (x := .rcx) rfl (H.rg.get (by simp))

/-- **The first scan** (`b43`, `b44`, `b45`). -/
theorem scanC_loop (hp : Placed code R.k) (G : Geo R) {i : Nat} {st : MachineState}
    (H : ScanC R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ FoundC R j st') st := by
  refine Sym.loop (fun n st ↦ ∃ i, n = R.np - i ∧ ScanC R j i st) (fun n st ⟨i, hn, H⟩ ↦ ?_)
    ⟨i, rfl, H⟩
  have hi := H.ilt
  have hnp := G.np256
  have hin := G.p_in hi
  have hwf := G.wf1 H.F.fr.kept (i := 3) (by omega) (by omega) hin (ret := 0)
  have hm : Match (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)] 0) (pS .r8) st.data :=
    match_fS H.F.fr (csz := [8]) (cs := [(R.pa + BitVec.ofNat 64 (8 * i), 8)]) ⟨rfl, trivial⟩
      ⟨al0 (by
        show (ix .rdx .r8 8).eval _ = R.pa + BitVec.ofNat 64 (8 * i)
        rw [ix_eval, H.rg.get (v := R.pa) (by simp), H.r8, ixs_ofNat]), trivial⟩
  refine blk hp b43_in_code (by simp [b43]) run_b43 H.F H.pc hwf hm nofun (o := 8) (by decide +kernel)
    (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
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
  have hk1 : Regs s1.data (sC R j) := H.rg.keep hm1 (by kdecC)
  by_cases he : R.pw i = R.qw j
  · rw [decide_eq_true he, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_39_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    exact .done _ (.inl (.inr ⟨hpc1', F1, H.lt, H.h0, H.lw0,
      done_succ0 H.lw0 H.h0 (hd1 ▸ H.mem) (pos_some hi he H.miss), hk1⟩))
  rw [decide_eq_false he] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b44_in_code (by simp [b44]) run_b44 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  have hr11 : reg s1.data .r11 = BitVec.ofNat 64 (8 * (R.np - i)) := kreg hm1 rfl H.r11
  have hr11' : (BitVec.ofNat 64 18446744073709551608 + BitVec.ofNat 64 (8 * (R.np - i))) =
      BitVec.ofNat 64 (8 * (R.np - (i + 1))) := by
    rw [show R.np - i = R.np - (i + 1) + 1 by omega]
    exact dec8 _
  have hpc2' := pc_cond hpc2 (b := decide (i + 1 ≠ R.np)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, add_eval, envRegs]
    rw [hr11, hr11', beq_ofNat (by omega) (by omega), not_beq_decide]
    by_cases h : i + 1 = R.np
    · rw [decide_eq_false (by omega : ¬i + 1 ≠ R.np), decide_eq_false (by omega)]
    · rw [decide_eq_true h, decide_eq_true (by omega)])
  have miss : ∀ i' < i + 1, R.pw i' ≠ R.qw j := fun i' hi' ↦ by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
    · exact H.miss i' h
    · exact he
  by_cases hl : i + 1 = R.np
  · rw [decide_eq_false (by omega)] at hpc2'
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc2'
    have hwf3 := G.wf0 F2.fr.kept (ret := 0)
    refine blk hp b45_in_code (by simp [b45]) run_b45 F2 (hpc2'.trans (congrArg Host.addrOf rfl))
      hwf3 (frMatch F2.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s3 F3 _ hpc3 _ ↦ ?_
    have := pc_jump hpc3
    rw [hp.label NativeRustcVmX64.Vm.WriteOpenings.label_45_at] at this
    exact Eventually.mono (fail_spec hp G this F3 (bad_of_none H.lt fun i' hi' ↦
      miss i' (by omega))) fun _ h ↦ .inl (.inl h)
  rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_37_at] at hpc2'
  simp only [↓reduceIte] at hpc2'
  refine .done _ (.inr ⟨R.np - (i + 1), by omega, i + 1, rfl, hpc2', F2, H.lt, H.h0, H.lw0,
    by omega, miss, hd2 ▸ hd1 ▸ H.mem, hk1.keep hm2 (by kdecC), ?_, ?_⟩)
  · refine (hm2.regs .r8 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [kreg hm1 rfl H.r8, ofNat_add]
  · refine (hm2.regs .r11 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [hr11, hr11']

/-- **Query `j` found** (`b46`, then `b47`): the epilogue, or the next query's word stored. -/
theorem foundC_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : FoundC R j st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtEnd R st' ∨ Scan2 R j 0 st') st := by
  have hj := H.lt
  have hnq := G.nq256
  have hnp := G.np256
  have hA : j + 1 < R.nq → 1544 * j + 1576 ≤ phaseBytes ∧ ob (j + 1) + 8 ≤ phaseBytes ∧
      8 * j + 16 ≤ 8 * R.nq ∧ 1544 * j + 1568 = ob (j + 1) := fun h ↦ by
    have := phaseBytes_val
    simp only [ob]
    omega
  have hwf := G.wf0 H.F.fr.kept (ret := 0)
  refine blk hp b46_in_code (by simp [b46]) run_b46 H.F H.pc hwf (frMatch H.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hax : boolRet s1.data = 1 := by
    unfold boolRet
    rw [show reg s1.data .rax = _ from hm1.regs .rax _ rfl]
    exact merge_one_mod _
  have hpc1' := pc_cond hpc1 (b := decide (j + 1 = R.nq)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, envRegs]
    rw [H.rg.get (v := R.qa + BitVec.ofNat 64 (8 * (j + 1))) (by simp),
      H.rg.get (v := R.qe) (by simp), beq_add (by omega) (by omega), beq_decide]
    by_cases h : j + 1 = R.nq
    · rw [decide_eq_true (by omega), decide_eq_true h]
    · rw [decide_eq_false (by omega), decide_eq_false h])
  by_cases hl : j + 1 = R.nq
  · rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_46_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    exact .done _ (.inl ⟨hpc1', F1, .inl ⟨hax, by rw [hd1, ← hl]; exact H.done⟩⟩)
  rw [decide_eq_false hl] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hk1 : Regs s1.data (hC R j) := H.rg.left.keep hm1 (by kdecC)
  have hr10 : reg s1.data .r10 = BitVec.ofNat 64 (1544 * j) :=
    kreg hm1 rfl (H.rg.get (v := BitVec.ofNat 64 (1544 * j)) (by simp))
  -- `b47`.
  have hj1 : j + 1 < R.nq := by omega
  obtain ⟨hA1, hO, hA3, hA4⟩ := hA hj1
  have hin2 : Inside (R.qa + BitVec.ofNat 64 (8 * j)) 16 (R.big 2) :=
    inside_off (A := R.big 2) (G.noWrap (by decide +kernel)) hA3 (by decide +kernel)
  have hin3 : Inside (R.oa (1544 * j)) 1576 (R.big 7) := G.o_in hA1 (by decide +kernel)
  have hwf2 := G.wf2 F1.fr.kept (i := 2) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin2 hin3 (ret := 0)
  have hm2 : Match (envOf R s1.data [(R.qa + BitVec.ofNat 64 (8 * j), 16), (R.oa (1544 * j), 1576)]
      0) q2S s1.data :=
    match_fS F1.fr (csz := [16, 1576])
      (cs := [(R.qa + BitVec.ofNat 64 (8 * j), 16), (R.oa (1544 * j), 1576)]) ⟨rfl, rfl, trivial⟩
      ⟨al0 (by
        show reg s1.data .rdi = R.qa + BitVec.ofNat 64 (8 * j)
        exact hk1.get (by simp)), al0 (by
        show BinOp.apply .add .W64 (reg s1.data .rbp) (reg s1.data .r10) = R.oa (1544 * j)
        rw [hk1.get (v := R.out) (by simp), hr10, add_eval]), trivial⟩
  refine blkW G hp b47_in_code (by simp [b47]) run_b47 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 hm2 nofun (o := 8) (by decide +kernel) (ro := 3) rfl (lo := 1568) (a := R.oa (ob (j + 1)))
    (n := 8) (addr_add hA4) (G.o_in hO (by decide +kernel)) (by decide +kernel)
    fun s2 F2 hm3 hpc2 hs2 ↦ .done _ (.inr ?_)
  have hq1 : (envOf R s1.data [(R.qa + BitVec.ofNat 64 (8 * j), 16), (R.oa (1544 * j), 1576)]
      0).load 2 8 8 = (R.qw (j + 1)).toBitVec := by
    rw [G.in_load F1.chg (r := 2) rfl (by omega) (i := 2) (by omega) (by omega) (by
      rw [NativeRustcVm.addr_add_add]; exact G.q_in (j := j + 1) (by omega) |>.take (le_refl _)
        |> fun h ↦ by rwa [show 8 * (j + 1) = 8 * j + 8 by omega] at h),
      NativeRustcVm.addr_add_add, show 8 * j + 8 = 8 * (j + 1) by omega]
    rfl
  have hw' : WordAt s2.data.dmem (R.oa (ob (j + 1))) (R.qw (j + 1)) :=
    word_at (stored_load hm3 (r := 3) (o := 1568) (sz := 1576) rfl (by decide +kernel) (r' := 2) (o' := 8)
      (by decide +kernel) hq1) hA4
  have hd : R.Done st.data.dmem (j + 1) := H.done
  refine ⟨(pc_fall hpc2).trans (congrArg Host.addrOf rfl), F2, by omega, H.h0, H.lw0, ?_, G.np0,
    fun _ h ↦ absurd h (Nat.not_lt_zero _),
    ⟨G.done_keep (o := ob (j + 1)) (n := 8) hs2 hO (by omega) (hd1 ▸ hd) (le_refl _),
      hw'⟩, ?_, hm3.regs .r10 _ rfl, ?_⟩
  · unfold boolRet
    rw [kreg hm3 (r := .rax) rfl rfl]
    exact hax
  · refine Regs.cons ?_ (Regs.cons ?_ (Regs.cons (kreg hm3 rfl (hk1.get (by simp)))
      (Regs.cons (kreg hm3 rfl (hk1.get (by simp))) (Regs.cons (kreg hm3 rfl (hk1.get (by simp)))
      (Regs.cons (kreg hm3 rfl (hk1.get (by simp))) (Regs.cons ((hm3.regs .rsi _ rfl).trans hq1)
      (Regs.nil _)))))))
    · refine (hm3.regs .rdi _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [hk1.get (v := R.qa + BitVec.ofNat 64 (8 * j)) (by simp)]
      exact lit_add (by omega)
    · refine (hm3.regs .r9 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [hk1.get (v := BitVec.ofNat 64 j) (by simp), ofNat_add, Nat.add_comm]
  · rw [Nat.sub_zero]
    exact kregV hm3 (x := .rcx) rfl (hk1.get (by simp))

/-- **The second scan** (`b48`, `b49`, `b50`). -/
theorem scan2_loop (hp : Placed code R.k) (G : Geo R) {i : Nat} {st : MachineState}
    (H : Scan2 R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ Found2 R j st') st := by
  refine Sym.loop (fun n st ↦ ∃ i, n = R.np - i ∧ Scan2 R j i st) (fun n st ⟨i, hn, H⟩ ↦ ?_)
    ⟨i, rfl, H⟩
  have hi := H.ilt
  have hnp := G.np256
  have hin := G.p_in hi
  have hwf := G.wf1 H.F.fr.kept (i := 3) (by omega) (by omega) hin (ret := 0)
  have hm : Match (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)] 0) (pS .r10) st.data :=
    match_fS H.F.fr (csz := [8]) (cs := [(R.pa + BitVec.ofNat 64 (8 * i), 8)]) ⟨rfl, trivial⟩
      ⟨al0 (by
        show (ix .rdx .r10 8).eval _ = R.pa + BitVec.ofNat 64 (8 * i)
        rw [ix_eval, H.rg.get (v := R.pa) (by simp), H.r10, ixs_ofNat]), trivial⟩
  refine blk hp b48_in_code (by simp [b48]) run_b48 H.F H.pc hwf hm nofun (o := 8) (by decide +kernel)
    (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hpw : (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)] 0).load 2 0 8 =
      (R.pw i).toBitVec := by
    rw [load_eq_wordOf]
    show (wordOf st.data.dmem (R.pa + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, G.rd H.F.chg (i := 3) (by omega) (by omega) hin]
    rfl
  have hpc1' := pc_cond hpc1 (b := decide (R.pw i = R.qw (j + 1))) (by
    simp only [SBool.eval, Sym.eval, eq_eval, envRegs]
    rw [hpw, H.rg.get (v := (R.qw (j + 1)).toBitVec) (by simp), beq_word])
  have hk1 : Regs s1.data (s2C R j) := H.rg.keep hm1 (by kdecC)
  have hal1 : boolRet s1.data = 1 := by unfold boolRet; rw [kreg hm1 (r := .rax) rfl rfl]; exact H.al
  by_cases he : R.pw i = R.qw (j + 1)
  · rw [decide_eq_true he, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_43_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    exact .done _ (.inl (.inr ⟨hpc1', F1, H.lt, H.h0, H.lw0, hal1,
      done_succ0 H.lw0 H.h0 (hd1 ▸ H.mem) (pos_some hi he H.miss), hk1.left⟩))
  rw [decide_eq_false he] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b49_in_code (by simp [b49]) run_b49 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  have hr8 : reg s1.data .r8 = BitVec.ofNat 64 (8 * (R.np - i)) := kreg hm1 rfl H.r8
  have hr8' : (BitVec.ofNat 64 18446744073709551608 + BitVec.ofNat 64 (8 * (R.np - i))) =
      BitVec.ofNat 64 (8 * (R.np - (i + 1))) := by
    rw [show R.np - i = R.np - (i + 1) + 1 by omega]
    exact dec8 _
  have hpc2' := pc_cond hpc2 (b := decide (i + 1 ≠ R.np)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, add_eval, envRegs]
    rw [hr8, hr8', beq_ofNat (by omega) (by omega), not_beq_decide]
    by_cases h : i + 1 = R.np
    · rw [decide_eq_false (by omega : ¬i + 1 ≠ R.np), decide_eq_false (by omega)]
    · rw [decide_eq_true h, decide_eq_true (by omega)])
  have miss : ∀ i' < i + 1, R.pw i' ≠ R.qw (j + 1) := fun i' hi' ↦ by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
    · exact H.miss i' h
    · exact he
  by_cases hl : i + 1 = R.np
  · rw [decide_eq_false (by omega)] at hpc2'
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc2'
    have hwf3 := G.wf0 F2.fr.kept (ret := 0)
    refine blk hp b50_in_code (by simp [b50]) run_b50 F2 (hpc2'.trans (congrArg Host.addrOf rfl))
      hwf3 (frMatch F2.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s3 F3 _ hpc3 _ ↦ ?_
    have := pc_jump hpc3
    rw [hp.label NativeRustcVmX64.Vm.WriteOpenings.label_45_at] at this
    exact Eventually.mono (fail_spec hp G this F3 (bad_of_none H.lt fun i' hi' ↦
      miss i' (by omega))) fun _ h ↦ .inl (.inl h)
  rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_41_at] at hpc2'
  simp only [↓reduceIte] at hpc2'
  refine .done _ (.inr ⟨R.np - (i + 1), by omega, i + 1, rfl, hpc2', F2, H.lt, H.h0, H.lw0,
    by unfold boolRet; rw [kreg hm2 (r := .rax) rfl rfl]; exact hal1,
    by omega, miss, hd2 ▸ hd1 ▸ H.mem, hk1.keep hm2 (by kdecC), ?_, ?_⟩)
  · refine (hm2.regs .r10 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [kreg hm1 rfl H.r10, ofNat_add]
  · refine (hm2.regs .r8 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [hr8, hr8']

/-- **Query `j + 1` found** (`b51`, `b52`): the head at `j + 2`, or the epilogue. -/
theorem found2_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : Found2 R j st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtEnd R st' ∨ HeadC R (j + 2) st') st := by
  have hj := H.lt
  have hnq := G.nq256
  have hwf := G.wf0 H.F.fr.kept (ret := 0)
  refine blk hp b51_in_code (by simp [b51]) run_b51 H.F H.pc hwf (frMatch H.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 : Regs s1.data (hC R (j + 2)) := H.rg.keep hm1 (by kdecC)
  have hal1 : boolRet s1.data = 1 := by unfold boolRet; rw [kreg hm1 (r := .rax) rfl rfl]; exact H.al
  have hpc1' := pc_cond hpc1 (b := decide (j + 2 ≠ R.nq)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, envRegs]
    rw [H.rg.get (v := R.qa + BitVec.ofNat 64 (8 * (j + 2))) (by simp),
      H.rg.get (v := R.qe) (by simp), beq_add (by omega) (by omega), not_beq_decide]
    by_cases h : j + 2 = R.nq
    · rw [decide_eq_false (by omega), decide_eq_false (by omega)]
    · rw [decide_eq_true (by omega), decide_eq_true h])
  by_cases hl : j + 2 ≠ R.nq
  · rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_36_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    exact .done _ (.inr ⟨hpc1', F1, by omega, H.h0, H.lw0, hd1 ▸ H.done, hk1⟩)
  rw [decide_eq_false hl] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b52_in_code (by simp [b52]) run_b52 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  refine .done _ (.inl ⟨(pc_jump hpc2).trans (hp.label NativeRustcVmX64.Vm.WriteOpenings.label_46_at), F2, .inl ⟨?_, ?_⟩⟩)
  · unfold boolRet; rw [kreg hm2 (r := .rax) rfl rfl]; exact hal1
  · rw [hd2, hd1, show R.nq = j + 2 by omega]; exact H.done

/-- **The path without levels and leaves**, from its head at query `j`. -/
theorem C_loop (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : HeadC R j st) :
    Eventually (step1 Host.exe) (Post R) st := by
  refine Sym.loop (fun n st ↦ ∃ j, n = R.nq - j ∧ HeadC R j st) (fun n st ⟨j, hn, H⟩ ↦ ?_)
    ⟨j, rfl, H⟩
  have hj := H.lt
  refine (headC_step hp G H).bind fun s1 H1 ↦ (scanC_loop hp G H1).bind fun s2 h2 ↦ ?_
  rcases h2 with h2 | H2
  · exact .done _ (.inl h2)
  refine (foundC_step hp G H2).bind fun s3 h3 ↦ ?_
  rcases h3 with h3 | H3
  · exact (end_spec hp G h3).mono fun _ h ↦ .inl h
  refine (scan2_loop hp G H3).bind fun s4 h4 ↦ ?_
  rcases h4 with h4 | H4
  · exact .done _ (.inl h4)
  refine (found2_step hp G H4).bind fun s5 h5 ↦ ?_
  rcases h5 with h5 | H5
  · exact (end_spec hp G h5).mono fun _ h ↦ .inl h
  · exact .done _ (.inr ⟨R.nq - (j + 2), by have := H4.lt; omega, j + 2, rfl, H5⟩)

end

end NativeRustcVmX64.Wire.WriteOpenings
