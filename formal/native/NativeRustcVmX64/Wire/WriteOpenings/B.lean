module

public import NativeRustcVmX64.Wire.WriteOpenings.C

/-!
# `write_openings` without levels, with leaves (`h = 0`, `0 < lw`, x86-64)

From the head at query `j` (`HeadB`, `b27`): the query's word stored, the positions scanned
(`ScanB`, `b28`, `b29`) to the query's (`FoundB`, `b32`), the leaf copied four words (`ChunkB`,
`b35`) then one word (`RemB`, `b38`) at a time (from `PreRemB`, `b37`), then the next query's head
or the epilogue (`LeafB`, `b39`). `noLev`: from the prologue's branch (`b25`), this path or path C.
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVmX64.Transcript (Frame merge_one_mod)
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

@[expose] public section

/-- The frame words of path B. -/
abbrev wBf (R : Run) : List (Nat × BitVec 64) :=
  [(16, R.lv + BitVec.ofNat 64 24), (24, R.lv), (32, BitVec.ofNat 64 R.lw)]

/-- The registers path B keeps through opening `j`. -/
abbrev cB (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  [(.rbp, R.out), (.rcx, BitVec.ofNat 64 (8 * R.np)), (.rdx, R.pa),
    (.r12, BitVec.ofNat 64 (q4 R.lw)), (.r13, R.oa (ob j + 32)), (.r8, R.oa (ob j + 8)),
    (.r15, BitVec.ofNat 64 (R.lw % 4))]

/-- The registers at the head. -/
abbrev hB (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  cB R j ++ [(.rdi, R.qa + BitVec.ofNat 64 (8 * j)), (.r9, BitVec.ofNat 64 j), (.r10, R.lv),
    (.rbx, R.lv + BitVec.ofNat 64 24), (.r14, R.qe)]

/-- The registers through the scan. -/
abbrev sB (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  cB R j ++ [(.rdi, R.qa + BitVec.ofNat 64 (8 * (j + 1))), (.r9, BitVec.ofNat 64 (j + 1)),
    (.rsi, R.qe), (.r11, (R.qw j).toBitVec)]

/-- The registers through the copy. -/
abbrev kB (R : Run) (j : Nat) : List (Reg64 × BitVec 64) :=
  cB R j ++ [(.rdi, R.qa + BitVec.ofNat 64 (8 * (j + 1))), (.r9, BitVec.ofNat 64 (j + 1)),
    (.r14, R.qe)]

/-- Decides a fact about path B's lists. -/
macro "kdecB" : tactic => `(tactic| (simp only [wBf, cB, hB, sB, kB, List.map_append,
  List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide +kernel))

/-- What the leaf's copy keeps. -/
structure KB (R : Run) (j i : Nat) (m : MachineData) : Prop where
  F : Fr R 8 m
  lt : j < R.nq
  h0 : R.h = 0
  ilt : i < R.np
  pos : R.pos (R.qw j) = some i
  mem : R.Begun j m.dmem
  w : FWs R m.dmem (wBf R)
  rg : Regs m (kB R j)

variable [Host]

/-- **The head** (`b27`) at query `j`. -/
structure HeadB (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 172
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : R.h = 0
  done : R.Done st.data.dmem j
  w : FWs R st.data.dmem (wBf R)
  rg : Regs st.data (hB R j)

/-- **The scan** (`b28`) of query `j` at position `i`. -/
structure ScanB (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 184
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : R.h = 0
  ilt : i < R.np
  miss : ∀ i' < i, R.pw i' ≠ R.qw j
  mem : R.Begun j st.data.dmem
  w : FWs R st.data.dmem (wBf R)
  rg : Regs st.data (sB R j)
  r14 : reg st.data .r14 = BitVec.ofNat 64 i
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i)
  r10 : reg st.data .r10 = R.lv + BitVec.ofNat 64 (512 * i + 24)
  rbx : reg st.data .rbx = BitVec.ofNat 64 (8 * (R.np - i))

/-- **Query `j` found at position `i`** (`b32`). -/
structure FoundB (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 194
  F : Fr R 8 st.data
  lt : j < R.nq
  h0 : R.h = 0
  ilt : i < R.np
  pos : R.pos (R.qw j) = some i
  mem : R.Begun j st.data.dmem
  w : FWs R st.data.dmem (wBf R)
  rg : Regs st.data (sB R j)
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i)
  r10 : reg st.data .r10 = R.lv + BitVec.ofNat 64 (512 * i + 24)

/-- **Four words at a time** (`b35`), `t` copied. -/
structure ChunkB (R : Run) (j i t : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 204
  k : KB R j i st.data
  leaf : R.LeafPart st.data.dmem j i t
  t4 : t % 4 = 0
  tq : t + 4 ≤ q4 R.lw
  r11 : reg st.data .r11 = BitVec.ofNat 64 t
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i)
  r10 : reg st.data .r10 = R.lv + BitVec.ofNat 64 (512 * i + 8 * t + 24)

/-- **Before the remaining words** (`b37`), `q4 lw` copied. -/
structure PreRemB (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 219
  k : KB R j i st.data
  leaf : R.LeafPart st.data.dmem j i (q4 R.lw)
  pos : 0 < R.lw % 4
  r11 : reg st.data .r11 = BitVec.ofNat 64 (q4 R.lw)
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i)

/-- **One word at a time** (`b38`), `q4 lw + u` copied. -/
structure RemB (R : Run) (j i u : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 224
  k : KB R j i st.data
  leaf : R.LeafPart st.data.dmem j i (q4 R.lw + u)
  ult : u < R.lw % 4
  r11 : reg st.data .r11 = BitVec.ofNat 64 u
  rax : reg st.data .rax = R.lv + BitVec.ofNat 64 (512 * i + 8 * q4 R.lw)
  r10 : reg st.data .r10 = R.oa (ob j + 8 + 8 * q4 R.lw)

/-- **The leaf copied** (`b39`). -/
structure LeafB (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 230
  k : KB R j i st.data
  leaf : R.LeafPart st.data.dmem j i R.lw

end

public section

variable {R : Run} {j i : Nat}

theorem KB.next {m m' : MachineData} (h : KB R j i m) (F : Fr R 8 m') (hd : m'.dmem = m.dmem)
    (hr : Regs m' (kB R j)) : KB R j i m' :=
  ⟨F, h.lt, h.h0, h.ilt, h.pos, hd ▸ h.mem, h.w.keep (FwK.of_eq hd _), hr⟩

theorem KB.write (G : Geo R) {m m' : MachineData} (h : KB R j i m) (F : Fr R 8 m') {o n : Nat}
    (hs : SameOutside m.dmem m'.dmem (R.FO o n)) (hon : o + n ≤ phaseBytes) (ho : ob j + 8 ≤ o)
    (hk : FwK R m.dmem m'.dmem ((wBf R).map Prod.fst)) (hr : Regs m' (kB R j)) : KB R j i m' :=
  ⟨F, h.lt, h.h0, h.ilt, h.pos, G.begun_keep hs hon h.lt h.mem ho, h.w.keep hk, hr⟩

variable [Host]

/-- **The query's word stored** (`b27`). -/
theorem headB_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : HeadB R j st) :
    Eventually (step1 Host.exe) (ScanB R j 0) st := by
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
  refine blkW G hp b27_in_code (by simp [b27]) run_b27 H.F H.pc hwf hm nofun (o := 8) (by decide +kernel)
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
      (by decide +kernel) hl2) (by simp only [ob]; omega)
  have hk := fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := (wBf R).map Prod.fst) (by kdecB)
    (by kdecB)
  refine ⟨pc_fall hpc1, F1, hj, H.h0, G.np0, fun _ h ↦ absurd h (Nat.not_lt_zero _),
    ⟨G.done_keep (o := ob j) (n := 8) hs (by omega) (by omega) H.done (le_refl _), hw'⟩,
    H.w.keep hk, ?_, hm1.regs .r14 _ rfl, ?_, ?_, ?_⟩
  · refine Regs.append (H.rg.left.keep hm1 (by kdecB)) (Regs.cons ?_ (Regs.cons ?_ (Regs.cons
      (kregV hm1 (x := .r14) rfl (H.rg.get (by simp))) (Regs.cons ((hm1.regs .r11 _ rfl).trans
        hl2) (Regs.nil _)))))
    · refine (hm1.regs .rdi _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [H.rg.get (v := R.qa + BitVec.ofNat 64 (8 * j)) (by simp)]
      exact lit_add (by omega)
    · refine (hm1.regs .r9 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [H.rg.get (v := BitVec.ofNat 64 j) (by simp), ofNat_add]
  · rw [Nat.mul_zero, NativeRustcVm.addr_add_zero]
    exact kregV hm1 (x := .r10) rfl (H.rg.get (by simp))
  · rw [Nat.mul_zero, Nat.zero_add]
    exact kregV hm1 (x := .rbx) rfl (H.rg.get (by simp))
  · rw [Nat.sub_zero]
    exact kregV hm1 (x := .rcx) rfl (H.rg.get (by simp))

/-- **The scan** (`b28`, `b29`, `b30`). -/
theorem scanB_loop (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : ScanB R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ ∃ i, FoundB R j i st') st := by
  refine Sym.loop (fun n st ↦ ∃ i, n = R.np - i ∧ ScanB R j i st) (fun n st ⟨i, hn, H⟩ ↦ ?_)
    ⟨i, rfl, H⟩
  have hi := H.ilt
  have hnp := G.np256
  have hin := G.p_in hi
  have hwf := G.wf1 H.F.fr.kept (i := 3) (by omega) (by omega) hin (ret := 0)
  have hm : Match (envOf R st.data [(R.pa + BitVec.ofNat 64 (8 * i), 8)] 0) (pS .r14) st.data :=
    match_fS H.F.fr (csz := [8]) (cs := [(R.pa + BitVec.ofNat 64 (8 * i), 8)]) ⟨rfl, trivial⟩
      ⟨al0 (by
        show (ix .rdx .r14 8).eval _ = R.pa + BitVec.ofNat 64 (8 * i)
        rw [ix_eval, H.rg.get (v := R.pa) (by simp), H.r14, ixs_ofNat]), trivial⟩
  refine blk hp b28_in_code (by simp [b28]) run_b28 H.F H.pc hwf hm nofun (o := 8) (by decide +kernel)
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
  have hk1 : Regs s1.data (sB R j) := H.rg.keep hm1 (by kdecB)
  have hw1 := H.w.keep (FwK.of_eq hd1 _)
  by_cases he : R.pw i = R.qw j
  · rw [decide_eq_true he, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_25_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    exact .done _ (.inl (.inr ⟨i, hpc1', F1, H.lt, H.h0, hi, pos_some hi he H.miss,
      hd1 ▸ H.mem, hw1, hk1, kreg hm1 rfl H.rax, kreg hm1 rfl H.r10⟩))
  rw [decide_eq_false he] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b29_in_code (by simp [b29]) run_b29 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  have hrb : reg s1.data .rbx = BitVec.ofNat 64 (8 * (R.np - i)) := kreg hm1 rfl H.rbx
  have hrb' : (BitVec.ofNat 64 18446744073709551608 + BitVec.ofNat 64 (8 * (R.np - i))) =
      BitVec.ofNat 64 (8 * (R.np - (i + 1))) := by
    rw [show R.np - i = R.np - (i + 1) + 1 by omega]
    exact dec8 _
  have hpc2' := pc_cond hpc2 (b := decide (i + 1 ≠ R.np)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, add_eval, envRegs]
    rw [hrb, hrb', beq_ofNat (by omega) (by omega), not_beq_decide]
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
    refine blk hp b30_in_code (by simp [b30]) run_b30 F2 (hpc2'.trans (congrArg Host.addrOf rfl))
      hwf3 (frMatch F2.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s3 F3 _ hpc3 _ ↦ ?_
    have := pc_jump hpc3
    rw [hp.label NativeRustcVmX64.Vm.WriteOpenings.label_45_at] at this
    exact Eventually.mono (fail_spec hp G this F3 (bad_of_none H.lt fun i' hi' ↦
      miss i' (by omega))) fun _ h ↦ .inl (.inl h)
  rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_23_at] at hpc2'
  simp only [↓reduceIte] at hpc2'
  refine .done _ (.inr ⟨R.np - (i + 1), by omega, i + 1, rfl, hpc2', F2, H.lt, H.h0, by omega,
    miss, hd2 ▸ hd1 ▸ H.mem, hw1.keep (FwK.of_eq hd2 _), hk1.keep hm2 (by kdecB), ?_, ?_, ?_, ?_⟩)
  · refine (hm2.regs .r14 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [kreg hm1 rfl H.r14, ofNat_add]
  · refine (hm2.regs .rax _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [kreg hm1 rfl H.rax]
    exact lit_add (by omega)
  · refine (hm2.regs .r10 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [kreg hm1 rfl H.r10]
    exact lit_add (by omega)
  · refine (hm2.regs .rbx _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [hrb, hrb']

/-- **The query found** (`b32`, then `b33` or `b34`): the leaf's copy. -/
theorem foundB_step (hp : Placed code R.k) (G : Geo R) (hlw0 : 0 < R.lw) {st : MachineState}
    (H : FoundB R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ ChunkB R j i 0 st' ∨ PreRemB R j i st') st := by
  have hlw := G.lw64
  have hq4d : q4 R.lw = R.lw / 4 * 4 := rfl
  have hwf := G.wf0 H.F.fr.kept (ret := 0)
  refine blk hp b32_in_code (by simp [b32]) run_b32 H.F H.pc hwf (frMatch H.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 : Regs s1.data (sB R j) := H.rg.keep hm1 (by kdecB)
  have hpc1' := pc_cond hpc1 (b := decide (4 ≤ R.lw)) (by
    simp only [SBool.eval, Sym.eval, ult_eval]
    rw [fw_load (H.w.get (v := BitVec.ofNat 64 R.lw) (by simp)), toNat_ofNat (by omega),
      toNat_ofNat (by decide +kernel)]
    by_cases h : 4 ≤ R.lw
    · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
    · rw [decide_eq_true (by omega), decide_eq_false h]; rfl)
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  have K : ∀ s : MachineState, Fr R 8 s.data → s.data.dmem = st.data.dmem →
      Regs s.data (kB R j) → KB R j i s.data := fun s F hd hr ↦
    ⟨F, H.lt, H.h0, H.ilt, H.pos, hd ▸ H.mem, H.w.keep (FwK.of_eq hd _), hr⟩
  by_cases h4 : 4 ≤ R.lw
  · rw [decide_eq_true h4, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_27_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    refine blk hp b34_in_code (by simp [b34]) run_b34 F1 hpc1' hwf2 (frMatch F1.fr) nofun (o := 8)
      (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
    have hd2 : s2.data.dmem = st.data.dmem := (hm2.dmem_eq hwf2 rfl).trans hd1
    refine .done _ (.inl ⟨(pc_fall hpc2).trans (congrArg Host.addrOf rfl), K s2 F2 hd2 ?_,
      leaf_zero, rfl, by omega, hm2.regs .r11 _ rfl, kreg hm2 rfl (kreg hm1 rfl H.rax), ?_⟩)
    · refine Regs.append (hk1.left.keep hm2 (by kdecB)) (Regs.cons
        (kreg hm2 rfl (hk1.get (by simp))) (Regs.cons (kreg hm2 rfl (hk1.get (by simp)))
        (Regs.cons (kregV hm2 (x := .rsi) rfl (hk1.get (by simp))) (Regs.nil _))))
    · rw [kreg hm2 rfl (kreg hm1 rfl H.r10)]
  rw [decide_eq_false h4] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  refine blk hp b33_in_code (by simp [b33]) run_b33 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = st.data.dmem := (hm2.dmem_eq hwf2 rfl).trans hd1
  have hq : q4 R.lw = 0 := by omega
  refine .done _ (.inr ⟨(pc_jump hpc2).trans (hp.label NativeRustcVmX64.Vm.WriteOpenings.label_30_at), K s2 F2 hd2 ?_,
    by rw [hq]; exact leaf_zero, by omega, (hm2.regs .r11 _ rfl).trans (by rw [hq]; rfl),
    kreg hm2 rfl (kreg hm1 rfl H.rax)⟩)
  refine Regs.append (hk1.left.keep hm2 (by kdecB)) (Regs.cons
    (kreg hm2 rfl (hk1.get (by simp))) (Regs.cons (kreg hm2 rfl (hk1.get (by simp)))
    (Regs.cons (kregV hm2 (x := .rsi) rfl (hk1.get (by simp))) (Regs.nil _))))

/-- **Four leaf words copied** (`b35`, then `b36`). -/
theorem chunkB_step (hp : Placed code R.k) (G : Geo R) {t : Nat} {st : MachineState}
    (H : ChunkB R j i t st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ ChunkB R j i (t + 4) st' ∨ LeafB R j i st' ∨ PreRemB R j i st') st := by
  have K := H.k
  have hlw := G.lw64
  have hq4d : q4 R.lw = R.lw / 4 * 4 := rfl
  have hnq := G.nq256
  have hi := K.ilt
  have hj := K.lt
  have hob := ob_le (j := j) (by omega)
  have hob' : 24 + 1544 * j + 1544 ≤ phaseBytes := hob
  have htq := H.tq
  have ht4 := H.t4
  have hin2 : Inside (R.lv + BitVec.ofNat 64 (512 * i + 8 * t)) 32 (R.big 4) :=
    G.l_in hi (by omega) (by omega)
  have hin3 : Inside (R.oa (ob j + 8 + 8 * t)) 32 (R.big 7) := G.o_in (by omega) (by omega)
  have hwf := G.wf2 K.F.fr.kept (i := 4) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin2 hin3 (ret := 0)
  have hm : Match (envOf R st.data [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 32),
      (R.oa (ob j + 8 + 8 * t), 32)] 0) (cS .r10 .r13 .r11) st.data :=
    match_fS K.F.fr (csz := [32, 32]) (cs := [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 32),
      (R.oa (ob j + 8 + 8 * t), 32)]) ⟨rfl, rfl, trivial⟩
      ⟨alN (o := 24) (by
        show reg st.data .r10 = R.lv + BitVec.ofNat 64 (512 * i + 8 * t) + BitVec.ofNat 64 24
        rw [H.r10]
        exact (addr_add rfl).symm), alN (o := 24) (by
        show (ix .r13 .r11 8).eval _ = R.oa (ob j + 8 + 8 * t) + BitVec.ofNat 64 24
        rw [ix_eval, K.rg.get (v := R.oa (ob j + 32)) (by simp), H.r11, ixs_ofNat, oa_add,
          oa_add]
        congr 1
        omega), trivial⟩
  refine blkW G hp b35_in_code (by simp [b35]) run_b35 K.F H.pc hwf hm nofun (o := 8)
    (by decide +kernel) (ro := 3) rfl (lo := 0) (a := R.oa (ob j + 8 + 8 * t)) (n := 32)
    (NativeRustcVm.addr_add_zero _) hin3 (by decide +kernel) fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hw : ∀ u, u < 4 → WordAt s1.data.dmem (R.oa (ob j + 8 + 8 * (t + u))) (R.lfw i (t + u)) := by
    intro u hu
    have hl := G.lfw_load K.F.chg (m := st.data) (rest := [(R.oa (ob j + 8 + 8 * t), 32)])
      (ret := 0) (n := 32) hi (t := t) (u := u) (by omega)
    rcases (by omega : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3) with rfl | rfl | rfl | rfl
    · exact word_at (stored_load hm1 (r := 3) (o := 0) (sz := 32) rfl (by omega) (r' := 2)
        (o' := 0) (by decide +kernel) hl) (by omega)
    · exact word_at (stored_load hm1 (r := 3) (o := 8) (sz := 32) rfl (by omega) (r' := 2)
        (o' := 8) (by decide +kernel) hl) (by omega)
    · exact word_at (stored_load hm1 (r := 3) (o := 16) (sz := 32) rfl (by omega) (r' := 2)
        (o' := 16) (by decide +kernel) hl) (by omega)
    · exact word_at (stored_load hm1 (r := 3) (o := 24) (sz := 32) rfl (by omega) (r' := 2)
        (o' := 24) (by decide +kernel) hl) (by omega)
  have hleaf : R.LeafPart s1.data.dmem j i (t + 4) :=
    leaf_succ (leaf_succ (leaf_succ (leaf_succ (G.leaf_keep hs1 (by omega) hj H.leaf
      (by omega)) (hw 0 (by omega))) (hw 1 (by omega))) (hw 2 (by omega))) (hw 3 (by omega))
  have K1 : KB R j i s1.data := K.write G F1 hs1 (by omega) (by omega)
    (fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := (wBf R).map Prod.fst) (by kdecB) (by kdecB))
    (K.rg.keep hm1 (by kdecB))
  have hr11 : reg s1.data .r11 = BitVec.ofNat 64 (t + 4) := by
    refine (hm1.regs .r11 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [H.r11, ofNat_add, Nat.add_comm]
  have hpc1' := pc_cond hpc1 (b := decide (q4 R.lw ≠ 4 + t)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, add_eval, envRegs]
    rw [K.rg.get (v := BitVec.ofNat 64 (q4 R.lw)) (by simp), H.r11, ofNat_add,
      beq_ofNat (by omega) (by omega), not_beq_decide])
  by_cases hl : q4 R.lw ≠ 4 + t
  · rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_28_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    refine .done _ (.inl ⟨hpc1', K1, hleaf, by omega, by omega, hr11, kreg hm1 rfl H.rax, ?_⟩)
    refine (hm1.regs .r10 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [H.r10]
    exact lit_add (by omega)
  rw [decide_eq_false hl] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hq : q4 R.lw = t + 4 := by omega
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b36_in_code (by simp [b36]) run_b36 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  have K2 : KB R j i s2.data := K1.next F2 hd2 (K1.rg.keep hm2 (by kdecB))
  have hpc2' := pc_cond hpc2 (b := decide (R.lw % 4 = 0)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, and_self_eval, envRegs]
    rw [K1.rg.get (v := BitVec.ofNat 64 (R.lw % 4)) (by simp), beq_ofNat (by omega) (by decide +kernel),
      beq_decide])
  by_cases h0 : R.lw % 4 = 0
  · rw [decide_eq_true h0, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_32_at] at hpc2'
    simp only [↓reduceIte] at hpc2'
    refine .done _ (.inr (.inl ⟨hpc2', K2, ?_⟩))
    rw [hd2, show R.lw = t + 4 by omega]
    exact hleaf
  rw [decide_eq_false h0] at hpc2'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2'
  refine .done _ (.inr (.inr ⟨hpc2'.trans (congrArg Host.addrOf rfl), K2, by
    rw [hd2, hq]; exact hleaf, by omega, by rw [kreg hm2 rfl hr11, hq], kreg hm2 rfl
    (kreg hm1 rfl H.rax)⟩))

/-- **Before the remaining words** (`b37`). -/
theorem remB_start (hp : Placed code R.k) (G : Geo R) {st : MachineState}
    (H : PreRemB R j i st) : Eventually (step1 Host.exe) (RemB R j i 0) st := by
  have K := H.k
  have hwf := G.wf0 K.F.fr.kept (ret := 0)
  refine blk hp b37_in_code (by simp [b37]) run_b37 K.F H.pc hwf (frMatch K.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  refine .done _ ⟨(pc_fall hpc1).trans (congrArg Host.addrOf rfl),
    K.next F1 hd1 (K.rg.keep hm1 (by kdecB)), by rw [hd1]; exact H.leaf, H.pos,
    hm1.regs .r11 _ rfl, ?_, ?_⟩
  · refine (hm1.regs .rax _ rfl).trans ?_
    show (ix .rax .r11 8).eval _ = _
    rw [ix_eval, H.rax, H.r11, ixs_ofNat]
    exact addr_add (by omega)
  · refine (hm1.regs .r10 _ rfl).trans ?_
    show (ix .r8 .r11 8).eval _ = _
    rw [ix_eval, K.rg.get (v := R.oa (ob j + 8)) (by simp), H.r11, ixs_ofNat, oa_add]

/-- **One remaining leaf word copied** (`b38`). -/
theorem remB_step (hp : Placed code R.k) (G : Geo R) {u : Nat} {st : MachineState}
    (H : RemB R j i u st) :
    Eventually (step1 Host.exe) (fun st' ↦ RemB R j i (u + 1) st' ∨ LeafB R j i st') st := by
  have K := H.k
  have hlw := G.lw64
  have hq4d : q4 R.lw = R.lw / 4 * 4 := rfl
  have hnq := G.nq256
  have hi := K.ilt
  have hj := K.lt
  have hob := ob_le (j := j) (by omega)
  have hob' : 24 + 1544 * j + 1544 ≤ phaseBytes := hob
  have hu := H.ult
  have hin2 : Inside (R.lv + BitVec.ofNat 64 (512 * i + 8 * (q4 R.lw + u))) 8 (R.big 4) :=
    G.l_in hi (by omega) (by omega)
  have hin3 : Inside (R.oa (ob j + 8 + 8 * (q4 R.lw + u))) 8 (R.big 7) :=
    G.o_in (by omega) (by omega)
  have hwf := G.wf2 K.F.fr.kept (i := 4) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin2 hin3 (ret := 0)
  have hm : Match (envOf R st.data [(R.lv + BitVec.ofNat 64 (512 * i + 8 * (q4 R.lw + u)), 8),
      (R.oa (ob j + 8 + 8 * (q4 R.lw + u)), 8)] 0) (rS .rax .r10 .r11) st.data :=
    match_fS K.F.fr (csz := [8, 8]) (cs := [(R.lv + BitVec.ofNat 64 (512 * i + 8 * (q4 R.lw + u)), 8),
      (R.oa (ob j + 8 + 8 * (q4 R.lw + u)), 8)]) ⟨rfl, rfl, trivial⟩
      ⟨al0 (by
        show (ix .rax .r11 8).eval _ = R.lv + BitVec.ofNat 64 (512 * i + 8 * (q4 R.lw + u))
        rw [ix_eval, H.rax, H.r11, ixs_ofNat]
        exact addr_add (by omega)), al0 (by
        show (ix .r10 .r11 8).eval _ = R.oa (ob j + 8 + 8 * (q4 R.lw + u))
        rw [ix_eval, H.r10, H.r11, ixs_ofNat, oa_add]
        congr 1
        omega), trivial⟩
  refine blkW G hp b38_in_code (by simp [b38]) run_b38 K.F H.pc hwf hm nofun (o := 8)
    (by decide +kernel) (ro := 3) rfl (lo := 0) (a := R.oa (ob j + 8 + 8 * (q4 R.lw + u))) (n := 8)
    (NativeRustcVm.addr_add_zero _) hin3 (by decide +kernel) fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hw : WordAt s1.data.dmem (R.oa (ob j + 8 + 8 * (q4 R.lw + u))) (R.lfw i (q4 R.lw + u)) :=
    word_at (stored_load hm1 (r := 3) (o := 0) (sz := 8) rfl (by omega) (r' := 2) (o' := 0)
      (by decide +kernel) (G.lfw_load K.F.chg (m := st.data)
        (rest := [(R.oa (ob j + 8 + 8 * (q4 R.lw + u)), 8)]) (ret := 0) (n := 8) hi
        (t := q4 R.lw + u) (u := 0) (by omega))) (by omega)
  have hleaf : R.LeafPart s1.data.dmem j i (q4 R.lw + u + 1) :=
    leaf_succ (G.leaf_keep hs1 (by omega) hj H.leaf (by omega)) hw
  have K1 : KB R j i s1.data := K.write G F1 hs1 (by omega) (by omega)
    (fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := (wBf R).map Prod.fst) (by kdecB) (by kdecB))
    (K.rg.keep hm1 (by kdecB))
  have hpc1' := pc_cond hpc1 (b := decide (R.lw % 4 ≠ u + 1)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, add_eval, envRegs]
    rw [K.rg.get (v := BitVec.ofNat 64 (R.lw % 4)) (by simp), H.r11, ofNat_add,
      beq_ofNat (by omega) (by omega), not_beq_decide])
  by_cases hl : R.lw % 4 ≠ u + 1
  · rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_31_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    refine .done _ (.inl ⟨hpc1', K1, hleaf, by omega, ?_, kreg hm1 rfl H.rax,
      kreg hm1 rfl H.r10⟩)
    refine (hm1.regs .r11 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [H.r11, ofNat_add]
  rw [decide_eq_false hl] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  refine .done _ (.inr ⟨hpc1'.trans (congrArg Host.addrOf rfl), K1, ?_⟩)
  rw [show R.lw = q4 R.lw + u + 1 by omega]
  exact hleaf

/-- **The leaf copied** (`b39`, `b40`): the next query's head, or the epilogue. -/
theorem leafB_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : LeafB R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ HeadB R (j + 1) st' ∨ AtEnd R st') st := by
  have K := H.k
  have hj := K.lt
  have hnq := G.nq256
  have hwf := G.wf0 K.F.fr.kept (ret := 0)
  refine blk hp b39_in_code (by simp [b39]) run_b39 K.F H.pc hwf (frMatch K.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hdone : R.Done s1.data.dmem (j + 1) := by
    rw [hd1]
    exact ⟨K.mem.1.1, fun j' hj' ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | rfl
      · exact K.mem.1.2 j' h
      · exact ⟨i, K.pos, K.mem.2, H.leaf, by rw [K.h0]; exact path_zero⟩⟩
  have hax : boolRet s1.data = 1 := by
    unfold boolRet
    rw [show reg s1.data .rax = _ from hm1.regs .rax _ rfl]
    exact merge_one_mod _
  have hpc1' := pc_cond hpc1 (b := decide (j + 1 ≠ R.nq)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, envRegs]
    rw [K.rg.get (v := R.qa + BitVec.ofNat 64 (8 * (j + 1))) (by simp),
      K.rg.get (v := R.qe) (by simp), beq_add (by omega) (by omega), not_beq_decide]
    by_cases h : j + 1 = R.nq
    · rw [decide_eq_false (by omega), decide_eq_false (by omega)]
    · rw [decide_eq_true (by omega), decide_eq_true h])
  by_cases hl : j + 1 ≠ R.nq
  · rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_22_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    refine .done _ (.inl ⟨hpc1', F1, by omega, K.h0, hdone, K.w.keep (FwK.of_eq hd1 _), ?_⟩)
    refine Regs.cons (kreg hm1 rfl (K.rg.get (by simp)))
      (Regs.cons (kreg hm1 rfl (K.rg.get (by simp))) (Regs.cons (kreg hm1 rfl (K.rg.get (by simp)))
      (Regs.cons (kreg hm1 rfl (K.rg.get (by simp))) (Regs.cons ?_ (Regs.cons ?_
      (Regs.cons (kreg hm1 rfl (K.rg.get (by simp)))
      (Regs.cons (kreg hm1 rfl (K.rg.get (by simp))) (Regs.cons (kreg hm1 rfl (K.rg.get (by simp)))
      (Regs.cons ((hm1.regs .r10 _ rfl).trans (fw_load (K.w.get (by simp))))
      (Regs.cons ((hm1.regs .rbx _ rfl).trans (fw_load (K.w.get (by simp))))
      (Regs.cons (kreg hm1 rfl (K.rg.get (by simp))) (Regs.nil _))))))))))))
    · refine (hm1.regs .r13 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [K.rg.get (v := R.oa (ob j + 32)) (by simp)]
      exact lit_add (x := ob j + 32) (z := ob (j + 1) + 32) (by simp only [ob]; omega)
    · refine (hm1.regs .r8 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [K.rg.get (v := R.oa (ob j + 8)) (by simp)]
      exact lit_add (x := ob j + 8) (z := ob (j + 1) + 8) (by simp only [ob]; omega)
  rw [decide_eq_false hl] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b40_in_code (by simp [b40]) run_b40 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  refine .done _ (.inr ⟨(pc_jump hpc2).trans (hp.label NativeRustcVmX64.Vm.WriteOpenings.label_46_at), F2, .inl ⟨?_, ?_⟩⟩)
  · unfold boolRet; rw [kreg hm2 (r := .rax) rfl rfl]; exact hax
  · rw [hd2, show R.nq = j + 1 by omega]; exact hdone

/-- **Path B**, from its head at query `j`. -/
theorem B_loop (hp : Placed code R.k) (G : Geo R) (hlw0 : 0 < R.lw) {st : MachineState}
    (H : HeadB R j st) : Eventually (step1 Host.exe) (Post R) st := by
  refine Sym.loop (fun n st ↦ ∃ j, n = R.nq - j ∧ HeadB R j st) (fun n st ⟨j, hn, H⟩ ↦ ?_)
    ⟨j, rfl, H⟩
  have hj := H.lt
  refine (headB_step hp G H).bind fun s1 H1 ↦ (scanB_loop hp G H1).bind fun s2 h2 ↦ ?_
  rcases h2 with h2 | ⟨i, H2⟩
  · exact .done _ (.inl h2)
  have leaf_done : ∀ s, LeafB R j i s → Eventually (step1 Host.exe)
      (fun st' ↦ Post R st' ∨ ∃ n' < n, ∃ j, n' = R.nq - j ∧ HeadB R j st') s := fun s H5 ↦
    (leafB_step hp G H5).bind fun s6 h6 ↦ by
      rcases h6 with H6 | h6
      · exact .done _ (.inr ⟨R.nq - (j + 1), by omega, j + 1, rfl, H6⟩)
      · exact (end_spec hp G h6).mono fun _ h ↦ .inl h
  have rem : ∀ u s, RemB R j i u s → Eventually (step1 Host.exe)
      (fun st' ↦ Post R st' ∨ ∃ n' < n, ∃ j, n' = R.nq - j ∧ HeadB R j st') s := by
    intro u s H4
    refine Sym.loop (fun m s ↦ ∃ u, m = R.lw % 4 - u ∧ RemB R j i u s)
      (fun m s ⟨u, hm, H4⟩ ↦ (remB_step hp G H4).bind fun s' h' ↦ ?_) ⟨u, rfl, H4⟩
    rcases h' with H' | H'
    · exact .done _ (.inr ⟨R.lw % 4 - (u + 1), by have := H4.ult; omega, u + 1, rfl, H'⟩)
    · exact (leaf_done _ H').mono fun _ h ↦ .inl h
  have pre : ∀ s, PreRemB R j i s → Eventually (step1 Host.exe)
      (fun st' ↦ Post R st' ∨ ∃ n' < n, ∃ j, n' = R.nq - j ∧ HeadB R j st') s :=
    fun s H3 ↦ (remB_start hp G H3).bind fun s' H' ↦ rem 0 s' H'
  refine (foundB_step hp G hlw0 H2).bind fun s3 h3 ↦ ?_
  rcases h3 with H3 | H3
  · refine Sym.loop (fun m s ↦ ∃ t, m = q4 R.lw - t ∧ ChunkB R j i t s)
      (fun m s ⟨t, hm, H4⟩ ↦ (chunkB_step hp G H4).bind fun s' h' ↦ ?_) ⟨0, rfl, H3⟩
    rcases h' with H' | H' | H'
    · exact .done _ (.inr ⟨q4 R.lw - (t + 4), by have := H4.tq; omega, t + 4, rfl, H'⟩)
    · exact (leaf_done _ H').mono fun _ h ↦ .inl h
    · exact (pre _ H').mono fun _ h ↦ .inl h
  · exact pre _ H3

/-- **Without levels** (`b25`, then `b26` or `b41`): path B or path C. -/
theorem noLev (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : Ent R 157 st)
    (h0 : R.h = 0) : Eventually (step1 Host.exe) (Post R) st := by
  have hlw := G.lw64
  have hnq := G.nq256
  have hnp := G.np256
  have hwf := G.wf0 H.F.fr.kept (ret := 0)
  refine blk hp b25_in_code (by simp [b25]) run_b25 H.F H.pc hwf (frMatch H.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hpc1' := pc_cond hpc1 (b := decide (R.lw = 0)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, and_self_eval, envRegs]
    rw [H.r9, beq_ofNat (by omega) (by decide +kernel), beq_decide])
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  by_cases hl0 : R.lw = 0
  · rw [decide_eq_true hl0, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_35_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    refine blk hp b41_in_code (by simp [b41]) run_b41 F1 hpc1' hwf2 (frMatch F1.fr) nofun (o := 8)
      (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
    have hd2 : s2.data.dmem = st.data.dmem := (hm2.dmem_eq hwf2 rfl).trans hd1
    refine C_loop hp G ⟨(pc_fall hpc2).trans (congrArg Host.addrOf rfl), F2, G.nq0, h0, hl0,
      ⟨hd2 ▸ H.head, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩, ?_⟩
    refine Regs.cons ((kreg hm2 rfl (kreg hm1 rfl H.rdi)).trans
      (by rw [Nat.mul_zero, NativeRustcVm.addr_add_zero]))
      (Regs.cons (hm2.regs .r9 _ rfl) (Regs.cons (kreg hm2 rfl (kreg hm1 rfl H.rbp))
      (Regs.cons (kreg hm2 rfl (kreg hm1 rfl H.rcx)) (Regs.cons (kreg hm2 rfl (kreg hm1 rfl H.rdx))
      (Regs.cons (kreg hm2 rfl (kreg hm1 rfl H.r14)) (Regs.nil _))))))
  rw [decide_eq_false hl0] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  refine blk hp b26_in_code (by simp [b26]) run_b26 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 hs2 ↦ ?_
  have hW : ∀ p, InRange R.out phaseBytes p → ¬InRange R.fb 160 p := G.frame_out
  have hr9 : reg s1.data .r9 = BitVec.ofNat 64 R.lw := kreg hm1 rfl H.r9
  have hr8 : reg s1.data .r8 = R.lv := kreg hm1 rfl H.r8
  have hrbp : reg s1.data .rbp = R.out := kreg hm1 rfl H.rbp
  refine B_loop hp G (by omega) ⟨(pc_fall hpc2).trans (congrArg Host.addrOf rfl), F2, G.nq0, h0,
    ⟨(G.done_keepW (j := 0) hs2 hW (by omega) ⟨hd1 ▸ H.head, fun _ h ↦ absurd h
      (Nat.not_lt_zero _)⟩).1, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩, ?_, ?_⟩
  · refine FWs.cons (fw_eq (fw_write hm2 (o := 16) (by omega)
      (v := .bin .add .W64 (.reg .r8) (.lit 24)) (by decide +kernel))
      (by simp only [Sym.eval, add_eval, envRegs]; rw [hr8]))
      (FWs.cons (fw_eq (fw_write hm2 (o := 24) (by omega) (v := .reg .r8) (by decide +kernel))
        (by rw [show (Sym.reg .r8).eval _ = reg s1.data .r8 from rfl, hr8]))
      (FWs.cons (fw_eq (fw_write hm2 (o := 32) (by omega) (v := .reg .r9) (by decide +kernel))
        (by rw [show (Sym.reg .r9).eval _ = reg s1.data .r9 from rfl, hr9])) (FWs.nil _)))
  · refine Regs.cons (kreg hm2 rfl hrbp) (Regs.cons (kreg hm2 rfl (kreg hm1 rfl H.rcx))
      (Regs.cons (kreg hm2 rfl (kreg hm1 rfl H.rdx)) (Regs.cons ?_ (Regs.cons ?_ (Regs.cons ?_
      (Regs.cons ?_ (Regs.cons ((kreg hm2 rfl (kreg hm1 rfl H.rdi)).trans
        (by rw [Nat.mul_zero, NativeRustcVm.addr_add_zero])) (Regs.cons (hm2.regs .r9 _ rfl)
      (Regs.cons ((hm2.regs .r10 _ rfl).trans hr8) (Regs.cons ?_
      (Regs.cons (kreg hm2 rfl (kreg hm1 rfl H.r14)) (Regs.nil _))))))))))))
    · refine (hm2.regs .r12 _ rfl).trans ?_
      simp only [Sym.eval, envRegs]
      rw [hr9, and124' (by omega)]
    · refine (hm2.regs .r13 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [hrbp]
    · refine (hm2.regs .r8 _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [hrbp]
    · refine (hm2.regs .r15 _ rfl).trans ?_
      simp only [Sym.eval, envRegs]
      rw [hr9, and3 (by omega)]
    · refine (hm2.regs .rbx _ rfl).trans ?_
      simp only [Sym.eval, add_eval, envRegs]
      rw [hr8]

end

end NativeRustcVmX64.Wire.WriteOpenings
