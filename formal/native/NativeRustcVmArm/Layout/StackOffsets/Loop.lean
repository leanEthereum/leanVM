module

public import NativeRustcVmArm.Layout.StackOffsets.Init

/-!
# `stack_offsets`: the main loop (`b16`-`b20`)

At its head `.LStackOffsets_15` (`b17`, `Loop m0 j`) the first `j` blocks of the order are placed
(`OutAt`, `P m0 j`), X8 their total, X9 at `order[j]`, X23 `8 (n - j)`. A turn (`step`): `b18`
loads `i = order[j]` (below `n`, so below `offsets`' length), `b19` stores the total at
`offsets[i]`, `b20` loads `sizes[i]` and fails past `63` (`Fail`), `b16` adds `2^size`, failing
on a carry. With X23 zero `b17` leaves for `.LStackOffsets_20` (`End`, `loop`).
-/

namespace NativeRustcVmArm.Layout.StackOffsets

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.StackOffsets
open NativeVm.Model NativeRustcVm.Layout
open NativeRustcVmArm.Arrays (regs_eq_of keepsAll)
open NativeRustcVm (WordAt WordsAt wordOf)

public section

/-- **The main loop's head**: `j` blocks placed. -/
structure Loop (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  regs : Regs m0 st
  le : j ≤ n m0
  x23 : st.regs.X23.toNat = 8 * (n m0 - j)
  x9 : st.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * j)
  x8 : st.regs.X8.toNat = (P m0 j).2
  x10 : st.regs.X10.toNat = 1
  ordw : WordsAt st.dmem (fb m0) (natWords (ord m0))
  out : OutAt m0 j st.dmem

/-- The registers `Loop` reads. -/
def loopRegs : List XReg := [.X8, .X9, .X10, .X19, .X20, .X21, .X22, .X23, .X24]

theorem regsList_loop : ∀ r ∈ regsList, r ∈ loopRegs := by
  intro r hr
  simp only [regsList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [loopRegs]

theorem Loop.of {m0 st st' : MachineData} {j : Nat} (h : Loop m0 j st) (fr : Fr m0 st')
    (he : ∀ r ∈ loopRegs, st'.regs.getXReg r = st.regs.getXReg r) (hd : st'.dmem = st.dmem) :
    Loop m0 j st' where
  fr := fr
  regs := h.regs.of fun r hr ↦ he r (regsList_loop r hr)
  le := h.le
  x23 := by rw [show st'.regs.X23 = st.regs.X23 from he .X23 (by simp [loopRegs])]; exact h.x23
  x9 := by rw [show st'.regs.X9 = st.regs.X9 from he .X9 (by simp [loopRegs])]; exact h.x9
  x8 := by rw [show st'.regs.X8 = st.regs.X8 from he .X8 (by simp [loopRegs])]; exact h.x8
  x10 := by rw [show st'.regs.X10 = st.regs.X10 from he .X10 (by simp [loopRegs])]; exact h.x10
  ordw := hd ▸ h.ordw
  out := hd ▸ h.out

/-- Word `j` of the order array. -/
theorem ord_word {m0 : MachineData} {d : Mem 64} (h : WordsAt d (fb m0) (natWords (ord m0)))
    {j : Nat} (hj : j < (ord m0).size) :
    WordAt d (fb m0 + BitVec.ofNat 64 (8 * j)) (ord m0)[j].toUInt64 := by
  have := NativeRustcVm.WordsAt.getElem h (i := j) (by simp [natWords]; exact hj)
  simpa [natWords] using this

/-- A byte of `b`'s range is not in a sub-range of a range apart from it. -/
theorem not_in_sub {a b : BitVec 64} {n n' o j c : Nat} (h : Apart a n b n') (ha : NoWrap a n)
    (hb : NoWrap b n') (hoj : o + j ≤ n) (hc : c < n') :
    ¬InRange (a + BitVec.ofNat 64 o) j (b + BitVec.ofNat 64 c) := by
  by_cases hj : j = 0
  · subst hj; unfold InRange; omega
  unfold NoWrap at ha hb
  unfold Apart at h
  have e1 : (a + BitVec.ofNat 64 o).toNat = a.toNat + o := Arrays.toNat_add_ofNat' (by omega)
  have e2 : (b + BitVec.ofNat 64 c).toNat = b.toNat + c := Arrays.toNat_add_ofNat' (by omega)
  rw [NativeRustcArm.Sym.inRange_iff (by rw [e1]; omega), e1, e2]
  omega

/-- A load of an `X` register's word: its value. -/
theorem load_val {st : MachineData} {a : BitVec 64} {sz : Nat} :
    (Env.ofMachine st [(a, sz)]).load 0 0 8 = (wordOf st.dmem a).toBitVec :=
  InsertionSort.load0

theorem ult_apply {x y : BitVec 64} {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b) :
    CmpOp.apply .ult .W64 x y = decide (a < b) := by
  simp only [CmpOp.apply, Sym.low_W64]
  exact ult_dec hx hy

theorem eq_apply {x y : BitVec 64} {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b) :
    CmpOp.apply .eq .W64 x y = decide (a = b) := by
  simp only [CmpOp.apply, Sym.low_W64]
  exact beq_dec hx hy

theorem addC_dec (a b : BitVec 64) :
    CmpOp.apply .addC .W64 a b = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by
  simp only [CmpOp.apply, Sym.low_W64, BitVec.unsigned]
  have ha := a.isLt
  have hb := b.isLt
  have h2 : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add a b
  rw [h2, Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq]
  constructor
  · intro h; omega
  · intro h; omega

theorem lslv_pow {x y : BitVec 64} (hx : x.toNat = 1) (hy : y.toNat < 64) :
    (BinOp.apply .lslv .W64 x y).toNat = 2 ^ y.toNat := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
  rw [show y.toNat % RegWidth.W64.bits = y.toNat from Nat.mod_eq_of_lt hy]
  rw [BitVec.toNat_shiftLeft, hx, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hy)

theorem add_apply {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (BinOp.apply .add .W64 x y).toNat = x.toNat + y.toNat := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem sub_apply {x : BitVec 64} {c : Nat} (h : c ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 c)).toNat = x.toNat - c := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
  exact sub_lit rfl h

/-- **A block writing nothing** keeps the frame and memory. -/
theorem Fr.of_noWrite [Labels] {m0 st st' : MachineData} (hS : StackOk m0 1328)
    {rs : List (BitVec 64 × Nat)} {S₀ S₁ : SState} (hb : Fr m0 st)
    (hm₀ : Match (Env.ofMachine st rs) S₀ st) (hm : Match (Env.ofMachine st rs) S₁ st')
    (hwf : (Env.ofMachine st rs).WF) (hk : keepsAll S₀ S₁ keptRegs = true) :
    Fr m0 st' ∧ st'.dmem = st.dmem := by
  have hmem := mem_nil_of_keepsAll hk
  have hd : st'.dmem = st.dmem := hm.dmem_eq hwf hmem
  exact ⟨Frame.of_block hb hS (Nat.le_refl _) hm₀ hm hwf (by rw [with_mem_nil hmem]; exact hk)
    (fun p _ ↦ by rw [hd]) (fun q _ i _ ↦ by rw [hd]), hd⟩

/-- At an epilogue: the frame (region 0), SP its base. -/
theorem Fr.exit_match [Labels] {m0 st : MachineData} (hS : StackOk m0 1328) (hb : Fr m0 st) :
    (Env.ofMachine st [(fb m0, 1328)]).WF ∧ Match (Env.ofMachine st [(fb m0, 1328)]) exitS st := by
  obtain ⟨hmap, hnw, -⟩ := Arrays.frame_ok hS (Nat.le_refl 1328)
  refine ⟨Arrays.wf_one (fun i hi ↦ hb.kept _ (hmap i hi)) hnw,
    match_ofMachine ⟨rfl, fun _ ↦ Arrays.frame_aligned hS (Nat.le_refl _) rfl, trivial⟩ ?_
      trivial trivial trivial trivial⟩
  rw [hb.sp]; simp [Sym.eval]

variable [Host] {k : Nat}

/-- **A failure**: at `b21`, the blocks not fitting. -/
abbrev Fail (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b21Offset) ∧ Fr m0 s.data ∧ ¬OffsetsFit (sizes m0)

/-- **The loop's end**: at `b22`, every block placed. -/
abbrev End (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b22Offset) ∧ Loop m0 (n m0) s.data

/-- `b16`: `2^size` added, or a carry. -/
theorem l16 (hp : Placed code k) {m0 : MachineData} (hpre : StackOffsetsPre m0) {j : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b16Offset)) (hfr : Fr m0 st.data)
    (hR : Regs m0 st.data) (hj : j < (ord m0).size)
    (h23 : st.data.regs.X23.toNat = 8 * (n m0 - j))
    (h9 : st.data.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * (j + 1)))
    (h8 : st.data.regs.X8.toNat = (P m0 j).2) (h10 : st.data.regs.X10.toNat = 1)
    (h11 : st.data.regs.X11.toNat = size m0 (ord m0)[j]) (h63 : size m0 (ord m0)[j] ≤ 63)
    (hordw : WordsAt st.data.dmem (fb m0) (natWords (ord m0)))
    (hout : OutAt m0 (j + 1) st.data.dmem) :
    Eventually (step1 Host.exe) (fun s ↦ Fail k m0 s ∨
      (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b17Offset) ∧ Loop m0 (j + 1) s.data)) st :=
  run_regs hpre.1 (infix_of b16_in_code (by simp [b16]) hp) run_b16
    (after_eq run_b16 ▸ b16_keeps) hpc hfr fun st' hm hpc' hfr' hd ↦ by
      have hn := ord_size m0
      have e10 : (st.data.regs.getXReg .X10).toBitVec.toNat = 1 := h10
      have e11 : (st.data.regs.getXReg .X11).toBitVec.toNat = size m0 (ord m0)[j] := h11
      have hl : (BinOp.apply .lslv .W64 (st.data.regs.getXReg .X10).toBitVec
          (st.data.regs.getXReg .X11).toBitVec).toNat = 2 ^ size m0 (ord m0)[j] := by
        rw [lslv_pow e10 (by rw [e11]; omega), e11]
      simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b16_length, NativeRustcVmArm.Vm.StackOffsets.b16Length] at hpc'
      obtain ⟨hy, hno⟩ := pc_of (P := 2 ^ 64 ≤ 2 ^ size m0 (ord m0)[j] + (P m0 j).2) hpc' (by
        simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
        rw [addC_dec, hl, show (st.data.regs.getXReg .X8).toBitVec.toNat = _ from h8])
      by_cases hc : 2 ^ 64 ≤ 2 ^ size m0 (ord m0)[j] + (P m0 j).2
      · exact .done _ (Or.inl ⟨(hy hc).trans (lbl_19 hp), hfr',
          not_fit_sum hj (by omega)⟩)
      · have he := regs_eq_of (match_nil _) hm (.X9 :: .X10 :: regsList) rfl
        refine .done _ (Or.inr ⟨hno hc, hfr', hR.of fun r hr ↦ he r (by simp [hr]), by omega,
          ?_, ?_, ?_, ?_, hd ▸ hordw, hd ▸ hout⟩)
        · have e23 : (st.data.regs.getXReg .X23).toBitVec.toNat = 8 * (n m0 - j) := h23
          show (st'.data.regs.getXReg .X23).toBitVec.toNat = _
          rw [hm.regs .X23 _ rfl]
          simp only [Sym.eval, Env.ofMachine_regs]
          rw [sub_apply (by rw [e23]; omega), e23]
          omega
        · rw [show st'.data.regs.X9 = st.data.regs.X9 from he .X9 (by simp)]; exact h9
        · have e8 : (st.data.regs.getXReg .X8).toBitVec.toNat = (P m0 j).2 := h8
          show (st'.data.regs.getXReg .X8).toBitVec.toNat = _
          rw [hm.regs .X8 _ rfl]
          simp only [Sym.eval, Env.ofMachine_regs]
          rw [add_apply (by rw [hl, e8]; omega), hl, e8, P_succ_snd hj]
          omega
        · rw [show st'.data.regs.X10 = st.data.regs.X10 from he .X10 (by simp)]; exact h10

/-- **A turn of the main loop** (`b18`, `b19`, `b20`, `b16`): block `order[j]` placed. -/
theorem step (hp : Placed code k) {m0 : MachineData} (hpre : StackOffsetsPre m0)
    (hcap : n m0 ≤ cap m0) {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b18Offset))
    (hL : Loop m0 j st.data) (hj : j < n m0) :
    Eventually (step1 Host.exe) (fun s ↦ Fail k m0 s ∨
      (s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b17Offset) ∧ Loop m0 (j + 1) s.data)) st := by
  have hS : StackOk m0 1328 := hpre.1
  have hn : n m0 ≤ 158 := hpre.2.1
  have hrs := hpre.2.2.1
  have hsoff : OffStack m0 m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat) 1328 := hpre.2.2.2.1
  have hro := hpre.2.2.2.2.1
  have hooff : Apart (out m0) (8 * cap m0) (fb m0) 1328 := hpre.2.2.2.2.2.1
  have hap := hpre.2.2.2.2.2.2
  have hjo : j < (ord m0).size := by rw [ord_size]; exact hj
  have hi : (ord m0)[j] < n m0 := ord_lt hjo
  have hfbn := fb_noWrap hS
  have hcapd : cap m0 = m0.regs.X3.toNat := rfl
  have hnd : n m0 = m0.regs.X1.toNat := rfl
  -- `b18`: `i = order[j]`
  have hrd : Readable st.data (fb m0 + BitVec.ofNat 64 (8 * j)) 8 :=
    frame_readable hS (Nat.le_refl _) hL.fr (by omega)
  have hwf := Arrays.wf_one hrd.1 hrd.2 (m := st.data)
  have hm : Match (Env.ofMachine st.data [(fb m0 + BitVec.ofNat 64 (8 * j), 8)]) wordS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨by
      show _ = fb m0 + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 0
      rw [ofInt_zero, BitVec.add_zero]; exact hL.x9, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b18_in_code (by simp [b18]) hp) run_b18 hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hfr1, hd1⟩ := Fr.of_noWrite hS hL.fr hm hm1 hwf (after_eq run_b18 ▸ b18_keeps)
  have he1 := regs_eq_of hm hm1 (.X8 :: .X10 :: .X23 :: regsList) rfl
  have hR1 : Regs m0 s1.data := hL.regs.of fun r hr ↦ he1 r (by simp [hr])
  have hw0 : wordOf st.data.dmem (fb m0 + BitVec.ofNat 64 (8 * j)) = (ord m0)[j].toUInt64 :=
    NativeRustcVm.wordOf_of_wordAt (ord_word hL.ordw hjo)
  have hi64 : (ord m0)[j] < 2 ^ 64 := by omega
  have h11 : (s1.data.regs.getXReg .X11).toBitVec.toNat = (ord m0)[j] := by
    rw [hm1.regs .X11 _ rfl]
    simp only [Sym.eval, load_val, hw0]
    exact InsertionSort.toNat_toUInt64 hi64
  have h19 : (st.data.regs.getXReg .X19).toBitVec.toNat = cap m0 :=
    congrArg UInt64.toNat hL.regs.x19
  simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b18_length, NativeRustcVmArm.Vm.StackOffsets.b18Length] at hpc1
  obtain ⟨-, hno1⟩ := pc_of (P := ¬(ord m0)[j] < cap m0) hpc1 (by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, load_val, hw0]
    rw [ult_apply (InsertionSort.toNat_toUInt64 hi64) h19, decide_not])
  have hpc1' := hno1 (by omega)
  -- `b19`: `offsets[i] = acc`
  have hb1 : (s1.data.regs.getXReg .X20).toBitVec = out m0 :=
    congrArg UInt64.toBitVec hR1.x20
  have hrd2 : Readable s1.data (out m0 + BitVec.ofNat 64 (8 * (ord m0)[j])) 8 :=
    readable_sub hro hfr1.kept (by omega)
  obtain ⟨hwf2, hm2⟩ := InsertionSort.ld_match (p := .X20) (r := .X11) (st := s1.data) hb1 h11 hrd2
  have hm2' : Match (Env.ofMachine s1.data [(out m0 + BitVec.ofNat 64 (8 * (ord m0)[j]), 8)])
      (ixS .X20 .X11) s1.data := hm2
  refine exec_at (infix_of b19_in_code (by simp [b19]) hp) run_b19 hwf2 (hpc1'.trans rfl) hm2'
    fun s2 hm3 hpc2 ↦ ?_
  obtain ⟨hk2, hw2, hv2⟩ := after_eq run_b19 ▸ b19_facts
  have hono := hro.2
  have hfr2 : Fr m0 s2.data := Frame.of_region hfr1 hm2' hm3 hwf2 hk2 hw2
    (fun p h ↦ Or.inl (NativeRustcVm.InRange.of_sub h hono (by omega)))
    fun q hq t ht ↦ by
      obtain ⟨h1, h2⟩ := slots_bounds q hq
      rw [NativeRustcVm.addr_add]
      exact not_in_sub hooff hono hfbn (by omega) (by omega)
  have hsame2 := same_of_region hm3 hwf2 (r := 0) rfl hw2
  have hwv := Match.wordAt_write hm3 (r := 0) (o := 0) rfl (by decide) hv2
  rw [NativeRustcVm.addr_add_zero] at hwv
  have hx8 : UInt64.ofBitVec ((Sym.reg .X8).eval (Env.ofMachine s1.data
      [(out m0 + BitVec.ofNat 64 (8 * (ord m0)[j]), 8)])) = (P m0 j).2.toUInt64 := by
    refine u64_eq ?_
    show (s1.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [he1 .X8 (by simp)]
    exact hL.x8
  rw [hx8] at hwv
  have hout2 : OutAt m0 (j + 1) s2.data.dmem :=
    (hd1 ▸ hL.out).step hjo hono hcap hwv hsame2
  have hordw2 : WordsAt s2.data.dmem (fb m0) (natWords (ord m0)) :=
    Arrays.bytesAt_congr (hd1 ▸ hL.ordw) fun t ht ↦ hsame2 _ (not_in_sub hooff hono hfbn
      (by omega) (by
        have : t < 8 * (natWords (ord m0)).length := by
          rwa [NativeRustcVm.length_wordsBytes] at ht
        simp only [natWords, List.length_map, Array.length_toList, ord_size] at this
        omega))
  have he2 := regs_eq_of hm2' hm3 (.X8 :: .X9 :: .X10 :: .X11 :: .X23 :: regsList) rfl
  have hR2 : Regs m0 s2.data := hR1.of fun r hr ↦ he2 r (by simp [hr])
  have h21 : (s1.data.regs.getXReg .X21).toBitVec.toNat = n m0 := congrArg UInt64.toNat hR1.x21
  simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b19_length, NativeRustcVmArm.Vm.StackOffsets.b19Length] at hpc2
  obtain ⟨-, hno2⟩ := pc_of (P := ¬(ord m0)[j] < n m0) hpc2 (by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [ult_apply h11 h21, decide_not])
  have hpc2' := hno2 (by omega)
  -- `b20`: `sizes[i]`
  have h11' : (s2.data.regs.getXReg .X11).toBitVec.toNat = (ord m0)[j] := by
    rw [he2 .X11 (by simp)]; exact h11
  have hb2 : (s2.data.regs.getXReg .X22).toBitVec = m0.regs.X0.toBitVec :=
    congrArg UInt64.toBitVec hR2.x22
  have hrd3 : Readable s2.data (m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 * (ord m0)[j])) 8 :=
    readable_sub hrs hfr2.kept (by omega)
  obtain ⟨hwf3, hm4⟩ := InsertionSort.ld_match (p := .X22) (r := .X11) (st := s2.data) hb2 h11' hrd3
  have hm4' : Match (Env.ofMachine s2.data [(m0.regs.X0.toBitVec +
      BitVec.ofNat 64 (8 * (ord m0)[j]), 8)]) (ixS .X22 .X11) s2.data := hm4
  have hsz : (wordOf s2.data.dmem (m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 * (ord m0)[j]))).toNat
      = size m0 (ord m0)[j] := by
    rw [show size m0 (ord m0)[j] = _ from natsOf_getD m0 m0.regs.X0 hi]
    refine congrArg UInt64.toNat (NativeRustcVm.wordOf_congr fun t ht ↦ ?_)
    rw [NativeRustcVm.addr_add]
    exact Arrays.same_of_apart hfr2.same hS hrs.2 hsoff hap hono _ (by omega)
  refine exec_at (infix_of b20_in_code (by simp [b20]) hp) run_b20 hwf3 (hpc2'.trans rfl) hm4'
    fun s3 hm5 hpc3 ↦ ?_
  obtain ⟨hfr3, hd3⟩ := Fr.of_noWrite hS hfr2 hm4' hm5 hwf3 (after_eq run_b20 ▸ b20_keeps)
  have he3 := regs_eq_of hm4' hm5 (.X8 :: .X9 :: .X10 :: .X23 :: regsList) rfl
  have h11'' : s3.data.regs.X11.toNat = size m0 (ord m0)[j] := by
    show (s3.data.regs.getXReg .X11).toBitVec.toNat = _
    rw [hm5.regs .X11 _ rfl]
    simp only [Sym.eval, load_val]
    exact hsz
  simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b20_length, NativeRustcVmArm.Vm.StackOffsets.b20Length] at hpc3
  obtain ⟨hy3, hno3⟩ := pc_of (P := size m0 (ord m0)[j] ≤ 63) hpc3 (by
    simp only [SBool.eval, Sym.eval, load_val]
    rw [ult_apply hsz (lit_toNat (by decide)), eq_apply hsz (lit_toNat (by decide)),
      Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega)
  by_cases h63 : size m0 (ord m0)[j] ≤ 63
  · refine l16 hp hpre ((hy3 h63).trans (lbl_14 hp)) hfr3
      (hR2.of fun r hr ↦ he3 r (by simp [hr])) hjo ?_ ?_ ?_ ?_ h11'' h63
      (hd3 ▸ hordw2) (hd3 ▸ hout2)
    · rw [show s3.data.regs.X23 = st.data.regs.X23 from (he3 .X23 (by simp)).trans
        ((he2 .X23 (by simp)).trans (he1 .X23 (by simp)))]
      exact hL.x23
    · rw [show s3.data.regs.X9 = s1.data.regs.X9 from (he3 .X9 (by simp)).trans
        (he2 .X9 (by simp))]
      show (s1.data.regs.getXReg .X9).toBitVec = _
      rw [hm1.regs .X9 _ rfl]
      show fb m0 + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 8 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add,
        show 8 * j + 8 = 8 * (j + 1) by omega]
    · rw [show s3.data.regs.X8 = st.data.regs.X8 from (he3 .X8 (by simp)).trans
        ((he2 .X8 (by simp)).trans (he1 .X8 (by simp)))]
      exact hL.x8
    · rw [show s3.data.regs.X10 = st.data.regs.X10 from (he3 .X10 (by simp)).trans
        ((he2 .X10 (by simp)).trans (he1 .X10 (by simp)))]
      exact hL.x10
  · exact .done _ (Or.inl ⟨hno3 h63, hfr3, not_fit_size hi (by omega)⟩)

/-- **The main loop**, from its head to `b22` or a failure. -/
theorem loop (hp : Placed code k) {m0 : MachineData} (hpre : StackOffsetsPre m0)
    (hcap : n m0 ≤ cap m0) {j : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b17Offset))
    (hL : Loop m0 j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ Fail k m0 s ∨ End k m0 s) st := by
  refine Sym.loop (fun r s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b17Offset) ∧ ∃ j, n m0 - j = r ∧ Loop m0 j s.data)
    (fun r s ⟨hpc, j, hr, hL⟩ ↦ ?_) ⟨hpc, j, rfl, hL⟩
  refine run_regs hpre.1 (infix_of b17_in_code (by simp [b17]) hp) run_b17
    (after_eq run_b17 ▸ b17_keeps) hpc hL.fr fun st' hm hpc' hfr hd ↦ ?_
  have hL' := hL.of hfr (regs_eq_of (match_nil _) hm loopRegs rfl) hd
  simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b17_length, NativeRustcVmArm.Vm.StackOffsets.b17Length] at hpc'
  obtain ⟨hy, hno⟩ := pc_of (P := 8 * (n m0 - j) = 0) hpc' (by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    exact eq_apply hL.x23 (lit_toNat (by decide)))
  by_cases h0 : 8 * (n m0 - j) = 0
  · have hjn : j = n m0 := by have := hL.le; omega
    exact .done _ (Or.inl (Or.inr ⟨(hy h0).trans (lbl_20 hp), hjn ▸ hL'⟩))
  · refine Eventually.mono (step hp hpre hcap (hno h0) hL' (by omega)) fun s h ↦ ?_
    rcases h with h | ⟨hpc'', hL''⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨n m0 - (j + 1), by omega, hpc'', j + 1, rfl, hL''⟩

end

end NativeRustcVmArm.Layout.StackOffsets
