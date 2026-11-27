module

public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.Mem.Common
public import NativeRustcArm.Mem.MemcpyBlocks

/-!
# `memcpy` meets its contract

`memcpy_spec`: rustc's `memcpy`, placed anywhere in the program, meets `MemcpyPre`/`MemcpyPost`.
Its blocks run by the symbolic executor (`NativeRustcArm.Mem.MemcpyBlocks`), each from a fresh
environment of the machine state it starts in; the word loop (operands and length multiples of 8,
`x8` the offset) and the byte loop (`x1`, `x8` the pointers, `x2` the bytes left) by invariants
(`WInv`, `BInv`) on the machine state at their heads, each iteration copying the next word or byte.
-/

namespace NativeRustcArm.Mem.Memcpy

open NativeRustcArm.Sym NativeRustcArm.Common.Memcpy NativeRustcArm

public section

section

variable [ElfHost] {sec k : Nat} (m : MachineData)

/-- `memcpy` done, at `.LMemcpy_7`. -/
structure Done (sec k : Nat) (st : MachineState) : Prop where
  pc : st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Memcpy.b8Offset)
  x0 : st.data.regs.X0 = m.regs.X0
  x30 : st.data.regs.X30 = m.regs.X30
  saved : Saved m st.data
  copied : BytesAt st.data.dmem m.regs.X0.toBitVec (bytesOf m.dmem m.regs.X1.toBitVec m.regs.X2.toNat)
  same : SameOutside m.dmem st.data.dmem (InRange m.regs.X0.toBitVec m.regs.X2.toNat)

/-- The word loop's head after `i` bytes. -/
structure WInv (sec k i : Nat) (st : MachineState) : Prop where
  pc : st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Memcpy.b7Offset)
  i8 : i % 8 = 0
  lt : i < m.regs.X2.toNat
  x0 : st.data.regs.X0 = m.regs.X0
  x1 : st.data.regs.X1 = m.regs.X1
  x2 : st.data.regs.X2 = m.regs.X2
  x8 : st.data.regs.X8.toNat = i
  x30 : st.data.regs.X30 = m.regs.X30
  saved : Saved m st.data
  copied : BytesAt st.data.dmem m.regs.X0.toBitVec (bytesOf m.dmem m.regs.X1.toBitVec i)
  same : SameOutside m.dmem st.data.dmem (InRange m.regs.X0.toBitVec i)

/-- The byte loop's head after `i` bytes. -/
structure BInv (sec k i : Nat) (st : MachineState) : Prop where
  pc : st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Memcpy.b3Offset)
  lt : i < m.regs.X2.toNat
  x0 : st.data.regs.X0 = m.regs.X0
  x1 : st.data.regs.X1.toBitVec = m.regs.X1.toBitVec + BitVec.ofNat 64 i
  x2 : st.data.regs.X2.toNat = m.regs.X2.toNat - i
  x8 : st.data.regs.X8.toBitVec = m.regs.X0.toBitVec + BitVec.ofNat 64 i
  x30 : st.data.regs.X30 = m.regs.X30
  saved : Saved m st.data
  copied : BytesAt st.data.dmem m.regs.X0.toBitVec (bytesOf m.dmem m.regs.X1.toBitVec i)
  same : SameOutside m.dmem st.data.dmem (InRange m.regs.X0.toBitVec i)

/-- `memcpy`'s postcondition, reached. -/
abbrev Post (st : MachineState) : Prop := st.pc = retOf m ∧ MemcpyPost m st.data

variable {m}

theorem infix_of {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j) (hne : b ≠ [])
    (hp : PlacedIn code sec k) : b.IsInfixAt (ElfHost.sectionProg sec) (k + j) :=
  hb.trans hp.1 hne

/-- From `.LMemcpy_7`: `ret`. -/
theorem finish {st : MachineState} (hp : PlacedIn code sec k) (hd : Done m sec k st) :
    Eventually (elfStep1 ElfHost.exe) (Post m) st := by
  refine exec_at_elf (infix_of b8_in_code (by simp [b8]) hp) e8 (Env.wf_nil _) hd.pc (match_nil _)
    fun st' hm' hpc' => .done _ ⟨?_, ?_⟩
  · have h30 : st'.data.regs.X30 = st.data.regs.X30 := Match.reg_eq (r := .X30) (match_nil _) hm' rfl rfl
    simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, h30, hd.x30]
  · have hdm : st'.data.dmem = st.data.dmem := hm'.dmem_eq (Env.wf_nil _) rfl
    refine ⟨(Match.reg_eq (r := .X0) (match_nil _) hm' rfl rfl).trans hd.x0, ?_, ?_, ?_⟩
    · rw [hdm]
      exact hd.copied
    · intro p hp'
      rw [hdm]
      exact hd.same p hp'
    · exact hd.saved.trans (Match.saved (match_nil _) hm' (Env.wf_nil _) rfl rfl)

omit [ElfHost] in
/-- A source byte, unchanged while the destination's first `i` bytes are written. -/
theorem src_same (hpre : MemcpyPre m) {d : DataMem} {i j : Nat} (hi : i ≤ m.regs.X2.toNat) (hj : j < m.regs.X2.toNat)
    (hs : SameOutside m.dmem d (InRange m.regs.X0.toBitVec i)) :
    d.get? (m.regs.X1.toBitVec + BitVec.ofNat 64 j) = m.dmem.get? (m.regs.X1.toBitVec + BitVec.ofNat 64 j) := by
  obtain ⟨-, -, hnd, hns, hap⟩ := hpre
  unfold NoWrap at hnd hns
  unfold Apart at hap
  apply hs
  rw [inRange_iff (by omega), toNat_add_ofNat _ _ (by omega)]
  omega

/-- The word loop's environment after `i` bytes: the next destination and source words. -/
abbrev wordEnv (m d : MachineData) (i : Nat) : Env :=
  Env.ofMachine d [(m.regs.X0.toBitVec + BitVec.ofNat 64 i, 8), (m.regs.X1.toBitVec + BitVec.ofNat 64 i, 8)]

/-- **One word**: from the word loop's head after `i` bytes, the next word copied, back at the head
or done. -/
theorem word_step (hp : PlacedIn code sec k) (hpre : MemcpyPre m) (h8 : m.regs.X2.toNat % 8 = 0) {i : Nat}
    {st : MachineState} (hI : WInv m sec k i st) :
    Eventually (elfStep1 ElfHost.exe) (fun st' => Post m st' ∨ WInv m sec k (i + 8) st') st := by
  have hpre' := hpre
  obtain ⟨hmd, hms, hnd, hns, hap⟩ := hpre'
  have hle : i + 8 ≤ m.regs.X2.toNat := by have := hI.i8; have := hI.lt; omega
  unfold NoWrap at hnd hns
  unfold Apart at hap
  have hkept := hI.saved.2.2
  have hdi : (m.regs.X0.toBitVec + BitVec.ofNat 64 i).toNat = m.regs.X0.toBitVec.toNat + i := toNat_add_ofNat _ _ (by omega)
  have hsi : (m.regs.X1.toBitVec + BitVec.ofNat 64 i).toNat = m.regs.X1.toBitVec.toNat + i := toNat_add_ofNat _ _ (by omega)
  have hx8i : st.data.regs.X8.toBitVec = BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hI.x8
  let env := wordEnv m st.data i
  have hwf : env.WF := Env.wf_of
    ⟨⟨fun j hj => by rw [addr_add]; exact Mapped.of_kept hmd hkept _ (by omega),
      by unfold NoWrap; simp only; omega⟩,
     ⟨fun j hj => by rw [addr_add]; exact Mapped.of_kept hms hkept _ (by omega),
      by unfold NoWrap; simp only; omega⟩, trivial⟩
    (List.pairwise_pair.mpr (by unfold Apart; simp only; omega))
  have hm : Match env sWord st.data := match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
    trivial trivial trivial
    ⟨show (idx .X0 .X8).eval env = env.base 0 + BitVec.ofInt 64 0 by
      rw [eval_idx, Env.base_ofMachine _ _ _ rfl]
      simp [env, Reg64s.getXReg, hI.x0, hx8i],
     show (idx .X1 .X8).eval env = env.base 1 + BitVec.ofInt 64 0 by
      rw [eval_idx, Env.base_ofMachine _ _ _ rfl]
      simp [env, Reg64s.getXReg, hI.x1, hx8i], trivial⟩
  refine exec_at_elf (infix_of b7_in_code (by simp [b7]) hp) e7 hwf hI.pc hm fun st' hm' hpc' => ?_
  have hx0 : st'.data.regs.X0 = m.regs.X0 := (Match.reg_eq (r := .X0) hm hm' rfl rfl).trans hI.x0
  have hx1 : st'.data.regs.X1 = m.regs.X1 := (Match.reg_eq (r := .X1) hm hm' rfl rfl).trans hI.x1
  have hx2 : st'.data.regs.X2 = m.regs.X2 := (Match.reg_eq (r := .X2) hm hm' rfl rfl).trans hI.x2
  have hx30 : st'.data.regs.X30 = m.regs.X30 :=
    (Match.reg_eq (r := .X30) hm hm' rfl rfl).trans hI.x30
  have hx8 : st'.data.regs.X8.toNat = i + 8 := by
    have h := hm'.regs .X8 _ rfl
    sym_simp at h
    show (st'.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [h, BitVec.toNat_add, Env.ofMachine_regs]
    show (st.data.regs.X8.toBitVec.toNat + 8 % 2 ^ 64) % 2 ^ 64 = i + 8
    rw [UInt64.toNat_toBitVec, hI.x8]
    omega
  have hsaved : Saved m st'.data := hI.saved.trans (Match.saved hm hm' hwf rfl rfl)
  -- the word written
  have hw : ∀ j < 8, st'.data.dmem.get? (m.regs.X0.toBitVec + BitVec.ofNat 64 (i + j)) =
      some ((m.dmem.get? (m.regs.X1.toBitVec + BitVec.ofNat 64 (i + j))).getD 0) := by
    intro j hj
    have h := hm'.bytesAt_write (r := 0) (o := 0) (n := 8) (b := m.regs.X0.toBitVec + BitVec.ofNat 64 i)
      (sz := 8) rfl (by omega) (v := .load 1 0 8) (fun j hj => findWrite_head hj) j (by simp; omega)
    simp only [List.getElem_map, List.getElem_range, addr_add3] at h
    rw [h]
    congr 1
    show byteOf (env.load 1 0 8) j = _
    rw [byteOf_load hj (by decide), Env.base_ofMachine _ _ _ rfl, Env.ofMachine_mem0, Nat.zero_add,
      addr_add, src_same hpre (by omega) (by omega) hI.same]
  have hout : ∀ a : BitVec 64, ¬(m.regs.X0.toBitVec.toNat + i ≤ a.toNat ∧ a.toNat < m.regs.X0.toBitVec.toNat + i + 8) →
      st'.data.dmem.get? a = st.data.dmem.get? a := by
    intro a ha
    refine hm'.get?_mem0 hwf ?_
    rintro ⟨w, hw, b, sz, hb, h1, h2⟩
    cases hw with
    | head =>
      cases hb
      rw [hdi] at h1 h2
      dsimp only at h1 h2
      exact ha ⟨by omega, by omega⟩
    | tail _ hw => cases hw
  obtain ⟨hc', hs'⟩ := extend (f := fun j => (m.dmem.get? (m.regs.X1.toBitVec + BitVec.ofNat 64 j)).getD 0)
    hnd hle hI.copied hI.same hw hout
  simp only [PcOk] at hpc'
  split at hpc'
  · rename_i hc
    have hlt : i + 8 < m.regs.X2.toNat := by
      sym_simp at hc
      simp only [env, BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, Env.ofMachine_regs,
        UInt64.toNat_toBitVec, BitVec.toNat_ofNat, MemWidth.bits, Reg64s.getXReg, hI.x8, hI.x2] at hc
      omega
    refine .done _ (Or.inr ⟨?_, by have := hI.i8; omega, hlt, hx0, hx1, hx2, hx8, hx30, hsaved, hc', hs'⟩)
    rw [hpc']
    exact hp.label NativeRustcArm.Common.Memcpy.label_6_at
  · rename_i hc
    have hn : i + 8 = m.regs.X2.toNat := by
      sym_simp at hc
      simp only [env, BitVec.ult, BitVec.toNat_add, Env.ofMachine_regs,
        UInt64.toNat_toBitVec, BitVec.toNat_ofNat, MemWidth.bits, Reg64s.getXReg, hI.x8, hI.x2,
        Bool.not_eq_true, decide_eq_false_iff_not] at hc
      omega
    rw [hn] at hc' hs'
    exact Eventually.mono_elf (finish hp ⟨hpc', hx0, hx30, hsaved, hc', hs'⟩) fun _ h => Or.inl h

/-- The byte loop's environment after `i` bytes: the next destination and source bytes. -/
abbrev byteEnv (m d : MachineData) (i : Nat) : Env :=
  Env.ofMachine d [(m.regs.X0.toBitVec + BitVec.ofNat 64 i, 1), (m.regs.X1.toBitVec + BitVec.ofNat 64 i, 1)]

/-- **One byte**: from the byte loop's head after `i` bytes, the next byte copied, back at the head
or done. -/
theorem byte_step (hp : PlacedIn code sec k) (hpre : MemcpyPre m) {i : Nat} {st : MachineState}
    (hI : BInv m sec k i st) :
    Eventually (elfStep1 ElfHost.exe) (fun st' => Post m st' ∨ BInv m sec k (i + 1) st') st := by
  have hpre' := hpre
  obtain ⟨hmd, hms, hnd, hns, hap⟩ := hpre'
  have hle : i + 1 ≤ m.regs.X2.toNat := hI.lt
  unfold NoWrap at hnd hns
  unfold Apart at hap
  have hkept := hI.saved.2.2
  have hdi : (m.regs.X0.toBitVec + BitVec.ofNat 64 i).toNat = m.regs.X0.toBitVec.toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  let env := byteEnv m st.data i
  have hwf : env.WF := Env.wf_of
    ⟨⟨fun j hj => by rw [addr_add]; exact Mapped.of_kept hmd hkept _ (by omega),
      by unfold NoWrap; simp only; omega⟩,
     ⟨fun j hj => by rw [addr_add]; exact Mapped.of_kept hms hkept _ (by omega),
      by unfold NoWrap; simp only; omega⟩, trivial⟩
    (List.pairwise_pair.mpr (by
      unfold Apart
      simp only
      rw [hdi, toNat_add_ofNat _ _ (by omega)]
      omega))
  have hm : Match env sByte st.data := match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
    ⟨show (st.data.regs.getXReg .X8).toBitVec = (Sym.ptr 0 0).eval env by
      simp [Sym.eval, env]
      exact hI.x8,
     show (st.data.regs.getXReg .X1).toBitVec = (Sym.ptr 1 0).eval env by
      simp [Sym.eval, env]
      exact hI.x1, trivial⟩
    trivial trivial trivial
  refine exec_at_elf (infix_of b3_in_code (by simp [b3]) hp) e3 hwf hI.pc hm fun st' hm' hpc' => ?_
  have hx0 : st'.data.regs.X0 = m.regs.X0 := (Match.reg_eq (r := .X0) hm hm' rfl rfl).trans hI.x0
  have hx30 : st'.data.regs.X30 = m.regs.X30 :=
    (Match.reg_eq (r := .X30) hm hm' rfl rfl).trans hI.x30
  have hx1 : st'.data.regs.X1.toBitVec = m.regs.X1.toBitVec + BitVec.ofNat 64 (i + 1) := by
    have h := hm'.regs .X1 _ rfl
    simp only [Sym.eval, env, Env.base_ofMachine_eq, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.map_some, Option.getD_some] at h
    exact h.trans (add_ofInt_one _ _)
  have hx8 : st'.data.regs.X8.toBitVec = m.regs.X0.toBitVec + BitVec.ofNat 64 (i + 1) := by
    have h := hm'.regs .X8 _ rfl
    simp only [Sym.eval, env, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some] at h
    exact h.trans (add_ofInt_one _ _)
  have hx2 : st'.data.regs.X2.toNat = m.regs.X2.toNat - i - 1 := by
    have h := hm'.regs .X2 _ rfl
    sym_simp at h
    show (st'.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [h, BitVec.toNat_sub, Env.ofMachine_regs]
    show (2 ^ 64 - (1 : Nat) % 2 ^ 64 + st.data.regs.X2.toBitVec.toNat) % 2 ^ 64 = _
    rw [UInt64.toNat_toBitVec, hI.x2]
    have := m.regs.X2.toNat_lt
    omega
  have hsaved : Saved m st'.data := hI.saved.trans (Match.saved hm hm' hwf rfl rfl)
  have hw : ∀ j < 1, st'.data.dmem.get? (m.regs.X0.toBitVec + BitVec.ofNat 64 (i + j)) =
      some ((m.dmem.get? (m.regs.X1.toBitVec + BitVec.ofNat 64 (i + j))).getD 0) := by
    intro j hj
    have h := hm'.bytesAt_write (r := 0) (o := 0) (n := 1) (b := m.regs.X0.toBitVec + BitVec.ofNat 64 i)
      (sz := 1) rfl (by omega) (v := .load 1 0 1) (fun j hj => findWrite_head hj) j (by simp; omega)
    simp only [List.getElem_map, List.getElem_range, addr_add3] at h
    rw [h]
    congr 1
    show byteOf (env.load 1 0 1) j = _
    rw [byteOf_load hj (by decide), Env.base_ofMachine _ _ _ rfl, Env.ofMachine_mem0, Nat.zero_add,
      addr_add, src_same hpre (by omega) (by omega) hI.same]
  have hout : ∀ a : BitVec 64, ¬(m.regs.X0.toBitVec.toNat + i ≤ a.toNat ∧
      a.toNat < m.regs.X0.toBitVec.toNat + i + 1) → st'.data.dmem.get? a = st.data.dmem.get? a := by
    intro a ha
    refine hm'.get?_mem0 hwf ?_
    rintro ⟨w, hw, b, sz, hb, h1, h2⟩
    cases hw with
    | head =>
      cases hb
      rw [hdi] at h1 h2
      dsimp only at h1 h2
      exact ha ⟨by omega, by omega⟩
    | tail _ hw => cases hw
  obtain ⟨hc', hs'⟩ := extend (f := fun j => (m.dmem.get? (m.regs.X1.toBitVec + BitVec.ofNat 64 j)).getD 0)
    hnd hle hI.copied hI.same hw hout
  simp only [PcOk] at hpc'
  have hx2' : (st.data.regs.X2.toBitVec == BitVec.ofNat 64 1) = (m.regs.X2.toNat - i == 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.toNat_eq, UInt64.toNat_toBitVec, hI.x2,
      BitVec.toNat_ofNat]
  have hce : (SBool.not (.cmp .eq .W64 (.reg .X2) (.lit 1))).eval env =
      !(m.regs.X2.toNat - i == 1) := by
    sym_simp
    simp only [env, Env.ofMachine_regs, Reg64s.getXReg]
    rw [hx2']
  split at hpc'
  · rename_i hc
    have hlt : i + 1 < m.regs.X2.toNat := by
      rw [hce] at hc
      simp at hc
      omega
    refine .done _ (Or.inr ⟨?_, hlt, hx0, hx1, by rw [hx2]; omega, hx8, hx30, hsaved, hc', hs'⟩)
    rw [hpc']
    exact hp.label NativeRustcArm.Common.Memcpy.label_3_at
  · rename_i hc
    have hn : i + 1 = m.regs.X2.toNat := by
      rw [hce] at hc
      simp at hc
      have := hI.lt
      omega
    rw [hn] at hc' hs'
    refine exec_at_elf (infix_of b4_in_code (by simp [b4]) hp) e4 (Env.wf_nil _) hpc' (match_nil _)
      fun st'' hm'' hpc'' => ?_
    have hd : st''.data.dmem = st'.data.dmem := hm''.dmem_eq (Env.wf_nil _) rfl
    refine Eventually.mono_elf (finish hp ⟨?_, ?_, ?_, ?_, ?_, ?_⟩) fun _ h => Or.inl h
    · simp only [PcOk] at hpc''
      rw [hpc'']
      exact hp.label NativeRustcArm.Common.Memcpy.label_7_at
    · exact (Match.reg_eq (r := .X0) (match_nil _) hm'' rfl rfl).trans hx0
    · exact (Match.reg_eq (r := .X30) (match_nil _) hm'' rfl rfl).trans hx30
    · exact hsaved.trans (Match.saved (match_nil _) hm'' (Env.wf_nil _) rfl rfl)
    · rw [hd]
      exact hc'
    · intro p hp'
      rw [hd]
      exact hs' p hp'

/-- The word loop, from its head after `i` bytes. -/
theorem word_loop (hp : PlacedIn code sec k) (hpre : MemcpyPre m) (h8 : m.regs.X2.toNat % 8 = 0)
    {i : Nat} {st : MachineState} (hI : WInv m sec k i st) : Eventually (elfStep1 ElfHost.exe) (Post m) st :=
  Sym.loop (fun μ st => ∃ i, μ = m.regs.X2.toNat - i ∧ WInv m sec k i st)
    (fun _ _ ⟨i, hμ, hI⟩ => Eventually.mono_elf (word_step hp hpre h8 hI) fun st' h =>
      h.imp_right fun h' => ⟨m.regs.X2.toNat - (i + 8), by have := hI.lt; omega, i + 8, rfl, h'⟩)
    ⟨i, rfl, hI⟩

/-- The byte loop, from its head after `i` bytes. -/
theorem byte_loop (hp : PlacedIn code sec k) (hpre : MemcpyPre m) {i : Nat} {st : MachineState}
    (hI : BInv m sec k i st) : Eventually (elfStep1 ElfHost.exe) (Post m) st :=
  Sym.loop (fun μ st => ∃ i, μ = m.regs.X2.toNat - i ∧ BInv m sec k i st)
    (fun _ _ ⟨i, hμ, hI⟩ => Eventually.mono_elf (byte_step hp hpre hI) fun st' h =>
      h.imp_right fun h' => ⟨m.regs.X2.toNat - (i + 1), by have := hI.lt; omega, i + 1, rfl, h'⟩)
    ⟨i, rfl, hI⟩

/-- **`memcpy` meets its contract** under a multi-section `ElfHost`. -/
theorem memcpy_spec_elf (hp : PlacedIn code sec k) :
    ElfSpec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost := by
  intro m hpre
  rw [hp.label NativeRustcArm.Common.Memcpy.entry_at]
  refine exec_then_elf (infix_of b0_in_code (by simp [b0]) hp) e0 (Env.wf_nil m) (match_nil m)
    fun st0 hm0 hpc0 => ?_
  have hd0 : st0.data.dmem = m.dmem := hm0.dmem_eq (Env.wf_nil _) rfl
  have hx0 : st0.data.regs.X0 = m.regs.X0 := Match.reg_eq (r := .X0) (match_nil m) hm0 rfl rfl
  have hx1 : st0.data.regs.X1 = m.regs.X1 := Match.reg_eq (r := .X1) (match_nil m) hm0 rfl rfl
  have hx2 : st0.data.regs.X2 = m.regs.X2 := Match.reg_eq (r := .X2) (match_nil m) hm0 rfl rfl
  have hx30 : st0.data.regs.X30 = m.regs.X30 := Match.reg_eq (r := .X30) (match_nil m) hm0 rfl rfl
  have hs0 : Saved m st0.data := Match.saved (match_nil m) hm0 (Env.wf_nil m) rfl rfl
  simp only [PcOk] at hpc0
  split at hpc0
  · -- aligned: the word loop
    rename_i hal
    have h8 : m.regs.X2.toNat % 8 = 0 := align_or3 hal
    refine exec_at_elf (infix_of b5_in_code (by simp [b5]) hp) e5 (Env.wf_nil _)
      (hpc0.trans (hp.label NativeRustcArm.Common.Memcpy.label_4_at)) (match_nil _) fun st5 hm5 hpc5 => ?_
    have hd5 : st5.data.dmem = m.dmem := (hm5.dmem_eq (Env.wf_nil _) rfl).trans hd0
    have hy0 : st5.data.regs.X0 = m.regs.X0 :=
      (Match.reg_eq (r := .X0) (match_nil _) hm5 rfl rfl).trans hx0
    have hy1 : st5.data.regs.X1 = m.regs.X1 :=
      (Match.reg_eq (r := .X1) (match_nil _) hm5 rfl rfl).trans hx1
    have hy2 : st5.data.regs.X2 = m.regs.X2 :=
      (Match.reg_eq (r := .X2) (match_nil _) hm5 rfl rfl).trans hx2
    have hy30 : st5.data.regs.X30 = m.regs.X30 :=
      (Match.reg_eq (r := .X30) (match_nil _) hm5 rfl rfl).trans hx30
    have hs5 : Saved m st5.data := hs0.trans (Match.saved (match_nil _) hm5 (Env.wf_nil _) rfl rfl)
    simp only [PcOk] at hpc5
    split at hpc5
    · rename_i hz
      have hn : m.regs.X2.toNat = 0 := by
        sym_simp at hz
        simp only [Env.ofMachine_regs, Reg64s.getXReg, beq_iff_eq] at hz
        rw [← hx2, ← UInt64.toNat_toBitVec, hz]
        rfl
      refine finish hp ⟨hpc5.trans (hp.label NativeRustcArm.Common.Memcpy.label_7_at), hy0, hy30, hs5, ?_, ?_⟩
      · rw [hn]
        exact bytesAt_nil _ _
      · exact sameOutside_of_eq hd5 _
    · rename_i hz
      have hn : m.regs.X2.toNat ≠ 0 := by
        sym_simp at hz
        simp only [Env.ofMachine_regs, Reg64s.getXReg, beq_iff_eq] at hz
        intro h
        apply hz
        rw [hx2]
        exact BitVec.eq_of_toNat_eq (by simp [h])
      refine exec_at_elf (infix_of b6_in_code (by simp [b6]) hp) e6 (Env.wf_nil _) hpc5 (match_nil _)
        fun st6 hm6 hpc6 => ?_
      have hd6 : st6.data.dmem = m.dmem := (hm6.dmem_eq (Env.wf_nil _) rfl).trans hd5
      refine word_loop (i := 0) hp hpre h8 ⟨hpc6, rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Match.reg_eq (r := .X0) (match_nil _) hm6 rfl rfl).trans hy0
      · exact (Match.reg_eq (r := .X1) (match_nil _) hm6 rfl rfl).trans hy1
      · exact (Match.reg_eq (r := .X2) (match_nil _) hm6 rfl rfl).trans hy2
      · have h := hm6.regs .X8 _ rfl
        show (st6.data.regs.getXReg .X8).toBitVec.toNat = 0
        rw [h]
        rfl
      · exact (Match.reg_eq (r := .X30) (match_nil _) hm6 rfl rfl).trans hy30
      · exact hs5.trans (Match.saved (match_nil _) hm6 (Env.wf_nil _) rfl rfl)
      · exact bytesAt_nil _ _
      · exact sameOutside_of_eq hd6 _
  · -- the byte loop
    refine exec_at_elf (infix_of b1_in_code (by simp [b1]) hp) e1 (Env.wf_nil _) hpc0 (match_nil _)
      fun st1 hm1 hpc1 => ?_
    have hd1 : st1.data.dmem = m.dmem := (hm1.dmem_eq (Env.wf_nil _) rfl).trans hd0
    have hy0 : st1.data.regs.X0 = m.regs.X0 :=
      (Match.reg_eq (r := .X0) (match_nil _) hm1 rfl rfl).trans hx0
    have hy1 : st1.data.regs.X1 = m.regs.X1 :=
      (Match.reg_eq (r := .X1) (match_nil _) hm1 rfl rfl).trans hx1
    have hy2 : st1.data.regs.X2 = m.regs.X2 :=
      (Match.reg_eq (r := .X2) (match_nil _) hm1 rfl rfl).trans hx2
    have hy30 : st1.data.regs.X30 = m.regs.X30 :=
      (Match.reg_eq (r := .X30) (match_nil _) hm1 rfl rfl).trans hx30
    have hs1 : Saved m st1.data := hs0.trans (Match.saved (match_nil _) hm1 (Env.wf_nil _) rfl rfl)
    simp only [PcOk] at hpc1
    split at hpc1
    · rename_i hz
      have hn : m.regs.X2.toNat = 0 := by
        sym_simp at hz
        simp only [Env.ofMachine_regs, Reg64s.getXReg, beq_iff_eq] at hz
        rw [← hx2, ← UInt64.toNat_toBitVec, hz]
        rfl
      refine finish hp ⟨hpc1.trans (hp.label NativeRustcArm.Common.Memcpy.label_7_at), hy0, hy30, hs1, ?_, ?_⟩
      · rw [hn]
        exact bytesAt_nil _ _
      · exact sameOutside_of_eq hd1 _
    · rename_i hz
      have hn : m.regs.X2.toNat ≠ 0 := by
        sym_simp at hz
        simp only [Env.ofMachine_regs, Reg64s.getXReg, beq_iff_eq] at hz
        intro h
        apply hz
        rw [hx2]
        exact BitVec.eq_of_toNat_eq (by simp [h])
      refine exec_at_elf (infix_of b2_in_code (by simp [b2]) hp) e2 (Env.wf_nil _) hpc1 (match_nil _)
        fun st2 hm2 hpc2 => ?_
      have hd2 : st2.data.dmem = m.dmem := (hm2.dmem_eq (Env.wf_nil _) rfl).trans hd1
      refine byte_loop (i := 0) hp hpre ⟨hpc2, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Match.reg_eq (r := .X0) (match_nil _) hm2 rfl rfl).trans hy0
      · rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, ← hy1]
        exact congrArg UInt64.toBitVec (Match.reg_eq (r := .X1) (match_nil _) hm2 rfl rfl)
      · rw [Nat.sub_zero, ← hy2]
        exact congrArg UInt64.toNat (Match.reg_eq (r := .X2) (match_nil _) hm2 rfl rfl)
      · rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, ← hy0]
        exact hm2.regs .X8 _ rfl
      · exact (Match.reg_eq (r := .X30) (match_nil _) hm2 rfl rfl).trans hy30
      · exact hs1.trans (Match.saved (match_nil _) hm2 (Env.wf_nil _) rfl rfl)
      · exact bytesAt_nil _ _
      · exact sameOutside_of_eq hd2 _

end

/-- **`memcpy` meets its contract.** -/
theorem memcpy_spec [h : NativeRustcArm.Host] {k : Nat} (hp : Placed code k) :
    Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost :=
  ElfSpec.toSpec (entry := fun [_] => label NativeRustcArm.Common.Memcpy.entryLabel)
    (P := fun [_] => MemcpyPre) (Q := fun [_] => MemcpyPost)
    (@memcpy_spec_elf (Host.toElfHost h) 0 k hp.toPlacedIn)

end

end NativeRustcArm.Mem.Memcpy
