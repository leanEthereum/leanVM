module

public import NativeRustcArm.Code.Common.Memset.Names

public import NativeRustcArm.Mem.MemsetBlocks

/-!
# `memset` meets its contract

`memset_spec`: rustc's `memset`, placed anywhere in the program, meets `MemsetPre`/`MemsetPost`.
Its blocks run by the symbolic executor (`NativeRustcArm.Mem.MemsetBlocks`), each from a fresh
environment of the machine state it starts in; the word loop (destination and length multiples of
8, `x8` the byte repeated eight times, `x9` the offset) and the byte loop (`x8` the pointer, `x2` the
bytes left) by invariants (`WInv`, `BInv`) on the machine state at their heads, each iteration
filling the next word or byte.
-/

namespace NativeRustcArm.Mem.Memset

open NativeRustcArm.Sym NativeRustcArm.Mem NativeRustcArm.Common.Memset NativeRustcArm

public section

/-- The fill byte's bytes, `f j = c` for every `j`. -/
abbrev fill (m : MachineData) : Nat → UInt8 := fun _ => m.regs.X1.toUInt8

theorem replicate_eq (n : Nat) (c : UInt8) : List.replicate n c = (List.range n).map fun _ => c := by
  rw [List.map_const', List.length_range]

theorem byte_split {q' : Nat} (a c q r : Nat) (hc : 0 < c) (hr : r < c) (h : a = c * q + r) (hq : q % 256 = q') :
    a / c % 256 = q' := by
  subst h
  rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hr, Nat.add_zero, hq]

theorem word_bytes (a : Nat) (ha : a < 256) (j : Nat) (hj : j < 8) :
    a * 72340172838076673 / 2 ^ (8 * j) % 256 = a := by
  match j, hj with
  | 0, _ => omega
  | 1, _ => exact byte_split _ _ (a * 282578800148737) (a * 1) (by decide) (by omega) (by omega) (by omega)
  | 2, _ => exact byte_split _ _ (a * 1103823438081) (a * 257) (by decide) (by omega) (by omega) (by omega)
  | 3, _ => exact byte_split _ _ (a * 4311810305) (a * 65793) (by decide) (by omega) (by omega) (by omega)
  | 4, _ => exact byte_split _ _ (a * 16843009) (a * 16843009) (by decide) (by omega) (by omega) (by omega)
  | 5, _ => exact byte_split _ _ (a * 65793) (a * 4311810305) (by decide) (by omega) (by omega) (by omega)
  | 6, _ => exact byte_split _ _ (a * 257) (a * 1103823438081) (by decide) (by omega) (by omega) (by omega)
  | 7, _ => exact byte_split _ _ (a * 1) (a * 282578800148737) (by decide) (by omega) (by omega) (by omega)

theorem word_eq (x : BitVec 64) :
    BinOp.apply .mul .W64 (BinOp.apply .and .W32 x (BitVec.ofNat 64 255))
      (BitVec.ofNat 64 72340172838076673) =
    ext .W32 (low .W32 x &&& low .W32 (BitVec.ofNat 64 255)) * BitVec.ofNat 64 72340172838076673 := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem and255_toNat (x : BitVec 64) :
    (ext .W32 (low .W32 x &&& low .W32 (BitVec.ofNat 64 255))).toNat = x.toNat % 256 := by
  rw [ext_W32, low_W32, low_W32, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    show 255 % 2 ^ 64 % 2 ^ 32 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 32)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem mulK_toNat (y : BitVec 64) (hy : y.toNat < 256) :
    (y * BitVec.ofNat 64 72340172838076673).toNat = y.toNat * 72340172838076673 := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (72340172838076673 : Nat) % 2 ^ 64 = 72340172838076673 from rfl]
  exact Nat.mod_eq_of_lt (show y.toNat * 72340172838076673 < 2 ^ 64 by omega)

theorem u8_mod (n : Nat) : UInt8.ofNat (n % 256) = UInt8.ofNat n := by
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat']
  omega

/-- The word `memset` stores: the byte repeated eight times. -/
theorem byteOf_word (x : BitVec 64) {j : Nat} (hj : j < 8) :
    byteOf (BinOp.apply .mul .W64 (BinOp.apply .and .W32 x (BitVec.ofNat 64 255))
      (BitVec.ofNat 64 72340172838076673)) j = UInt8.ofNat x.toNat := by
  have hlt : x.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [word_eq, byteOf_mod, mulK_toNat _ (by rw [and255_toNat]; exact hlt), and255_toNat,
    word_bytes _ hlt j hj, u8_mod]

variable [Host] {k : Nat} (m : MachineData)

/-- `memset` done, at `.LMemset_7`. -/
structure Done (k : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcArm.Common.Memset.b8Offset)
  x0 : st.data.regs.X0 = m.regs.X0
  x30 : st.data.regs.X30 = m.regs.X30
  saved : Saved m st.data
  filled : BytesAt st.data.dmem m.regs.X0.toBitVec ((List.range m.regs.X2.toNat).map (fill m))
  same : SameOutside m.dmem st.data.dmem (InRange m.regs.X0.toBitVec m.regs.X2.toNat)

/-- The word loop's head after `i` bytes. -/
structure WInv (k i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcArm.Common.Memset.b7Offset)
  i8 : i % 8 = 0
  lt : i < m.regs.X2.toNat
  x0 : st.data.regs.X0 = m.regs.X0
  x2 : st.data.regs.X2 = m.regs.X2
  x8 : ∀ j < 8, byteOf st.data.regs.X8.toBitVec j = m.regs.X1.toUInt8
  x9 : st.data.regs.X9.toNat = i
  x30 : st.data.regs.X30 = m.regs.X30
  saved : Saved m st.data
  filled : BytesAt st.data.dmem m.regs.X0.toBitVec ((List.range i).map (fill m))
  same : SameOutside m.dmem st.data.dmem (InRange m.regs.X0.toBitVec i)

/-- The byte loop's head after `i` bytes. -/
structure BInv (k i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcArm.Common.Memset.b3Offset)
  lt : i < m.regs.X2.toNat
  x0 : st.data.regs.X0 = m.regs.X0
  x1 : st.data.regs.X1 = m.regs.X1
  x2 : st.data.regs.X2.toNat = m.regs.X2.toNat - i
  x8 : st.data.regs.X8.toBitVec = m.regs.X0.toBitVec + BitVec.ofNat 64 i
  x30 : st.data.regs.X30 = m.regs.X30
  saved : Saved m st.data
  filled : BytesAt st.data.dmem m.regs.X0.toBitVec ((List.range i).map (fill m))
  same : SameOutside m.dmem st.data.dmem (InRange m.regs.X0.toBitVec i)

/-- `memset`'s postcondition, reached. -/
abbrev Post (st : MachineState) : Prop := st.pc = retOf m ∧ MemsetPost m st.data

variable {m}

theorem infix_of {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j) (hne : b ≠ [])
    (hp : Placed code k) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- From `.LMemset_7`: `ret`. -/
theorem finish {st : MachineState} (hp : Placed code k) (hd : Done m k st) :
    Eventually (step1 Host.exe) (Post m) st := by
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) e8 (Env.wf_nil _) hd.pc (match_nil _)
    fun st' hm' hpc' => .done _ ⟨?_, ?_⟩
  · have h30 : st'.data.regs.X30 = st.data.regs.X30 :=
      Match.reg_eq (r := .X30) (match_nil _) hm' rfl rfl
    simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, h30, hd.x30]
  · have hdm : st'.data.dmem = st.data.dmem := hm'.dmem_eq (Env.wf_nil _) rfl
    refine ⟨(Match.reg_eq (r := .X0) (match_nil _) hm' rfl rfl).trans hd.x0, ?_, ?_, ?_⟩
    · rw [hdm, replicate_eq]
      exact hd.filled
    · intro p hp'
      rw [hdm]
      exact hd.same p hp'
    · exact hd.saved.trans (Match.saved (match_nil _) hm' (Env.wf_nil _) rfl rfl)

/-- The word loop's environment after `i` bytes: the next destination word. -/
abbrev wordEnv (m d : MachineData) (i : Nat) : Env :=
  Env.ofMachine d [(m.regs.X0.toBitVec + BitVec.ofNat 64 i, 8)]

/-- **One word**: from the word loop's head after `i` bytes, the next word filled, back at the head
or done. -/
theorem word_step (hp : Placed code k) (hpre : MemsetPre m) (h8 : m.regs.X2.toNat % 8 = 0)
    {i : Nat} {st : MachineState} (hI : WInv m k i st) :
    Eventually (step1 Host.exe) (fun st' => Post m st' ∨ WInv m k (i + 8) st') st := by
  obtain ⟨hmd, hnd⟩ := hpre
  have hle : i + 8 ≤ m.regs.X2.toNat := by have := hI.i8; have := hI.lt; omega
  have hn64 := m.regs.X2.toNat_lt
  unfold NoWrap at hnd
  have hkept := hI.saved.2.2
  have hdi : (m.regs.X0.toBitVec + BitVec.ofNat 64 i).toNat = m.regs.X0.toBitVec.toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  have hx9i : st.data.regs.X9.toBitVec = BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hI.x9
  let env := wordEnv m st.data i
  have hwf : env.WF := Env.wf_of
    ⟨⟨fun j hj => by rw [addr_add]; exact Mapped.of_kept hmd hkept _ (by omega),
      by unfold NoWrap; simp only; omega⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hm : Match env sWord st.data := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    trivial trivial trivial
    ⟨show (idx .X0 .X9).eval env = env.base 0 + BitVec.ofInt 64 0 by
      rw [eval_idx, Env.base_ofMachine _ _ _ rfl]
      simp [env, Reg64s.getXReg, hI.x0, hx9i], trivial⟩
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) e7 hwf hI.pc hm fun st' hm' hpc' => ?_
  have hx0 : st'.data.regs.X0 = m.regs.X0 := (Match.reg_eq (r := .X0) hm hm' rfl rfl).trans hI.x0
  have hx2 : st'.data.regs.X2 = m.regs.X2 := (Match.reg_eq (r := .X2) hm hm' rfl rfl).trans hI.x2
  have hx8 : st'.data.regs.X8 = st.data.regs.X8 := Match.reg_eq (r := .X8) hm hm' rfl rfl
  have hx30 : st'.data.regs.X30 = m.regs.X30 :=
    (Match.reg_eq (r := .X30) hm hm' rfl rfl).trans hI.x30
  have hx9 : st'.data.regs.X9.toNat = i + 8 := by
    have h := hm'.regs .X9 _ rfl
    sym_simp at h
    show (st'.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [h, BitVec.toNat_add, Env.ofMachine_regs]
    show (st.data.regs.X9.toBitVec.toNat + 8 % 2 ^ 64) % 2 ^ 64 = i + 8
    rw [UInt64.toNat_toBitVec, hI.x9]
    omega
  have hsaved : Saved m st'.data := hI.saved.trans (Match.saved hm hm' hwf rfl rfl)
  have hw : ∀ j < 8, st'.data.dmem.get? (m.regs.X0.toBitVec + BitVec.ofNat 64 (i + j)) =
      some (fill m (i + j)) := by
    intro j hj
    have h := hm'.bytesAt_write (r := 0) (o := 0) (n := 8) (b := m.regs.X0.toBitVec + BitVec.ofNat 64 i)
      (sz := 8) rfl (by omega) (v := .reg .X8) (fun j hj => findWrite_head hj) j (by simp; omega)
    simp only [List.getElem_map, List.getElem_range, addr_add3] at h
    rw [h]
    exact congrArg some (hI.x8 j hj)
  have hout : ∀ a : BitVec 64, ¬(m.regs.X0.toBitVec.toNat + i ≤ a.toNat ∧
      a.toNat < m.regs.X0.toBitVec.toNat + i + 8) → st'.data.dmem.get? a = st.data.dmem.get? a := by
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
  obtain ⟨hc', hs'⟩ := extend (f := fill m) hnd hle hI.filled hI.same hw hout
  simp only [PcOk] at hpc'
  split at hpc'
  · rename_i hc
    have hlt : i + 8 < m.regs.X2.toNat := by
      sym_simp at hc
      simp only [env, BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, Env.ofMachine_regs,
        UInt64.toNat_toBitVec, BitVec.toNat_ofNat, MemWidth.bits, Reg64s.getXReg, hI.x9,
        hI.x2] at hc
      omega
    refine .done _ (Or.inr ⟨?_, by have := hI.i8; omega, hlt, hx0, hx2, by rw [hx8]; exact hI.x8,
      hx9, hx30, hsaved, hc', hs'⟩)
    rw [hpc']
    exact hp.label NativeRustcArm.Common.Memset.label_6_at
  · rename_i hc
    have hn : i + 8 = m.regs.X2.toNat := by
      sym_simp at hc
      simp only [env, BitVec.ult, BitVec.toNat_add, Env.ofMachine_regs,
        UInt64.toNat_toBitVec, BitVec.toNat_ofNat, MemWidth.bits, Reg64s.getXReg, hI.x9, hI.x2,
        Bool.not_eq_true, decide_eq_false_iff_not] at hc
      omega
    rw [hn] at hc' hs'
    exact Eventually.mono (finish hp ⟨hpc', hx0, hx30, hsaved, hc', hs'⟩) fun _ h => Or.inl h

/-- The byte loop's environment after `i` bytes: the next destination byte. -/
abbrev byteEnv (m d : MachineData) (i : Nat) : Env :=
  Env.ofMachine d [(m.regs.X0.toBitVec + BitVec.ofNat 64 i, 1)]

/-- **One byte**: from the byte loop's head after `i` bytes, the next byte filled, back at the head
or done. -/
theorem byte_step (hp : Placed code k) (hpre : MemsetPre m) {i : Nat} {st : MachineState}
    (hI : BInv m k i st) :
    Eventually (step1 Host.exe) (fun st' => Post m st' ∨ BInv m k (i + 1) st') st := by
  obtain ⟨hmd, hnd⟩ := hpre
  have hle : i + 1 ≤ m.regs.X2.toNat := hI.lt
  unfold NoWrap at hnd
  have hkept := hI.saved.2.2
  have hdi : (m.regs.X0.toBitVec + BitVec.ofNat 64 i).toNat = m.regs.X0.toBitVec.toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  let env := byteEnv m st.data i
  have hwf : env.WF := Env.wf_of
    ⟨⟨fun j hj => by rw [addr_add]; exact Mapped.of_kept hmd hkept _ (by omega),
      by unfold NoWrap; simp only; omega⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hm : Match env sByte st.data := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨show (st.data.regs.getXReg .X8).toBitVec = (Sym.ptr 0 0).eval env by
      simp [Sym.eval, env]
      exact hI.x8, trivial⟩
    trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) e3 hwf hI.pc hm fun st' hm' hpc' => ?_
  have hx0 : st'.data.regs.X0 = m.regs.X0 := (Match.reg_eq (r := .X0) hm hm' rfl rfl).trans hI.x0
  have hx1 : st'.data.regs.X1 = m.regs.X1 := (Match.reg_eq (r := .X1) hm hm' rfl rfl).trans hI.x1
  have hx30 : st'.data.regs.X30 = m.regs.X30 :=
    (Match.reg_eq (r := .X30) hm hm' rfl rfl).trans hI.x30
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
      some (fill m (i + j)) := by
    intro j hj
    have h := hm'.bytesAt_write (r := 0) (o := 0) (n := 1) (b := m.regs.X0.toBitVec + BitVec.ofNat 64 i)
      (sz := 1) rfl (by omega) (v := .reg .X1) (fun j hj => findWrite_head hj) j (by simp; omega)
    simp only [List.getElem_map, List.getElem_range, addr_add3] at h
    rw [h]
    congr 1
    obtain rfl : j = 0 := by omega
    show byteOf (st.data.regs.getXReg .X1).toBitVec 0 = m.regs.X1.toUInt8
    rw [← hI.x1]
    show UInt8.ofNat (st.data.regs.X1.toBitVec.toNat / 2 ^ (8 * 0)) = _
    rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, UInt64.toNat_toBitVec]
    rfl
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
  obtain ⟨hc', hs'⟩ := extend (f := fill m) hnd hle hI.filled hI.same hw hout
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
    exact hp.label NativeRustcArm.Common.Memset.label_3_at
  · rename_i hc
    have hn : i + 1 = m.regs.X2.toNat := by
      rw [hce] at hc
      simp at hc
      have := hI.lt
      omega
    rw [hn] at hc' hs'
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) e4 (Env.wf_nil _) hpc' (match_nil _)
      fun st'' hm'' hpc'' => ?_
    have hd : st''.data.dmem = st'.data.dmem := hm''.dmem_eq (Env.wf_nil _) rfl
    refine Eventually.mono (finish hp ⟨?_, ?_, ?_, ?_, ?_, ?_⟩) fun _ h => Or.inl h
    · simp only [PcOk] at hpc''
      rw [hpc'']
      exact hp.label NativeRustcArm.Common.Memset.label_7_at
    · exact (Match.reg_eq (r := .X0) (match_nil _) hm'' rfl rfl).trans hx0
    · exact (Match.reg_eq (r := .X30) (match_nil _) hm'' rfl rfl).trans hx30
    · exact hsaved.trans (Match.saved (match_nil _) hm'' (Env.wf_nil _) rfl rfl)
    · rw [hd]
      exact hc'
    · intro p hp'
      rw [hd]
      exact hs' p hp'

/-- The word loop, from its head after `i` bytes. -/
theorem word_loop (hp : Placed code k) (hpre : MemsetPre m) (h8 : m.regs.X2.toNat % 8 = 0)
    {i : Nat} {st : MachineState} (hI : WInv m k i st) : Eventually (step1 Host.exe) (Post m) st :=
  Sym.loop (fun μ st => ∃ i, μ = m.regs.X2.toNat - i ∧ WInv m k i st)
    (fun _ _ ⟨i, hμ, hI⟩ => Eventually.mono (word_step hp hpre h8 hI) fun st' h =>
      h.imp_right fun h' => ⟨m.regs.X2.toNat - (i + 8), by have := hI.lt; omega, i + 8, rfl, h'⟩)
    ⟨i, rfl, hI⟩

/-- The byte loop, from its head after `i` bytes. -/
theorem byte_loop (hp : Placed code k) (hpre : MemsetPre m) {i : Nat} {st : MachineState}
    (hI : BInv m k i st) : Eventually (step1 Host.exe) (Post m) st :=
  Sym.loop (fun μ st => ∃ i, μ = m.regs.X2.toNat - i ∧ BInv m k i st)
    (fun _ _ ⟨i, hμ, hI⟩ => Eventually.mono (byte_step hp hpre hI) fun st' h =>
      h.imp_right fun h' => ⟨m.regs.X2.toNat - (i + 1), by have := hI.lt; omega, i + 1, rfl, h'⟩)
    ⟨i, rfl, hI⟩

/-- **`memset` meets its contract.** -/
theorem memset_spec (hp : Placed code k) : Spec (label NativeRustcArm.Common.Memset.entryLabel) MemsetPre MemsetPost := by
  intro m hpre
  rw [hp.label NativeRustcArm.Common.Memset.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) e0 (Env.wf_nil m) (match_nil m)
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
    have h8 : m.regs.X2.toNat % 8 = 0 := align_or2 hal
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) e5 (Env.wf_nil _)
      (hpc0.trans (hp.label NativeRustcArm.Common.Memset.label_4_at)) (match_nil _) fun st5 hm5 hpc5 => ?_
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
      refine finish hp ⟨hpc5.trans (hp.label NativeRustcArm.Common.Memset.label_7_at), hy0, hy30, hs5, ?_, ?_⟩
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
      refine exec_at (infix_of b6_in_code (by simp [b6]) hp) e6 (Env.wf_nil _) hpc5 (match_nil _)
        fun st6 hm6 hpc6 => ?_
      have hd6 : st6.data.dmem = m.dmem := (hm6.dmem_eq (Env.wf_nil _) rfl).trans hd5
      refine word_loop (i := 0) hp hpre h8 ⟨hpc6, rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Match.reg_eq (r := .X0) (match_nil _) hm6 rfl rfl).trans hy0
      · exact (Match.reg_eq (r := .X2) (match_nil _) hm6 rfl rfl).trans hy2
      · intro j hj
        have h := hm6.regs .X8 _ rfl
        show byteOf (st6.data.regs.getXReg .X8).toBitVec j = _
        rw [h]
        show byteOf (BinOp.apply .mul .W64 (BinOp.apply .and .W32 (st5.data.regs.getXReg .X1).toBitVec
          (BitVec.ofNat 64 255)) (BitVec.ofNat 64 72340172838076673)) j = _
        rw [byteOf_word _ hj]
        show _ = UInt8.ofNat m.regs.X1.toNat
        rw [← hy1]
        rfl
      · have h := hm6.regs .X9 _ rfl
        show (st6.data.regs.getXReg .X9).toBitVec.toNat = 0
        rw [h]
        rfl
      · exact (Match.reg_eq (r := .X30) (match_nil _) hm6 rfl rfl).trans hy30
      · exact hs5.trans (Match.saved (match_nil _) hm6 (Env.wf_nil _) rfl rfl)
      · exact bytesAt_nil _ _
      · exact sameOutside_of_eq hd6 _
  · -- the byte loop
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) e1 (Env.wf_nil _) hpc0 (match_nil _)
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
      refine finish hp ⟨hpc1.trans (hp.label NativeRustcArm.Common.Memset.label_7_at), hy0, hy30, hs1, ?_, ?_⟩
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
      refine exec_at (infix_of b2_in_code (by simp [b2]) hp) e2 (Env.wf_nil _) hpc1 (match_nil _)
        fun st2 hm2 hpc2 => ?_
      have hd2 : st2.data.dmem = m.dmem := (hm2.dmem_eq (Env.wf_nil _) rfl).trans hd1
      refine byte_loop (i := 0) hp hpre ⟨hpc2, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Match.reg_eq (r := .X0) (match_nil _) hm2 rfl rfl).trans hy0
      · exact (Match.reg_eq (r := .X1) (match_nil _) hm2 rfl rfl).trans hy1
      · rw [Nat.sub_zero, ← hy2]
        exact congrArg UInt64.toNat (Match.reg_eq (r := .X2) (match_nil _) hm2 rfl rfl)
      · rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, ← hy0]
        exact hm2.regs .X8 _ rfl
      · exact (Match.reg_eq (r := .X30) (match_nil _) hm2 rfl rfl).trans hy30
      · exact hs1.trans (Match.saved (match_nil _) hm2 (Env.wf_nil _) rfl rfl)
      · exact bytesAt_nil _ _
      · exact sameOutside_of_eq hd2 _

end

end NativeRustcArm.Mem.Memset
