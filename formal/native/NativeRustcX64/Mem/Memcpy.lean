module

public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.Mem.MemcpyBlocks

/-!
# `memcpy` meets its contract

`memcpy_spec`: rustc's x86-64 `memcpy`, placed anywhere in the program, meets
`MemcpyPre`/`MemcpyPost`. Its blocks run by the symbolic executor
(`NativeRustcX64.Mem.MemcpyBlocks`), each from a fresh environment of the machine state it starts
in; the word loop (operands and length multiples of 8) and the byte loop, `rcx` the offset in
both, by invariants (`WInv`, `BInv`) on the machine state at their heads, each iteration copying
the next word or byte; the final `retq` by `ret_then`.
-/

namespace NativeRustcX64.Mem.Memcpy

open NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcX64.Common.Memcpy

public section

variable [ElfHost] {sec k : Nat} (m : MachineData)

/-- The destination. -/
abbrev dst : BitVec 64 := m.regs.get64 .rdi
/-- The source. -/
abbrev src : BitVec 64 := m.regs.get64 .rsi
/-- The length. -/
abbrev len : Nat := (m.regs.get64 .rdx).toNat

/-- `memcpy` done, at `.LMemcpy_7`. -/
structure Done (sec k : Nat) (st : MachineState) : Prop where
  pc : st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Memcpy.b8Offset)
  rax : st.data.regs.get64 .rax = dst m
  rsp : st.data.regs.get64 .rsp = rspOf m
  saved : Saved m st.data
  copied : BytesAt st.data.dmem (dst m) (bytesOf m.dmem (src m) (len m))
  same : SameOutside m.dmem st.data.dmem (InRange (dst m) (len m))

/-- The loops' common part after `i` bytes. -/
structure Loop (k i : Nat) (st : MachineState) : Prop where
  lt : i < len m
  rax : st.data.regs.get64 .rax = dst m
  rsi : st.data.regs.get64 .rsi = src m
  rdx : st.data.regs.get64 .rdx = m.regs.get64 .rdx
  rcx : (st.data.regs.get64 .rcx).toNat = i
  rsp : st.data.regs.get64 .rsp = rspOf m
  saved : Saved m st.data
  copied : BytesAt st.data.dmem (dst m) (bytesOf m.dmem (src m) i)
  same : SameOutside m.dmem st.data.dmem (InRange (dst m) i)

/-- The word loop's head after `i` bytes. -/
structure WInv (sec k i : Nat) (st : MachineState) : Prop extends Loop m k i st where
  pc : st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Memcpy.b7Offset)
  i8 : i % 8 = 0

/-- The byte loop's head after `i` bytes. -/
structure BInv (sec k i : Nat) (st : MachineState) : Prop extends Loop m k i st where
  pc : st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Memcpy.b3Offset)

/-- `memcpy`'s postcondition, reached. -/
abbrev Post (st : MachineState) : Prop :=
  st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧ MemcpyPost m st.data

variable {m}

omit [ElfHost] in
/-- `memcpy`'s precondition's parts, in the names of this file. -/
theorem pre_parts (h : MemcpyPre m) : StackOk m 0 ∧ Mapped m.dmem (dst m) (len m) ∧
    Mapped m.dmem (src m) (len m) ∧ NoWrap (dst m) (len m) ∧ NoWrap (src m) (len m) ∧
    Apart (dst m) (len m) (src m) (len m) ∧ Apart (dst m) (len m) (rspOf m) 8 := h

theorem infix_of {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j) (hne : b ≠ [])
    (hp : PlacedIn code sec k) : b.IsInfixAt (ElfHost.sectionProg sec) (k + j) :=
  hb.trans hp.1 hne

/-- From `.LMemcpy_7`: `retq`. -/
theorem finish {st : MachineState} (hp : PlacedIn code sec k) (hpre : MemcpyPre m)
    (hd : Done m sec k st) :
    Eventually (elfStep1 ElfHost.exe) (Post m) st := by
  obtain ⟨hstk, -, -, hnd, -, -, hsp⟩ := pre_parts hpre
  have hslot : ∀ i < 8, st.data.dmem.get? (rspOf m + BitVec.ofNat 64 i) =
      m.dmem.get? (rspOf m + BitVec.ofNat 64 i) := by
    intro i hi
    apply hd.same
    unfold NoWrap at hnd
    unfold Apart at hsp
    rw [inRange_iff hnd, toNat_add_ofNat _ _ (by have := hstk.2.1; omega)]
    omega
  refine Eventually.mono_elf (ret_then_elf (infix_of b8_in_code (by simp [b8]) hp) e8 rfl rfl rfl
    (by decide) hd.pc hstk hd.rsp hslot) fun st' ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1, h2, h4.trans hd.rax, ?_, ?_, hd.saved.trans h5⟩
  · rw [h3]
    exact hd.copied
  · intro p hp'
    rw [h3]
    exact hd.same p hp'

omit [ElfHost] in
/-- A source byte, unchanged while the destination's first `i` bytes are written. -/
theorem src_same (hpre : MemcpyPre m) {d : DataMem} {i j : Nat} (hi : i ≤ len m)
    (hj : j < len m) (hs : SameOutside m.dmem d (InRange (dst m) i)) :
    d.get? (src m + BitVec.ofNat 64 j) = m.dmem.get? (src m + BitVec.ofNat 64 j) := by
  obtain ⟨-, -, -, hnd, hns, hap, -⟩ := pre_parts hpre
  unfold NoWrap at hnd hns
  unfold Apart at hap
  apply hs
  rw [inRange_iff (by omega), toNat_add_ofNat _ _ (by omega)]
  omega

omit [ElfHost] in
theorem ofNat_of_toNat {x : BitVec 64} {i : Nat} (h : x.toNat = i) : x = BitVec.ofNat 64 i := by
  subst h
  exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm

omit [ElfHost] in
/-- The loops' environment after `i` bytes, its `w` destination and source bytes as regions, is
well formed. -/
theorem loopEnv_wf (hpre : MemcpyPre m) {d : MachineData} (hk : Kept m.dmem d.dmem) {i w : Nat}
    (hw : 0 < w) (hle : i + w ≤ len m) :
    (Env.ofMachine d [(dst m + BitVec.ofNat 64 i, w), (src m + BitVec.ofNat 64 i, w)]).WF := by
  obtain ⟨-, hmd, hms, hnd, hns, hap, -⟩ := pre_parts hpre
  unfold NoWrap at hnd hns
  unfold Apart at hap
  have hdi : (dst m + BitVec.ofNat 64 i).toNat = (dst m).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  have hsi : (src m + BitVec.ofNat 64 i).toNat = (src m).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  refine Env.wf_of ⟨⟨fun j hj => ?_, ?_⟩, ⟨fun j hj => ?_, ?_⟩, trivial⟩
    (List.pairwise_pair.mpr ?_)
  · rw [Env.ofMachine_mem0, addr_add]
    exact Mapped.of_kept hmd hk _ (by simp only at hj; omega)
  · show (dst m + BitVec.ofNat 64 i).toNat + w ≤ 2 ^ 64
    omega
  · rw [Env.ofMachine_mem0, addr_add]
    exact Mapped.of_kept hms hk _ (by simp only at hj; omega)
  · show (src m + BitVec.ofNat 64 i).toNat + w ≤ 2 ^ 64
    omega
  · show (dst m + BitVec.ofNat 64 i).toNat + w ≤ (src m + BitVec.ofNat 64 i).toNat ∨
      (src m + BitVec.ofNat 64 i).toNat + w ≤ (dst m + BitVec.ofNat 64 i).toNat
    omega

/-- The aliases of the loops' states hold in their environment. -/
theorem loopAliases {d : MachineData} {i w : Nat} {st : MachineState} (hL : Loop m k i st)
    (hd : d = st.data) :
    AllOf (fun p : Sym × Nat × Int => p.1.eval (Env.ofMachine d
      [(dst m + BitVec.ofNat 64 i, w), (src m + BitVec.ofNat 64 i, w)]) =
      (Env.ofMachine d [(dst m + BitVec.ofNat 64 i, w), (src m + BitVec.ofNat 64 i, w)]).base
        p.2.1 + BitVec.ofInt 64 p.2.2) [(ix .rax .rcx, (0, 0)), (ix .rsi .rcx, (1, 0))] := by
  subst hd
  have hrcx := ofNat_of_toNat hL.rcx
  refine ⟨?_, ?_, trivial⟩ <;>
    simp [eval_ix, Env.ofMachine_regs, hL.rax, hL.rsi, hrcx]

/-- The symbolic register `r` of a block from a state where it is its atom, kept. -/
theorem keep {env : Env} {S₀ S : SState} {m₀ m₁ : MachineData} (hm₀ : Match env S₀ m₀)
    (hm : Match env S m₁) (r : Reg64) (h₀ : S₀.reg r = some (.reg r))
    (h : S.reg r = some (.reg r)) : m₁.regs.get64 r = m₀.regs.get64 r :=
  Match.reg_eq hm₀ hm h₀ h

omit [ElfHost] in
theorem toNat_add_lit {x : BitVec 64} {i c : Nat} (hx : x.toNat = i) (h : i + c < 2 ^ 64) :
    (BitVec.ofNat 64 c + x).toNat = i + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, hx]
  omega

omit [ElfHost] in
theorem toNat_add_lit' {x : BitVec 64} {i c : Nat} (hx : x.toNat = i) (h : i + c < 2 ^ 64) :
    (x + BitVec.ofNat 64 c).toNat = i + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, hx]
  omega

/-- **One word**: from the word loop's head after `i` bytes, the next word copied, back at the head
or done. -/
theorem word_step (hp : PlacedIn code sec k) (hpre : MemcpyPre m) (h8 : len m % 8 = 0) {i : Nat}
    {st : MachineState} (hI : WInv m sec k i st) :
    Eventually (elfStep1 ElfHost.exe) (fun st' => Post m st' ∨ WInv m sec k (i + 8) st') st := by
  have hle : i + 8 ≤ len m := by have := hI.i8; have := hI.lt; omega
  obtain ⟨-, -, -, hnd, hns, -, -⟩ := pre_parts hpre
  unfold NoWrap at hnd hns
  have hlen : len m < 2 ^ 64 := (m.regs.get64 .rdx).isLt
  have hdi : (dst m + BitVec.ofNat 64 i).toNat = (dst m).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  let env := Env.ofMachine st.data [(dst m + BitVec.ofNat 64 i, 8), (src m + BitVec.ofNat 64 i, 8)]
  have hwf : env.WF := loopEnv_wf hpre hI.saved.2 (by decide) hle
  have hm : Match env sWord st.data := match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial
    trivial (loopAliases hI.toLoop rfl)
  refine exec_at_elf (infix_of b7_in_code (by simp [b7]) hp) e7 hwf (fun _ h => nomatch h) hI.pc hm
    fun st' hm' hpc' => ?_
  have hrax := (keep hm hm' .rax rfl rfl).trans hI.rax
  have hrsi := (keep hm hm' .rsi rfl rfl).trans hI.rsi
  have hrdx := (keep hm hm' .rdx rfl rfl).trans hI.rdx
  have hrsp := (keep hm hm' .rsp rfl rfl).trans hI.rsp
  have hrcx : (st'.data.regs.get64 .rcx).toNat = i + 8 := by
    rw [hm'.regs .rcx _ rfl]
    exact toNat_add_lit hI.rcx (by omega)
  have hsaved : Saved m st'.data := hI.saved.trans (Match.saved hm hm' hwf rfl (by decide))
  -- the word written
  have hw : ∀ j < 8, st'.data.dmem.get? (dst m + BitVec.ofNat 64 (i + j)) =
      some ((m.dmem.get? (src m + BitVec.ofNat 64 (i + j))).getD 0) := by
    intro j hj
    have h := hm'.bytesAt_write (r := 0) (o := 0) (n := 8) (b := dst m + BitVec.ofNat 64 i)
      (sz := 8) rfl (by omega) (v := .load 1 0 8) (fun j hj => findWrite_head hj) j
      (by simp; omega)
    simp only [List.getElem_map, List.getElem_range] at h
    rw [addr_add, addr_add, Nat.zero_add] at h
    rw [h]
    congr 1
    show byteOf (env.load 1 0 8) j = _
    rw [byteOf_load hj (by decide), Env.base_ofMachine _ _ _ _ rfl, Env.ofMachine_mem0,
      Nat.zero_add, addr_add, src_same hpre (by omega) (by omega) hI.same]
  have hout : ∀ a : BitVec 64, ¬((dst m).toNat + i ≤ a.toNat ∧ a.toNat < (dst m).toNat + i + 8) →
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
  obtain ⟨hc', hs'⟩ := extend
    (f := fun j => (m.dmem.get? (src m + BitVec.ofNat 64 j)).getD 0) hnd hle hI.copied hI.same hw
    hout
  have hce : (SBool.cmp .ult .W64 (.bin .add .W64 (.lit 8) (.reg .rcx)) (.reg .rdx)).eval env =
      decide (i + 8 < len m) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.ult,
      Env.ofMachine_regs, env]
    rw [toNat_add_lit hI.rcx (by omega), hI.rdx]
  simp only [PcOk] at hpc'
  split at hpc'
  · rename_i hc
    have hlt : i + 8 < len m := by rw [hce] at hc; simpa using hc
    refine .done _ (Or.inr ⟨⟨hlt, hrax, hrsi, hrdx, hrcx, hrsp, hsaved, hc', hs'⟩, ?_,
      by have := hI.i8; omega⟩)
    rw [hpc']
    exact hp.label NativeRustcX64.Common.Memcpy.label_6_at
  · rename_i hc
    have hn : i + 8 = len m := by
      rw [hce] at hc
      simp at hc
      omega
    rw [hn] at hc' hs'
    exact Eventually.mono_elf (finish hp hpre ⟨hpc', hrax, hrsp, hsaved, hc', hs'⟩) fun _ h => Or.inl h

omit [ElfHost] in
/-- The byte `movzbl` then `movb` copy. -/
theorem byteOf_movzb (x : BitVec 64) :
    byteOf (UnOp.apply .trunc .W8 (UnOp.apply (.zext .W8) .W32 x)) 0 = byteOf x 0 := by
  simp only [byteOf_mod, UnOp.apply, toNat_ext, toNat_low, BitVec.zeroExtend,
    BitVec.toNat_setWidth, Width.bits]
  congr 1
  omega

/-- **One byte**: from the byte loop's head after `i` bytes, the next byte copied, back at the head
or done. -/
theorem byte_step (hp : PlacedIn code sec k) (hpre : MemcpyPre m) {i : Nat} {st : MachineState}
    (hI : BInv m sec k i st) :
    Eventually (elfStep1 ElfHost.exe) (fun st' => Post m st' ∨ BInv m sec k (i + 1) st') st := by
  have hle : i + 1 ≤ len m := hI.lt
  obtain ⟨-, -, -, hnd, hns, -, -⟩ := pre_parts hpre
  unfold NoWrap at hnd hns
  have hlen : len m < 2 ^ 64 := (m.regs.get64 .rdx).isLt
  have hdi : (dst m + BitVec.ofNat 64 i).toNat = (dst m).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  let env := Env.ofMachine st.data [(dst m + BitVec.ofNat 64 i, 1), (src m + BitVec.ofNat 64 i, 1)]
  have hwf : env.WF := loopEnv_wf hpre hI.saved.2 (by decide) hle
  have hm : Match env sByte st.data := match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial
    trivial (loopAliases hI.toLoop rfl)
  refine exec_at_elf (infix_of b3_in_code (by simp [b3]) hp) e3 hwf (fun _ h => nomatch h) hI.pc hm
    fun st' hm' hpc' => ?_
  have hrax := (keep hm hm' .rax rfl rfl).trans hI.rax
  have hrsi := (keep hm hm' .rsi rfl rfl).trans hI.rsi
  have hrdx := (keep hm hm' .rdx rfl rfl).trans hI.rdx
  have hrsp := (keep hm hm' .rsp rfl rfl).trans hI.rsp
  have hrcx : (st'.data.regs.get64 .rcx).toNat = i + 1 := by
    rw [hm'.regs .rcx _ rfl]
    exact toNat_add_lit' hI.rcx (by omega)
  have hsaved : Saved m st'.data := hI.saved.trans (Match.saved hm hm' hwf rfl (by decide))
  have hw : ∀ j < 1, st'.data.dmem.get? (dst m + BitVec.ofNat 64 (i + j)) =
      some ((m.dmem.get? (src m + BitVec.ofNat 64 (i + j))).getD 0) := by
    intro j hj
    have h := hm'.bytesAt_write (r := 0) (o := 0) (n := 1) (b := dst m + BitVec.ofNat 64 i)
      (sz := 1) rfl (by omega) (fun j hj => findWrite_head hj) j (by simp; omega)
    simp only [List.getElem_map, List.getElem_range] at h
    rw [addr_add, addr_add, Nat.zero_add] at h
    rw [h]
    congr 1
    obtain rfl : j = 0 := by omega
    show byteOf (UnOp.apply .trunc .W8 (UnOp.apply (.zext .W8) .W32 (env.load 1 0 1))) 0 = _
    rw [byteOf_movzb, byteOf_load (by decide) (by decide), Env.base_ofMachine _ _ _ _ rfl,
      Env.ofMachine_mem0, addr_add, src_same hpre (by omega) (by omega) hI.same]
  have hout : ∀ a : BitVec 64, ¬((dst m).toNat + i ≤ a.toNat ∧ a.toNat < (dst m).toNat + i + 1) →
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
  obtain ⟨hc', hs'⟩ := extend
    (f := fun j => (m.dmem.get? (src m + BitVec.ofNat 64 j)).getD 0) hnd hle hI.copied hI.same hw
    hout
  have hce :
      (SBool.not (.cmp .eq .W64 (.reg .rdx) (.bin .add .W64 (.reg .rcx) (.lit 1)))).eval env =
      !decide (len m = i + 1) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs, env]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, hI.rdx]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [toNat_add_lit' hI.rcx (by omega)] at this
      exact this
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [toNat_add_lit' hI.rcx (by omega)]
      exact h
  simp only [PcOk] at hpc'
  split at hpc'
  · rename_i hc
    have hlt : i + 1 < len m := by
      rw [hce] at hc
      simp at hc
      omega
    refine .done _ (Or.inr ⟨⟨hlt, hrax, hrsi, hrdx, hrcx, hrsp, hsaved, hc', hs'⟩, ?_⟩)
    rw [hpc']
    exact hp.label NativeRustcX64.Common.Memcpy.label_3_at
  · rename_i hc
    have hn : i + 1 = len m := by
      rw [hce] at hc
      simp at hc
      omega
    rw [hn] at hc' hs'
    refine exec_at_elf (infix_of b4_in_code (by simp [b4]) hp) e4 (Env.wf_nil _)
      (fun _ h => nomatch h) hpc' (match_nil _) fun st'' hm'' hpc'' => ?_
    have hd : st''.data.dmem = st'.data.dmem := hm''.dmem_eq (Env.wf_nil _) rfl
    refine Eventually.mono_elf (finish hp hpre ⟨?_, ?_, ?_, ?_, ?_, ?_⟩) fun _ h => Or.inl h
    · simp only [PcOk] at hpc''
      rw [hpc'']
      exact hp.label NativeRustcX64.Common.Memcpy.label_7_at
    · exact (keep (match_nil _) hm'' .rax rfl rfl).trans hrax
    · exact (keep (match_nil _) hm'' .rsp rfl rfl).trans hrsp
    · exact hsaved.trans (Match.saved (match_nil _) hm'' (Env.wf_nil _) rfl (by decide))
    · rw [hd]
      exact hc'
    · intro p hp'
      rw [hd]
      exact hs' p hp'

/-- The word loop, from its head after `i` bytes. -/
theorem word_loop (hp : PlacedIn code sec k) (hpre : MemcpyPre m) (h8 : len m % 8 = 0)
    {i : Nat} {st : MachineState} (hI : WInv m sec k i st) :
    Eventually (elfStep1 ElfHost.exe) (Post m) st :=
  Sym.loop (fun μ st => ∃ i, μ = len m - i ∧ WInv m sec k i st)
    (fun _ _ ⟨i, hμ, hI⟩ => Eventually.mono_elf (word_step hp hpre h8 hI) fun st' h =>
      h.imp_right fun h' => ⟨len m - (i + 8), by have := hI.lt; omega, i + 8, rfl, h'⟩)
    ⟨i, rfl, hI⟩

/-- The byte loop, from its head after `i` bytes. -/
theorem byte_loop (hp : PlacedIn code sec k) (hpre : MemcpyPre m) {i : Nat} {st : MachineState}
    (hI : BInv m sec k i st) : Eventually (elfStep1 ElfHost.exe) (Post m) st :=
  Sym.loop (fun μ st => ∃ i, μ = len m - i ∧ BInv m sec k i st)
    (fun _ _ ⟨i, hμ, hI⟩ => Eventually.mono_elf (byte_step hp hpre hI) fun st' h =>
      h.imp_right fun h' => ⟨len m - (i + 1), by have := hI.lt; omega, i + 1, rfl, h'⟩)
    ⟨i, rfl, hI⟩

/-- **`memcpy` meets its contract** under `ElfHost`. -/
theorem memcpy_spec_elf (hp : PlacedIn code sec k) :
    ElfSpec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost := by
  intro m hpre
  rw [hp.label NativeRustcX64.Common.Memcpy.entry_at]
  refine exec_then_elf (infix_of b0_in_code (by simp [b0]) hp) e0 (Env.wf_nil m)
    (fun _ h => nomatch h) (match_nil m) fun st0 hm0 hpc0 => ?_
  have hd0 : st0.data.dmem = m.dmem := hm0.dmem_eq (Env.wf_nil _) rfl
  have hx1 := keep (match_nil m) hm0 .rsi rfl rfl
  have hx2 := keep (match_nil m) hm0 .rdx rfl rfl
  have hsp := keep (match_nil m) hm0 .rsp rfl rfl
  have hax : st0.data.regs.get64 .rax = dst m := by
    rw [hm0.regs .rax _ rfl]
    rfl
  have hs0 : Saved m st0.data := Match.saved (match_nil m) hm0 (Env.wf_nil m) rfl (by decide)
  /- From a state `st` after `b0`, its registers and memory as there: a block `ds` from `sNone`
  keeping RAX, RSI, RDX, RSP and the callee-saved registers. -/
  have step {ds : List Directive} {j : Nat} {S' : SState} {x : Exit} {st : MachineState}
      {R : MachineState → Prop} (hj : ds.IsInfixAt (ElfHost.sectionProg sec) (k + j))
      (hx : exec ds sNone = some (S', x)) (hxc : ∀ l, x ≠ .call l)
      (hrax : S'.reg .rax = some (.reg .rax)) (hrsi : S'.reg .rsi = some (.reg .rsi))
      (hrdx : S'.reg .rdx = some (.reg .rdx)) (hrsp : S'.reg .rsp = some (.reg .rsp))
      (hmem : S'.mem = []) (hkeeps : keeps sNone S' = true)
      (hpc : st.pc = ElfHost.addrOf sec (k + j))
      (hst : st.data.regs.get64 .rax = dst m ∧ st.data.regs.get64 .rsi = src m ∧
        st.data.regs.get64 .rdx = m.regs.get64 .rdx ∧ st.data.regs.get64 .rsp = rspOf m ∧
        Saved m st.data ∧ st.data.dmem = m.dmem)
      (cont : ∀ st', Match (Env.ofMachine st.data []) S' st'.data →
        PcOk (Env.ofMachine st.data []) x (ElfHost.addrOf sec (k + j + ds.length)) st' →
        st'.data.regs.get64 .rax = dst m ∧ st'.data.regs.get64 .rsi = src m ∧
        st'.data.regs.get64 .rdx = m.regs.get64 .rdx ∧ st'.data.regs.get64 .rsp = rspOf m ∧
        Saved m st'.data ∧ st'.data.dmem = m.dmem → Eventually (elfStep1 ElfHost.exe) R st') :
      Eventually (elfStep1 ElfHost.exe) R st := by
    refine exec_at_elf hj hx (Env.wf_nil _) (fun l h => absurd h (hxc l)) hpc (match_nil _)
      fun st' hm' hpc' => cont st' hm' hpc' ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (keep (match_nil _) hm' .rax rfl hrax).trans hst.1
    · exact (keep (match_nil _) hm' .rsi rfl hrsi).trans hst.2.1
    · exact (keep (match_nil _) hm' .rdx rfl hrdx).trans hst.2.2.1
    · exact (keep (match_nil _) hm' .rsp rfl hrsp).trans hst.2.2.2.1
    · exact hst.2.2.2.2.1.trans (Match.saved (match_nil _) hm' (Env.wf_nil _) rfl hkeeps)
    · exact (hm'.dmem_eq (Env.wf_nil _) hmem).trans hst.2.2.2.2.2
  have hst0 : st0.data.regs.get64 .rax = dst m ∧ st0.data.regs.get64 .rsi = src m ∧
      st0.data.regs.get64 .rdx = m.regs.get64 .rdx ∧ st0.data.regs.get64 .rsp = rspOf m ∧
      Saved m st0.data ∧ st0.data.dmem = m.dmem := ⟨hax, hx1, hx2, hsp, hs0, hd0⟩
  /- The length zero: done. -/
  have zero {st : MachineState}
      (hpc : st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Memcpy.b8Offset)) (hn : len m = 0)
      (hst : st.data.regs.get64 .rax = dst m ∧ st.data.regs.get64 .rsi = src m ∧
        st.data.regs.get64 .rdx = m.regs.get64 .rdx ∧ st.data.regs.get64 .rsp = rspOf m ∧
        Saved m st.data ∧ st.data.dmem = m.dmem) :
      Eventually (elfStep1 ElfHost.exe) (Post m) st := by
    obtain ⟨h1, -, -, h4, h5, h6⟩ := hst
    refine finish hp hpre ⟨hpc, h1, h4, h5, ?_, sameOutside_of_eq h6 _⟩
    rw [hn]
    exact bytesAt_nil _ _
  /- The length's zero test `testq %rdx, %rdx; je .LMemcpy_7`. -/
  have hz {st : MachineState} (hst : st.data.regs.get64 .rdx = m.regs.get64 .rdx) :
      (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0)).eval
        (Env.ofMachine st.data []) = decide (len m = 0) := by
    rw [eval_test_self]
    simp only [Sym.eval, Env.ofMachine_regs, hst]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      show (m.regs.get64 .rdx).toNat = 0
      rw [h]
      rfl
    · intro h
      exact BitVec.eq_of_toNat_eq h
  simp only [PcOk] at hpc0
  split at hpc0
  · -- aligned: the word loop
    rename_i hal
    have h8 : len m % 8 = 0 := align_or hal
    refine step (infix_of b5_in_code (by simp [b5]) hp) e5 (fun _ h => nomatch h) rfl rfl rfl
      rfl rfl (by decide) (hpc0.trans (hp.label NativeRustcX64.Common.Memcpy.label_4_at)) hst0 fun st5 hm5 hpc5 hst5 => ?_
    simp only [PcOk] at hpc5
    split at hpc5
    · rename_i hc
      rw [hz hst0.2.2.1] at hc
      exact zero (hpc5.trans (hp.label NativeRustcX64.Common.Memcpy.label_7_at)) (by simpa using hc) hst5
    · rename_i hc
      rw [hz hst0.2.2.1] at hc
      have hn : len m ≠ 0 := by simpa using hc
      refine step (infix_of b6_in_code (by simp [b6]) hp) e6 (fun _ h => nomatch h) rfl rfl rfl
        rfl rfl (by decide) hpc5 hst5 fun st6 hm6 hpc6 hst6 => ?_
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst6
      refine word_loop (i := 0) hp hpre h8 ⟨⟨by omega, h1, h2, h3, ?_, h4, h5, ?_, ?_⟩, hpc6, rfl⟩
      · rw [hm6.regs .rcx _ rfl]
        rfl
      · exact bytesAt_nil _ _
      · exact sameOutside_of_eq h6 _
  · -- the byte loop
    refine step (infix_of b1_in_code (by simp [b1]) hp) e1 (fun _ h => nomatch h) rfl rfl rfl
      rfl rfl (by decide) hpc0 hst0 fun st1 hm1 hpc1 hst1 => ?_
    simp only [PcOk] at hpc1
    split at hpc1
    · rename_i hc
      rw [hz hst0.2.2.1] at hc
      exact zero (hpc1.trans (hp.label NativeRustcX64.Common.Memcpy.label_7_at)) (by simpa using hc) hst1
    · rename_i hc
      rw [hz hst0.2.2.1] at hc
      have hn : len m ≠ 0 := by simpa using hc
      refine step (infix_of b2_in_code (by simp [b2]) hp) e2 (fun _ h => nomatch h) rfl rfl rfl
        rfl rfl (by decide) hpc1 hst1 fun st2 hm2 hpc2 hst2 => ?_
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst2
      refine byte_loop (i := 0) hp hpre ⟨⟨by omega, h1, h2, h3, ?_, h4, h5, ?_, ?_⟩, hpc2⟩
      · rw [hm2.regs .rcx _ rfl]
        rfl
      · exact bytesAt_nil _ _
      · exact sameOutside_of_eq h6 _

end

public section

/-- **`memcpy` meets its contract.** -/
theorem memcpy_spec [Host] {k : Nat} (hp : Placed code k) :
    Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost :=
  ElfSpec.toSpec (entry := fun [Labels] => label NativeRustcX64.Common.Memcpy.entryLabel)
    (P := fun [Labels] => MemcpyPre) (Q := fun [Labels] => MemcpyPost)
    (@memcpy_spec_elf (Host.toElfHost _) 0 k hp.toPlacedIn)

end

end NativeRustcX64.Mem.Memcpy
