module

public import NativeRustcX64.Code.Common.Memset.Names

public import NativeRustcX64.Mem.MemsetBlocks

/-!
# `memset` meets its contract

`memset_spec`: rustc's x86-64 `memset`, placed anywhere in the program, meets
`MemsetPre`/`MemsetPost`. Its blocks run by the symbolic executor
(`NativeRustcX64.Mem.MemsetBlocks`), each from a fresh environment of the machine state it starts
in; the word loop (destination and length multiples of 8, `rcx` the byte repeated eight times,
`rsi` the offset) and the byte loop (`rcx` the offset) by invariants (`WInv`, `BInv`) on the
machine state at their heads, each iteration filling the next word or byte; the final `retq` by
`ret_then`.
-/

namespace NativeRustcX64.Mem.Memset

open NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcX64.Common.Memset

public section

theorem replicate_eq (n : Nat) (c : UInt8) :
    List.replicate n c = (List.range n).map fun _ => c := by
  rw [List.map_const', List.length_range]

theorem byte_split {q' : Nat} (a c q r : Nat) (hc : 0 < c) (hr : r < c) (h : a = c * q + r)
    (hq : q % 256 = q') : a / c % 256 = q' := by
  subst h
  rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hr, Nat.add_zero, hq]

theorem word_bytes (a : Nat) (ha : a < 256) (j : Nat) (hj : j < 8) :
    a * 72340172838076673 / 2 ^ (8 * j) % 256 = a := by
  match j, hj with
  | 0, _ => omega
  | 1, _ =>
    exact byte_split _ _ (a * 282578800148737) (a * 1) (by decide) (by omega) (by omega) (by omega)
  | 2, _ =>
    exact byte_split _ _ (a * 1103823438081) (a * 257) (by decide) (by omega) (by omega) (by omega)
  | 3, _ =>
    exact byte_split _ _ (a * 4311810305) (a * 65793) (by decide) (by omega) (by omega) (by omega)
  | 4, _ =>
    exact byte_split _ _ (a * 16843009) (a * 16843009) (by decide) (by omega) (by omega) (by omega)
  | 5, _ =>
    exact byte_split _ _ (a * 65793) (a * 4311810305) (by decide) (by omega) (by omega) (by omega)
  | 6, _ =>
    exact byte_split _ _ (a * 257) (a * 1103823438081) (by decide) (by omega) (by omega) (by omega)
  | 7, _ =>
    exact byte_split _ _ (a * 1) (a * 282578800148737) (by decide) (by omega) (by omega) (by omega)

theorem u8_mod (n : Nat) : UInt8.ofNat (n % 256) = UInt8.ofNat n := by
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat']
  omega

/-- The word `memset` stores: the byte repeated eight times. -/
theorem byteOf_word (x : BitVec 64) {j : Nat} (hj : j < 8) :
    byteOf (BinOp.apply .mul .W64 (BitVec.ofNat 64 72340172838076673)
      (UnOp.apply (.zext .W8) .W32 x)) j = UInt8.ofNat x.toNat := by
  have hz : (UnOp.apply (.zext .W8) .W32 x).toNat = x.toNat % 256 := by
    simp only [UnOp.apply, toNat_ext, BitVec.zeroExtend, BitVec.toNat_setWidth, toNat_low,
      Width.bits]
    omega
  have hv : (BinOp.apply .mul .W64 (BitVec.ofNat 64 72340172838076673)
      (UnOp.apply (.zext .W8) .W32 x)).toNat = x.toNat % 256 * 72340172838076673 := by
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat, hz]
    have : x.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
    omega
  rw [byteOf_mod, hv, word_bytes _ (Nat.mod_lt _ (by decide)) j hj, u8_mod]

/-- The byte `movb %sil` stores. -/
theorem byteOf_sil (x : BitVec 64) : byteOf (UnOp.apply .trunc .W8 x) 0 = UInt8.ofNat x.toNat := by
  rw [byteOf_mod, ← u8_mod x.toNat]
  congr 1
  simp only [UnOp.apply, toNat_ext, toNat_low, Width.bits]
  omega

variable [ElfHost] {sec k : Nat} (m : MachineData)

/-- The destination. -/
abbrev dst : BitVec 64 := m.regs.get64 .rdi
/-- The length. -/
abbrev len : Nat := (m.regs.get64 .rdx).toNat
/-- The fill byte. -/
abbrev fill : UInt8 := UInt8.ofNat (m.regs.get64 .rsi).toNat
/-- The bytes of the first `i` filled. -/
abbrev filled (i : Nat) : List UInt8 := (List.range i).map fun _ => fill m

/-- `memset` done, at `.LMemset_7`. -/
structure Done (sec k : Nat) (st : MachineState) : Prop where
  pc : st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Memset.b8Offset)
  rax : st.data.regs.get64 .rax = dst m
  rsp : st.data.regs.get64 .rsp = rspOf m
  saved : Saved m st.data
  filled : BytesAt st.data.dmem (dst m) (filled m (len m))
  same : SameOutside m.dmem st.data.dmem (InRange (dst m) (len m))

/-- The loops' common part after `i` bytes. -/
structure Loop (i : Nat) (st : MachineState) : Prop where
  lt : i < len m
  rax : st.data.regs.get64 .rax = dst m
  rdx : st.data.regs.get64 .rdx = m.regs.get64 .rdx
  rsp : st.data.regs.get64 .rsp = rspOf m
  saved : Saved m st.data
  filled : BytesAt st.data.dmem (dst m) (filled m i)
  same : SameOutside m.dmem st.data.dmem (InRange (dst m) i)

/-- The word loop's head after `i` bytes. -/
structure WInv (sec k i : Nat) (st : MachineState) : Prop extends Loop m i st where
  pc : st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Memset.b7Offset)
  i8 : i % 8 = 0
  rsi : (st.data.regs.get64 .rsi).toNat = i
  rcx : ∀ j < 8, byteOf (st.data.regs.get64 .rcx) j = fill m

/-- The byte loop's head after `i` bytes. -/
structure BInv (sec k i : Nat) (st : MachineState) : Prop extends Loop m i st where
  pc : st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Memset.b3Offset)
  rsi : st.data.regs.get64 .rsi = m.regs.get64 .rsi
  rcx : (st.data.regs.get64 .rcx).toNat = i

/-- `memset`'s postcondition, reached. -/
abbrev Post (st : MachineState) : Prop :=
  st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧ MemsetPost m st.data

variable {m}

omit [ElfHost] in
/-- `memset`'s precondition's parts, in the names of this file. -/
theorem pre_parts (h : MemsetPre m) : StackOk m 0 ∧ Mapped m.dmem (dst m) (len m) ∧
    NoWrap (dst m) (len m) ∧ Apart (dst m) (len m) (rspOf m) 8 := h

theorem infix_of {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j) (hne : b ≠ [])
    (hp : PlacedIn code sec k) : b.IsInfixAt (ElfHost.sectionProg sec) (k + j) :=
  hb.trans hp.1 hne

/-- From `.LMemset_7`: `retq`. -/
theorem finish {st : MachineState} (hp : PlacedIn code sec k) (hpre : MemsetPre m)
    (hd : Done m sec k st) :
    Eventually (elfStep1 ElfHost.exe) (Post m) st := by
  obtain ⟨hstk, -, hnd, hsp⟩ := pre_parts hpre
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
  · show BytesAt _ _ (List.replicate _ _)
    rw [h3, replicate_eq]
    exact hd.filled
  · intro p hp'
    rw [h3]
    exact hd.same p hp'

omit [ElfHost] in
/-- The loops' environment after `i` bytes, its `w` destination bytes a region, is well formed. -/
theorem loopEnv_wf (hpre : MemsetPre m) {d : MachineData} (hk : Kept m.dmem d.dmem) {i w : Nat}
    (hw : 0 < w) (hle : i + w ≤ len m) :
    (Env.ofMachine d [(dst m + BitVec.ofNat 64 i, w)]).WF := by
  obtain ⟨-, hmd, hnd, -⟩ := pre_parts hpre
  unfold NoWrap at hnd
  have hdi : (dst m + BitVec.ofNat 64 i).toNat = (dst m).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  refine Env.wf_of ⟨⟨fun j hj => ?_, ?_⟩, trivial⟩ (List.pairwise_singleton _ _)
  · rw [Env.ofMachine_mem0, addr_add]
    exact Mapped.of_kept hmd hk _ (by simp only at hj; omega)
  · show (dst m + BitVec.ofNat 64 i).toNat + w ≤ 2 ^ 64
    omega

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

/-- **One word**: from the word loop's head after `i` bytes, the next word filled, back at the head
or done. -/
theorem word_step (hp : PlacedIn code sec k) (hpre : MemsetPre m) (h8 : len m % 8 = 0) {i : Nat}
    {st : MachineState} (hI : WInv m sec k i st) :
    Eventually (elfStep1 ElfHost.exe) (fun st' => Post m st' ∨ WInv m sec k (i + 8) st') st := by
  have hle : i + 8 ≤ len m := by have := hI.i8; have := hI.lt; omega
  obtain ⟨-, -, hnd, -⟩ := pre_parts hpre
  unfold NoWrap at hnd
  have hlen : len m < 2 ^ 64 := (m.regs.get64 .rdx).isLt
  have hdi : (dst m + BitVec.ofNat 64 i).toNat = (dst m).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  let env := Env.ofMachine st.data [(dst m + BitVec.ofNat 64 i, 8)]
  have hwf : env.WF := loopEnv_wf hpre hI.saved.2 (by decide) hle
  have hm : Match env sWord st.data := match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial
    ⟨by simp [eval_ix, hI.rax, ofNat_toNat_eq hI.rsi], trivial⟩
  refine exec_at_elf (infix_of b7_in_code (by simp [b7]) hp) e7 hwf (fun _ h => nomatch h) hI.pc hm
    fun st' hm' hpc' => ?_
  have hrax := (keep hm hm' .rax rfl rfl).trans hI.rax
  have hrdx := (keep hm hm' .rdx rfl rfl).trans hI.rdx
  have hrsp := (keep hm hm' .rsp rfl rfl).trans hI.rsp
  have hrcx := keep hm hm' .rcx rfl rfl
  have hrsi : (st'.data.regs.get64 .rsi).toNat = i + 8 := by
    rw [hm'.regs .rsi _ rfl]
    exact toNat_add_lit hI.rsi (by omega)
  have hsaved : Saved m st'.data := hI.saved.trans (Match.saved hm hm' hwf rfl (by decide))
  have hw : ∀ j < 8, st'.data.dmem.get? (dst m + BitVec.ofNat 64 (i + j)) = some (fill m) := by
    intro j hj
    have h := hm'.bytesAt_write (r := 0) (o := 0) (n := 8) (b := dst m + BitVec.ofNat 64 i)
      (sz := 8) rfl (by omega) (fun j hj => findWrite_head hj) j (by simp; omega)
    simp only [List.getElem_map, List.getElem_range] at h
    rw [addr_add, addr_add, Nat.zero_add] at h
    rw [h]
    congr 1
    exact hI.rcx j hj
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
  obtain ⟨hc', hs'⟩ := extend (f := fun _ => fill m) hnd hle hI.filled hI.same hw hout
  have hce : (SBool.cmp .ult .W64 (.bin .add .W64 (.lit 8) (.reg .rsi)) (.reg .rdx)).eval env =
      decide (i + 8 < len m) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.ult,
      Env.ofMachine_regs, env]
    rw [toNat_add_lit hI.rsi (by omega), hI.rdx]
  simp only [PcOk] at hpc'
  split at hpc'
  · rename_i hc
    have hlt : i + 8 < len m := by rw [hce] at hc; simpa using hc
    refine .done _ (Or.inr ⟨⟨hlt, hrax, hrdx, hrsp, hsaved, hc', hs'⟩, ?_,
      by have := hI.i8; omega, hrsi, by rw [hrcx]; exact hI.rcx⟩)
    rw [hpc']
    exact hp.label NativeRustcX64.Common.Memset.label_6_at
  · rename_i hc
    have hn : i + 8 = len m := by
      rw [hce] at hc
      simp at hc
      omega
    rw [hn] at hc' hs'
    exact Eventually.mono_elf (finish hp hpre ⟨hpc', hrax, hrsp, hsaved, hc', hs'⟩) fun _ h => Or.inl h

/-- **One byte**: from the byte loop's head after `i` bytes, the next byte filled, back at the head
or done. -/
theorem byte_step (hp : PlacedIn code sec k) (hpre : MemsetPre m) {i : Nat} {st : MachineState}
    (hI : BInv m sec k i st) :
    Eventually (elfStep1 ElfHost.exe) (fun st' => Post m st' ∨ BInv m sec k (i + 1) st') st := by
  have hle : i + 1 ≤ len m := hI.lt
  obtain ⟨-, -, hnd, -⟩ := pre_parts hpre
  unfold NoWrap at hnd
  have hlen : len m < 2 ^ 64 := (m.regs.get64 .rdx).isLt
  have hdi : (dst m + BitVec.ofNat 64 i).toNat = (dst m).toNat + i :=
    toNat_add_ofNat _ _ (by omega)
  let env := Env.ofMachine st.data [(dst m + BitVec.ofNat 64 i, 1)]
  have hwf : env.WF := loopEnv_wf hpre hI.saved.2 (by decide) hle
  have hm : Match env sByte st.data := match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial
    ⟨by simp [eval_ix, hI.rax, ofNat_toNat_eq hI.rcx], trivial⟩
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
  have hw : ∀ j < 1, st'.data.dmem.get? (dst m + BitVec.ofNat 64 (i + j)) = some (fill m) := by
    intro j hj
    have h := hm'.bytesAt_write (r := 0) (o := 0) (n := 1) (b := dst m + BitVec.ofNat 64 i)
      (sz := 1) rfl (by omega) (fun j hj => findWrite_head hj) j (by simp; omega)
    simp only [List.getElem_map, List.getElem_range] at h
    rw [addr_add, addr_add, Nat.zero_add] at h
    rw [h]
    congr 1
    obtain rfl : j = 0 := by omega
    show byteOf (UnOp.apply .trunc .W8 (st.data.regs.get64 .rsi)) 0 = _
    rw [byteOf_sil, hI.rsi]
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
  obtain ⟨hc', hs'⟩ := extend (f := fun _ => fill m) hnd hle hI.filled hI.same hw hout
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
    refine .done _ (Or.inr ⟨⟨hlt, hrax, hrdx, hrsp, hsaved, hc', hs'⟩, ?_, hrsi, hrcx⟩)
    rw [hpc']
    exact hp.label NativeRustcX64.Common.Memset.label_3_at
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
      exact hp.label NativeRustcX64.Common.Memset.label_7_at
    · exact (keep (match_nil _) hm'' .rax rfl rfl).trans hrax
    · exact (keep (match_nil _) hm'' .rsp rfl rfl).trans hrsp
    · exact hsaved.trans (Match.saved (match_nil _) hm'' (Env.wf_nil _) rfl (by decide))
    · rw [hd]
      exact hc'
    · intro p hp'
      rw [hd]
      exact hs' p hp'

/-- The word loop, from its head after `i` bytes. -/
theorem word_loop (hp : PlacedIn code sec k) (hpre : MemsetPre m) (h8 : len m % 8 = 0)
    {i : Nat} {st : MachineState} (hI : WInv m sec k i st) :
    Eventually (elfStep1 ElfHost.exe) (Post m) st :=
  Sym.loop (fun μ st => ∃ i, μ = len m - i ∧ WInv m sec k i st)
    (fun _ _ ⟨i, hμ, hI⟩ => Eventually.mono_elf (word_step hp hpre h8 hI) fun st' h =>
      h.imp_right fun h' => ⟨len m - (i + 8), by have := hI.lt; omega, i + 8, rfl, h'⟩)
    ⟨i, rfl, hI⟩

/-- The byte loop, from its head after `i` bytes. -/
theorem byte_loop (hp : PlacedIn code sec k) (hpre : MemsetPre m) {i : Nat} {st : MachineState}
    (hI : BInv m sec k i st) : Eventually (elfStep1 ElfHost.exe) (Post m) st :=
  Sym.loop (fun μ st => ∃ i, μ = len m - i ∧ BInv m sec k i st)
    (fun _ _ ⟨i, hμ, hI⟩ => Eventually.mono_elf (byte_step hp hpre hI) fun st' h =>
      h.imp_right fun h' => ⟨len m - (i + 1), by have := hI.lt; omega, i + 1, rfl, h'⟩)
    ⟨i, rfl, hI⟩

/-- **`memset` meets its contract** under `ElfHost`. -/
theorem memset_spec_elf (hp : PlacedIn code sec k) :
    ElfSpec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost := by
  intro m hpre
  rw [hp.label NativeRustcX64.Common.Memset.entry_at]
  refine exec_then_elf (infix_of b0_in_code (by simp [b0]) hp) e0 (Env.wf_nil m)
    (fun _ h => nomatch h) (match_nil m) fun st0 hm0 hpc0 => ?_
  have hd0 : st0.data.dmem = m.dmem := hm0.dmem_eq (Env.wf_nil _) rfl
  have hax : st0.data.regs.get64 .rax = dst m := by
    rw [hm0.regs .rax _ rfl]
    rfl
  have hst0 : st0.data.regs.get64 .rax = dst m ∧ st0.data.regs.get64 .rsi = m.regs.get64 .rsi ∧
      st0.data.regs.get64 .rdx = m.regs.get64 .rdx ∧ st0.data.regs.get64 .rsp = rspOf m ∧
      Saved m st0.data ∧ st0.data.dmem = m.dmem :=
    ⟨hax, keep (match_nil m) hm0 .rsi rfl rfl, keep (match_nil m) hm0 .rdx rfl rfl,
      keep (match_nil m) hm0 .rsp rfl rfl,
      Match.saved (match_nil m) hm0 (Env.wf_nil m) rfl (by decide), hd0⟩
  /- From a state `st` after `b0`, its registers and memory as there: a block `ds` from `sNone`
  keeping RAX, RSI, RDX, RSP and the callee-saved registers. -/
  have step {ds : List Directive} {j : Nat} {S' : SState} {x : Exit} {st : MachineState}
      {R : MachineState → Prop} (hj : ds.IsInfixAt (ElfHost.sectionProg sec) (k + j))
      (hx : exec ds sNone = some (S', x)) (hxc : ∀ l, x ≠ .call l)
      (hrax : S'.reg .rax = some (.reg .rax)) (hrsi : S'.reg .rsi = some (.reg .rsi))
      (hrdx : S'.reg .rdx = some (.reg .rdx)) (hrsp : S'.reg .rsp = some (.reg .rsp))
      (hmem : S'.mem = []) (hkeeps : keeps sNone S' = true)
      (hpc : st.pc = ElfHost.addrOf sec (k + j))
      (hst : st.data.regs.get64 .rax = dst m ∧ st.data.regs.get64 .rsi = m.regs.get64 .rsi ∧
        st.data.regs.get64 .rdx = m.regs.get64 .rdx ∧ st.data.regs.get64 .rsp = rspOf m ∧
        Saved m st.data ∧ st.data.dmem = m.dmem)
      (cont : ∀ st', Match (Env.ofMachine st.data []) S' st'.data →
        PcOk (Env.ofMachine st.data []) x (ElfHost.addrOf sec (k + j + ds.length)) st' →
        st'.data.regs.get64 .rax = dst m ∧ st'.data.regs.get64 .rsi = m.regs.get64 .rsi ∧
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
  /- The length zero: done. -/
  have zero {st : MachineState}
      (hpc : st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Memset.b8Offset)) (hn : len m = 0)
      (hst : st.data.regs.get64 .rax = dst m ∧ st.data.regs.get64 .rsi = m.regs.get64 .rsi ∧
        st.data.regs.get64 .rdx = m.regs.get64 .rdx ∧ st.data.regs.get64 .rsp = rspOf m ∧
        Saved m st.data ∧ st.data.dmem = m.dmem) :
      Eventually (elfStep1 ElfHost.exe) (Post m) st := by
    obtain ⟨h1, -, -, h4, h5, h6⟩ := hst
    refine finish hp hpre ⟨hpc, h1, h4, h5, ?_, sameOutside_of_eq h6 _⟩
    rw [hn]
    exact bytesAt_nil _ _
  /- The length's zero test `testq %rdx, %rdx; je .LMemset_7`. -/
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
      rfl rfl (by decide) (hpc0.trans (hp.label NativeRustcX64.Common.Memset.label_4_at)) hst0 fun st5 hm5 hpc5 hst5 => ?_
    simp only [PcOk] at hpc5
    split at hpc5
    · rename_i hc
      rw [hz hst0.2.2.1] at hc
      exact zero (hpc5.trans (hp.label NativeRustcX64.Common.Memset.label_7_at)) (by simpa using hc) hst5
    · rename_i hc
      rw [hz hst0.2.2.1] at hc
      have hn : len m ≠ 0 := by simpa using hc
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst5
      refine exec_at_elf (infix_of b6_in_code (by simp [b6]) hp) e6 (Env.wf_nil _)
        (fun _ h => nomatch h) hpc5 (match_nil _) fun st6 hm6 hpc6 => ?_
      refine word_loop (i := 0) hp hpre h8 ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpc6, rfl, ?_, ?_⟩
      · exact (keep (match_nil _) hm6 .rax rfl rfl).trans h1
      · exact (keep (match_nil _) hm6 .rdx rfl rfl).trans h3
      · exact (keep (match_nil _) hm6 .rsp rfl rfl).trans h4
      · exact h5.trans (Match.saved (match_nil _) hm6 (Env.wf_nil _) rfl (by decide))
      · exact bytesAt_nil _ _
      · exact sameOutside_of_eq ((hm6.dmem_eq (Env.wf_nil _) rfl).trans h6) _
      · rw [hm6.regs .rsi _ rfl]
        rfl
      · intro j hj
        rw [hm6.regs .rcx _ rfl]
        show byteOf (BinOp.apply .mul .W64 (BitVec.ofNat 64 72340172838076673)
          (UnOp.apply (.zext .W8) .W32 (st5.data.regs.get64 .rsi))) j = _
        rw [byteOf_word _ hj, h2]
  · -- the byte loop
    refine step (infix_of b1_in_code (by simp [b1]) hp) e1 (fun _ h => nomatch h) rfl rfl rfl
      rfl rfl (by decide) hpc0 hst0 fun st1 hm1 hpc1 hst1 => ?_
    simp only [PcOk] at hpc1
    split at hpc1
    · rename_i hc
      rw [hz hst0.2.2.1] at hc
      exact zero (hpc1.trans (hp.label NativeRustcX64.Common.Memset.label_7_at)) (by simpa using hc) hst1
    · rename_i hc
      rw [hz hst0.2.2.1] at hc
      have hn : len m ≠ 0 := by simpa using hc
      refine step (infix_of b2_in_code (by simp [b2]) hp) e2 (fun _ h => nomatch h) rfl rfl rfl
        rfl rfl (by decide) hpc1 hst1 fun st2 hm2 hpc2 hst2 => ?_
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst2
      refine byte_loop (i := 0) hp hpre ⟨⟨by omega, h1, h3, h4, h5, ?_, ?_⟩, hpc2, h2, ?_⟩
      · exact bytesAt_nil _ _
      · exact sameOutside_of_eq h6 _
      · rw [hm2.regs .rcx _ rfl]
        rfl

end

public section

/-- **`memset` meets its contract.** -/
theorem memset_spec [Host] {k : Nat} (hp : Placed code k) :
    Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost :=
  ElfSpec.toSpec (entry := fun [Labels] => label NativeRustcX64.Common.Memset.entryLabel)
    (P := fun [Labels] => MemsetPre) (Q := fun [Labels] => MemsetPost)
    (@memset_spec_elf (Host.toElfHost _) 0 k hp.toPlacedIn)

end

end NativeRustcX64.Mem.Memset
