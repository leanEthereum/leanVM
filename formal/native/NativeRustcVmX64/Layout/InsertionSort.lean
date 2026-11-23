module

public import NativeRustcVmX64.Layout.InsertionSort.Exec
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.InsertionSortOfStackOffsets.Names

/-!
# `insertion_sort` (with `stack_offsets`' order) on x86-64

**`insertionSort_spec`**: rustc's `insertion_sort(order, |i, j| …)` (the closure's `sizes` in RDX,
RCX), placed anywhere in the program, meets `InsertionSortPre`/`InsertionSortPost`: `order` ends as
the model's `insertionSort (sortLt size) order`. No elements: `b0` returns. Else the prologue
(`b1`) pushes R14, RBX (`Base`: the frame, the arguments, memory but `order`). The outer loop
(`.L2`, `Outer`) holds `acc i`, the model's fold after `i` elements; `b5` takes `a = order[i]` and
the inner loop (`.L4`, `Inner`) swaps it down: `b6` loads `b = order[j - 1]`, `b7`-`b17` decide
`lt a b` (`Q`, by `sortLt` of the sizes, `0` past `sizes`), `b18` swaps, `b19` goes on with
`j - 1`. Either exit is `.L17` with `acc (i + 1)` (`Done`); `b21`, `b22` pop and return.
-/

namespace NativeRustcVmX64.Layout.InsertionSort

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InsertionSortOfStackOffsets
open NativeVm.Model NativeRustcVm.Layout
open NativeRustcVmX64.Transcript (after after_eq exec_after infix_of Frame frameEnv)
open NativeRustcVmX64.Arrays (pc_cond regs_eq_of keepsRegs)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt wordOf_of_wordAt wordOf_congr)

public section

/-! ## The model -/

/-- `order`. -/
abbrev ord (m : MachineData) : BitVec 64 := reg m .rdi
/-- `|order|`. -/
abbrev n (m : MachineData) : Nat := (reg m .rsi).toNat
/-- `sizes`. -/
abbrev szs (m : MachineData) : BitVec 64 := reg m .rdx
/-- `|sizes|`. -/
abbrev ns (m : MachineData) : Nat := (reg m .rcx).toNat
/-- A block's size, `0` past `sizes`. -/
def sz (m : MachineData) (t : Nat) : Nat := (natsOf m (reg m .rdx) (ns m)).getD t 0
/-- The order. -/
abbrev lt (m : MachineData) : Nat → Nat → Bool := sortLt (sz m)
/-- `order` at the entry. -/
abbrev xs0 (m : MachineData) : Array Nat := natsOf m (reg m .rdi) (n m)

/-- The model's fold after `i` elements. -/
def acc (m : MachineData) (i : Nat) : Array Nat :=
  (List.range i).foldl (fun a i ↦ swapDown (lt m) a i) (xs0 m)

theorem acc_succ (m : MachineData) (i : Nat) : acc m (i + 1) = swapDown (lt m) (acc m i) i := by
  simp [acc, List.range_succ, List.foldl_append]

theorem size_natsOf (m : MachineData) (a : BitVec 64) (k : Nat) : (natsOf m a k).size = k := by
  simp [natsOf, wordsOf]

theorem insertionSort_eq (m : MachineData) : insertionSort (lt m) (xs0 m) = acc m (n m) := by
  unfold insertionSort acc
  rw [size_natsOf]

theorem swapDown_succ {lt' : Nat → Nat → Bool} (xs : Array Nat) (j : Nat) :
    swapDown lt' xs (j + 1) = if lt' xs[j + 1]! xs[j]! then
      swapDown lt' (xs.swapIfInBounds (j + 1) j) j else xs := rfl

theorem sz_ge {m : MachineData} {t : Nat} (h : ns m ≤ t) : sz m t = 0 := by
  have : ¬t < (natsOf m (reg m .rdx) (ns m)).size := by rw [size_natsOf]; omega
  simp [sz, Array.getD, this]

theorem sz_lt {m : MachineData} {t : Nat} (h : t < ns m) :
    sz m t = (wordOf m.dmem (szs m + BitVec.ofNat 64 (8 * t))).toNat :=
  natsOf_getD m (reg m .rdx) h

theorem sz_lt64 (m : MachineData) (t : Nat) : sz m t < 2 ^ 64 := by
  rcases Nat.lt_or_ge t (ns m) with h | h
  · rw [sz_lt h]; exact UInt64.toNat_lt _
  · rw [sz_ge h]; decide

theorem lt_def (m0 : MachineData) (a b : Nat) : lt m0 a b =
    (decide (sz m0 b < sz m0 a) || (decide (sz m0 a = sz m0 b) && decide (a < b))) := rfl

theorem ofNat_ult {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    CmpOp.apply .ult .W64 (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy]

theorem ofNat_eq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    CmpOp.apply .eq .W64 (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x = y) := by
  simp only [CmpOp.apply, low_W64]
  exact NativeRustcX64.Sym.ofNat_beq hx hy

theorem toBitVec_toUInt64 (x : Nat) : x.toUInt64.toBitVec = BitVec.ofNat 64 x := rfl

/-! ## The frame -/

/-- **The frame**: the pushes, the arguments, memory the entry's but in `order` and the pushes. -/
structure Base (m0 st : MachineData) : Prop where
  frame : Frame m0 16 slots 0 st
  regs : ∀ r ∈ kA, reg st r = reg m0 r
  same : ∀ q, ¬InRange (ord m0) (8 * n m0) q → ¬InRange (stackBelow m0 16) 16 q →
    st.dmem.get? q = m0.dmem.get? q

theorem Base.rdi {m0 st : MachineData} (h : Base m0 st) : reg st .rdi = reg m0 .rdi :=
  h.regs .rdi (by simp [kA])
theorem Base.rsi {m0 st : MachineData} (h : Base m0 st) : reg st .rsi = reg m0 .rsi :=
  h.regs .rsi (by simp [kA])
theorem Base.rdx {m0 st : MachineData} (h : Base m0 st) : reg st .rdx = reg m0 .rdx :=
  h.regs .rdx (by simp [kA])
theorem Base.rcx {m0 st : MachineData} (h : Base m0 st) : reg st .rcx = reg m0 .rcx :=
  h.regs .rcx (by simp [kA])

/-- A quiet block keeps the frame and memory. -/
theorem Base.quiet [Labels] {m0 st st' : MachineData} {rest : List (BitVec 64 × Nat)}
    {S : SState} (hb : Base m0 st) (hwf : (frameEnv m0 st 16 rest).WF)
    (hm : Match (frameEnv m0 st 16 rest) S st')
    (hq : Quiet S) (hk : ∀ r ∈ kA, reg st' r = reg st r) :
    Base m0 st' ∧ st'.dmem = st.dmem := by
  have hd : st'.dmem = st.dmem := hm.dmem_eq hwf hq.2
  exact ⟨⟨Frame.of_block hb.frame hwf hm hq.1 slots_le, fun r hr ↦ (hk r hr).trans (hb.regs r hr),
    fun q h1 h2 ↦ by rw [hd]; exact hb.same q h1 h2⟩, hd⟩

/-- **The sorted array so far** in `order`: its numbers, words. -/
structure Arr (m0 : MachineData) (cur : Array Nat) (d : Mem 64) : Prop where
  size : cur.size = n m0
  lt64 : ∀ t (h : t < cur.size), cur[t] < 2 ^ 64
  words : WordsAt d (ord m0) (natWords cur)

theorem Arr.word {m0 : MachineData} {cur : Array Nat} {d : Mem 64} (h : Arr m0 cur d) {t : Nat}
    (ht : t < cur.size) : WordAt d (ord m0 + BitVec.ofNat 64 (8 * t)) cur[t].toUInt64 := by
  have := NativeRustcVm.WordsAt.getElem h.words (i := t) (by simp [natWords]; exact ht)
  simpa [natWords] using this

/-- The facts of the precondition the blocks use. -/
structure Facts (m0 : MachineData) : Prop where
  stack : StackOk m0 16
  or : Readable m0 (ord m0) (8 * n m0)
  oo : OffStack m0 (ord m0) (8 * n m0) 16
  sr : Readable m0 (szs m0) (8 * ns m0)
  so : OffStack m0 (szs m0) (8 * ns m0) 16
  apart : Apart (ord m0) (8 * n m0) (szs m0) (8 * ns m0)

theorem Facts.of_pre {m0 : MachineData} (h : InsertionSortPre m0) : Facts m0 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `(p, x, 8)`'s address. -/
theorem addr_eval [Labels] {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {st : MachineData} (p x : Reg64) :
    (addr p x).eval (Env.ofMachine st rs vars ret) =
      reg st p + BitVec.ofNat 64 (8 * (reg st x).toNat) := by
  simp only [addr, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, NativeRustcX64.reg]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show Width.W64.bits = 64 from rfl]
  omega

/-- The environment of a block reading `l` bytes at `o` of a readable argument off the stack. -/
theorem Facts.wf_el {m0 st : MachineData} (hF : Facts m0) (hk : Kept m0.dmem st.dmem)
    {a : BitVec 64} {N : Nat} (hR : Readable m0 a N) (hO : OffStack m0 a N 16) {o l : Nat}
    (h : o + l ≤ N) (hl : 0 < l) :
    (frameEnv m0 st 16 [(a + BitVec.ofNat 64 o, l)]).WF :=
  Transcript.frame_wf ⟨NativeRustcVm.Transcript.Mapped.keeps
      (Transcript.frame_mapped hF.stack le_rfl) hk, Transcript.frame_noWrap hF.stack le_rfl⟩
    (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨NativeRustcVm.Transcript.Mapped.keeps (NativeRustcVm.Mapped.sub hR.1 h) hk,
        NativeRustcVm.NoWrap.sub hR.2 h⟩)
    (List.pairwise_pair.mpr (by
      have ha := hO
      have hn : a.toNat + N ≤ 2 ^ 64 := hR.2
      unfold OffStack NativeRustcX64.Apart at ha
      show NativeRustcVm.Apart (stackBelow m0 16) (16 + 8) (a + BitVec.ofNat 64 o) l
      unfold NativeRustcVm.Apart
      rw [NativeRustcVm.toNat_add_ofNat (by omega)]
      omega))

/-- The block state at an element: the frame, the element at `(p, x, 8)`. -/
theorem match_el [Labels] {m0 st : MachineData} {p x : Reg64} {a : BitVec 64} {t l : Nat}
    (hf : Frame m0 16 slots 0 st) (hp : reg st p = a) (hx : (reg st x).toNat = t) :
    Match (frameEnv m0 st 16 [(a + BitVec.ofNat 64 (8 * t), l)])
      (init [24, l] [(.rsp, .ptr 0 0)] [] [] [(addr p x, 1, 0)]) st := by
  refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial
    ⟨?_, trivial⟩
  show (addr p x).eval _ = _ + BitVec.ofInt 64 0
  rw [addr_eval, hp, hx, Transcript.ofInt_zero64, BitVec.add_zero]
  rfl

/-- A word of `sizes` in a body's memory. -/
theorem Base.size {m0 st : MachineData} (hF : Facts m0) (hb : Base m0 st) {t : Nat}
    (ht : t < ns m0) :
    wordOf st.dmem (szs m0 + BitVec.ofNat 64 (8 * t)) = (sz m0 t).toUInt64 := by
  have hw : ∀ i < 8, st.dmem.get? (szs m0 + BitVec.ofNat 64 (8 * t) + BitVec.ofNat 64 i) =
      m0.dmem.get? (szs m0 + BitVec.ofNat 64 (8 * t) + BitVec.ofNat 64 i) := by
    intro i hi
    have hsn : (szs m0).toNat + 8 * ns m0 ≤ 2 ^ 64 := hF.sr.2
    have hon : (ord m0).toNat + 8 * n m0 ≤ 2 ^ 64 := hF.or.2
    have hap := hF.apart
    have hso := hF.so
    have hS1 := hF.stack.1
    have hS2 := hF.stack.2.1
    unfold OffStack NativeRustcX64.Apart at hso
    unfold NativeRustcX64.Apart at hap
    rw [Arrays.stackBelow_toNat hS1] at hso
    rw [NativeRustcVm.addr_add_add]
    refine hb.same _ (fun h ↦ ?_) (fun h ↦ ?_)
    · rw [Sym.inRange_iff hon, NativeRustcVm.toNat_add_ofNat (by omega)] at h; omega
    · rw [Sym.inRange_iff (by rw [Arrays.stackBelow_toNat hS1]; omega),
        Arrays.stackBelow_toNat hS1, NativeRustcVm.toNat_add_ofNat (by omega)] at h; omega
  rw [sz_lt ht, wordOf_congr hw]
  simp

/-! ## The comparison -/

/-- **During the comparison** of `a` (R9) with `b` (R11, `order[j - 1]`): memory `D`. -/
structure Cmp (m0 : MachineData) (D : Mem 64) (i j a b : Nat) (st : MachineData) : Prop where
  base : Base m0 st
  dmem : st.dmem = D
  r8 : reg st .r8 = BitVec.ofNat 64 i
  rax : reg st .rax + 1#64 = BitVec.ofNat 64 i
  r9 : reg st .r9 = BitVec.ofNat 64 a
  r10 : reg st .r10 = BitVec.ofNat 64 (j - 1)
  r11 : reg st .r11 = BitVec.ofNat 64 b
  alt : a < 2 ^ 64
  blt : b < 2 ^ 64

/-- A quiet block keeping the comparison's registers keeps the comparison. -/
theorem Cmp.quiet [Labels] {m0 st st' : MachineData} {D : Mem 64} {i j a b : Nat}
    {rest : List (BitVec 64 × Nat)} {S : SState} (hc : Cmp m0 D i j a b st)
    (hwf : (frameEnv m0 st 16 rest).WF)
    (hm : Match (frameEnv m0 st 16 rest) S st') (hq : Quiet S)
    (hk : ∀ r ∈ kC, reg st' r = reg st r) : Cmp m0 D i j a b st' := by
  obtain ⟨hb, hd⟩ := hc.base.quiet hwf hm hq fun r hr ↦ hk r (by
    simp only [kC, kB, List.mem_append]; exact Or.inl (Or.inl hr))
  exact ⟨hb, hd.trans hc.dmem, (hk .r8 (by simp [kC, kB])).trans hc.r8,
    by rw [hk .rax (by simp [kC, kB])]; exact hc.rax, (hk .r9 (by simp [kC, kB])).trans hc.r9,
    (hk .r10 (by simp [kC, kB])).trans hc.r10, (hk .r11 (by simp [kC, kB])).trans hc.r11,
    hc.alt, hc.blt⟩

variable [Host] {k : Nat}

/-- Where the comparison ends: `.L17` when `lt a b` fails, the swap `b18` when it holds. -/
def Q (k : Nat) (m0 : MachineData) (D : Mem 64) (i j a b : Nat) (s : MachineState) : Prop :=
  (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b3Offset) ∧ Cmp m0 D i j a b s.data ∧ lt m0 a b = false) ∨
  (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b18Offset) ∧ Cmp m0 D i j a b s.data ∧ lt m0 a b = true)

omit [Host] in
/-- A frame-only block from a comparison state. -/
theorem match_regs [Labels] {m0 st : MachineData} (hf : Frame m0 16 slots 0 st) :
    Match (frameEnv m0 st 16 []) regsS st :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial

omit [Host] in
theorem Facts.wf0 {m0 st : MachineData} (hF : Facts m0) (hk : Kept m0.dmem st.dmem) :
    (frameEnv m0 st 16 []).WF :=
  Transcript.frame_wf ⟨NativeRustcVm.Transcript.Mapped.keeps
      (Transcript.frame_mapped hF.stack le_rfl) hk, Transcript.frame_noWrap hF.stack le_rfl⟩
    (by simp) (List.pairwise_singleton _ _)

/-- **`.L14`** (`b17`): `sz a = sz b` decides the swap (with `a < b`, `¬ sz b < sz a`). -/
theorem l14 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {D : Mem 64} {i j a b : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b17Offset)) (hc : Cmp m0 D i j a b st.data)
    (hrbx : reg st.data .rbx = BitVec.ofNat 64 (sz m0 a))
    (hr14 : reg st.data .r14 = BitVec.ofNat 64 (sz m0 b)) (hab : a < b)
    (hns : ¬sz m0 b < sz m0 a) : Eventually (step1 Host.exe) (Q k m0 D i j a b) st := by
  have hwf := hF.wf0 hc.base.frame.kept (st := st.data)
  have hm := match_regs hc.base.frame
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) run_b17 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hq, hk, hzf⟩ := after_eq run_b17 ▸ b17_facts
  have hc' := hc.quiet hwf hm' hq (regs_eq_of hm hm' hk)
  simp only [PcOk] at hpc'
  obtain ⟨hy, hn⟩ := pc_cond hpc'
  simp only [SBool.eval, Sym.eval] at hy hn
  rw [show (frameEnv m0 st.data 16 []).regs .rbx = reg st.data .rbx from rfl,
    show (frameEnv m0 st.data 16 []).regs .r14 = reg st.data .r14 from rfl, hrbx, hr14,
    ofNat_eq (sz_lt64 _ _) (sz_lt64 _ _)] at hy hn
  have hlab := lt_def m0 a b
  by_cases he : sz m0 a = sz m0 b
  · exact .done _ (Or.inr ⟨(hn (by simpa using he)).trans (congrArg Host.addrOf
      (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b17_next])), hc', by simp [hlab, he, hab]⟩)
  · exact .done _ (Or.inl ⟨(hy (by simpa using he)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_17_at), hc',
      by simp [hlab, he, hns]⟩)

/-- **`.L10`** (`b12`, then `b13` or `b16`): `sz a` in RBX, `¬ sz b < sz a`. -/
theorem l10 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {D : Mem 64} {i j a b : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b12Offset)) (hc : Cmp m0 D i j a b st.data)
    (hrbx : reg st.data .rbx = BitVec.ofNat 64 (sz m0 a)) (hns : ¬sz m0 b < sz m0 a) :
    Eventually (step1 Host.exe) (Q k m0 D i j a b) st := by
  have hwf := hF.wf0 hc.base.frame.kept (st := st.data)
  have hm := match_regs hc.base.frame
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, hcf⟩ := after_eq run_b12 ▸ b12_facts
  have e1 := regs_eq_of hm hm1 hk
  have hc1 := hc.quiet hwf hm1 hq fun r hr ↦ e1 r (by simp only [List.mem_append]; exact Or.inl hr)
  have hrbx1 : reg st1.data .rbx = BitVec.ofNat 64 (sz m0 a) := (e1 .rbx (by simp)).trans hrbx
  have hcns : reg st.data .rcx = BitVec.ofNat 64 (ns m0) := by
    rw [hc.base.rcx]; simp
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval] at hy hn
  rw [show (frameEnv m0 st.data 16 []).regs .r11 = reg st.data .r11 from rfl,
    show (frameEnv m0 st.data 16 []).regs .rcx = reg st.data .rcx from rfl, hc.r11, hcns,
    ofNat_ult hc.blt (by have := (reg m0 .rcx).isLt; omega)] at hy hn
  have hlab := lt_def m0 a b
  by_cases hbn : b < ns m0
  · -- `b13`: `sz b`
    have hpc2 := hn (by simpa using hbn)
    have hwf2 := hF.wf_el (st := st1.data) hc1.base.frame.kept hF.sr hF.so (o := 8 * b) (l := 8)
      (by omega) (by omega)
    have hm2 := match_el (p := .rdx) (x := .r11) (t := b) (l := 8) hc1.base.frame hc1.base.rdx
      (by rw [hc1.r11, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc.blt)
    refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13 hwf2 nofun
      (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b12_next))) hm2
      fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hq3, hk3, h14, hcf3⟩ := after_eq run_b13 ▸ b13_facts
    have e3 := regs_eq_of hm2 hm3 hk3
    have hc3 := hc1.quiet hwf2 hm3 hq3 fun r hr ↦ e3 r (by
      simp only [List.mem_append]; exact Or.inl hr)
    have hld : (frameEnv m0 st1.data 16 [(szs m0 + BitVec.ofNat 64 (8 * b), 8)]).load 1 0 8 =
        BitVec.ofNat 64 (sz m0 b) := by
      rw [Arrays.load8_eq, show (frameEnv m0 st1.data 16 [(szs m0 + BitVec.ofNat 64 (8 * b), 8)]).base
        1 = szs m0 + BitVec.ofNat 64 (8 * b) from rfl, BitVec.add_zero, Env.ofMachine_mem0,
        hc1.base.size hF hbn]
      rfl
    have hr14 : reg st3.data .r14 = BitVec.ofNat 64 (sz m0 b) := (hm3.regs .r14 _ h14).trans hld
    simp only [PcOk] at hpc3
    obtain ⟨hy3, hn3⟩ := pc_cond hpc3
    simp only [SBool.eval, Sym.eval] at hy3 hn3
    rw [show (frameEnv m0 st1.data 16 [(szs m0 + BitVec.ofNat 64 (8 * b), 8)]).regs .r9 =
        reg st1.data .r9 from rfl,
      show (frameEnv m0 st1.data 16 [(szs m0 + BitVec.ofNat 64 (8 * b), 8)]).regs .r11 =
        reg st1.data .r11 from rfl, hc1.r9, hc1.r11, ofNat_ult hc.alt hc.blt] at hy3 hn3
    by_cases hab : a < b
    · exact l14 hp hF ((hy3 (by simpa using hab)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_14_at)) hc3
        ((e3 .rbx (by simp)).trans hrbx1) hr14 hab hns
    · -- `b14`: no swap
      have hpc4 := hn3 (by simpa using hab)
      have hwf4 := hF.wf0 hc3.base.frame.kept (st := st3.data)
      have hm4 := match_regs hc3.base.frame
      refine exec_at (infix_of b14_in_code (by simp [b14]) hp) run_b14 hwf4 nofun
        (hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b13_next))) hm4
        fun st4 hm4' hpc5 ↦ ?_
      obtain ⟨hq4, hk4⟩ := after_eq run_b14 ▸ b14_facts
      simp only [PcOk] at hpc5
      exact .done _ (Or.inl ⟨hpc5.trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_17_at),
        hc3.quiet hwf4 hm4' hq4 (regs_eq_of hm4 hm4' hk4), by simp [hlab, hns, hab]⟩)
  · -- `b16`: `sz b = 0`
    have hpc2 := (hy (by simpa using hbn)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_11_at)
    have hwf2 := hF.wf0 hc1.base.frame.kept (st := st1.data)
    have hm2 := match_regs hc1.base.frame
    refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf2 nofun hpc2 hm2
      fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hq3, hk3, h14, hcf3⟩ := after_eq run_b16 ▸ b16_facts
    have e3 := regs_eq_of hm2 hm3 hk3
    have hc3 := hc1.quiet hwf2 hm3 hq3 fun r hr ↦ e3 r (by
      simp only [List.mem_append]; exact Or.inl hr)
    have hszb := sz_ge (m := m0) (t := b) (by omega)
    have hr14 : reg st3.data .r14 = BitVec.ofNat 64 (sz m0 b) := by
      rw [hszb]; exact hm3.regs .r14 _ h14
    simp only [PcOk] at hpc3
    obtain ⟨hy3, hn3⟩ := pc_cond hpc3
    simp only [SBool.eval, Sym.eval] at hy3 hn3
    rw [show (frameEnv m0 st1.data 16 []).regs .r9 = reg st1.data .r9 from rfl,
      show (frameEnv m0 st1.data 16 []).regs .r11 = reg st1.data .r11 from rfl, hc1.r9, hc1.r11,
      ofNat_ult hc.alt hc.blt] at hy3 hn3
    by_cases hab : a < b
    · exact l14 hp hF ((hn3 (by simpa using hab)).trans (congrArg Host.addrOf
        (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b16_next]))) hc3 ((e3 .rbx (by simp)).trans hrbx1) hr14
        hab hns
    · exact .done _ (Or.inl ⟨(hy3 (by simpa using hab)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_17_at), hc3,
        by simp [hlab, hns, hab]⟩)

omit [Host] in
/-- `sizes[x]` loaded in a block from `szS`. -/
theorem size_load [Labels] {m0 st : MachineData} (hF : Facts m0) (hb : Base m0 st) {x : Nat}
    (hx : x < ns m0) :
    (frameEnv m0 st 16 [(szs m0 + BitVec.ofNat 64 (8 * x), 8)]).load 1 0 8 =
      BitVec.ofNat 64 (sz m0 x) := by
  rw [Arrays.load8_eq, show (frameEnv m0 st 16 [(szs m0 + BitVec.ofNat 64 (8 * x), 8)]).base 1 =
    szs m0 + BitVec.ofNat 64 (8 * x) from rfl, BitVec.add_zero, Env.ofMachine_mem0,
    hb.size hF hx]
  rfl

/-- **`.L9`** (`b11`): `sz a` read; `sz b < sz a` swaps, else on to `.L10`. -/
theorem l11 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {D : Mem 64} {i j a b : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b11Offset)) (hc : Cmp m0 D i j a b st.data)
    (han : a < ns m0) (hr14 : reg st.data .r14 = BitVec.ofNat 64 (sz m0 b)) :
    Eventually (step1 Host.exe) (Q k m0 D i j a b) st := by
  have hwf := hF.wf_el (st := st.data) hc.base.frame.kept hF.sr hF.so (o := 8 * a) (l := 8)
    (by omega) (by omega)
  have hm := match_el (p := .rdx) (x := .r9) (t := a) (l := 8) hc.base.frame hc.base.rdx
    (by rw [hc.r9, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc.alt)
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, hbx, hcf⟩ := after_eq run_b11 ▸ b11_facts
  have e1 := regs_eq_of hm hm1 hk
  have hc1 := hc.quiet hwf hm1 hq fun r hr ↦ e1 r (by simp only [List.mem_append]; exact Or.inl hr)
  have hrbx : reg st1.data .rbx = BitVec.ofNat 64 (sz m0 a) :=
    (hm1.regs .rbx _ hbx).trans (size_load hF hc.base han)
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval] at hy hn
  rw [show (frameEnv m0 st.data 16 [(szs m0 + BitVec.ofNat 64 (8 * a), 8)]).regs .r14 =
      reg st.data .r14 from rfl, hr14, size_load hF hc.base han,
    ofNat_ult (sz_lt64 _ _) (sz_lt64 _ _)] at hy hn
  by_cases hlt : sz m0 b < sz m0 a
  · exact .done _ (Or.inr ⟨(hy (by simpa using hlt)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_15_at), hc1,
      by simp [lt_def, hlt]⟩)
  · exact l10 hp hF ((hn (by simpa using hlt)).trans (congrArg Host.addrOf
      (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b11_next]))) hc1 hrbx hlt

/-- **`.L8`** (`b8`): `a` past `sizes`, `sz a = 0`. -/
theorem l8 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {D : Mem 64} {i j a b : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b8Offset)) (hc : Cmp m0 D i j a b st.data)
    (han : ns m0 ≤ a) : Eventually (step1 Host.exe) (Q k m0 D i j a b) st := by
  have hwf := hF.wf0 hc.base.frame.kept (st := st.data)
  have hm := match_regs hc.base.frame
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, hbx⟩ := after_eq run_b8 ▸ b8_facts
  have hc1 := hc.quiet hwf hm1 hq (regs_eq_of hm hm1 hk)
  simp only [PcOk] at hpc1
  refine l10 hp hF (hpc1.trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_10_at)) hc1 ?_ (by rw [sz_ge han]; omega)
  rw [sz_ge han]; exact hm1.regs .rbx _ hbx

/-- **`b7`**: `b` in `sizes`, its size read; is `a`? -/
theorem l7 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {D : Mem 64} {i j a b : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b7Offset)) (hc : Cmp m0 D i j a b st.data)
    (hbn : b < ns m0) : Eventually (step1 Host.exe) (Q k m0 D i j a b) st := by
  have hwf := hF.wf_el (st := st.data) hc.base.frame.kept hF.sr hF.so (o := 8 * b) (l := 8)
    (by omega) (by omega)
  have hm := match_el (p := .rdx) (x := .r11) (t := b) (l := 8) hc.base.frame hc.base.rdx
    (by rw [hc.r11, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc.blt)
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, h14, hcf⟩ := after_eq run_b7 ▸ b7_facts
  have e1 := regs_eq_of hm hm1 hk
  have hc1 := hc.quiet hwf hm1 hq e1
  have hr14 : reg st1.data .r14 = BitVec.ofNat 64 (sz m0 b) :=
    (hm1.regs .r14 _ h14).trans (size_load hF hc.base hbn)
  have hcns : reg st.data .rcx = BitVec.ofNat 64 (ns m0) := by rw [hc.base.rcx]; simp
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval] at hy hn
  rw [show (frameEnv m0 st.data 16 [(szs m0 + BitVec.ofNat 64 (8 * b), 8)]).regs .r9 =
      reg st.data .r9 from rfl,
    show (frameEnv m0 st.data 16 [(szs m0 + BitVec.ofNat 64 (8 * b), 8)]).regs .rcx =
      reg st.data .rcx from rfl, hc.r9, hcns,
    ofNat_ult hc.alt (by have := (reg m0 .rcx).isLt; omega)] at hy hn
  by_cases han : a < ns m0
  · exact l11 hp hF ((hy (by simpa using han)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_9_at)) hc1 han hr14
  · exact l8 hp hF ((hn (by simpa using han)).trans (congrArg Host.addrOf
      (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b7_next]))) hc1 (by omega)

/-- **`.L5`** (`b10`): `b` past `sizes`, `sz b = 0`; is `a` in `sizes`? -/
theorem l5 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {D : Mem 64} {i j a b : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b10Offset)) (hc : Cmp m0 D i j a b st.data)
    (hbn : ns m0 ≤ b) : Eventually (step1 Host.exe) (Q k m0 D i j a b) st := by
  have hwf := hF.wf0 hc.base.frame.kept (st := st.data)
  have hm := match_regs hc.base.frame
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, h14, hcf⟩ := after_eq run_b10 ▸ b10_facts
  have hc1 := hc.quiet hwf hm1 hq (regs_eq_of hm hm1 hk)
  have hr14 : reg st1.data .r14 = BitVec.ofNat 64 (sz m0 b) := by
    rw [sz_ge hbn]; exact hm1.regs .r14 _ h14
  have hcns : reg st.data .rcx = BitVec.ofNat 64 (ns m0) := by rw [hc.base.rcx]; simp
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval] at hy hn
  rw [show (frameEnv m0 st.data 16 []).regs .r9 = reg st.data .r9 from rfl,
    show (frameEnv m0 st.data 16 []).regs .rcx = reg st.data .rcx from rfl, hc.r9, hcns,
    ofNat_ult hc.alt (by have := (reg m0 .rcx).isLt; omega)] at hy hn
  by_cases han : a < ns m0
  · exact l11 hp hF ((hn (by simpa using han)).trans (congrArg Host.addrOf
      (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b10_next]))) hc1 han hr14
  · exact l8 hp hF ((hy (by simpa using han)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_8_at)) hc1 (by omega)

/-! ## The loops -/

omit [Host] in
/-- **The swap** of `cur[j - 1]` and `cur[j]` in memory. -/
theorem Arr.swap {m0 : MachineData} {cur : Array Nat} {d d' : Mem 64} (h : Arr m0 cur d)
    (hnw : NativeRustcVm.NoWrap (ord m0) (8 * n m0)) {j : Nat} (hj : 1 ≤ j) (hjs : j < cur.size)
    (w0 : WordAt d' (ord m0 + BitVec.ofNat 64 (8 * (j - 1))) cur[j].toUInt64)
    (w1 : WordAt d' (ord m0 + BitVec.ofNat 64 (8 * (j - 1)) + BitVec.ofNat 64 8)
      (cur[j - 1]'(by omega)).toUInt64)
    (hs : ∀ p, ¬InRange (ord m0 + BitVec.ofNat 64 (8 * (j - 1))) 16 p → d'.get? p = d.get? p) :
    Arr m0 (cur.swapIfInBounds j (j - 1)) d' := by
  have hsz := h.size
  unfold NativeRustcVm.NoWrap at hnw
  refine ⟨by rw [Array.size_swapIfInBounds, hsz], fun t ht ↦ ?_, ?_⟩
  · rw [Array.getElem_swapIfInBounds]
    split
    · exact h.lt64 _ _
    · split
      · exact h.lt64 _ _
      · exact h.lt64 _ _
  · rw [NativeRustcVm.wordsAt_iff]
    intro t ht
    have ht' : t < cur.size := by simpa [natWords] using ht
    simp only [natWords, List.getElem_map, Array.getElem_toList]
    rw [Array.getElem_swapIfInBounds]
    split
    · rename_i hc
      obtain ⟨rfl, -⟩ := hc
      rw [NativeRustcVm.addr_add_add, show 8 * (t - 1) + 8 = 8 * t by omega] at w1
      exact w1
    · split
      · rename_i _ hc
        obtain ⟨rfl, -⟩ := hc
        exact w0
      · rename_i h1 h2
        have h1' : t ≠ j := fun he ↦ h1 ⟨he, by omega⟩
        have h2' : t ≠ j - 1 := fun he ↦ h2 ⟨he, hjs⟩
        refine Arrays.wordAt_congr (h.word ht') fun q hq ↦ hs _ fun hin ↦ ?_
        have hts : t < n m0 := by omega
        rw [NativeRustcVm.addr_add_add, Sym.inRange_iff (by rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega),
          NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)] at hin
        omega

/-- **The inner loop's head** `.L4`: `a = cur[j]` being swapped down, the result the model's. -/
structure Inner (m0 : MachineData) (i j : Nat) (cur : Array Nat) (st : MachineData) : Prop where
  base : Base m0 st
  r8 : reg st .r8 = BitVec.ofNat 64 i
  rax : reg st .rax + 1#64 = BitVec.ofNat 64 i
  r9 : reg st .r9 = BitVec.ofNat 64 cur[j]!
  r10 : reg st .r10 = BitVec.ofNat 64 (j - 1)
  pos : 1 ≤ j
  le : j ≤ i
  ilt : i < n m0
  arr : Arr m0 cur st.dmem
  goal : swapDown (lt m0) (acc m0 i) i = swapDown (lt m0) cur j

/-- **At `.L17`**: element `i` placed. -/
structure Done (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  base : Base m0 st
  r8 : reg st .r8 = BitVec.ofNat 64 i
  rax : reg st .rax + 1#64 = BitVec.ofNat 64 i
  ilt : i < n m0
  arr : Arr m0 (acc m0 (i + 1)) st.dmem

omit [Host] in
theorem n_lt {m0 : MachineData} (hF : Facts m0) : 8 * n m0 ≤ 2 ^ 64 := by
  have : (ord m0).toNat + 8 * n m0 ≤ 2 ^ 64 := hF.or.2
  omega

/-- `b6`: `b = order[j - 1]` loaded, on to the comparison. -/
theorem l6 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {i j : Nat}
    {cur : Array Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b6Offset))
    (hI : Inner m0 i j cur st.data) :
    Eventually (step1 Host.exe) (Q k m0 st.data.dmem i j cur[j]! cur[j - 1]!) st := by
  have hsz := hI.arr.size
  have hj1 : j - 1 < cur.size := by have := hI.le; have := hI.ilt; omega
  have hjl : j < cur.size := by have := hI.le; have := hI.ilt; omega
  have hn8 := n_lt hF
  have hwf := hF.wf_el (st := st.data) hI.base.frame.kept hF.or hF.oo (o := 8 * (j - 1)) (l := 8)
    (by have := hI.le; have := hI.ilt; omega) (by omega)
  have hm := match_el (p := .rdi) (x := .r10) (t := j - 1) (l := 8) hI.base.frame hI.base.rdi
    (by rw [hI.r10, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, h11, hcf⟩ := after_eq run_b6 ▸ b6_facts
  have e1 := regs_eq_of hm hm1 hk
  have hld : (frameEnv m0 st.data 16 [(ord m0 + BitVec.ofNat 64 (8 * (j - 1)), 8)]).load 1 0 8 =
      BitVec.ofNat 64 cur[j - 1]! := by
    rw [getElem!_pos cur (j - 1) hj1]
    refine (Arrays.load_word ?_).trans (toBitVec_toUInt64 _)
    rw [show (frameEnv m0 st.data 16 [(ord m0 + BitVec.ofNat 64 (8 * (j - 1)), 8)]).base 1 =
      ord m0 + BitVec.ofNat 64 (8 * (j - 1)) from rfl, BitVec.add_zero]
    exact hI.arr.word hj1
  obtain ⟨hb1, hd1⟩ := hI.base.quiet hwf hm1 hq fun r hr ↦ e1 r (by
    simp only [kB, List.mem_append]; exact Or.inl (Or.inl hr))
  have ha := hI.arr.lt64 j hjl
  have hb := hI.arr.lt64 (j - 1) hj1
  have hc : Cmp m0 st.data.dmem i j cur[j]! cur[j - 1]! st1.data :=
    ⟨hb1, hd1, (e1 .r8 (by simp [kB])).trans hI.r8, by rw [e1 .rax (by simp [kB])]; exact hI.rax,
      (e1 .r9 (by simp [kB])).trans hI.r9, (e1 .r10 (by simp [kB])).trans hI.r10,
      (hm1.regs .r11 _ h11).trans hld, by rw [getElem!_pos cur j hjl]; exact ha,
      by rw [getElem!_pos cur (j - 1) hj1]; exact hb⟩
  have hcns : reg st.data .rcx = BitVec.ofNat 64 (ns m0) := by rw [hI.base.rcx]; simp
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn'⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval, Bool.not_eq_true'] at hy hn'
  rw [hld, show (frameEnv m0 st.data 16 [(ord m0 + BitVec.ofNat 64 (8 * (j - 1)), 8)]).regs .rcx =
      reg st.data .rcx from rfl, hcns, ofNat_ult hc.blt (by have := (reg m0 .rcx).isLt; omega)]
    at hy hn'
  by_cases hbn : cur[j - 1]! < ns m0
  · exact l7 hp hF ((hn' (by simpa using hbn)).trans (congrArg Host.addrOf
      (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b6_next]))) hc hbn
  · exact l5 hp hF ((hy (by simpa using hbn)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_5_at)) hc (by omega)

omit [Host] in
theorem addC_m1 {t : Nat} (ht : t < 2 ^ 64) :
    CmpOp.apply .addC .W64 (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 t) =
      decide (t ≠ 0) := by
  simp only [CmpOp.apply, low_W64, BitVec.unsigned, BitVec.toNat_add, BitVec.toNat_ofNat,
    show Width.W64.bits = 64 from rfl]
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ne_eq]
  constructor
  · intro h h0; subst h0; simp at h
  · intro h; omega

/-- **A turn of the inner loop**: `b` compared, swapped or not. -/
theorem inner (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {i j : Nat}
    {cur : Array Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b6Offset))
    (hI : Inner m0 i j cur st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b3Offset) ∧ Done m0 i s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b6Offset) ∧ ∃ cur', Inner m0 i (j - 1) cur' s.data)) st := by
  have hsz := hI.arr.size
  have hjl : j < cur.size := by have := hI.le; have := hI.ilt; omega
  have hj1 : j - 1 < cur.size := by omega
  have hpos := hI.pos
  have hn8 := n_lt hF
  have hsd : swapDown (lt m0) cur j = if lt m0 cur[j]! cur[j - 1]! then
      swapDown (lt m0) (cur.swapIfInBounds j (j - 1)) (j - 1) else cur := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact swapDown_succ cur j'
  refine Eventually.bind (l6 hp hF hpc hI) fun s hq ↦ ?_
  rcases hq with ⟨hpc', hc, hf⟩ | ⟨hpc', hc, ht⟩
  · -- no swap: `cur` is the result
    refine .done _ (Or.inl ⟨hpc', hc.base, hc.r8, hc.rax, hI.ilt, ?_⟩)
    rw [acc_succ, hI.goal, hsd, hf, hc.dmem]
    exact hI.arr
  · -- `b18`: the swap
    have hle := hI.le
    have hil := hI.ilt
    have hwf := hF.wf_el (st := s.data) hc.base.frame.kept hF.or hF.oo (o := 8 * (j - 1))
      (l := 16) (by omega) (by omega)
    have hm := match_el (p := .rdi) (x := .r10) (t := j - 1) (l := 16) hc.base.frame
      hc.base.rdi (by rw [hc.r10, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
    refine exec_at (infix_of b18_in_code (by simp [b18]) hp) run_b18 hwf nofun hpc' hm
      fun s' hm' hpc'' ↦ ?_
    obtain ⟨hmid, hk, hw, hv0, hv1, h11, hcf⟩ := after_eq run_b18 ▸ b18_facts
    have e1 := regs_eq_of hm hm' hk
    have w0 := Arrays.wordAt_of_write hm' (r := 1) (o := 0) (b := ord m0 + BitVec.ofNat 64 (8 * (j - 1)))
      (sz := 16) (v := .reg .r9) rfl (by omega) hv0
    have w1 := Arrays.wordAt_of_write hm' (r := 1) (o := 8) (b := ord m0 + BitVec.ofNat 64 (8 * (j - 1)))
      (sz := 16) (v := .reg .r11) rfl (by omega) hv1
    rw [Arrays.eval_reg, Env.ofMachine_regs] at w0 w1
    rw [BitVec.add_zero, show s.data.regs.get64 .r9 = reg s.data .r9 from rfl, hc.r9,
      getElem!_pos cur j hjl] at w0
    rw [show s.data.regs.get64 .r11 = reg s.data .r11 from rfl, hc.r11,
      getElem!_pos cur (j - 1) hj1] at w1
    have hws : ∀ q, ¬InRange (ord m0 + BitVec.ofNat 64 (8 * (j - 1))) 16 q →
        s'.data.dmem.get? q = s.data.dmem.get? q := fun q hq ↦
      hm'.get?_mem0 hwf fun hW ↦ hq (by
        obtain ⟨e, he, hin⟩ := written_in hwf (rs := [(1, 16)])
          (by intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨16, rfl, le_rfl⟩)
          (fun w hw' ↦ ⟨(1, 16), by simp, (hw w hw').1, (hw w hw').2⟩) hW
        simp only [List.mem_singleton] at he
        subst he
        exact hin)
    have harr := (hc.dmem ▸ hI.arr).swap hF.or.2 hpos hjl
      (by convert w0 using 2; exact (toBitVec_toUInt64 _).symm) w1 hws
    have hbase : Base m0 s'.data := by
      refine ⟨Frame.of_block hc.base.frame hwf hm' hmid slots_le, fun r hr ↦ (e1 r (by
          simp only [kB, List.mem_append]; exact Or.inl (Or.inl hr))).trans (hc.base.regs r hr),
        fun q h1 h2 ↦ (hws q fun h ↦ h1 ?_).trans (hc.base.same q h1 h2)⟩
      exact NativeRustcVm.InRange.of_sub h hF.or.2 (by omega)
    have hgoal : swapDown (lt m0) (acc m0 i) i =
        swapDown (lt m0) (cur.swapIfInBounds j (j - 1)) (j - 1) := by
      rw [hI.goal, hsd, ht]; rfl
    have hr10 : reg s.data .r10 = BitVec.ofNat 64 (j - 1) := hc.r10
    simp only [PcOk] at hpc''
    obtain ⟨hy, hn'⟩ := pc_cond hpc''
    simp only [SBool.eval, Sym.eval, Bool.not_eq_true'] at hy hn'
    rw [show (frameEnv m0 s.data 16 [(ord m0 + BitVec.ofNat 64 (8 * (j - 1)), 16)]).regs .r10 =
      reg s.data .r10 from rfl, hr10, addC_m1 (by omega)] at hy hn'
    by_cases h1 : j = 1
    · refine .done _ (Or.inl ⟨(hy (by simp [h1])).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_17_at), hbase,
        (e1 .r8 (by simp [kB])).trans hc.r8, by rw [e1 .rax (by simp [kB])]; exact hc.rax,
        hI.ilt, ?_⟩)
      have h0 : j - 1 = 0 := by omega
      rw [acc_succ, hgoal, h0]
      rw [h0] at harr
      exact harr
    · -- `b19`: on with `j - 1`
      have hpc2 := hn' (by simp; omega)
      have hwf2 := hF.wf0 hbase.frame.kept (st := s'.data)
      have hm2 := match_regs hbase.frame
      refine exec_at (infix_of b19_in_code (by simp [b19]) hp) run_b19 hwf2 nofun
        (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b18_next))) hm2
        fun s2 hm3 hpc3 ↦ ?_
      obtain ⟨hq2, hk2, h10, hcf2⟩ := after_eq run_b19 ▸ b19_facts
      have e2 := regs_eq_of hm2 hm3 hk2
      obtain ⟨hb2, hd2⟩ := hbase.quiet hwf2 hm3 hq2 fun r hr ↦ e2 r (by
        simp only [kB, List.mem_append]; exact Or.inl (Or.inl hr))
      have hr11 : reg s'.data .r11 = BitVec.ofNat 64 (j - 1 - 1) := by
        rw [show reg s'.data .r11 = _ from hm'.regs .r11 _ h11]
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
        rw [show s.data.regs.get64 .r10 = reg s.data .r10 from rfl, hr10]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show Width.W64.bits = 64 from rfl]
        omega
      simp only [PcOk] at hpc3
      obtain ⟨hy3, hn3⟩ := pc_cond hpc3
      simp only [SBool.eval, Sym.eval] at hy3 hn3
      rw [show (frameEnv m0 s'.data 16 []).regs .r10 = reg s'.data .r10 from rfl,
        show (frameEnv m0 s'.data 16 []).regs .rsi = reg s'.data .rsi from rfl,
        (e1 .r10 (by simp [kB])).trans hr10, hbase.rsi,
        show reg m0 .rsi = BitVec.ofNat 64 (n m0) by simp,
        ofNat_ult (by omega) (by have := (reg m0 .rsi).isLt; omega)] at hy3 hn3
      refine .done _ (Or.inr ⟨(hy3 (by simp; omega)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_4_at),
        cur.swapIfInBounds j (j - 1), ⟨hb2, ?_, ?_, ?_, ?_, by omega, by omega, hI.ilt,
          by rw [hd2]; exact harr, hgoal⟩⟩)
      · rw [e2 .r8 (by simp [kB]), e1 .r8 (by simp [kB])]; exact hc.r8
      · rw [e2 .rax (by simp [kB]), e1 .rax (by simp [kB])]; exact hc.rax
      · rw [e2 .r9 (by simp [kB]), e1 .r9 (by simp [kB]), hc.r9,
          getElem!_pos cur j hjl,
          getElem!_pos _ (j - 1) (by rw [Array.size_swapIfInBounds]; exact hj1),
          Array.getElem_swapIfInBounds]
        split
        · rename_i hc'; omega
        · split
          · rfl
          · rename_i h2; exact absurd ⟨rfl, hjl⟩ h2
      · rw [show reg s2.data .r10 = _ from hm3.regs .r10 _ h10]
        exact hr11

/-- **The inner loop**, to `.L17`. -/
theorem innerLoop (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {i j : Nat}
    {cur : Array Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b6Offset))
    (hI : Inner m0 i j cur st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b3Offset) ∧ Done m0 i s.data) st := by
  refine Sym.loop (fun j s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b6Offset) ∧ ∃ cur, Inner m0 i j cur s.data)
    (fun j s ⟨hpc, cur, hI⟩ ↦ ?_) ⟨hpc, cur, hI⟩
  refine Eventually.mono (inner hp hF hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', cur', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨j - 1, by have := hI.pos; omega, hpc', cur', hI'⟩

/-- **The outer loop's head** `.L2`: `i` elements placed. -/
structure Outer (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  base : Base m0 st
  r8 : reg st .r8 = BitVec.ofNat 64 i
  rax : reg st .rax + 1#64 = BitVec.ofNat 64 i
  ilt : i < n m0
  arr : Arr m0 (acc m0 i) st.dmem

omit [Host] in
theorem rax_val {x : BitVec 64} {i : Nat} (h : x + 1#64 = BitVec.ofNat 64 i) (hi : 1 ≤ i)
    (hi' : i < 2 ^ 64) : x = BitVec.ofNat 64 (i - 1) := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- `b4`, `b5`: element `i` taken, swapped down. -/
theorem outer (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {i : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b4Offset)) (hO : Outer m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b3Offset) ∧ Done m0 i s.data) st := by
  have hn8 := n_lt hF
  have hil := hO.ilt
  have hwf := hF.wf0 hO.base.frame.kept (st := st.data)
  have hm := match_regs hO.base.frame
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf nofun hpc hm
    fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hq, hk, hzf⟩ := after_eq run_b4 ▸ b4_facts
  have e1 := regs_eq_of hm hm1 hk
  obtain ⟨hb1, hd1⟩ := hO.base.quiet hwf hm1 hq fun r hr ↦ e1 r (by
    simp only [kB, List.mem_append]; exact Or.inl hr)
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn'⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    BitVec.and_self] at hy hn'
  rw [show (frameEnv m0 st.data 16 []).regs .r8 = reg st.data .r8 from rfl, hO.r8,
    NativeRustcX64.Sym.ofNat_beq (by omega) (by decide)] at hy hn'
  by_cases h0 : i = 0
  · refine .done _ ⟨(hy (by simpa using h0)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_17_at), hb1,
      (e1 .r8 (by simp [kB])).trans hO.r8, by rw [e1 .rax (by simp [kB])]; exact hO.rax, hil, ?_⟩
    rw [acc_succ, h0, hd1]
    rw [h0] at hO
    exact hO.arr
  · have hpc2 := hn' (by simpa using h0)
    have hsz := hO.arr.size
    have hil' : i < (acc m0 i).size := by omega
    have hwf2 := hF.wf_el (st := s1.data) hb1.frame.kept hF.or hF.oo (o := 8 * i) (l := 8)
      (by omega) (by omega)
    have hm2 := match_el (p := .rdi) (x := .r8) (t := i) (l := 8) hb1.frame hb1.rdi
      (by rw [e1 .r8 (by simp [kB]), hO.r8, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf2 nofun
      (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b4_next))) hm2
      fun s2 hm3 hpc3 ↦ ?_
    obtain ⟨hq2, hk2, h9, h10⟩ := after_eq run_b5 ▸ b5_facts
    have e2 := regs_eq_of hm2 hm3 hk2
    obtain ⟨hb2, hd2⟩ := hb1.quiet hwf2 hm3 hq2 fun r hr ↦ e2 r (by
      simp only [kB, List.mem_append]; exact Or.inl hr)
    have hrax : reg s1.data .rax = BitVec.ofNat 64 (i - 1) := by
      rw [e1 .rax (by simp [kB])]; exact rax_val hO.rax (by omega) (by omega)
    simp only [PcOk] at hpc3
    have hl5 : b5.length = 3 := rfl
    refine innerLoop hp hF (hpc3.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b5_next))) ⟨hb2, ?_, ?_, ?_, ?_, by omega, le_refl _, hil, by rw [hd2, hd1]; exact hO.arr, rfl⟩
    · rw [e2 .r8 (by simp [kB]), e1 .r8 (by simp [kB])]; exact hO.r8
    · rw [e2 .rax (by simp [kB]), e1 .rax (by simp [kB])]; exact hO.rax
    · rw [show reg s2.data .r9 = _ from hm3.regs .r9 _ h9, getElem!_pos _ i hil']
      refine (Arrays.load_word ?_).trans (toBitVec_toUInt64 _)
      rw [show (frameEnv m0 s1.data 16 [(ord m0 + BitVec.ofNat 64 (8 * i), 8)]).base 1 =
        ord m0 + BitVec.ofNat 64 (8 * i) from rfl, BitVec.add_zero, Env.ofMachine_mem0, hd1]
      exact hO.arr.word hil'
    · rw [show reg s2.data .r10 = _ from hm3.regs .r10 _ h10]; exact hrax

/-- `insertion_sort`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ InsertionSortPost m0 s.data

/-- `b21`, `b22`: the pops and the return. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b21Offset)) (hb : Base m0 st.data)
    (ha : Arr m0 (acc m0 (n m0)) st.data.dmem) : Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := hF.wf0 hb.frame.kept (st := st.data)
  have hm := match_regs hb.frame
  refine exec_at (infix_of b21_in_code (by simp [b21]) hp) run_b21 hwf nofun hpc hm
    fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  refine exec_at (infix_of b22_in_code (by simp [b22]) hp) (exec_after run_b21 run_b22) hwf nofun
    (hpc1.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b21_next))) hm1
    fun s2 hm2 hpc2 ↦ ?_
  obtain ⟨hepi, hmem⟩ := after_eq (exec_after run_b21 run_b22) ▸ b21_facts
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hb.frame hwf hm2 hepi
  have hd : s2.data.dmem = st.data.dmem := hm2.dmem_eq hwf hmem
  simp only [PcOk] at hpc2
  refine .done _ ⟨by rw [hpc2]; exact hb.frame.load_ret hF.stack le_rfl, hrsp, ?_, ?_, hsv⟩
  · show WordsAt _ _ (natWords (insertionSort (lt m0) (xs0 m0)))
    rw [insertionSort_eq, hd]; exact ha.words
  · intro q hq
    rw [hd]
    exact hb.same q (fun h ↦ hq (Or.inl h)) (fun h ↦ hq (Or.inr h))

omit [Host] in
/-- `order` at the entry. -/
theorem arr0 {m0 : MachineData} (hF : Facts m0) : Arr m0 (acc m0 0) m0.dmem := by
  refine ⟨size_natsOf _ _ _, fun t ht ↦ ?_, ?_⟩
  · simp [acc, xs0, natsOf]
    exact UInt64.toNat_lt _
  · have : natWords (acc m0 0) = wordsOf m0.dmem (ord m0) (n m0) := by
      simp [acc, xs0, natsOf, natWords, List.map_map, Function.comp_def]
    rw [this]
    exact NativeRustcVm.wordsAt_of_mapped hF.or.1

/-- **`insertion_sort` meets its contract.** -/
theorem insertionSort_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.entryLabel) InsertionSortPre InsertionSortPost := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  have hn8 := n_lt hF
  rw [show Labels.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b0Offset) from hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.entry_at]
  have hwf := hF.wf0 (st := m0) fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 16 []) entryS m0 := Field.match_frame
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm
    fun s hm1 hpc ↦ ?_
  obtain ⟨hkeep, hmem0, hkA, hzf⟩ := after_eq run_b0 ▸ b0_facts
  simp only [PcOk, NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b0_length] at hpc
  obtain ⟨hy, hn'⟩ := pc_cond hpc
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    BitVec.and_self] at hy hn'
  rw [show (frameEnv m0 m0 16 []).regs .rsi = BitVec.ofNat 64 (n m0) by simp,
    NativeRustcX64.Sym.ofNat_beq (by omega) (by decide)] at hy hn'
  by_cases h0 : n m0 = 0
  · -- no elements: `b22` returns
    refine exec_at (infix_of b22_in_code (by simp [b22]) hp) (exec_after run_b0 run_b22e) hwf
      nofun ((hy (by simpa using h0)).trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_19_at)) hm1 fun s2 hm2 hpc2 ↦ ?_
    obtain ⟨hsp, hkp, hmem⟩ := after_eq (exec_after run_b0 run_b22e) ▸ b22e_facts
    obtain ⟨h1, h2, h3, h4⟩ := Field.leaf_done hF.stack hm2 hpc2 hsp hkp (by simp)
    refine .done _ ⟨h1, h2, ?_, fun q hq ↦ h3 q fun h ↦ hq (Or.inr h), h4⟩
    show WordsAt _ _ (natWords (insertionSort (lt m0) (xs0 m0)))
    rw [insertionSort_eq, h0]
    have := (arr0 hF).words
    rw [show s2.data.dmem = m0.dmem from hm2.dmem_eq hwf hmem]
    exact this
  · -- the prologue, then the loop
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf nofun
      (hn' (by simpa using h0)) hm1 fun s1 hm2 hpc2 ↦ ?_
    obtain ⟨hpro, hw, hk, hrax, hr8⟩ := after_eq run_b1 ▸ b1_facts
    have hf := Frame.of_prologue (Frame.entry (m0 := m0) (F := 16)) hwf hm2 hpro slots_le slots_cs
    have e := regs_eq_of hm hm2 hk
    have hb : Base m0 s1.data := ⟨hf, e, fun q _ h2 ↦ hm2.get?_mem0 hwf fun hW ↦ h2
      (Arrays.written_region0 (k := 16) rfl hwf (by omega) hw hW)⟩
    have hd : ∀ q, ¬InRange (stackBelow m0 16) 16 q → s1.data.dmem.get? q = m0.dmem.get? q :=
      fun q h2 ↦ hm2.get?_mem0 hwf fun hW ↦ h2
        (Arrays.written_region0 (k := 16) rfl hwf (by omega) hw hW)
    have harr : Arr m0 (acc m0 0) s1.data.dmem := by
      obtain ⟨h1, h2, h3⟩ := arr0 hF
      refine ⟨h1, h2, ?_⟩
      rw [NativeRustcVm.wordsAt_iff]
      intro t ht
      have ht' : t < n m0 := by simpa [natWords, h1] using ht
      refine Arrays.wordAt_congr (NativeRustcVm.WordsAt.getElem h3 ht) fun q hq ↦ hd _ fun h ↦ ?_
      have hO := hF.oo
      have hsn := Transcript.stack_noWrap hF.stack
      have hon : (ord m0).toNat + 8 * n m0 ≤ 2 ^ 64 := hF.or.2
      unfold OffStack NativeRustcX64.Apart at hO
      unfold NativeRustcVm.NoWrap at hsn
      rw [NativeRustcVm.addr_add_add, Sym.inRange_iff hsn,
        NativeRustcVm.toNat_add_ofNat (by omega)] at h
      omega
    simp only [PcOk] at hpc2
    have hO : Outer m0 0 s1.data :=
      ⟨hb, hm2.regs .r8 _ hr8, by
        rw [show reg s1.data .rax = _ from hm2.regs .rax _ hrax]
        show BitVec.ofNat 64 18446744073709551615 + 1#64 = BitVec.ofNat 64 0
        decide,
        by omega, harr⟩
    refine Sym.loop (fun r s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b4Offset) ∧ ∃ i, n m0 - i = r ∧ Outer m0 i s.data)
      (fun r s ⟨hpc, i, hr, hO⟩ ↦ ?_) ⟨hpc2.trans (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_2_at), 0, rfl, hO⟩
    refine Eventually.bind (outer hp hF hpc hO) fun s2 ⟨hpc2, hD⟩ ↦ ?_
    -- `b3`: the next element, or the end
    have hil := hD.ilt
    have hwf3 := hF.wf0 hD.base.frame.kept (st := s2.data)
    have hm3 := match_regs hD.base.frame
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf3 nofun hpc2 hm3
      fun s3 hm4 hpc3 ↦ ?_
    obtain ⟨hq3, hk3, h8', hax', hzf3⟩ := after_eq run_b3 ▸ b3_facts
    obtain ⟨hb3, hd3⟩ := hD.base.quiet hwf3 hm4 hq3 (regs_eq_of hm3 hm4 hk3)
    have hr8 : reg s3.data .r8 = BitVec.ofNat 64 (i + 1) := by
      rw [show reg s3.data .r8 = _ from hm4.regs .r8 _ h8']
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show s2.data.regs.get64 .r8 = reg s2.data .r8 from rfl, hD.r8, BitVec.ofNat_add]
    have hrax : reg s3.data .rax + 1#64 = BitVec.ofNat 64 (i + 1) := by
      rw [show reg s3.data .rax = _ from hm4.regs .rax _ hax']
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show s2.data.regs.get64 .rax = reg s2.data .rax from rfl, BitVec.add_assoc,
        BitVec.add_comm 1#64, ← BitVec.add_assoc, hD.rax, BitVec.ofNat_add]
    simp only [PcOk] at hpc3
    obtain ⟨hy3, hn3⟩ := pc_cond hpc3
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64] at hy3 hn3
    rw [show (frameEnv m0 s2.data 16 []).regs .r8 = reg s2.data .r8 from rfl,
      show (frameEnv m0 s2.data 16 []).regs .rsi = reg s2.data .rsi from rfl, hD.r8, hD.base.rsi,
      show reg m0 .rsi = BitVec.ofNat 64 (n m0) by simp, ← BitVec.ofNat_add,
      NativeRustcX64.Sym.ofNat_beq (by omega) (by omega)] at hy3 hn3
    by_cases hlast : i + 1 = n m0
    · exact Eventually.mono (finish hp hF ((hy3 (by simpa using hlast)).trans
        (hp.label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.label_18_at)) hb3 (by rw [← hlast, hd3]; exact hD.arr)) fun _ h ↦ Or.inl h
    · exact .done _ (Or.inr ⟨n m0 - (i + 1), by omega, (hn3 (by simpa using hlast)).trans
        (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.b3_next)), i + 1, rfl,
        hb3, hr8, hrax, by omega, by rw [hd3]; exact hD.arr⟩)

end

end NativeRustcVmX64.Layout.InsertionSort
