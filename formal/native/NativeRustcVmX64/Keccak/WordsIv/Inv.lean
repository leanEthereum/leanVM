module

public import NativeRustcVmX64.Keccak.WordsHash.Lane
public import NativeRustcVmX64.Keccak.WordsIv.Vals
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.MemLemmas
public import NativeRustcVmX64.Code.Vm.IvWord.Names

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` (x86-64): what holds between its blocks

From the machine state `m0` at the entry (`out`, `count = n + 2`, `len = 9 + 8 n`, the bytecode
`bc` of `n` words in RDI, RSI, RDX, RCX, R8): the frame, the lanes and `pre` are
`keccak256_words::<hash_words's closure>`'s (`WordsHash.frame`, `Lanes`, `pre`, `Ctx`). The
bytecode's words at entry `bcw` (any words there are them, `eq_bcw`), the closure's word `i`
(`wv`: `ivWord`, zero from the count), the whole blocks' count `nb = len / 136`. `ICtx m0 R o m`:
`Ctx` with the slots `nb`, `len`, `out` (`slotsI`) and R13 the count, R12 the bytecode, R15 its
word count, then the registers `R`. `call_iv`: a call of `iv_word` for word `i` below the count
returns `wv m0 i` in RAX.
-/

namespace NativeRustcVmX64.WordsIv

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt)
open NativeRustcVmX64.WordsHash (frame Ctx Lanes pre LowSlots RegsAt stk_eq stack_facts
  frame_mapped frame_add_toNat)
open NativeRustcVmX64.Keccak (bytesAt_of_same not_inRange_of_apart)

@[expose] public section

/-- The bytecode's word count `n`. -/
def nW (m0 : MachineData) : Nat := (m0.regs.get64 .r8).toNat

/-- The bytecode. -/
def bc (m0 : MachineData) : BitVec 64 := m0.regs.get64 .rcx

/-- The count of words the closure gives, `n + 2`. -/
def cnt (m0 : MachineData) : Nat := (m0.regs.get64 .rsi).toNat

/-- The byte length, `9 + 8 n`. -/
def lenI (m0 : MachineData) : Nat := (m0.regs.get64 .rdx).toNat

/-- The whole blocks' count. -/
def nb (m0 : MachineData) : Nat := lenI m0 / 136

/-- The bytecode's words at the entry. -/
def bcw (m0 : MachineData) : List UInt64 := NativeRustcVm.wordsOf m0.dmem (bc m0) (nW m0)

/-- Word `i` the closure gives `keccak256_words`: `ivWord` of the bytecode, zero from the
count. -/
def wv (m0 : MachineData) (i : Nat) : UInt64 :=
  if i < cnt m0 then NativeRustcVm.Keccak.ivWord (bcw m0) i else 0

/-- The function's slots: `nb`, `len`, `out`. -/
def slotsI (m0 : MachineData) : List (Nat × BitVec 64) :=
  [(16, BitVec.ofNat 64 (nb m0)), (24, m0.regs.get64 .rdx), (32, m0.regs.get64 .rdi)]

/-- **What holds throughout the body**: R13 the count, R12 the bytecode, R15 its word count, then
`R`. -/
abbrev ICtx (m0 : MachineData) (R : List (Reg64 × BitVec 64)) (o : Nat) (m : MachineData) :
    Prop :=
  Ctx m0 (slotsI m0) ((.r13, m0.regs.get64 .rsi) :: (.r12, bc m0) :: (.r15, m0.regs.get64 .r8) ::
    R) o m

/-- Word `B + j` (`B` in `x`) is below the count R13. -/
def cmpI (x : Reg64) (j : Nat) : SBool :=
  .cmp .ult .W64 (.bin .add .W64 (.reg x) (.lit j)) (.reg .r13)

/-- The facts of the precondition the steps use. -/
structure Geo [Labels] (m0 : MachineData) : Prop where
  stk : StackOk m0 NativeRustcVmX64.keccak256WordsStack
  rc : NativeRustcVmX64.RcAt m0 NativeRustcVmX64.keccak256WordsStack
  cnt : cnt m0 = nW m0 + 2
  len : lenI m0 = 9 + 8 * nW m0
  small : 9 + 8 * nW m0 < 2 ^ 32
  map : Mapped m0.dmem (bc m0) (8 * nW m0)
  nw : NoWrap (bc m0) (8 * nW m0)
  ap : 0 < nW m0 → Apart (bc m0) (8 * nW m0) (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
    (NativeRustcVmX64.keccak256WordsStack + 8)
  got : GotAt m0 NativeRustcVmX64.keccak256WordsStack
    [(m0.regs.get64 .rdi, 32), (NativeRustcVmX64.rcAddr, 192)] ["memcpy", "memset"]

end

public section

theorem slotsI_low (m0 : MachineData) : LowSlots (slotsI m0) := by
  simp [LowSlots, AllOf, slotsI]

theorem wv_of_lt {m0 : MachineData} {i : Nat} (h : i < cnt m0) :
    wv m0 i = NativeRustcVm.Keccak.ivWord (bcw m0) i := by
  simp [wv, h]

theorem wv_of_ge {m0 : MachineData} {i : Nat} (h : cnt m0 ≤ i) : wv m0 i = 0 := by
  simp [wv, show ¬ i < cnt m0 by omega]

theorem bv_eq_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

section

variable [Labels]

/-- Every word of a whole block is below the count. -/
theorem full_lt {m0 : MachineData} (g : Geo m0) {b j : Nat} (hb : b < nb m0) (hj : j ≤ 16) :
    17 * b + j < cnt m0 := by
  have := g.len
  have := g.cnt
  unfold nb at hb
  omega

theorem nb_small {m0 : MachineData} (g : Geo m0) : nb m0 < 2 ^ 25 := by
  have := g.len
  have := g.small
  unfold nb
  omega

theorem cnt_small {m0 : MachineData} (g : Geo m0) : cnt m0 < 2 ^ 32 := by
  have := g.len
  have := g.small
  have := g.cnt
  omega

theorem nb17_le {m0 : MachineData} (g : Geo m0) : 17 * nb m0 ≤ cnt m0 := by
  have := g.len
  have := g.cnt
  unfold nb
  omega

/-- The bytecode's bytes are outside the stack the function uses. -/
theorem bc_same {m0 : MachineData} (g : Geo m0) {i : Nat} (hi : i < 8 * nW m0) :
    ¬ InRange (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
      NativeRustcVmX64.keccak256WordsStack (bc m0 + BitVec.ofNat 64 i) := by
  have hs := stack_facts g.stk
  have hap := g.ap (by omega)
  rw [stk_eq] at hap ⊢
  refine not_inRange_of_apart g.nw (by unfold NoWrap; omega) (by unfold Apart at hap ⊢; omega) hi

/-- **The bytecode's words**, in any state whose memory is the entry's outside the stack. -/
theorem wordsAt_bcw {m0 : MachineData} (g : Geo m0) {d : DataMem}
    (hs : SameOutside m0.dmem d (InRange (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
      NativeRustcVmX64.keccak256WordsStack)) :
    NativeRustcVm.WordsAt d (bc m0) (bcw m0) :=
  bytesAt_of_same hs (NativeRustcVm.wordsAt_of_mapped g.map) fun i hi => bc_same g (by
    rw [NativeRustcVm.length_wordsBytes, bcw, NativeRustcVm.length_wordsOf] at hi
    exact hi)

/-- The words of the bytecode at entry are `bcw`. -/
theorem eq_bcw {m0 : MachineData} (g : Geo m0) {w : List UInt64} (hlen : w.length = nW m0)
    (hw : NativeRustcVm.WordsAt m0.dmem (bc m0) w) : w = bcw m0 := by
  have hb := NativeRustcVm.wordsAt_of_mapped g.map
  refine List.ext_getElem (by rw [hlen, bcw, NativeRustcVm.length_wordsOf]) fun i h1 h2 => ?_
  exact (NativeRustcVm.WordsAt.getElem hw h1).unique (NativeRustcVm.WordsAt.getElem hb h2)

/-- The comparison of word `B + j` with the count. -/
theorem cmpI_eval {m0 : MachineData} (g : Geo m0) {env : Env} {x : Reg64} {B j : Nat}
    (hx : env.regs x = BitVec.ofNat 64 B) (h13 : env.regs .r13 = m0.regs.get64 .rsi)
    (hB : B + j < 2 ^ 32) : (cmpI x j).eval env = decide (B + j < cnt m0) := by
  have hc := cnt_small g
  simp only [cmpI, SBool.eval, Sym.eval, CmpOp.apply, low_W64, NativeRustcVmX64.WordsHash.add64,
    hx, h13]
  rw [bv_eq_ofNat (m0.regs.get64 .rsi)]
  exact NativeRustcVmX64.WordsHash.ult_ofNat (by omega) (by unfold cnt at hc; omega)

end

variable [Host]

/-- **A call of `iv_word`** for word `i` below the count, RSP at the frame. -/
theorem call_iv (hiv : Spec (label NativeRustcVmX64.Vm.IvWord.entryLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {m0 : MachineData} (g : Geo m0)
    {L : List (Nat × BitVec 64)} {R : List (Reg64 × BitVec 64)} {st : MachineState} {env : Env}
    {next : Int64} (hc : Ctx m0 L R 0 st.data)
    (hrdi : st.data.regs.get64 .rdi = bc m0) (hrsi : st.data.regs.get64 .rsi = m0.regs.get64 .r8)
    {i : Nat} (hrdx : st.data.regs.get64 .rdx = BitVec.ofNat 64 i) (hi : i < cnt m0)
    (hpc : PcOk env (.call NativeRustcVmX64.Vm.IvWord.entryLabel) next st) {Q : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → rspOf st'.data = rspOf st.data + 8#64 →
      st'.data.dmem = st.data.dmem → Saved st.data st'.data →
      st'.data.regs.get64 .rax = (wv m0 i).toBitVec →
      Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hs := stack_facts g.stk
  have hc32 := cnt_small g
  have hsp : rspOf st.data = frame m0 := by rw [hc.rsp]; exact BitVec.add_zero _
  have hw := wordsAt_bcw g hc.same
  have hlen : (bcw m0).length = nW m0 := by rw [bcw, NativeRustcVm.length_wordsOf]
  have hpre : NativeRustcVmX64.IvWordPre st.data := by
    refine ⟨⟨Nat.zero_le _, by rw [hsp]; omega, fun j hj => ?_⟩, ?_, ?_⟩
    · rw [hsp, BitVec.sub_zero]
      exact frame_mapped g.stk hc.kept _ (by omega)
    · simp only [NativeRustcX64.reg, hrdi, hrsi]
      exact fun j hj => hc.kept _ (g.map j hj)
    · simp only [NativeRustcX64.reg, hrdi, hrsi]
      exact g.nw
  refine call_then hpc hiv hpre fun st' hpc' hrsp' hpost => ?_
  obtain ⟨hax, hd, hsv⟩ := hpost
  refine cont st' hpc' hrsp' hd hsv ?_
  have h := hax (bcw m0) (by rw [hlen]; simp only [NativeRustcX64.reg, hrsi]; rfl)
    (by simp only [NativeRustcX64.reg, hrdi]; exact hw)
  simp only [NativeRustcX64.reg, hrdx] at h
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), wv_of_lt hi,
    Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD,
    NativeRustcVm.Keccak.getD_ivWords]

end

end NativeRustcVmX64.WordsIv
