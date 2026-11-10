import Rv64Verifier.Proofs.Hash.KeccakHashChecks
import Rv64Verifier.Proofs.Hash.HashBytes
import Rv64Verifier.Proofs.Hash.Arith
import Rv64Verifier.Proofs.Hash.KeccakF
import Rv64Verifier.Proofs.Hash.XorBlock

/-!
# `verifier::hash::keccak_hash`

compiled at `0x8000c8e0` (`Blocks/F50.lean`): a 448-byte frame, the state at `sp + 8` cleared by
`memset` (`0x8000c8e0`); the whole blocks' length (`0x8000c938`, `div136`); per whole block
`xor_block` and `keccak_f` (`0x8000c970` .. `0x8000c98c`); the last block at `sp + 208` cleared
by `memset`, the tail copied by `memcpy`, padded (`0x8000c9c4`, `pad_run`), `xor_block`,
`keccak_f`; the digest's bytes (`0x8000c9fc`, `digest_bytes`). The callees' contracts are
hypotheses.
-/

namespace Rv64Verifier.Hash.KeccakHash
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Blocks.F50 Rv64Verifier.Contracts
  Rv64Verifier.Model

/-! ## The data and the absorbed state -/

def len (s : MachineState) : Nat := (s.getReg .x12).toNat

def dataB (s : MachineState) : List (BitVec 8) := bytesAt s (s.getReg .x11) (len s)

/-- The whole blocks. -/
def nb (s : MachineState) : Nat := len s / 136

/-- The state after `j` whole blocks. -/
def absorbed (s : MachineState) (j : Nat) : List Word :=
  (List.range j).foldl (fun state j ↦
    keccakFRust (xorBlockRust state (((dataB s).drop (136 * j)).take 136))) (List.replicate 25 0)

theorem absorbed_succ (s : MachineState) (j : Nat) :
    absorbed s (j + 1) =
      keccakFRust (xorBlockRust (absorbed s j) (((dataB s).drop (136 * j)).take 136)) := by
  rw [absorbed, absorbed, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem keccakHashRust_absorbed (s : MachineState) :
    keccakHashRust (dataB s) = (List.range 4).flatMap fun i ↦ toLeBytes
      ((keccakFRust (xorBlockRust (absorbed s (nb s))
        (padBlockRust ((dataB s).drop (136 * nb s))))).getD i 0) := by
  unfold keccakHashRust absorbed nb
  simp only [dataB, length_bytesAt, len]

/-! ## Bounds and what the calls keep -/

structure Bounds (s : MachineState) : Prop where
  sp : 0x20 + 1104 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
    (s.getReg .x2).toNat % 16 = 0
  out : (s.getReg .x10).toNat % 8 = 0 ∧ (s.getReg .x10).toNat + 32 ≤ 2 ^ 64
  data : (s.getReg .x11).toNat + len s ≤ 2 ^ 64
  outStack : Apart (s.getReg .x10) 32 (s.getReg .x2 - 1104) 1104
  dataStack : Apart (s.getReg .x11) (len s) (s.getReg .x2 - 1104) 1104
  tables : Apart keccakTablesAddr keccakTablesSize (s.getReg .x2 - 1104) 1104
  dataEnd : len s = 0 ∨ (s.getReg .x11).toNat + len s ≤ 0xc0000001

theorem _root_.Rv64Verifier.Contracts.KeccakHashPre.bounds {s : MachineState}
    (h : KeccakHashPre s) : Bounds s := by
  have hs := h.stack.bounds (by decide) (by decide)
  have ho := h.outStack
  have hd := h.dataStack
  have ht := h.tablesStack
  simp only [stackLo, keccakHashStack, keccakFStack, memStack] at hs ho hd ht
  refine ⟨by omega, ⟨h.outAligned, h.out.1⟩, h.data.1, ho, hd, ht, ?_⟩
  by_cases h0 : len s = 0
  · exact Or.inl h0
  · right
    have hv := h.data.2 (len s - 1) (by simp only [len] at h0 ⊢; omega)
    have hw := h.data.1
    simp only [isValidMemAddr, MEM_START, MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START,
      RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat] at hv
    simp only [len] at h0 hv hw ⊢
    omega

/-- A part of `keccak_hash`'s stack is valid. -/
theorem stack_sub {s : MachineState} (hpre : KeccakHashPre s) {b : Word} {m : Nat}
    (h1 : (s.getReg .x2).toNat - 1104 ≤ b.toNat) (h2 : b.toNat + 8 * m ≤ (s.getReg .x2).toNat)
    (h3 : b.toNat % 8 = 0) : ValidMemRange b m := by
  have hb := hpre.bounds
  refine ValidMemRange.sub hpre.stack.valid ?_ ?_ ?_ <;> addr_omega [hb.sp, h1, h2, h3]

/-- The saved registers, and memory outside the stack. -/
structure Common (s t : MachineState) : Prop where
  saved : t.readWords (s.getReg .x2 - 104) 13 = KeccakF.savedRegs s
  frame : ∀ a, ¬ Within a (s.getReg .x2 - 1104) 1104 → t.getMem a = s.getMem a

theorem Common.tables {s t : MachineState} (hpre : KeccakHashPre s) (hc : Common s t) :
    KeccakTables t := by
  have hb := hpre.bounds
  unfold KeccakTables
  rw [← hpre.tables]
  apply readWords_congr
  intro i hi
  exact hc.frame _ (by addr_omega [hb.tables, hb.sp, hi])

/-- A byte outside an aligned range is in a doubleword outside it. -/
theorem align_not_within {a lo : Word} {n : Nat} (hlo : lo.toNat % 8 = 0) (hn : n % 8 = 0)
    (h : ¬ Within a lo n) : ¬ Within (alignToDword a) lo n := by
  have := alignToDword_toNat a
  simp only [Within] at h ⊢
  omega

theorem Common.data {s t : MachineState} (hpre : KeccakHashPre s) (hc : Common s t) {k m : Nat}
    (hkm : k + m ≤ len s) :
    bytesAt t (s.getReg .x11 + BitVec.ofNat 64 k) m = bytesAt s (s.getReg .x11 + BitVec.ofNat 64 k) m := by
  have hb := hpre.bounds
  apply bytesAt_congr
  intro i hi
  apply getByte_congr
  apply hc.frame
  apply align_not_within (by addr_omega [hb.sp]) (by decide)
  rw [ofNat_add_ofNat]
  addr_omega [hb.dataStack, hb.data, hb.sp, hi, hkm]

/-- Memory outside the stack below the saved registers is unchanged from `t` to `u`. -/
def Scratch (s t u : MachineState) : Prop :=
  ∀ a, ¬ Within a (s.getReg .x2 - 1104) 1000 → u.getMem a = t.getMem a

theorem Scratch.refl (s t : MachineState) : Scratch s t t := fun _ _ ↦ rfl

theorem Scratch.trans {s t u v : MachineState} (h₁ : Scratch s t u) (h₂ : Scratch s u v) :
    Scratch s t v := fun a ha ↦ (h₂ a ha).trans (h₁ a ha)

theorem Common.of_scratch {s t u : MachineState} (hb : Bounds s) (hc : Common s t)
    (hf : Scratch s t u) : Common s u where
  saved := by
    rw [← hc.saved]
    apply readWords_congr
    intro i hi
    exact hf _ (by addr_omega [hb.sp, hi])
  frame a ha := by
    rw [← hc.frame a ha]
    exact hf a (by addr_omega [hb.sp, ha])

/-! ## Entry -/

/-- At the loop head, before whole block `j`. -/
structure Loop (s t : MachineState) (j : Nat) : Prop extends Common s t where
  pc : t.pc = 0x8000c970
  lt : j < nb s
  sp : t.getReg .x2 = s.getReg .x2 - 448
  x8 : t.getReg .x8 = s.getReg .x10
  x9 : t.getReg .x9 = BitVec.ofNat 64 (len s % 136)
  x18 : t.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (136 * nb s)
  x11 : t.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (136 * j)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (136 * (nb s - j))
  state : t.readWords (s.getReg .x2 - 440) 25 = absorbed s j

/-- After the whole blocks. -/
structure Tail (s t : MachineState) : Prop extends Common s t where
  pc : t.pc = 0x8000c998
  sp : t.getReg .x2 = s.getReg .x2 - 448
  x8 : t.getReg .x8 = s.getReg .x10
  x9 : t.getReg .x9 = BitVec.ofNat 64 (len s % 136)
  x18 : t.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (136 * nb s)
  state : t.readWords (s.getReg .x2 - 440) 25 = absorbed s (nb s)

theorem blocksE_eval (v : MachineState) :
    blocksE.eval v = BitVec.ofNat 64 (136 * ((v.getReg .x19).toNat / 136)) := by
  simp only [blocksE, mulE, E.eval, BinOp.eval]
  exact div136 _

theorem setup (hMemset : MemsetSpec) {s : MachineState} (hpc : s.pc = 0x8000c8e0)
    (hpre : KeccakHashPre s) :
    ∃ t, Reaches Image.code s t ∧ (Loop s t 0 ∨ Tail s t ∨ Dead Image.code t) := by
  have hb := hpre.bounds
  obtain ⟨t₁, hr₁, h₁⟩ := BlockSpec.reaches b8000c8e0_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hb.sp])
  have k₁ := b8000c8e0_keeps h₁
  have hf₁ := b8000c8e0_frame h₁ (by addr_omega [hb.sp])
  have ht₁2 := b8000c8e0_x2 h₁
  have h200 : (t₁.getReg .x12).toNat = 200 := by rw [b8000c8e0_x12 h₁]; rfl
  have hmpre : MemsetPre t₁ := {
    dst := by
      rw [h200, b8000c8e0_x10 h₁]
      exact bytesValid_of_range (n := 25) (by
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp])
    stack := ⟨by
        simp only [stackLo, memStack, ht₁2]
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp],
      by rw [ht₁2]; addr_omega [hb.sp]⟩
    dstStack := by
      rw [h200, b8000c8e0_x10 h₁]; simp only [stackLo, memStack, ht₁2]; addr_omega [hb.sp] }
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ := hMemset.call hr₁ (b8000c8e0_pc h₁) hmpre
  swap
  · exact ⟨v, hr₂, Or.inr (Or.inr hdead)⟩
  have hfr₂ (a : Word) (h₁a : Apart a 8 (s.getReg .x2 - 440) 200)
      (h₂a : ¬ Within a (s.getReg .x2 - 464) 16) : v.getMem a = t₁.getMem a := by
    apply hpost.frame a
    · rw [h200, b8000c8e0_x10 h₁]; exact h₁a
    · simp only [stackLo, memStack, ht₁2]; addr_omega [h₂a, hb.sp]
  have hzero : bytesAt v (s.getReg .x2 - 440) 200 = List.replicate 200 0 := by
    have := hpost.bytes
    rw [h200, b8000c8e0_x10 h₁, b8000c8e0_x11 h₁] at this
    exact this
  have hv2 : v.getReg .x2 = s.getReg .x2 - 448 := (hpres.reg .x2).trans ht₁2
  have hv8 : v.getReg .x8 = s.getReg .x10 := (hpres.reg .x8).trans (b8000c8e0_x8 h₁)
  have hv9 : v.getReg .x9 = s.getReg .x11 := (hpres.reg .x9).trans (b8000c8e0_x9 h₁)
  have hv19 : v.getReg .x19 = s.getReg .x12 := (hpres.reg .x19).trans (b8000c8e0_x19 h₁)
  obtain ⟨w, hr₃, h₃⟩ := BlockSpec.reaches b8000c938_spec
    (by rw [hvpc, returnAddress_eq, b8000c8e0_x1 h₁]; decide) trivial
  have k₃ := b8000c938_keeps h₃
  have hm₃ := b8000c938_mem_same h₃
  have hregs := blocks_regs
  simp only [Bool.and_eq_true] at hregs
  have hx20 : w.getReg .x20 = BitVec.ofNat 64 (136 * nb s) := by
    rw [h₃.reg_of_ok hregs.1.1, blocksE_eval, hv19]; rfl
  have hx9 : w.getReg .x9 = BitVec.ofNat 64 (len s % 136) := by
    rw [h₃.reg_of_ok hregs.1.2]
    simp only [E.eval, BinOp.eval, blocksE_eval, hv19]
    have : (s.getReg .x12).toNat = len s := rfl
    addr_omega [this, hb.dataEnd]
  have hx18 : w.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (136 * nb s) := by
    rw [h₃.reg_of_ok hregs.2]
    simp only [E.eval, BinOp.eval, blocksE_eval, hv19, hv9]
    rfl
  have hcommon : Common s w := {
    saved := by
      simp only [MachineState.readWords_succ, MachineState.readWords_zero, KeccakF.savedRegs,
        List.cons.injEq, and_true]
      rv_eval []
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        rw [hm₃, hfr₂ _ (by addr_omega [hb.sp]) (by addr_omega [hb.sp])]
      · exact b8000c8e0_m_x2_n104 h₁
      · exact b8000c8e0_m_x2_n96 h₁
      · exact b8000c8e0_m_x2_n88 h₁
      · exact b8000c8e0_m_x2_n80 h₁
      · exact b8000c8e0_m_x2_n72 h₁
      · exact b8000c8e0_m_x2_n64 h₁
      · exact b8000c8e0_m_x2_n56 h₁
      · exact b8000c8e0_m_x2_n48 h₁
      · exact b8000c8e0_m_x2_n40 h₁
      · exact b8000c8e0_m_x2_n32 h₁
      · exact b8000c8e0_m_x2_n24 h₁
      · exact b8000c8e0_m_x2_n16 h₁
      · exact b8000c8e0_m_x2_n8 h₁
    frame := fun a ha ↦ by
      rw [hm₃, hfr₂ a (by addr_omega [ha, hb.sp]) (by addr_omega [ha, hb.sp]),
        hf₁ a (by addr_omega [ha, hb.sp])] }
  have hstate : w.readWords (s.getReg .x2 - 440) 25 = absorbed s 0 := by
    apply readWords_eq (by rfl)
    intro i hi
    rw [hm₃, getMem_of_bytesAt_zero (by addr_omega [hb.sp]) hzero (by omega), absorbed,
      List.range_zero, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp only [hi, ↓reduceIte, Option.getD_some]
  have hw2 : w.getReg .x2 = s.getReg .x2 - 448 := (k₃ .x2 (by decide)).trans hv2
  have hw8 : w.getReg .x8 = s.getReg .x10 := (k₃ .x8 (by decide)).trans hv8
  by_cases hlt : len s < 136
  · have hnb : nb s = 0 := Nat.div_eq_of_lt hlt
    refine ⟨w, hr₂.trans hr₃, Or.inr (Or.inl ⟨hcommon, b8000c938_pc_taken h₃ ?_, hw2, hw8, hx9, hx18,
      by rw [hnb]; exact hstate⟩)⟩
    rw [hv19]; exact hlt
  · refine ⟨w, hr₂.trans hr₃, Or.inl ⟨hcommon, b8000c938_pc_not_taken h₃ ?_, ?_, hw2, hw8, hx9, hx18,
      ?_, ?_, hstate⟩⟩
    · rw [hv19]; exact Nat.le_of_not_lt hlt
    · simp only [nb]; omega
    · rw [b8000c938_x11 h₃, hv9]; simp
    · rw [hx20]; simp

/-! ## A whole block -/

theorem scratch_of {s t u : MachineState} (hb : Bounds s) {lo₁ lo₂ : Word} {n₁ n₂ : Nat}
    (h₁ : (s.getReg .x2).toNat - 1104 ≤ lo₁.toNat ∧ lo₁.toNat + n₁ ≤ (s.getReg .x2).toNat - 104)
    (h₂ : (s.getReg .x2).toNat - 1104 ≤ lo₂.toNat ∧ lo₂.toNat + n₂ ≤ (s.getReg .x2).toNat - 104)
    (hf : ∀ a, ¬ Within a lo₁ n₁ → ¬ Within a lo₂ n₂ → u.getMem a = t.getMem a) :
    Scratch s t u :=
  fun a ha ↦ hf a (by addr_omega [ha, h₁, hb.sp]) (by addr_omega [ha, h₂, hb.sp])

theorem body (hXor : XorBlockSpec) (hKf : KeccakFSpec) {s t : MachineState}
    (hpre : KeccakHashPre s) {j : Nat} (ht : Loop s t j) :
    ∃ u, Reaches Image.code t u ∧ (Loop s u (j + 1) ∨ Tail s u ∨ Dead Image.code u) := by
  have hb := hpre.bounds
  have hj := ht.lt
  have hjl : 136 * j + 136 ≤ len s := by simp only [nb] at hj; omega
  obtain ⟨u₁, hr₁, h₁⟩ := BlockSpec.reaches b8000c970_spec ht.pc trivial
  have k₁ := b8000c970_keeps h₁
  have hm₁ := b8000c970_mem_same h₁
  have hu₁2 : u₁.getReg .x2 = s.getReg .x2 - 448 := (k₁ .x2 (by decide)).trans ht.sp
  have hu₁10 : u₁.getReg .x10 = s.getReg .x2 - 440 := by
    rw [b8000c970_x10 h₁, ht.sp]; addr_omega [hb.sp]
  have hu₁11 : u₁.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (136 * j) :=
    (k₁ .x11 (by decide)).trans ht.x11
  have hc₁ : Common s u₁ := Common.of_scratch hb ht.toCommon fun a _ ↦ hm₁ a
  have hxpre : XorBlockPre u₁ := {
    state := by rw [hu₁10]; refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp]
    block := by rw [hu₁11]; exact bytesValid_sub hpre.data hjl
    stack := ⟨by
        simp only [stackLo, xorBlockStack, hu₁2]
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp],
      by rw [hu₁2]; addr_omega [hb.sp]⟩
    stateStack := by rw [hu₁10]; simp only [stackLo, xorBlockStack, hu₁2]; addr_omega [hb.sp]
    blockStack := by
      rw [hu₁11]; simp only [stackLo, xorBlockStack, hu₁2]
      addr_omega [hb.sp, hb.dataStack, hb.data, hjl]
    stateBlock := by rw [hu₁10, hu₁11]; addr_omega [hb.sp, hb.dataStack, hb.data, hjl] }
  obtain ⟨v₁, hr₂, ⟨hv₁pc, hpres₁, hpost₁⟩ | hdead⟩ := hXor.call hr₁ (b8000c970_pc h₁) hxpre
  swap
  · exact ⟨v₁, hr₂, Or.inr (Or.inr hdead)⟩
  have hsc₁ : Scratch s u₁ v₁ := scratch_of hb (lo₁ := s.getReg .x2 - 440) (n₁ := 200)
    (lo₂ := s.getReg .x2 - 960) (n₂ := 512) (by addr_omega [hb.sp]) (by addr_omega [hb.sp])
    fun a h₁a h₂a ↦ hpost₁.frame a (by rw [hu₁10]; exact h₁a)
      (by simp only [stackLo, xorBlockStack, hu₁2]; addr_omega [h₂a, hb.sp])
  have hc₂ : Common s v₁ := Common.of_scratch hb hc₁ hsc₁
  have hv₁2 : v₁.getReg .x2 = s.getReg .x2 - 448 := (hpres₁.reg .x2).trans hu₁2
  obtain ⟨u₂, hr₃, h₃⟩ := BlockSpec.reaches b8000c980_spec
    (by rw [hv₁pc, returnAddress_eq, b8000c970_x1 h₁]; decide) trivial
  have k₃ := b8000c980_keeps h₃
  have hm₃ := b8000c980_mem_same h₃
  have hu₂2 : u₂.getReg .x2 = s.getReg .x2 - 448 := (k₃ .x2 (by decide)).trans hv₁2
  have hu₂10 : u₂.getReg .x10 = s.getReg .x2 - 440 := by
    rw [b8000c980_x10 h₃, hv₁2]; addr_omega [hb.sp]
  have hc₃ : Common s u₂ := Common.of_scratch hb hc₂ fun a _ ↦ hm₃ a
  have hkpre : KeccakFPre u₂ := {
    state := by rw [hu₂10]; refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp]
    stack := ⟨by
        simp only [stackLo, keccakFStack, memStack, hu₂2]
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp],
      by rw [hu₂2]; addr_omega [hb.sp]⟩
    stateStack := by
      rw [hu₂10]; simp only [stackLo, keccakFStack, memStack, hu₂2]; addr_omega [hb.sp]
    tables := hc₃.tables hpre
    tablesState := by rw [hu₂10]; addr_omega [hb.tables, hb.sp]
    tablesStack := by
      simp only [stackLo, keccakFStack, memStack, hu₂2]; addr_omega [hb.tables, hb.sp] }
  obtain ⟨v₂, hr₄, ⟨hv₂pc, hpres₂, hpost₂⟩ | hdead⟩ := hKf.call hr₃ (b8000c980_pc h₃) hkpre
  swap
  · exact ⟨v₂, hr₂.trans hr₄, Or.inr (Or.inr hdead)⟩
  have hsc₂ : Scratch s u₂ v₂ := scratch_of hb (lo₁ := s.getReg .x2 - 440) (n₁ := 200)
    (lo₂ := s.getReg .x2 - 1104) (n₂ := 656) (by addr_omega [hb.sp]) (by addr_omega [hb.sp])
    fun a h₁a h₂a ↦ hpost₂.frame a (by rw [hu₂10]; exact h₁a)
      (by simp only [stackLo, keccakFStack, memStack, hu₂2]; addr_omega [h₂a, hb.sp])
  have hc₄ : Common s v₂ := Common.of_scratch hb hc₃ hsc₂
  have hstate : v₂.readWords (s.getReg .x2 - 440) 25 = absorbed s (j + 1) := by
    rw [← hu₂10, hpost₂.value, hu₂10,
      show u₂.readWords (s.getReg .x2 - 440) 25 = v₁.readWords (s.getReg .x2 - 440) 25 from
        readWords_congr fun i _ ↦ hm₃ _,
      ← hu₁10, hpost₁.value, hu₁10,
      show u₁.readWords (s.getReg .x2 - 440) 25 = t.readWords (s.getReg .x2 - 440) 25 from
        readWords_congr fun i _ ↦ hm₁ _, ht.state, absorbed_succ, hu₁11,
      hc₁.data hpre hjl, dataB, bytesAt_drop_take _ _ hjl]
  obtain ⟨u, hr₅, h₅⟩ := BlockSpec.reaches b8000c98c_spec
    (by rw [hv₂pc, returnAddress_eq, b8000c980_x1 h₃]; decide) trivial
  have k₅ := b8000c98c_keeps h₅
  have hm₅ := b8000c98c_mem_same h₅
  have hc : Common s u := Common.of_scratch hb hc₄ fun a _ ↦ hm₅ a
  have hx20 : v₂.getReg .x20 = BitVec.ofNat 64 (136 * (nb s - j)) := by
    rw [hpres₂.reg .x20, k₃ .x20 (by decide), hpres₁.reg .x20, k₁ .x20 (by decide), ht.x20]
  have hreg (r : Reg) (hr : r ∈ calleeSaved) (h₁r : r ∈ ([.x2, .x8, .x9, .x18, .x19] : List Reg))
      (h₃r : r ∈ ([.x2, .x8, .x9, .x18, .x19] : List Reg)) (h₅r : r ∈ ([.x2, .x8, .x9, .x18, .x19] : List Reg)) :
      u.getReg r = u₁.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁r h₃r h₅r
    rw [k₅ r (by rcases h₅r with rfl | rfl | rfl | rfl | rfl <;> decide), hpres₂ r hr,
      k₃ r (by rcases h₃r with rfl | rfl | rfl | rfl | rfl <;> decide), hpres₁ r hr]
  have hu2 := hreg .x2 (by decide) (by simp) (by simp) (by simp)
  have hu8 := hreg .x8 (by decide) (by simp) (by simp) (by simp)
  have hu9 := hreg .x9 (by decide) (by simp) (by simp) (by simp)
  have hu18 := hreg .x18 (by decide) (by simp) (by simp) (by simp)
  have hu19 := hreg .x19 (by decide) (by simp) (by simp) (by simp)
  rw [hu₁2] at hu2
  rw [k₁ .x8 (by decide), ht.x8] at hu8
  rw [k₁ .x9 (by decide), ht.x9] at hu9
  rw [k₁ .x18 (by decide), ht.x18] at hu18
  rw [b8000c970_x19 h₁, ht.x11] at hu19
  have hnbl : 136 * nb s ≤ len s := by simp only [nb]; omega
  by_cases hlast : j + 1 < nb s
  · refine ⟨u, hr₂.trans (hr₄.trans hr₅), Or.inl ⟨hc, b8000c98c_pc_taken h₅ ?_, hlast, hu2, hu8,
      hu9, hu18, ?_, ?_, ?_⟩⟩
    · rw [hx20]; addr_omega [hlast, hb.dataEnd, hnbl]
    · rw [b8000c98c_x11 h₅, hpres₂.reg .x19, k₃ .x19 (by decide), hpres₁.reg .x19,
        b8000c970_x19 h₁, ht.x11]
      addr_omega [hjl, hb.data, hb.dataEnd]
    · rw [b8000c98c_x20 h₅, hx20]; addr_omega [hlast, hb.dataEnd, hnbl]
    · rw [readWords_congr fun i _ ↦ hm₅ _]; exact hstate
  · have hnb : j + 1 = nb s := by omega
    refine ⟨u, hr₂.trans (hr₄.trans hr₅), Or.inr (Or.inl ⟨hc, b8000c98c_pc_not_taken h₅ ?_, hu2,
      hu8, hu9, hu18, ?_⟩)⟩
    · rw [hx20]; addr_omega [hnb, hb.dataEnd, hnbl]
    · rw [readWords_congr fun i _ ↦ hm₅ _, ← hnb]; exact hstate

/-! ## The padding -/

theorem padSig_toState {v : MachineState} {tl : Nat} (h9 : v.getReg .x9 = BitVec.ofNat 64 tl)
    (h19 : v.getReg .x19 = v.getReg .x2 + 208) : (padSig tl).toState v v.code v.pc = v := by
  apply Sym.MachineState.ext' <;> try rfl
  funext q
  simp only [SymState.toState, padSig]
  split
  · rename_i h0; subst h0; rfl
  · rename_i h0
    by_cases h₁ : q = .x19
    · subst h₁
      rw [RegFile.get_set_self _ _ (by decide)]
      simp only [spE, E.eval, BinOp.eval]
      exact h19.symm
    · rw [RegFile.get_set_ne _ _ h₁]
      by_cases h₂ : q = .x9
      · subst h₂
        rw [RegFile.get_set_self _ _ (by decide)]
        simp only [E.eval]
        exact h9.symm
      · rw [RegFile.get_set_ne _ _ h₂, show SymState.init.regs = RegFile.init from rfl,
          RegFile.init_get_eval]
        cases q <;> first | exact absurd rfl h0 | rfl

theorem getD_set {α : Type} (l : List α) {k : Nat} (i : Nat) (v d : α) (hk : k < l.length) :
    (l.set k v).getD i d = if k = i then v else l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  split <;> simp_all

theorem padBlockRust_getD (tail : List (BitVec 8)) (htl : tail.length < 136) {i : Nat}
    (hi : i < 136) : (padBlockRust tail).getD i 0 =
      (if i < tail.length then tail.getD i 0 else 0) ^^^ (if i = tail.length then 1 else 0) ^^^
        (if i = 135 then 0x80 else 0) := by
  have hlen : (tail ++ List.drop tail.length (List.replicate 136 (0 : BitVec 8))).length = 136 := by
    simp; omega
  have hget (k : Nat) (hk : k < 136) :
      (tail ++ List.drop tail.length (List.replicate 136 (0 : BitVec 8))).getD k 0 =
        if k < tail.length then tail.getD k 0 else 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    by_cases h : k < tail.length
    · rw [List.getElem?_append_left h]
      simp only [h, ↓reduceIte]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop, List.getElem?_replicate]
      simp only [show tail.length + (k - tail.length) < 136 by omega, h, ↓reduceIte,
        Option.getD_some]
  simp only [padBlockRust]
  rw [getD_set _ _ _ _ (by rw [List.length_set, hlen]; decide),
    getD_set _ _ _ _ (by rw [hlen]; exact htl), getD_set _ _ _ _ (by rw [hlen]; exact htl)]
  simp only [hget _ hi, hget _ htl, hget 135 (by decide)]
  by_cases h135 : i = 135 <;> by_cases ht : tail.length = i
  · subst h135; rw [← ht]; simp
  · subst h135; simp [ht, Ne.symm ht]
  · subst ht; simp [h135, Ne.symm h135]
  · simp [h135, ht, Ne.symm ht, Ne.symm h135]

theorem trunc_xor (x : BitVec 8) (c : Word) :
    ((x.setWidth 64) ^^^ c).setWidth 8 = x ^^^ c.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show i < 64 by omega]

theorem flipE_eval (v : MachineState) (e : E) {bo : Nat} (hbo : bo < 8) (c : Word) {q : Nat}
    (hq : q < 8) : extractByte ((flipE e bo c).eval v) q =
      if bo = q then extractByte (e.eval v) bo ^^^ c.setWidth 8 else extractByte (e.eval v) q := by
  simp only [flipE, E.eval, BinOp.eval, UnOp.eval, StoreKind.merge, LoadKind.fromWord]
  rw [extractByte_replaceByte _ hbo hq]
  split
  · rename_i h; subst h
    rw [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, trunc_xor]
  · rfl

set_option linter.unusedSimpArgs false in
/-- The padding's two bytes, and the block's other bytes unchanged. -/
theorem pad_bytes {v w : MachineState} {tl : Nat} (htl : tl < 136) (h : (padX tl).Holds v w)
    (hal : (v.getReg .x2).toNat % 8 = 0) (hw : (v.getReg .x2).toNat + 344 < 2 ^ 64) {i : Nat}
    (hi : i < 136) :
    w.getByte (v.getReg .x2 + BitVec.ofNat 64 (208 + i)) =
      v.getByte (v.getReg .x2 + BitVec.ofNat 64 (208 + i)) ^^^ (if i = tl then 1 else 0) ^^^
        (if i = 135 then 0x80 else 0) := by
  have hc : (BitVec.ofNat 64 (208 + i)).toNat = 208 + i := by rw [BitVec.toNat_ofNat]; omega
  have hd : alignToDword (v.getReg .x2 + BitVec.ofNat 64 (208 + i)) =
      v.getReg .x2 + BitVec.ofNat 64 (208 + i - i % 8) := by
    rw [XorBlock.alignToDword_add_aligned hal (by omega)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, hc, BitVec.toNat_ofNat]
    omega
  have hbo : byteOffset (v.getReg .x2 + BitVec.ofNat 64 (208 + i)) = i % 8 := by
    rw [XorBlock.byteOffset_add_aligned hal (by omega), byteOffset_eq, hc]; omega
  simp only [MachineState.getByte, hd, hbo]
  have hkey (off : Nat) : (spKey off).eval v = v.getReg .x2 + BitVec.ofNat 64 off := rfl
  have hld (off : Nat) : (E.ld (spE off)).eval v = v.getMem (v.getReg .x2 + BitVec.ofNat 64 off) :=
    rfl
  have hi8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have htl8 : tl % 8 < 8 := Nat.mod_lt _ (by decide)
  by_cases hhi : 128 ≤ i
  · have hm := h.2.2.1 (spKey 336, padHigh tl) (by unfold padX; split <;> simp)
    rw [hkey] at hm
    rw [show 208 + i - i % 8 = 336 by omega, hm, padHigh, flipE_eval _ _ (by decide) _ hi8]
    by_cases h128 : 128 ≤ tl
    · simp only [h128, ↓reduceIte]
      rw [padLow, flipE_eval _ _ htl8 _ hi8, flipE_eval _ _ htl8 _ (by decide), hld,
        show lowOff tl = 336 by unfold lowOff; omega]
      by_cases h135 : i = 135
      · subst h135
        by_cases ht : tl = 135
        · subst ht; simp
        · simp [show tl % 8 ≠ 7 by omega, show (135 : Nat) ≠ tl by omega]
      · by_cases ht : tl = i
        · subst ht; simp [show tl % 8 ≠ 7 by omega, show ¬ 7 = tl % 8 by omega, h135]
        · simp [show ¬ 7 = i % 8 by omega, show ¬ tl % 8 = i % 8 by omega, Ne.symm ht, h135]
    · simp only [h128, ↓reduceIte]
      rw [hld]
      by_cases h135 : i = 135
      · subst h135; simp [show (135 : Nat) ≠ tl by omega]
      · simp [show ¬ 7 = i % 8 by omega, show i ≠ tl by omega, h135]
  · by_cases hsame : i / 8 = tl / 8
    · have hm := h.2.2.1 (spKey (lowOff tl), padLow tl) (by
        unfold padX; simp only [show ¬ (128 ≤ tl) by omega, ↓reduceIte]; simp)
      rw [hkey] at hm
      rw [show 208 + i - i % 8 = lowOff tl by unfold lowOff; omega, hm, padLow,
        flipE_eval _ _ htl8 _ hi8, hld]
      by_cases ht : tl = i
      · subst ht; simp [show tl ≠ 135 by omega]
      · simp [show ¬ tl % 8 = i % 8 by omega, Ne.symm ht, show i ≠ 135 by omega]
    · rw [h.2.2.2 _ (by
        intro k hk
        simp only [padX, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> rw [hkey] <;> (try unfold lowOff) <;>
          addr_omega [hal, hw, hi, hhi, hsame, htl])]
      simp [show i ≠ 135 by omega, show i ≠ tl by omega]

/-! ## The digest -/

theorem byteOf_eval (s : MachineState) {j : Nat} (hj : j < 8) :
    ∀ (e : E) {v : E}, byteOf e j = some v → extractByte (e.eval s) j = (v.eval s).setWidth 8 := by
  intro e
  induction e with
  | bin op a b iha _ =>
    intro v h
    cases op with
    | st k bo =>
      cases k with
      | b =>
        simp only [byteOf] at h
        simp only [E.eval, BinOp.eval, StoreKind.merge]
        by_cases hbo : bo = j
        · subst hbo
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          rw [extractByte_replaceByte _ hj hj]
          simp
        · simp only [hbo, ↓reduceIte] at h
          split at h
          · rename_i hb8
            rw [extractByte_replaceByte _ hb8 hj]
            simp only [hbo, ↓reduceIte]; exact iha h
          · cases h
      | _ => simp [byteOf] at h
    | _ => simp [byteOf] at h
  | _ => intro v h; simp [byteOf] at h

theorem laneByteE_eval (s : MachineState) (i : Nat) {j : Nat} (hj : j < 8) :
    (laneByteE i j).eval s = s.getMem (s.getReg .x2 + BitVec.ofNat 64 (8 + 8 * i)) >>> (8 * j) := by
  unfold laneByteE
  split
  · rename_i h; subst h; simp [spE, E.eval, BinOp.eval]
  · simp only [spE, E.eval, BinOp.eval, BitVec.toNat_ofNat]
    congr 1
    omega

/-- Byte `j` of the digest's doubleword `i` is lane `i`'s. -/
theorem digest_byte {s t : MachineState} (h : b8000c9fc.Holds s t)
    (hal : (s.getReg .x8).toNat % 8 = 0) {i j : Nat} (hi : i < 4) (hj : j < 8) :
    t.getByte (s.getReg .x8 + BitVec.ofNat 64 (8 * i + j)) =
      (s.getMem (s.getReg .x2 + BitVec.ofNat 64 (8 + 8 * i)) >>> (8 * j)).setWidth 8 := by
  have hc := List.all_eq_true.mp (List.all_eq_true.mp digest_bytes i (List.mem_range.mpr hi)) j
    (List.mem_range.mpr hj)
  obtain ⟨p, hp, hm⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true] at hm
  obtain ⟨hk, hv⟩ := hm
  split at hv
  · rename_i v hv'
    have hmem := h.2.2.1 p hp
    rw [Addr.beq_eq hk] at hmem
    have hal' : (s.getReg .x8 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [← ofNat_add_ofNat, getByte_aligned t hal' hj]
    simp only [Addr.eval, E.eval] at hmem
    rw [hmem, byteOf_eval s hj _ hv', E.acEq_eval s hv, laneByteE_eval s i hj]
  · cases hv

theorem flatMap_toLeBytes_getD (f : Nat → Word) {k : Nat} (hk : k < 32) :
    ((List.range 4).flatMap fun i ↦ toLeBytes (f i)).getD k 0 =
      (f (k / 8) >>> (8 * (k % 8))).setWidth 8 := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, toLeBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  interval_cases k <;> rfl

/-! ## The last block and the digest -/

/-- The tail of the data, `len % 136` bytes. -/
def tailB (s : MachineState) : List (BitVec 8) := (dataB s).drop (136 * nb s)

theorem tl_bounds (s : MachineState) : 136 * nb s + len s % 136 = len s ∧ len s % 136 < 136 := by
  simp only [nb]; omega

theorem tailB_eq (s : MachineState) :
    tailB s = bytesAt s (s.getReg .x11 + BitVec.ofNat 64 (136 * nb s)) (len s % 136) := by
  rw [tailB, dataB, bytesAt_drop]
  congr 1
  have := tl_bounds s
  omega

theorem tail (hXor : XorBlockSpec) (hKf : KeccakFSpec) (hMemcpy : MemcpySpec)
    (hMemset : MemsetSpec) {s t : MachineState} (hpre : KeccakHashPre s) (ht : Tail s t) :
    ∃ u, Reaches Image.code t u ∧
      ((u.pc = returnAddress s ∧ Preserves s u ∧ KeccakHashPost s u) ∨ Dead Image.code u) := by
  have hb := hpre.bounds
  obtain ⟨htl1, htl2⟩ := tl_bounds s
  -- `memset` of the last block
  obtain ⟨u₁, hr₁, h₁⟩ := BlockSpec.reaches b8000c998_spec ht.pc trivial
  have k₁ := b8000c998_keeps h₁
  have hm₁ := b8000c998_mem_same h₁
  have hu₁2 : u₁.getReg .x2 = s.getReg .x2 - 448 := (k₁ .x2 (by decide)).trans ht.sp
  have hu₁10 : u₁.getReg .x10 = s.getReg .x2 - 240 := by
    rw [b8000c998_x10 h₁, ht.sp]; addr_omega [hb.sp]
  have h136 : (u₁.getReg .x12).toNat = 136 := by rw [b8000c998_x12 h₁]; rfl
  have hbuf : BytesValid (s.getReg .x2 - 240) 136 := bytesValid_of_range (n := 17) (by
    refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp])
  have hc₁ : Common s u₁ := Common.of_scratch hb ht.toCommon fun a _ ↦ hm₁ a
  obtain ⟨v₁, hr₂, ⟨hv₁pc, hpres₁, hpost₁⟩ | hdead⟩ := hMemset.call hr₁ (b8000c998_pc h₁) {
    dst := by rw [h136, hu₁10]; exact hbuf
    stack := ⟨by
        simp only [stackLo, memStack, hu₁2]
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp],
      by rw [hu₁2]; addr_omega [hb.sp]⟩
    dstStack := by rw [h136, hu₁10]; simp only [stackLo, memStack, hu₁2]; addr_omega [hb.sp] }
  swap
  · exact ⟨v₁, hr₂, Or.inr hdead⟩
  have hsc₁ : Scratch s u₁ v₁ := fun a ha ↦ hpost₁.frame a
    (by rw [h136, hu₁10]; addr_omega [ha, hb.sp])
    (by simp only [stackLo, memStack, hu₁2]; addr_omega [ha, hb.sp])
  have hc₂ : Common s v₁ := Common.of_scratch hb hc₁ hsc₁
  have hzero : bytesAt v₁ (s.getReg .x2 - 240) 136 = List.replicate 136 0 := by
    have := hpost₁.bytes
    rw [h136, hu₁10, b8000c998_x11 h₁] at this
    exact this
  -- `memcpy` of the tail
  obtain ⟨u₂, hr₃, h₃⟩ := BlockSpec.reaches b8000c9b0_spec
    (by rw [hv₁pc, returnAddress_eq, b8000c998_x1 h₁]; decide) trivial
  have k₃ := b8000c9b0_keeps h₃
  have hm₃ := b8000c9b0_mem_same h₃
  have hv₁ (r : Reg) (hr : r ∈ calleeSaved) : v₁.getReg r = u₁.getReg r := hpres₁ r hr
  have hu₂2 : u₂.getReg .x2 = s.getReg .x2 - 448 := by
    rw [k₃ .x2 (by decide), hv₁ .x2 (by decide), hu₁2]
  have hu₂10 : u₂.getReg .x10 = s.getReg .x2 - 240 := by
    rw [b8000c9b0_x10 h₃, hv₁ .x2 (by decide), hu₁2]; addr_omega [hb.sp]
  have hu₂11 : u₂.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (136 * nb s) := by
    rw [b8000c9b0_x11 h₃, hv₁ .x18 (by decide), k₁ .x18 (by decide), ht.x18]
  have hu₂12 : (u₂.getReg .x12).toNat = len s % 136 := by
    rw [b8000c9b0_x12 h₃, hv₁ .x9 (by decide), k₁ .x9 (by decide), ht.x9, BitVec.toNat_ofNat]
    omega
  have hc₃ : Common s u₂ := Common.of_scratch hb hc₂ fun a _ ↦ hm₃ a
  obtain ⟨v₂, hr₄, ⟨hv₂pc, hpres₂, hpost₂⟩ | hdead⟩ := hMemcpy.call hr₃ (b8000c9b0_pc h₃) {
    dst := by
      rw [hu₂12, hu₂10]
      refine ⟨by have := hbuf.1; omega, fun i hi ↦ hbuf.2 i ?_⟩
      omega
    src := by
      rw [hu₂12, hu₂11]
      exact bytesValid_sub (k := 136 * nb s) (m := len s % 136) hpre.data htl1.le
    apart := by
      rw [hu₂12, hu₂10, hu₂11]; addr_omega [hb.sp, hb.dataStack, hb.data, htl1]
    stack := ⟨by
        simp only [stackLo, memStack, hu₂2]
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp],
      by rw [hu₂2]; addr_omega [hb.sp]⟩
    dstStack := by rw [hu₂12, hu₂10]; simp only [stackLo, memStack, hu₂2]; addr_omega [hb.sp]
    srcStack := by
      rw [hu₂12, hu₂11]; simp only [stackLo, memStack, hu₂2]
      addr_omega [hb.sp, hb.dataStack, hb.data, htl1] }
  swap
  · exact ⟨v₂, hr₂.trans hr₄, Or.inr hdead⟩
  have hsc₂ : Scratch s u₂ v₂ := fun a ha ↦ hpost₂.frame a
    (by rw [hu₂12, hu₂10]; addr_omega [ha, hb.sp])
    (by simp only [stackLo, memStack, hu₂2]; addr_omega [ha, hb.sp])
  have hc₄ : Common s v₂ := Common.of_scratch hb hc₃ hsc₂
  -- the block before the padding
  have hblock (i : Nat) (hi : i < 136) : v₂.getByte (s.getReg .x2 - 240 + BitVec.ofNat 64 i) =
      if i < len s % 136 then (tailB s).getD i 0 else 0 := by
    split
    · rename_i hlt
      have := getByte_of_bytesAt hpost₂.bytes (by rw [hu₂12]; exact hlt)
      rw [hu₂10] at this
      rw [this, hu₂12, hu₂11, hc₃.data hpre (k := 136 * nb s) (m := len s % 136) (by omega),
        ← tailB_eq]
    · rename_i hge
      rw [hpost₂.byteFrame _ (by rw [hu₂10, hu₂12]; addr_omega [hb.sp, hge, hi])
          (by simp only [stackLo, memStack, hu₂2]; addr_omega [hb.sp, hi]),
        getByte_congr (hm₃ _), getByte_of_bytesAt hzero hi, List.getD_eq_getElem?_getD,
        List.getElem?_replicate]
      simp only [hi, ↓reduceIte, Option.getD_some]
  -- the padding
  have hv₂2 : v₂.getReg .x2 = s.getReg .x2 - 448 := (hpres₂.reg .x2).trans hu₂2
  have hv₂8 : v₂.getReg .x8 = s.getReg .x10 := by
    rw [hpres₂.reg .x8, k₃ .x8 (by decide), hv₁ .x8 (by decide), k₁ .x8 (by decide), ht.x8]
  have hv₂9 : v₂.getReg .x9 = BitVec.ofNat 64 (len s % 136) := by
    rw [hpres₂.reg .x9, k₃ .x9 (by decide), hv₁ .x9 (by decide), k₁ .x9 (by decide), ht.x9]
  have hv₂19 : v₂.getReg .x19 = v₂.getReg .x2 + 208 := by
    rw [hpres₂.reg .x19, k₃ .x19 (by decide), hv₁ .x19 (by decide), b8000c998_x19 h₁, hv₂2,
      ht.sp]
  have hpc₂ : v₂.pc = 0x8000c9c4 := by
    rw [hv₂pc, returnAddress_eq, b8000c9b0_x1 h₃]; decide
  obtain ⟨w, hst₅, hw⟩ := run_spec (cfg := cfg) (rs := []) (bs := [])
    (List.all_eq_true.mp pad_run _ (List.mem_range.mpr htl2)) (codeWindow_sub _ _ _ (by decide))
    (s := v₂) (u := v₂) (by rw [← hpc₂]; exact padSig_toState hv₂9 hv₂19)
    (fun _ h ↦ by cases h) List.Pairwise.nil (fun _ h ↦ by cases h) (by
      show Oblig.all v₂ [.valid (spKey 343) 1, .align8 (.reg .x2),
        .valid (spKey (208 + len s % 136)) 1]
      simp only [Oblig.all, Oblig.holds, spKey, Addr.eval, E.eval, hv₂2]
      refine ⟨?_, ?_, ?_⟩
      · show isValidMemAddr _ = true
        rw [show s.getReg .x2 - 448 + BitVec.ofNat 64 343 =
          s.getReg .x2 - 240 + BitVec.ofNat 64 135 by addr_omega [hb.sp]]
        exact hbuf.2 135 (by decide)
      · addr_omega [hb.sp]
      · show isValidMemAddr _ = true
        rw [show s.getReg .x2 - 448 + BitVec.ofNat 64 (208 + len s % 136) =
          s.getReg .x2 - 240 + BitVec.ofNat 64 (len s % 136) by addr_omega [hb.sp, htl2]]
        exact hbuf.2 _ htl2)
  have hr₅ : Reaches Image.code v₂ w := ⟨_, hst₅⟩
  have hwr (r : Reg) (e : E) (hm : (r, e) ∈ (padX (len s % 136)).regs) : w.getReg r = e.eval v₂ :=
    hw.2.1 _ hm
  have hw2 : w.getReg .x2 = s.getReg .x2 - 448 := (hwr .x2 (.reg .x2) (by simp [padX])).trans hv₂2
  have hw8 : w.getReg .x8 = s.getReg .x10 := (hwr .x8 (.reg .x8) (by simp [padX])).trans hv₂8
  have hw10 : w.getReg .x10 = s.getReg .x2 - 440 := by
    rw [hwr .x10 (spE 8) (by simp [padX])]; simp only [spE, E.eval, BinOp.eval, hv₂2]
    addr_omega [hb.sp]
  have hw11 : w.getReg .x11 = s.getReg .x2 - 240 := by
    rw [hwr .x11 (spE 208) (by simp [padX])]; simp only [spE, E.eval, BinOp.eval, hv₂2]
    addr_omega [hb.sp]
  have hwfr (a : Word) (ha₁ : a ≠ s.getReg .x2 - 112)
      (ha₂ : a ≠ s.getReg .x2 - 448 + BitVec.ofNat 64 (lowOff (len s % 136))) :
      w.getMem a = v₂.getMem a :=
    hw.2.2.2 a fun k hk ↦ by
      simp only [padX, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · show a ≠ v₂.getReg .x2 + BitVec.ofNat 64 336
        rw [hv₂2]; intro h; exact ha₁ (by rw [h]; addr_omega [hb.sp])
      · show a ≠ v₂.getReg .x2 + BitVec.ofNat 64 (lowOff (len s % 136))
        rw [hv₂2]; exact ha₂
  have hsc₃ : Scratch s v₂ w := fun a ha ↦ hwfr a (by addr_omega [ha, hb.sp])
    (by unfold lowOff; addr_omega [ha, hb.sp, htl2])
  have hc₅ : Common s w := Common.of_scratch hb hc₄ hsc₃
  have hpad : bytesAt w (s.getReg .x2 - 240) 136 = padBlockRust (tailB s) := by
    have hlen : (tailB s).length = len s % 136 := by rw [tailB_eq, length_bytesAt]
    apply List.ext_getElem
    · rw [length_bytesAt]
      simp [padBlockRust, hlen]; omega
    · intro i hi _
      rw [length_bytesAt] at hi
      rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, bytesAt_getD _ _ hi,
        padBlockRust_getD _ (by omega) hi, hlen, ← hblock i hi,
        show s.getReg .x2 - 240 + BitVec.ofNat 64 i = v₂.getReg .x2 + BitVec.ofNat 64 (208 + i) by
          rw [hv₂2]; addr_omega [hb.sp, hi]]
      exact pad_bytes htl2 hw (by rw [hv₂2]; addr_omega [hb.sp]) (by rw [hv₂2]; addr_omega [hb.sp]) hi
  have hstate₅ : w.readWords (s.getReg .x2 - 440) 25 = absorbed s (nb s) := by
    rw [← ht.state]
    apply readWords_congr
    intro i hi
    rw [hwfr _ (by addr_omega [hb.sp, hi]) (by unfold lowOff; addr_omega [hb.sp, hi, htl2]),
      hpost₂.frame _ (by rw [hu₂12, hu₂10]; addr_omega [hb.sp, hi])
        (by simp only [stackLo, memStack, hu₂2]; addr_omega [hb.sp, hi]), hm₃,
      hpost₁.frame _ (by rw [h136, hu₁10]; addr_omega [hb.sp, hi])
        (by simp only [stackLo, memStack, hu₁2]; addr_omega [hb.sp, hi]), hm₁]
  -- `xor_block` and `keccak_f` of the last block
  have hwpc : w.pc = 0x8000e5c8 := hw.1
  obtain ⟨v₃, hr₆, ⟨hv₃pc, hpres₃, hpost₃⟩ | hdead⟩ := hXor.call (Reaches.refl w) hwpc {
    state := by rw [hw10]; refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp]
    block := by rw [hw11]; exact hbuf
    stack := ⟨by
        simp only [stackLo, xorBlockStack, hw2]
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp],
      by rw [hw2]; addr_omega [hb.sp]⟩
    stateStack := by rw [hw10]; simp only [stackLo, xorBlockStack, hw2]; addr_omega [hb.sp]
    blockStack := by rw [hw11]; simp only [stackLo, xorBlockStack, hw2]; addr_omega [hb.sp]
    stateBlock := by rw [hw10, hw11]; addr_omega [hb.sp] }
  swap
  · exact ⟨v₃, hr₂.trans (hr₄.trans (hr₅.trans hr₆)), Or.inr hdead⟩
  have hsc₄ : Scratch s w v₃ := scratch_of hb (lo₁ := s.getReg .x2 - 440) (n₁ := 200)
    (lo₂ := s.getReg .x2 - 960) (n₂ := 512) (by addr_omega [hb.sp]) (by addr_omega [hb.sp])
    fun a h₁a h₂a ↦ hpost₃.frame a (by rw [hw10]; exact h₁a)
      (by simp only [stackLo, xorBlockStack, hw2]; addr_omega [h₂a, hb.sp])
  have hc₆ : Common s v₃ := Common.of_scratch hb hc₅ hsc₄
  have hv₃2 : v₃.getReg .x2 = s.getReg .x2 - 448 := (hpres₃.reg .x2).trans hw2
  obtain ⟨u₃, hr₇, h₇⟩ := BlockSpec.reaches b8000c9f0_spec
    (by rw [hv₃pc, returnAddress_eq, hwr .x1 (.c 0x8000c9f0) (by simp [padX])]; simp only [E.eval]; decide) trivial
  have k₇ := b8000c9f0_keeps h₇
  have hm₇ := b8000c9f0_mem_same h₇
  have hu₃2 : u₃.getReg .x2 = s.getReg .x2 - 448 := (k₇ .x2 (by decide)).trans hv₃2
  have hu₃10 : u₃.getReg .x10 = s.getReg .x2 - 440 := by
    rw [b8000c9f0_x10 h₇, hv₃2]; addr_omega [hb.sp]
  have hc₇ : Common s u₃ := Common.of_scratch hb hc₆ fun a _ ↦ hm₇ a
  obtain ⟨v₄, hr₈, ⟨hv₄pc, hpres₄, hpost₄⟩ | hdead⟩ := hKf.call hr₇ (b8000c9f0_pc h₇) {
    state := by rw [hu₃10]; refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp]
    stack := ⟨by
        simp only [stackLo, keccakFStack, memStack, hu₃2]
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp],
      by rw [hu₃2]; addr_omega [hb.sp]⟩
    stateStack := by
      rw [hu₃10]; simp only [stackLo, keccakFStack, memStack, hu₃2]; addr_omega [hb.sp]
    tables := hc₇.tables hpre
    tablesState := by rw [hu₃10]; addr_omega [hb.tables, hb.sp]
    tablesStack := by
      simp only [stackLo, keccakFStack, memStack, hu₃2]; addr_omega [hb.tables, hb.sp] }
  swap
  · exact ⟨v₄, hr₂.trans (hr₄.trans (hr₅.trans (hr₆.trans hr₈))), Or.inr hdead⟩
  have hsc₅ : Scratch s u₃ v₄ := scratch_of hb (lo₁ := s.getReg .x2 - 440) (n₁ := 200)
    (lo₂ := s.getReg .x2 - 1104) (n₂ := 656) (by addr_omega [hb.sp]) (by addr_omega [hb.sp])
    fun a h₁a h₂a ↦ hpost₄.frame a (by rw [hu₃10]; exact h₁a)
      (by simp only [stackLo, keccakFStack, memStack, hu₃2]; addr_omega [h₂a, hb.sp])
  have hc₈ : Common s v₄ := Common.of_scratch hb hc₇ hsc₅
  have hfinal : v₄.readWords (s.getReg .x2 - 440) 25 = keccakFRust (xorBlockRust
      (absorbed s (nb s)) (padBlockRust ((dataB s).drop (136 * nb s)))) := by
    rw [← hu₃10, hpost₄.value, hu₃10,
      show u₃.readWords (s.getReg .x2 - 440) 25 = v₃.readWords (s.getReg .x2 - 440) 25 from
        readWords_congr fun i _ ↦ hm₇ _, ← hw10, hpost₃.value, hw10, hstate₅, hw11, hpad, tailB]
  have hv₄2 : v₄.getReg .x2 = s.getReg .x2 - 448 := (hpres₄.reg .x2).trans hu₃2
  have hv₄8 : v₄.getReg .x8 = s.getReg .x10 := by
    rw [hpres₄.reg .x8, k₇ .x8 (by decide), hpres₃.reg .x8, hw8]
  -- the digest and the return
  have hal := hb.out.1
  have hok : RegionsOk v₄ [outR, frameR] := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · show ValidMemRange (v₄.getReg .x8 + 0) 4
      rw [Sym.add_zero_lit, hv₄8]
      intro q hq
      exact XorBlock.dword_valid (hpre.out.2 (8 * q) (by omega))
        (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (le_refl _)
        (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hb.out.2; omega)
    · show ValidMemRange (v₄.getReg .x2 + 0) 56
      rw [Sym.add_zero_lit, hv₄2]
      refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp]
  have hap : RegionsApart v₄ [outR, frameR] := List.pairwise_cons.mpr ⟨fun R hR ↦ by
    simp only [List.mem_singleton] at hR
    subst hR
    show Apart (v₄.getReg .x8 + 0) (8 * 4) (v₄.getReg .x2 + 0) (8 * 56)
    rw [Sym.add_zero_lit, Sym.add_zero_lit, hv₄8, hv₄2]
    addr_omega [hb.outStack, hb.sp, hb.out.2], List.pairwise_singleton _ _⟩
  have hbok : BRegionsOk v₄ [outB] := by
    intro B hB i hi
    simp only [List.mem_singleton] at hB
    subst hB
    show isValidMemAddr (v₄.getReg .x8 + 0 + BitVec.ofNat 64 i) = true
    rw [Sym.add_zero_lit, hv₄8]
    exact hpre.out.2 i hi
  obtain ⟨u, hr₉, h₉⟩ := BlockSpec.reaches b8000c9fc_spec
    (by rw [hv₄pc, returnAddress_eq, b8000c9f0_x1 h₇]; decide)
    (oblig_all hok hap hbok (extra := [.align8 (.reg .x8)])
      (by show (v₄.getReg .x8).toNat % 8 = 0; rw [hv₄8]; exact hal) digest_obl)
  have hsv := hc₈.saved
  simp only [MachineState.readWords_succ, MachineState.readWords_zero, KeccakF.savedRegs,
    List.cons.injEq, and_true] at hsv
  rv_eval [] at hsv
  obtain ⟨h27, h26, h25, h24, h23, h22, h21, h20, h19, h18, h9, h8, h1⟩ := hsv
  have hx (r : Reg) (off : Nat) {a : Word} {v : Word}
      (hr : u.getReg r = v₄.getMem (v₄.getReg .x2 + BitVec.ofNat 64 off))
      (ha : s.getReg .x2 - 448 + BitVec.ofNat 64 off = a) (hv : v₄.getMem a = v) :
      u.getReg r = v := by
    rw [hr, hv₄2, ha, hv]
  refine ⟨u, hr₂.trans (hr₄.trans (hr₅.trans (hr₆.trans (hr₈.trans hr₉)))), Or.inl
    ⟨?_, ?_, ⟨?_, fun a h₁a h₂a ↦ ?_⟩⟩⟩
  · rw [b8000c9fc_pc h₉, returnAddress_eq, hv₄2,
      show s.getReg .x2 - 448 + (440 : Word) = s.getReg .x2 - 8 by addr_omega [hb.sp], h1]
  · apply preserves_of
    · rw [b8000c9fc_x2 h₉, hv₄2]; addr_omega [hb.sp]
    · exact hx .x8 432 (b8000c9fc_x8 h₉) (by addr_omega [hb.sp]) h8
    · exact hx .x9 424 (b8000c9fc_x9 h₉) (by addr_omega [hb.sp]) h9
    · exact hx .x18 416 (b8000c9fc_x18 h₉) (by addr_omega [hb.sp]) h18
    · exact hx .x19 408 (b8000c9fc_x19 h₉) (by addr_omega [hb.sp]) h19
    · intro r hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hx .x20 400 (b8000c9fc_x20 h₉) (by addr_omega [hb.sp]) h20
      · exact hx .x21 392 (b8000c9fc_x21 h₉) (by addr_omega [hb.sp]) h21
      · exact hx .x22 384 (b8000c9fc_x22 h₉) (by addr_omega [hb.sp]) h22
      · exact hx .x23 376 (b8000c9fc_x23 h₉) (by addr_omega [hb.sp]) h23
      · exact hx .x24 368 (b8000c9fc_x24 h₉) (by addr_omega [hb.sp]) h24
      · exact hx .x25 360 (b8000c9fc_x25 h₉) (by addr_omega [hb.sp]) h25
      · exact hx .x26 352 (b8000c9fc_x26 h₉) (by addr_omega [hb.sp]) h26
      · exact hx .x27 344 (b8000c9fc_x27 h₉) (by addr_omega [hb.sp]) h27
  · show bytesAt u (s.getReg .x10) 32 = keccakHashRust (dataB s)
    rw [keccakHashRust_absorbed]
    apply List.ext_getElem (by simp [length_bytesAt, toLeBytes])
    intro k hk _
    rw [length_bytesAt] at hk
    rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, bytesAt_getD _ _ hk,
      flatMap_toLeBytes_getD _ hk, ← hfinal, readWords_getD _ _ _ _ (by omega),
      show k = 8 * (k / 8) + k % 8 by omega, ← hv₄8]
    rw [digest_byte h₉ (by rw [hv₄8]; exact hal) (by omega)
      (by omega), hv₄2]
    congr 3
    · addr_omega [hb.sp, hk]
    · omega
  · rw [b8000c9fc_frame h₉ (by rw [hv₄8]; exact hb.out.2) a (by rw [hv₄8]; exact h₁a),
      hc₈.frame a (by simpa [stackLo, keccakHashStack, keccakFStack, memStack] using h₂a)]

/-! ## `keccak_hash` -/

/-- **`keccak_hash` meets its contract**, given `xor_block`'s, `keccak_f`'s, `memcpy`'s and
`memset`'s. -/
theorem keccak_hash_spec (hXor : XorBlockSpec) (hKf : KeccakFSpec) (hMemcpy : MemcpySpec)
    (hMemset : MemsetSpec) : KeccakHashSpec := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hfin {t : MachineState} (hst : Reaches Image.code s t) (ht : Tail s t) :
      ∃ u, Reaches Image.code s u ∧ ((u.pc = returnAddress s ∧ Preserves s u ∧
        KeccakHashPost s u) ∨ Dead Image.code u) := by
    obtain ⟨u, htu, hu⟩ := tail hXor hKf hMemcpy hMemset hpre ht
    exact ⟨u, hst.trans htu, hu⟩
  obtain ⟨t, hst, ht | ht | hdead⟩ := setup hMemset hpc hpre
  · obtain ⟨u, htu, hu | hdead⟩ := Reaches.loop (code := Image.code) (fun t ↦ ∃ j, Loop s t j)
      (fun t ↦ (t.getReg .x20).toNat) (fun u ↦ Tail s u ∨ Dead Image.code u)
      (fun t ⟨j, ht⟩ ↦ by
        obtain ⟨u, hr, hu | hu | hu⟩ := body hXor hKf hpre ht
        · refine Or.inr ⟨u, hr, ⟨j + 1, hu⟩, ?_⟩
          have hlt := hu.lt
          have hd := hb.data
          simp only [nb] at hlt
          rw [hu.x20, ht.x20, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          simp only [nb]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        · exact Or.inl ⟨u, hr, Or.inl hu⟩
        · exact Or.inl ⟨u, hr, Or.inr hu⟩) t ⟨0, ht⟩
    · exact hfin (hst.trans htu) hu
    · exact ⟨u, hst.trans htu, Or.inr hdead⟩
  · exact hfin hst ht
  · exact ⟨t, hst, Or.inr hdead⟩

end Rv64Verifier.Hash.KeccakHash
