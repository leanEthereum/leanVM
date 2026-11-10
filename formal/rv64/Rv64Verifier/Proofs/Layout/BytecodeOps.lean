import Rv64Verifier.Proofs.Layout.BytecodeStart

/-!
# `Flushes::bytecode`: the operands, the prefix and the counter

The second `spec_extend`, with the operands; `term(sp', One, SEP_BYTECODE)`, `col(sp' + 24, 0, 0)` and
`col(sp' + 72, count, 1)`.
-/

namespace Rv64Verifier.Layout.Bytecode
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F11 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.MemoryCols (Built)

theorem mul24 (x : Word) : x * 16 + x * 8 = BitVec.ofNat 64 (24 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

/-- `SEP_BYTECODE` in `.rodata`, at `0xa00000e0`. -/
theorem eAt_sep {s : MachineState} (h : RodataOk s) : eAt s 0xa00000e0 = sepBytecodeRust := by
  have h0 : s.getMem 0xa00000e0 = 4 := h.word
  have h1 : s.getMem (0xa00000e0 + 8) = 0 := h.word
  have h2 : s.getMem (0xa00000e0 + 16) = 0 := h.word
  exact eq_of_limbs (by rw [limbs_eAt, h0, h1, h2]; rfl)

/-- At `counted`: the prefix at `sp'`, the counter at `sp' + 72`, the suffix's `Vec` at `sp' + 48`. -/
structure AtCounted (s t : MachineState) : Prop extends Inv s t where
  p0 : Built s t (s.getReg .x2 - 144) (constantRust sepBytecodeRust)
  p1 : Built s t (s.getReg .x2 - 120) (colRust 0 0)
  cnt : Built s t (s.getReg .x2 - 72) (colRust (s.getReg .x11).toNat 1)
  v : VBuilt s t (s.getReg .x2 - 96)
    ([constantRust (gpowRust (s.getReg .x12).toNat)] ++ formVecOf s (s.getReg .x13))

theorem toCounted (hS : SpecExtendSpec) (hT : TermSpec) (hC : ColSpec) {s u0 u : MachineState}
    (hpre : BytecodePre s) (A : AtOps s u) (hr : Reaches Image.code u0 u) :
    ∃ t, Reaches Image.code u0 t ∧ ((t.pc = 0x80004ccc ∧ AtCounted s t) ∨ Dead Image.code t) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hlo₀ := hpre.heap.lo
  have hraw := hpre.opsOk.vec.raw
  have hcl := hpre.opsOk.vec.len
  have hobf := hpre.opsBuf
  have hobs := hpre.opsBufStack
  simp only [bytecodeStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hobs
  simp only [RawVecOk, Buf] at hraw
  obtain ⟨P, hP⟩ : ∃ P, P = vecPtr s (s.getReg .x13) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (vecLen s (s.getReg .x13)).toNat := ⟨_, rfl⟩
  rw [← hP, ← hn] at hobf hobs
  rw [← hP] at hraw
  rw [← hn] at hcl
  have hpl : P.toNat + 24 * n < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have := P.isLt; omega
    · rcases hraw.2 with h0 | h0
      · rw [Nat.mul_eq_zero] at h0; omega
      · simp only [heapNext] at h0 ⊢; have := hpre.heap.hi; simp only [heapNext, heapEnd] at this; omega
  have hPb : n = 0 ∨ heapStart ≤ P.toNat ∧ P.toNat + 24 * n ≤ heapNext s := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · rcases hraw.2 with h0 | h0
      · rw [Nat.mul_eq_zero] at h0; omega
      · exact Or.inr ⟨h0.1, by omega⟩
  -- the second `spec_extend`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004c68_spec A.pc trivial
  have hm₁ := b80004c68_mem_same h₁
  have k₁ := b80004c68_keeps h₁
  obtain ⟨c₁, -, kv₁⟩ := A.toInv.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have v₁ := kv₁ _ _ A.v (by addr_omega [hsb])
  have hfa := formsAt_keep c₁.frame (p := P) (k := n) (by rw [hP, hn]; exact hpre.opsOk.forms)
    hpre.heap c₁.mono c₁.heap.hi hab hobf hobs hpl.le
  have hhi₁ := c₁.heap.hi
  have hm₁' := c₁.mono
  obtain ⟨v, hr₂, ⟨hpc₂, -, c₂, v₂⟩ | hdead⟩ := extendCall hS hpre c₁ (hr.trans hr₁)
    (b80004c68_pc h₁) v₁ (p := P) (n := n)
    (by rw [b80004c68_x10 h₁, A.x2]; rv_eval []) (by rw [b80004c68_x11 h₁, A.x19, hP])
    (by rw [b80004c68_x12 h₁, A.x19, A.x20, mul24, ← hP, ← hn])
    (by
      rcases hPb with h | h
      · intro i hi; omega
      · exact validMemRange_of (by have := hraw.1; omega) (Or.inl ⟨by simp only [heapStart] at h; omega,
          by have := hpre.heap.hi; simp only [heapNext, heapEnd] at h this ⊢; omega⟩))
    hfa.2.1 (by addr_omega [hobf, hm₁']) (by addr_omega [hobs])
    (fun x hx h ↦ by
      have hd := (v₁.deep x (Or.inl h)).1
      rcases hx with hx | hx
      · rcases hPb with h' | h'
        · subst h'; simp only [Within] at hx; omega
        · simp only [Within] at hx; omega
      · rw [hfa.2.2] at hx
        obtain ⟨i, hi, hx⟩ := hx
        have := ((hpre.opsOk.forms i (by rw [← hP, hn] at *; omega)).buf_below
          (by rw [hP] at hx; exact hx)).2
        omega)
    hpl
  swap
  · exact ⟨v, hr₂, Or.inr hdead⟩
  rw [hfa.1, hP, hn, ← formVecOf] at v₂
  -- `term(sp', One, SEP_BYTECODE)`
  have x2₂ := c₂.x2
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004c88_spec
    (by rw [hpc₂, returnAddress_eq, b80004c68_x1 h₁]; decide) (by
      rv_eval [x2₂]
      valid_access hpre.stack.valid [hsb])
  have hm₃ := b80004c88_frame h₃ (by addr_omega [hsb, x2₂])
  rw [x2₂] at hm₃
  have k₃ := b80004c88_keeps h₃
  obtain ⟨c₃, -, kv₃, -⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have v₃ := kv₃ _ _ v₂ (by addr_omega [hsb]) (by addr_omega [hsb])
  have tag₃ : t₃.getMem (s.getReg .x2 - 72) = 0 := by
    have := b80004c88_m_x2_72 h₃; rw [x2₂] at this; rv_eval [] at this; exact this
  obtain ⟨w, hr₄, ⟨hpc₄, c₄, b₄, k₄⟩ | hdead⟩ := termCall hT hpre c₃ hr₃ (b80004c88_pc h₃)
    (o := s.getReg .x2 - 144) (m := s.getReg .x2 - 72) (q := 0xa00000e0)
    (by rw [b80004c88_x10 h₃, x2₂]) (by rw [b80004c88_x11 h₃, x2₂]; rv_eval [])
    (b80004c88_x12 h₃) tag₃ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
    (validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)) (by addr_omega [])
    (by addr_omega [hsb, hro])
  swap
  · exact ⟨w, hr₂.trans hr₄, Or.inr hdead⟩
  rw [eAt_sep c₃.rodata] at b₄
  have v₄ := k₄.2 _ _ v₃ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  -- `col(sp' + 24, 0, 0)`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80004ca4_spec
    (by rw [hpc₄, returnAddress_eq, b80004c88_x1 h₃]; decide) trivial
  have hm₅ := b80004ca4_mem_same h₅
  obtain ⟨c₅, kb₅, kv₅⟩ := c₄.same hpre hm₅ fun r hr ↦ b80004ca4_keeps h₅ r (mem_of_mem hr _)
  obtain ⟨w₂, hr₆, ⟨hpc₆, c₆, b₆, k₆⟩ | hdead⟩ := colCall hC hpre c₅ (hr₄.trans hr₅) (b80004ca4_pc h₅)
    (o := s.getReg .x2 - 120) (by rw [b80004ca4_x10 h₅, c₄.x2]; rv_eval []) (by addr_omega [hsb])
    (by addr_omega [hsb]) (by addr_omega [hsb])
  swap
  · exact ⟨w₂, hr₂.trans hr₆, Or.inr hdead⟩
  rw [b80004ca4_x11 h₅, b80004ca4_x12 h₅] at b₆
  have b₆' := k₆.1 _ _ (kb₅ _ _ b₄ (by addr_omega [hsb])) (by addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb])
  have v₆ := k₆.2 _ _ (kv₅ _ _ v₄ (by addr_omega [hsb])) (by addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb])
  -- `col(sp' + 72, count, 1)`
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80004cb8_spec
    (by rw [hpc₆, returnAddress_eq, b80004ca4_x1 h₅]; decide) trivial
  have hm₇ := b80004cb8_mem_same h₇
  obtain ⟨c₇, kb₇, kv₇⟩ := c₆.same hpre hm₇ fun r hr ↦ b80004cb8_keeps h₇ r (mem_of_mem hr _)
  obtain ⟨w₃, hr₈, ⟨hpc₈, c₈, b₈, k₈⟩ | hdead⟩ := colCall hC hpre c₇ (hr₆.trans hr₇) (b80004cb8_pc h₇)
    (o := s.getReg .x2 - 72) (by rw [b80004cb8_x10 h₇, c₆.x2]; rv_eval []) (by addr_omega [hsb])
    (by addr_omega [hsb]) (by addr_omega [hsb])
  swap
  · exact ⟨w₃, hr₂.trans hr₈, Or.inr hdead⟩
  rw [b80004cb8_x11 h₇, b80004cb8_x12 h₇, c₆.x8] at b₈
  refine ⟨w₃, hr₂.trans hr₈, Or.inl ⟨by rw [hpc₈, returnAddress_eq, b80004cb8_x1 h₇]; decide, {
    toInv := c₈
    p0 := k₈.1 _ _ (kb₇ _ _ b₆' (by addr_omega [hsb])) (by addr_omega [hsb]) (by addr_omega [hsb])
      (by addr_omega [hsb])
    p1 := k₈.1 _ _ (kb₇ _ _ b₆ (by addr_omega [hsb])) (by addr_omega [hsb]) (by addr_omega [hsb])
      (by addr_omega [hsb])
    cnt := b₈
    v := k₈.2 _ _ (kv₇ _ _ v₆ (by addr_omega [hsb])) (by addr_omega [hsb]) (by addr_omega [hsb])
      (by addr_omega [hsb]) }⟩⟩

end Rv64Verifier.Layout.Bytecode
