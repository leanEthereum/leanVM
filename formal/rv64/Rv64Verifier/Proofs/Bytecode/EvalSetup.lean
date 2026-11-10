import Rv64Verifier.Proofs.Bytecode.EvalExit

/-!
# `Bytecode::evaluate`: the prologue

`0x80010e24` saves the registers and checks `point.len() < 64`, `0x80010e64` checks
`self.len == 1 << point.len()` (both fail to `Err`, `err_exit`); `0x80010e74`..`0x80010e8c` split
the point at `min(len, 14)` and call `eq_kernel` on the low part, `0x80010eb4` on the high part;
`0x80010ec8` calls `vec![ZERO; 2048]`; `0x80010efc` branches to the empty-table `Ok(ZERO)` when
there is no block; `0x80010f04` caches the fields the loop reads and enters it at `0x80011090`.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- From the entry to the first call: the frame saved, the size checked, the point split. -/
structure PreCall (s t : MachineState) : Prop where
  saved : Saved s t
  out : t.getMem (s.getReg .x2 - 1960) = s.getReg .x10
  mem : ∀ a, ¬ Within a (stackLo s evalStack) evalStack → t.getMem a = s.getMem a
  bframe : ByteFrame s t fun a ↦ Within a (stackLo s evalStack) evalStack
  short : (s.getReg .x13).toNat < 64
  len : (readBytecode s (s.getReg .x11)).len = 2 ^ (s.getReg .x13).toNat
  x8 : t.getReg .x8 = s.getReg .x11
  x9 : t.getReg .x9 = s.getReg .x12 + BitVec.ofNat 64 (24 * min (s.getReg .x13).toNat 14)
  x10 : t.getReg .x10 = s.getReg .x2 - 1760
  x11 : t.getReg .x11 = s.getReg .x12
  x12 : (t.getReg .x12).toNat = min (s.getReg .x13).toNat 14
  x18 : (t.getReg .x18).toNat = (s.getReg .x13).toNat - min (s.getReg .x13).toNat 14
  x1 : t.getReg .x1 = 0x80010eb4

set_option maxHeartbeats 1000000 in
/-- The prologue up to the call of `eq_kernel` on the low part, or `Err`. -/
theorem prologue {s : MachineState} (hpc : s.pc = 0x80010e24) (hpre : EvaluatePre s) :
    ∃ t, Reaches Image.code s t ∧
      ((t.pc = 0x800116dc ∧ Saved s t ∧ t.getReg .x10 = s.getReg .x10 ∧
          (∀ a, ¬ Within a (stackLo s evalStack) evalStack → t.getMem a = s.getMem a) ∧
          ¬ ((s.getReg .x13).toNat < 64 ∧
            (readBytecode s (s.getReg .x11)).len = 2 ^ (s.getReg .x13).toNat)) ∨
        (t.pc = 0x8000cb38 ∧ PreCall s t)) := by
  have hsp := sp_bounds hpre.stack
  have hst := hpre.stack.valid
  have hbc := hpre.bc.self
  have hbca := hpre.bc.align
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80010e24_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst [hsp])
  have k₀ := b80010e24_keeps h₀
  have hf₀ := b80010e24_frame h₀ (by addr_omega [hsp])
  have hm₀ : ∀ a, ¬ Within a (stackLo s evalStack) evalStack → t₀.getMem a = s.getMem a :=
    fun a ha ↦ hf₀ a (by addr_omega [ha, hsp])
  have hs₀ : Saved s t₀ := {
    sp := by rw [b80010e24_x2 h₀]; rfl
    r1 := by rw [b80010e24_m_x2_n8 h₀]
    r8 := by rw [b80010e24_m_x2_n16 h₀]
    r9 := by rw [b80010e24_m_x2_n24 h₀]
    r18 := by rw [b80010e24_m_x2_n32 h₀]
    r19 := by rw [b80010e24_m_x2_n40 h₀]
    r20 := by rw [b80010e24_m_x2_n48 h₀]
    r21 := by rw [b80010e24_m_x2_n56 h₀]
    r22 := by rw [b80010e24_m_x2_n64 h₀]
    r23 := by rw [b80010e24_m_x2_n72 h₀]
    r24 := by rw [b80010e24_m_x2_n80 h₀]
    r25 := by rw [b80010e24_m_x2_n88 h₀]
    r26 := by rw [b80010e24_m_x2_n96 h₀]
    r27 := by rw [b80010e24_m_x2_n104 h₀] }
  by_cases hn : (63 : Word).toNat < (s.getReg .x13).toNat
  · refine ⟨t₀, hr₀, Or.inl ⟨b80010e24_pc_taken h₀ hn, hs₀, k₀ .x10 (by decide), hm₀, ?_⟩⟩
    rintro ⟨h, -⟩
    simp only [Sym.wordToNatLit] at hn
    omega
  have hn' : (s.getReg .x13).toNat < 64 := by simp only [Sym.wordToNatLit] at hn; omega
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010e64_spec (b80010e24_pc_not_taken h₀
    (Nat.not_lt.mp hn)) (by
    rv_eval [k₀ .x11 (by decide)]
    valid_in hbc [hbc, hbca])
  have k₁ := b80010e64_keeps h₁
  have pc₁ := h₁.pc
  rv_eval [k₀ .x11 (by decide), k₀ .x13 (by decide)] at pc₁
  have hlen96 : t₀.getMem (s.getReg .x11 + 96) = s.getMem (s.getReg .x11 + 96) :=
    hm₀ _ (by addr_omega [hpre.bcClear.self, hsp, hbc])
  rw [hlen96] at pc₁
  have hpow : (1 : Word) * BitVec.ofNat 64 (2 ^ ((s.getReg .x13).toNat % 64)) =
      BitVec.ofNat 64 (2 ^ (s.getReg .x13).toNat) := by
    rw [Nat.mod_eq_of_lt hn']; simp
  have hlenEq : s.getMem (s.getReg .x11 + 96) = BitVec.ofNat 64 (2 ^ (s.getReg .x13).toNat) ↔
      (readBytecode s (s.getReg .x11)).len = 2 ^ (s.getReg .x13).toNat := by
    simp only [readBytecode]
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn')
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn')).symm
  by_cases hl : s.getMem (s.getReg .x11 + 96) = BitVec.ofNat 64 (2 ^ (s.getReg .x13).toNat)
  swap
  · refine ⟨t₁, hr₀.trans hr₁, Or.inl ⟨?_, ?_, ?_, ?_, fun h ↦ hl (hlenEq.mpr h.2)⟩⟩
    · rw [pc₁, hpow]; exact ite_bne_of_ne hl
    · exact hs₀.of_frame (k₁ .x2 (by decide)) (fun a _ _ ↦ b80010e64_mem_same h₁ a)
        (by addr_omega [hsp])
    · rw [k₁ .x10 (by decide), k₀ .x10 (by decide)]
    · intro a ha; rw [b80010e64_mem_same h₁, hm₀ a ha]
  have pc₁' : t₁.pc = 0x80010e74 := by rw [pc₁, hpow]; exact ite_bne_of_eq hl
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80010e74_spec pc₁' (by
    rv_eval [k₁ .x2 (by decide), b80010e24_x2 h₀]
    valid_access hst [hsp])
  have k₂ := b80010e74_keeps h₂
  have e2 : t₁.getReg .x2 = s.getReg .x2 - 1968 := by rw [k₁ .x2 (by decide), b80010e24_x2 h₀]
  have hf₂ := b80010e74_frame h₂ (by rw [e2]; addr_omega [hsp])
  rw [e2] at hf₂
  have m₂ := b80010e74_m_x2_8 h₂
  rw [e2, k₁ .x10 (by decide), k₀ .x10 (by decide)] at m₂
  rv_eval [] at m₂
  have x13₁ : t₁.getReg .x13 = s.getReg .x13 := by rw [k₁ .x13 (by decide), k₀ .x13 (by decide)]
  -- the split point `min(len, 14)` in `a4`
  obtain ⟨t₃, hr₃, pc₃, k₃, x14₃, hm₃⟩ : ∃ t₃, Reaches Image.code t₂ t₃ ∧ t₃.pc = 0x80010e8c ∧
      (∀ r ∈ [Reg.x1, .x2, .x8, .x9, .x10, .x11, .x12, .x13, .x18, .x19, .x20, .x21, .x22, .x23,
        .x24, .x25, .x26, .x27], t₃.getReg r = t₂.getReg r) ∧
      (t₃.getReg .x14).toNat = min (s.getReg .x13).toNat 14 ∧ ∀ a, t₃.getMem a = t₂.getMem a := by
    by_cases h14 : (t₁.getReg .x13).toNat < (14 : Word).toNat
    · refine ⟨t₂, Reaches.refl _, b80010e74_pc_taken h₂ h14, fun _ _ ↦ rfl, ?_, fun _ ↦ rfl⟩
      rw [b80010e74_x14 h₂, x13₁]
      rw [x13₁] at h14
      simp only [Sym.wordToNatLit] at h14
      omega
    · obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010e88_spec
        (b80010e74_pc_not_taken h₂ (Nat.not_lt.mp h14)) trivial
      refine ⟨t₃, hr₃, b80010e88_pc h₃, fun r hr ↦ (b80010e88_keeps h₃) r (mem_of_mem hr _), ?_,
        b80010e88_mem_same h₃⟩
      rw [b80010e88_x14 h₃]
      rw [x13₁] at h14
      simp only [Sym.wordToNatLit] at h14 ⊢
      omega
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80010e8c_spec pc₃ trivial
  have k₄ := b80010e8c_keeps h₄
  have hm₄ := b80010e8c_mem_same h₄
  have e13 : t₃.getReg .x13 = s.getReg .x13 := by
    rw [k₃ .x13 (by decide), k₂ .x13 (by decide), x13₁]
  have e12 : t₃.getReg .x12 = s.getReg .x12 := by
    rw [k₃ .x12 (by decide), k₂ .x12 (by decide), k₁ .x12 (by decide), k₀ .x12 (by decide)]
  have e2' : t₃.getReg .x2 = s.getReg .x2 - 1968 := by
    rw [k₃ .x2 (by decide), k₂ .x2 (by decide), e2]
  have hmin : min (s.getReg .x13).toNat 14 ≤ (s.getReg .x13).toNat := Nat.min_le_left _ _
  have hmem : ∀ a, ¬ Within a (stackLo s evalStack) evalStack → t₄.getMem a = s.getMem a := by
    intro a ha
    rw [hm₄, hm₃, hf₂ a (by addr_omega [ha, hsp]), b80010e64_mem_same h₁, hm₀ a ha]
  refine ⟨t₄, hr₀.trans (hr₁.trans (hr₂.trans (hr₃.trans hr₄))), Or.inr ⟨b80010e8c_pc h₄, ?_⟩⟩
  exact {
    saved := hs₀.of_frame (by rw [k₄ .x2 (by decide), k₃ .x2 (by decide), k₂ .x2 (by decide),
        k₁ .x2 (by decide)])
      (fun a h1 h2 ↦ by
        rw [hm₄, hm₃, hf₂ a (by addr_omega [h1, h2, hsp]), b80010e64_mem_same h₁])
      (by addr_omega [hsp])
    out := by rw [hm₄, hm₃, m₂]
    mem := hmem
    bframe := by
      have u₀ := h₀.unaligned (by rv_eval []; and_intros <;> addr_omega [hsp])
      have u₂ := h₂.unaligned (by rv_eval [e2]; addr_omega [hsp])
      refine ByteFrame.of_memFrame (lo := stackLo s evalStack) (n := evalStack) hmem
        (by addr_omega [hsp]) (by decide) fun a ha ↦ ?_
      rw [hm₄, hm₃, u₂ a ha, b80010e64_mem_same h₁, u₀ a ha]
    short := hn'
    len := hlenEq.mp hl
    x8 := by rw [k₄ .x8 (by decide), k₃ .x8 (by decide), b80010e74_x8 h₂, k₁ .x11 (by decide),
      k₀ .x11 (by decide)]
    x9 := by rw [b80010e8c_x9 h₄, e12, mul24, x14₃]
    x10 := by rw [b80010e8c_x10 h₄, e2']; rv_eval []
    x11 := by rw [b80010e8c_x11 h₄, e12]
    x12 := by rw [b80010e8c_x12 h₄, x14₃]
    x18 := by
      rw [b80010e8c_x18 h₄, e13, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [x14₃]; exact hmin)),
        x14₃]
    x1 := b80010e8c_x1 h₄ }

/-! ## The calls -/

/-- Doublewords none of whose bytes are in `W` are unchanged. -/
def DW (s t : MachineState) (W : Word → Prop) : Prop :=
  ∀ a, (∀ i < 8, ¬ W (a + BitVec.ofNat 64 i)) → t.getMem a = s.getMem a

theorem DW.trans {s t u : MachineState} {W W' V : Word → Prop} (h₁ : DW s t W) (h₂ : DW t u W')
    (hW : ∀ a, W a → V a) (hW' : ∀ a, W' a → V a) : DW s u V :=
  fun a ha ↦ (h₂ a fun i hi h ↦ ha i hi (hW' _ h)).trans (h₁ a fun i hi h ↦ ha i hi (hW _ h))

theorem _root_.Rv64Verifier.Runtime.ByteFrame.dw {s t : MachineState} {W : Word → Prop} (h : ByteFrame s t W) : DW s t W :=
  fun _ ha ↦ h.getMem ha

theorem DW.of_same {s t : MachineState} (h : ∀ a, t.getMem a = s.getMem a) (W : Word → Prop) :
    DW s t W :=
  fun a _ ↦ h a

/-- A doubleword frame of a range. -/
theorem DW.of_mem {s t : MachineState} {lo : Word} {n : Nat}
    (h : ∀ a, ¬ Within a lo n → t.getMem a = s.getMem a) : DW s t (Within · lo n) :=
  fun a ha ↦ h a (by have := ha 0 (by decide); simpa using this)

/-- A byte frame that misses `.rodata` keeps it: an aligned doubleword of it lies in it, and an
unaligned one is not written. -/
theorem RodataOk.of_byteFrame {s t : MachineState} {W : Word → Prop} (h : RodataOk s)
    (hf : ByteFrame s t W) (hw : ∀ a, Within a rodataBase rodataSize → ¬ W a) : RodataOk t :=
  RodataOk.of_dwords h fun a ha ↦ by
    by_cases h8 : a.toNat % 8 = 0
    · exact hf.getMem fun i hi ↦ hw _ (by addr_omega [ha, h8, hi])
    · exact hf.unaligned a h8

theorem HeapOk.of_next {s t : MachineState} (h : HeapOk s)
    (he : t.getMem nextAddr = s.getMem nextAddr) : HeapOk t :=
  ⟨by simp only [heapNext, he]; exact h.lo, by simp only [heapNext, he]; exact h.hi⟩

/-- The callees' stacks lie in `evaluate`'s. -/
theorem rtStack_inner {s t : MachineState} (h : RtStack s evalStack)
    (ht : t.getReg .x2 = s.getReg .x2 - 1968) {n : Nat} (hn : n ≤ eqKernelStack) (h8 : n % 8 = 0)
    (h0 : 8 ≤ n) : RtStack t n := by
  have hsp := sp_bounds h
  have hv := h.valid
  have hr := h.rodata
  have hx := h.next
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [stackLo, ht]
    refine ValidMemRange.sub hv ?_ ?_ ?_ <;> addr_omega [hsp, hn, h8, h0]
  · rw [ht]; addr_omega [hsp]
  · simp only [stackLo, ht]; addr_omega [hsp, hn]
  · simp only [stackLo, ht]; addr_omega [hsp, hn, hx]
  · simp only [stackLo, ht]; addr_omega [hsp, hn, hr]

/-- When the table has no block: `0x800116ec` sets the total to zero. -/
structure EmptyOk (s t : MachineState) : Prop where
  saved : Saved s t
  out : t.getMem (s.getReg .x2 - 1960) = s.getReg .x10
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  frame : ByteFrame s t fun a ↦
    Within a (stackLo s evalStack) evalStack ∨ Within a nextAddr 8 ∨ Fresh s t a
  short : (s.getReg .x13).toNat < 64
  len : (readBytecode s (s.getReg .x11)).len = 2 ^ (s.getReg .x13).toNat
  empty : vecLen s (s.getReg .x11) = 0

/-- The registers at the loop's head the first time. -/
structure InitRegs (e : Env) (t : MachineState) : Prop where
  x13 : t.getReg .x13 = e.blocksPtr
  x12 : t.getReg .x12 = 0
  x19 : t.getReg .x19 = 0
  x11 : t.getReg .x11 = 0
  x5 : t.getReg .x5 = 0
  x17 : t.getReg .x17 = 0
  x16 : t.getReg .x16 = 0
  x9 : t.getReg .x9 = e.low
  x18 : (t.getReg .x18).toNat = 2 ^ e.m
  x20 : t.getReg .x20 = e.bk
  x21 : t.getReg .x21 = 2048
  x23 : t.getReg .x23 = e.s.getReg .x2 - 136
  nonempty : e.blocksLen ≠ 0

/-- After the three calls, at `0x80010efc`: the eq tables and the buckets in fresh memory. -/
structure Called (s u : MachineState) (low high bk : Word) : Prop where
  saved : Saved s u
  out : u.getMem (s.getReg .x2 - 1960) = s.getReg .x10
  short : (s.getReg .x13).toNat < 64
  len : (readBytecode s (s.getReg .x11)).len = 2 ^ (s.getReg .x13).toNat
  x8 : u.getReg .x8 = s.getReg .x11
  x9 : u.getReg .x9 = low
  x18 : (u.getReg .x18).toNat = 2 ^ min (s.getReg .x13).toNat 14
  c56 : u.getMem (s.getReg .x2 - 1912) = high
  c64 : (u.getMem (s.getReg .x2 - 1904)).toNat = 2 ^ ((s.getReg .x13).toNat - min (s.getReg .x13).toNat 14)
  c264 : u.getMem (s.getReg .x2 - 1704) = bk
  c272 : u.getMem (s.getReg .x2 - 1696) = 2048
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  rodata : RodataOk u
  frame : ByteFrame s u fun a ↦
    Within a (stackLo s evalStack) evalStack ∨ Within a nextAddr 8 ∨ Fresh s u a
  lowIn : heapNext s ≤ low.toNat ∧ low.toNat + 24 * 2 ^ min (s.getReg .x13).toNat 14 ≤ heapNext u ∧
    low.toNat % 8 = 0
  highIn : heapNext s ≤ high.toNat ∧
    high.toNat + 24 * 2 ^ ((s.getReg .x13).toNat - min (s.getReg .x13).toNat 14) ≤ heapNext u ∧
    high.toNat % 8 = 0
  bkIn : heapNext s ≤ bk.toNat ∧ bk.toNat + 49152 ≤ heapNext u ∧ bk.toNat % 8 = 0
  lowBk : Apart low (24 * 2 ^ min (s.getReg .x13).toNat 14) bk 49152
  highBk : Apart high (24 * 2 ^ ((s.getReg .x13).toNat - min (s.getReg .x13).toNat 14)) bk 49152
  lowVals : eListAt u low (2 ^ min (s.getReg .x13).toNat 14) =
    Model.eqKernelRust ((eListAt s (s.getReg .x12) (s.getReg .x13).toNat).take
      (min (s.getReg .x13).toNat 14))
  highVals : eListAt u high (2 ^ ((s.getReg .x13).toNat - min (s.getReg .x13).toNat 14)) =
    Model.eqKernelRust ((eListAt s (s.getReg .x12) (s.getReg .x13).toNat).drop
      (min (s.getReg .x13).toNat 14))
  bkVals : eListAt u bk 2048 = List.replicate 2048 0

end Rv64Verifier.Proofs.Bytecode.Eval
