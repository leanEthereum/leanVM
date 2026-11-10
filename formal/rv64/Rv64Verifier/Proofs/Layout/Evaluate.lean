import Rv64Verifier.Proofs.Layout.Contracts
import Rv64Verifier.Proofs.Field.All
import Rv64Verifier.Blocks.F80

/-!
# `Form::evaluate`, at `0x80010924`

```rust
pub fn evaluate(&self, column: &[E]) -> E {
    E::sum(self.terms.iter().map(|&(monomial, c)| match monomial {
        Monomial::One => c,
        Monomial::X(i) => c * column[i],
        Monomial::Xy(i, j) => c * column[i] * column[j],
    }))
}
```

compiled (`Blocks/F80.lean`), with `sp'` the entry's `sp - 144`: `0x80010924` saves eleven registers
in the frame and goes to `0x80010a44` (an empty form: zero) or `0x8001095c`, which sets the
accumulator `(s7, s6, s5)` to zero, `s4` to the first coefficient, `s3` to the count. The loop head
`0x800109bc` reads the tag: `0` copies the coefficient to `sp' + 8` (`0x80010980`); `1` checks the
index (`0x800109cc`, else the trap at `0x80010a90`) and multiplies into `sp' + 8` (`0x800109d0`);
otherwise both indices are checked and two products go through `sp' + 32` (`0x800109f4`,
`0x800109f8`, `0x80010a1c`, `0x80010a20`). `0x80010998` adds `sp' + 8` into the accumulator and
advances; `0x80010a50` writes it out, restores and returns.
-/

namespace Rv64Verifier.Layout.Evaluate
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Blocks.F80 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

@[rv_addr] def len (s : MachineState) : Nat := (s.getReg .x12).toNat
@[rv_addr] def clen (s : MachineState) : Nat := (s.getReg .x14).toNat

def column (s : MachineState) : List E := eListAt s (s.getReg .x13) (clen s)

/-- The accumulator after `k` terms. -/
def acc (s : MachineState) (k : Nat) : E :=
  ((termsOf s (s.getReg .x11) (len s)).take k).foldl (fun a t ↦ a + termValue (column s) t) 0

/-- Term `k`'s value. -/
def val (s : MachineState) (k : Nat) : E :=
  termValue (column s) (termOf s (s.getReg .x11 + BitVec.ofNat 64 (48 * k)))

theorem acc_zero (s : MachineState) : acc s 0 = 0 := by simp [acc]

theorem acc_succ {s : MachineState} {k : Nat} (hk : k < len s) : acc s (k + 1) = acc s k + val s k := by
  have hl : k < (termsOf s (s.getReg .x11) (len s)).length := by rw [termsOf_length]; exact hk
  rw [acc, List.take_succ_eq_append_getElem hl, List.foldl_append, termsOf_getElem]
  rfl

theorem acc_len (s : MachineState) :
    acc s (len s) = FormRust.evaluate ⟨termsOf s (s.getReg .x11) (len s)⟩ (column s) := by
  rw [acc, List.take_of_length_le (by rw [termsOf_length]), FormRust.evaluate, List.foldl_map]

theorem column_getD {s : MachineState} {i : Nat} (h : i < clen s) :
    (column s).getD i 0 = eAt s (s.getReg .x13 + BitVec.ofNat 64 (24 * i)) := by
  simp [column, eListAt, List.getD_eq_getElem?_getD, h]

/-- `i << 4 + i << 3`, the offset of element `i`. -/
theorem offset24 (i : Word) :
    i * 16 + i * 8 = BitVec.ofNat 64 (24 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

theorem limbs_add_xor (a v : E) :
    Model.limbs (a + v) = ((Model.limbs v).1 ^^^ (Model.limbs a).1,
      (Model.limbs v).2.1 ^^^ (Model.limbs a).2.1, (Model.limbs v).2.2 ^^^ (Model.limbs a).2.2) := by
  rw [limbs_add]
  simp only [BitVec.xor_comm]

/-- The frame after the prologue `u`: `sp`, `out`, the saved registers (in the top 88 bytes, as
`u` holds them) and memory changed only on the stack. -/
structure FrameInv (s u t : MachineState) : Prop where
  sp : t.getReg .x2 = s.getReg .x2 - 144
  out : t.getReg .x8 = s.getReg .x10
  kept : ∀ r ∈ [Reg.x26, .x27], t.getReg r = s.getReg r
  top : ∀ a, Within a (s.getReg .x2 - 88) 88 → t.getMem a = u.getMem a
  mem : MemFrame s t (stackLo s evaluateStack) evaluateStack

/-- At the loop head, before term `k`. -/
structure LoopInv (s u t : MachineState) (k : Nat) : Prop extends FrameInv s u t where
  lt : k < len s
  pc : t.pc = 0x800109bc
  x9 : t.getReg .x9 = s.getReg .x14
  x18 : t.getReg .x18 = s.getReg .x13
  x19 : t.getReg .x19 = BitVec.ofNat 64 (len s - k)
  x20 : t.getReg .x20 = s.getReg .x11 + BitVec.ofNat 64 (48 * k) + 24
  x24 : t.getReg .x24 = 1
  acc : Model.limbs (acc s k) = (t.getReg .x23, t.getReg .x22, t.getReg .x21)

/-- The registers a step to `0x80010998` keeps. -/
def loopRegs : List Reg := [.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27]

/-- A frame step that writes only the window `[sp - 136, sp - 88)` and, below `sp'`, the stack. -/
theorem FrameInv.step {s u t v : MachineState} (hpre : EvaluatePre s) (h : FrameInv s u t)
    (hm : MemFrame t v (s.getReg .x2 - 1168) 1080)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x26, .x27], v.getReg r = t.getReg r) : FrameInv s u v := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  simp only [evaluateStack, mulStack] at hsb
  exact {
    sp := (hr _ (by decide)).trans h.sp
    out := (hr _ (by decide)).trans h.out
    kept := fun r hr' ↦ (hr r (mem_of_mem hr' _)).trans (h.kept r hr')
    top := fun a ha ↦ (hm a (by addr_omega [ha, hsb])).trans (h.top a ha)
    mem := h.mem.trans hm fun a ha ↦ by addr_omega [ha, hsb] }

/-- Terms and column are the entry's at any point of the run. -/
theorem FrameInv.terms {s u t : MachineState} (hpre : EvaluatePre s) (h : FrameInv s u t)
    {a : Word} (h1 : (s.getReg .x11).toNat ≤ a.toNat)
    (h2 : a.toNat + 8 ≤ (s.getReg .x11).toNat + 48 * len s) : t.getMem a = s.getMem a := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hts := hpre.termsStack
  simp only [evaluateStack, mulStack] at hsb hts
  exact h.mem a (by addr_omega [h1, h2, hsb, hts])

theorem FrameInv.col {s u t : MachineState} (hpre : EvaluatePre s) (h : FrameInv s u t)
    {a : Word} (h1 : (s.getReg .x13).toNat ≤ a.toNat)
    (h2 : a.toNat + 8 ≤ (s.getReg .x13).toNat + 24 * clen s) : t.getMem a = s.getMem a := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hcs := hpre.columnStack
  simp only [evaluateStack, mulStack] at hsb hcs
  exact h.mem a (by addr_omega [h1, h2, hsb, hcs])

/-- `mul`'s arguments at a call from the loop: the result in the window, the operands in the
window or the input. -/
theorem mulPre {s u w : MachineState} (hpre : EvaluatePre s) (h : FrameInv s u w)
    (hout : w.getReg .x10 = s.getReg .x2 - 136 ∨ w.getReg .x10 = s.getReg .x2 - 112)
    (hl : ValidMemRange (w.getReg .x11) 3) (hr : ValidMemRange (w.getReg .x12) 3)
    (hol : Apart (w.getReg .x10) 24 (w.getReg .x11) 24)
    (hor : Apart (w.getReg .x10) 24 (w.getReg .x12) 24)
    (hls : Apart (w.getReg .x11) 24 (s.getReg .x2 - 1168) 1024)
    (hrs : Apart (w.getReg .x12) 24 (s.getReg .x2 - 1168) 1024) : MulPre w := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hro := hpre.stackRodata
  simp only [evaluateStack, mulStack] at hsb hro
  have hsl : stackLo w mulStack = s.getReg .x2 - 1168 := by
    simp only [stackLo, h.sp, mulStack]; rv_eval []
  exact {
    out := by rcases hout with h' | h' <;> rw [h'] <;> valid_sub hpre.stack.valid [hsb]
    lhs := hl
    rhs := hr
    stack := ⟨by rw [hsl]; valid_sub hpre.stack.valid [hsb], by rw [h.sp]; addr_omega [hsb]⟩
    outLhs := hol
    outRhs := hor
    outStack := by rw [hsl]; rcases hout with h' | h' <;> rw [h'] <;> addr_omega [hsb]
    lhsStack := by rw [hsl]; exact hls
    rhsStack := by rw [hsl]; exact hrs
    rodata := hpre.rodata.frame h.mem hro
    stackRodata := by rw [hsl]; addr_omega [hro, hsb] }

theorem trap : Image.code.fetch 0x80010a90 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- An `E` of a slice apart from the stack is the entry's. -/
theorem FrameInv.eAt_in {s u t : MachineState} (hpre : EvaluatePre s) (h : FrameInv s u t)
    {a lo : Word} {n : Nat} (hap : Apart lo n (stackLo s evaluateStack) evaluateStack)
    (h1 : lo.toNat ≤ a.toNat) (h2 : a.toNat + 24 ≤ lo.toNat + n) (hw : lo.toNat + n ≤ 0xc0000008) :
    eAt t a = eAt s a := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  simp only [evaluateStack, mulStack] at hsb hap
  exact eAt_congr' (h.mem _ (by addr_omega [hap, h1, h2, hw, hsb]))
    (h.mem _ (by addr_omega [hap, h1, h2, hw, hsb])) (h.mem _ (by addr_omega [hap, h1, h2, hw, hsb]))

/-- A step that writes no memory. -/
theorem FrameInv.same {s u t v : MachineState} (hpre : EvaluatePre s) (h : FrameInv s u t)
    (hm : ∀ a, v.getMem a = t.getMem a) (hr : ∀ r ∈ [Reg.x2, .x8, .x26, .x27], v.getReg r = t.getReg r) :
    FrameInv s u v :=
  h.step hpre (MemFrame.of_same hm _ _) hr

/-- A `mul` call from the loop, `out` in the window, keeps the frame. -/
theorem FrameInv.mul {s u w v : MachineState} (hpre : EvaluatePre s) (h : FrameInv s u w)
    (hout : w.getReg .x10 = s.getReg .x2 - 136 ∨ w.getReg .x10 = s.getReg .x2 - 112)
    (hpres : Preserves w v) (hpost : MulPost w v) : FrameInv s u v := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  simp only [evaluateStack, mulStack] at hsb
  have hsl : stackLo w mulStack = s.getReg .x2 - 1168 := by
    simp only [stackLo, h.sp, mulStack]; rv_eval []
  refine h.step hpre (MemFrame.of_two (lo₁ := w.getReg .x10) (n₁ := 24)
    (lo₂ := stackLo w mulStack) (n₂ := mulStack) hpost.frame ?_ ?_) fun r hr ↦ hpres r (mem_of_mem hr calleeSaved)
  · intro a ha
    rcases hout with h' | h' <;> rw [h'] at ha <;> addr_omega [ha, hsb]
  · intro a ha
    rw [hsl] at ha
    simp only [mulStack] at ha
    addr_omega [ha, hsb]

/-- Term `k`'s value into `sp' + 8`, at `0x80010998`, or a trap. -/
theorem termStep (hMul : MulSpec) {s u t : MachineState} (hpre : EvaluatePre s) {k : Nat}
    (ht : LoopInv s u t k) :
    ∃ v, Reaches Image.code t v ∧ ((v.pc = 0x80010998 ∧ FrameInv s u v ∧
      (∀ r ∈ loopRegs, v.getReg r = t.getReg r) ∧
      eAt v (s.getReg .x2 - 136) = val s k) ∨ Dead Image.code v) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hts := hpre.termsStack
  have hcs := hpre.columnStack
  simp only [evaluateStack, mulStack] at hsb hts hcs
  have hk := ht.lt
  have hT := ValidMemRange.bounds hpre.terms (by simp only [len] at hk; omega)
  simp only [len] at hk
  obtain ⟨q, hq⟩ : ∃ q, q = s.getReg .x11 + BitVec.ofNat 64 (48 * k) := ⟨_, rfl⟩
  have hqn : q.toNat = (s.getReg .x11).toNat + 48 * k := by rw [hq]; addr_omega [hT, hk]
  have hx20 : t.getReg .x20 = q + 24 := by rw [ht.x20, hq]
  have hx2 := ht.sp
  have tq0 : t.getMem q = s.getMem q := ht.terms hpre (by omega) (by simp only [len]; omega)
  have tq8 : t.getMem (q + 8) = s.getMem (q + 8) :=
    ht.terms hpre (by addr_omega [hqn, hT, hk]) (by simp only [len]; addr_omega [hqn, hT, hk])
  have tq16 : t.getMem (q + 16) = s.getMem (q + 16) :=
    ht.terms hpre (by addr_omega [hqn, hT, hk]) (by simp only [len]; addr_omega [hqn, hT, hk])
  have hc : eAt t (q + 24) = eAt s (q + 24) :=
    ht.eAt_in hpre hpre.termsStack (by addr_omega [hqn, hT, hk])
      (by addr_omega [hqn, hT, hk]) (by addr_omega [hT])
  have hvq : val s k = termValue (column s) (monoOf s q, eAt s (q + 24)) := by
    simp only [val, termOf, ← hq]
  have hlv : ValidMemRange (q + 24) 3 := by valid_sub hpre.terms [hqn, hT, hk]
  have hla : Apart (q + 24) 24 (s.getReg .x2 - 1168) 1024 := by addr_omega [hqn, hT, hk, hts, hsb]
  -- the tag
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800109bc_spec ht.pc (by
    rv_eval [hx20]; valid_access hpre.terms [hqn, hT, hk])
  have k₁ := b800109bc_keeps h₁
  have htag : t.getMem (t.getReg .x20 - 24) = s.getMem q := by
    rw [hx20, show q + 24 - 24 = q by rv_eval [], tq0]
  have inv₁ := ht.toFrameInv.same hpre (b800109bc_mem_same h₁) fun r hr ↦ k₁ r (mem_of_mem hr _)
  by_cases h0 : s.getMem q = 0
  · -- `One`: the coefficient
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80010980_spec
      (b800109bc_pc_taken h₁ (htag.trans h0)) (by
        rv_eval [k₁ .x2 (by decide), k₁ .x20 (by decide), hx2, hx20]
        and_intros <;> first
          | valid_access hpre.stack.valid [hsb]
          | valid_access hpre.terms [hqn, hT, hk])
    have k₂ := b80010980_keeps h₂
    have hm₂ := b80010980_frame h₂ (by rw [k₁ .x2 (by decide), hx2]; addr_omega [hsb])
    rw [k₁ .x2 (by decide), hx2] at hm₂
    refine ⟨t₂, hr₁.trans hr₂, Or.inl ⟨b80010980_pc h₂, inv₁.step hpre
      (hm₂.mono fun a ha ↦ by addr_omega [ha, hsb]) fun r hr ↦ k₂ r (mem_of_mem hr _),
      fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _)), ?_⟩⟩
    have m₀ := b80010980_m_x2_8 h₂
    have m₈ := b80010980_m_x2_16 h₂
    have m₁₆ := b80010980_m_x2_24 h₂
    rw [k₁ .x2 (by decide), k₁ .x20 (by decide), hx2, hx20, b800109bc_mem_same h₁] at m₀ m₈ m₁₆
    rv_eval [] at m₀ m₈ m₁₆
    rw [hvq, show monoOf s q = .one by simp [monoOf, h0], ← hc]
    exact eAt_congr m₀
      (by rw [show s.getReg .x2 - 136 + 8 = s.getReg .x2 - 128 by rv_eval [], BitVec.add_assoc]; exact m₈)
      (by rw [show s.getReg .x2 - 136 + 16 = s.getReg .x2 - 120 by rv_eval [], BitVec.add_assoc]; exact m₁₆)
  -- an index: read and checked
  have hx24₁ : t₁.getReg .x24 = 1 := (k₁ .x24 (by decide)).trans ht.x24
  have htag₁ : t₁.getReg .x11 = s.getMem q := (b800109bc_x11 h₁).trans htag
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800109c4_spec
    (b800109bc_pc_not_taken h₁ (htag.trans_ne h0)) (by
      rv_eval [k₁ .x20 (by decide), hx20]; valid_access hpre.terms [hqn, hT, hk])
  have k₂ := b800109c4_keeps h₂
  have ρ₂ : ∀ r ∈ loopRegs, t₂.getReg r = t.getReg r := fun r hr ↦
    (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _))
  have inv₂ := inv₁.same hpre (b800109c4_mem_same h₂) fun r hr ↦ k₂ r (mem_of_mem hr _)
  have hm₂ (a : Word) : t₂.getMem a = t.getMem a :=
    (b800109c4_mem_same h₂ a).trans (b800109bc_mem_same h₁ a)
  have hi₂ : t₂.getReg .x10 = s.getMem (q + 8) := by
    rw [b800109c4_x10 h₂, k₁ .x20 (by decide), hx20, show q + 24 - 16 = q + 8 by rv_eval [],
      b800109bc_mem_same h₁, tq8]
  have hx9₂ : t₂.getReg .x9 = s.getReg .x14 := (ρ₂ .x9 (by decide)).trans ht.x9
  have hx18₂ : t₂.getReg .x18 = s.getReg .x13 := (ρ₂ .x18 (by decide)).trans ht.x18
  have hx2₂ : t₂.getReg .x2 = s.getReg .x2 - 144 := (ρ₂ .x2 (by decide)).trans hx2
  obtain ⟨iw, hiw⟩ : ∃ iw, iw = s.getMem (q + 8) := ⟨_, rfl⟩
  rw [← hiw] at hi₂
  -- an element of the row, for `mul`
  have elem (w : Word) (hw : w.toNat < clen s) :
      ValidMemRange (s.getReg .x13 + BitVec.ofNat 64 (24 * w.toNat)) 3 ∧
      Apart (s.getReg .x13 + BitVec.ofNat 64 (24 * w.toNat)) 24 (s.getReg .x2 - 1168) 1024 ∧
      Apart (s.getReg .x2 - 136) 24 (s.getReg .x13 + BitVec.ofNat 64 (24 * w.toNat)) 24 ∧
      Apart (s.getReg .x2 - 112) 24 (s.getReg .x13 + BitVec.ofNat 64 (24 * w.toNat)) 24 ∧
      ∀ v, FrameInv s u v → eAt v (s.getReg .x13 + BitVec.ofNat 64 (24 * w.toNat)) =
        (column s).getD w.toNat 0 := by
    have hC := ValidMemRange.bounds hpre.column (by simp only [clen] at hw; omega)
    simp only [clen] at hw
    refine ⟨by valid_sub hpre.column [hC, hw], by addr_omega [hC, hw, hcs, hsb],
      by addr_omega [hC, hw, hcs, hsb], by addr_omega [hC, hw, hcs, hsb], fun v hv ↦ ?_⟩
    rw [column_getD (by simp only [clen]; exact hw)]
    exact hv.eAt_in hpre hpre.columnStack (by addr_omega [hC, hw]) (by addr_omega [hC, hw])
      (by addr_omega [hC])
  by_cases h1 : s.getMem q = 1
  · -- `X(i)`
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800109cc_spec
      (b800109c4_pc_not_taken h₂ (by rw [htag₁, hx24₁, h1])) trivial
    by_cases hi : iw.toNat < clen s
    swap
    · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (dead_of_fetch (by
        rw [b800109cc_pc_taken h₃ (by rw [hx9₂, hi₂]; simp only [clen] at hi; omega)]; exact trap))⟩
    obtain ⟨hrv, hra, hor, -, hval⟩ := elem iw hi
    obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800109d0_spec
      (b800109cc_pc_not_taken h₃ (by rw [hx9₂, hi₂]; simp only [clen] at hi; omega)) trivial
    have k₃ := b800109cc_keeps h₃
    have k₄ := b800109d0_keeps h₄
    have inv₄ := (inv₂.same hpre (b800109cc_mem_same h₃) fun r hr ↦ k₃ r (mem_of_mem hr _)).same
      hpre (b800109d0_mem_same h₄) fun r hr ↦ k₄ r (mem_of_mem hr _)
    have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 136 := by
      rw [b800109d0_x10 h₄, k₃ .x2 (by decide), hx2₂]; rv_eval []
    have x11₄ : t₄.getReg .x11 = q + 24 := by
      rw [b800109d0_x11 h₄, k₃ .x20 (by decide), ρ₂ .x20 (by decide), hx20]
    have x12₄ : t₄.getReg .x12 = s.getReg .x13 + BitVec.ofNat 64 (24 * iw.toNat) := by
      rw [b800109d0_x12 h₄, k₃ .x18 (by decide), k₃ .x10 (by decide), hx18₂, hi₂, offset24]
    obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hdead⟩ := hMul.call
      (hr₁.trans (hr₂.trans (hr₃.trans hr₄))) (b800109d0_pc h₄)
      (mulPre hpre inv₄ (Or.inl x10₄) (by rw [x11₄]; exact hlv) (by rw [x12₄]; exact hrv)
        (by rw [x10₄, x11₄]; addr_omega [hqn, hT, hk, hts, hsb]) (by rw [x10₄, x12₄]; exact hor)
        (by rw [x11₄]; exact hla) (by rw [x12₄]; exact hra))
    swap
    · exact ⟨t₅, hr₅, Or.inr hdead⟩
    obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800109f0_spec
      (by rw [hpc₅, returnAddress_eq, b800109d0_x1 h₄]; decide) trivial
    have k₆ := b800109f0_keeps h₆
    have inv₅ := inv₄.mul hpre (Or.inl x10₄) hpres₅ hpost₅
    refine ⟨t₆, hr₅.trans hr₆, Or.inl ⟨b800109f0_pc h₆,
      inv₅.same hpre (b800109f0_mem_same h₆) fun r hr ↦ k₆ r (mem_of_mem hr _), fun r hr ↦ ?_, ?_⟩⟩
    · rw [k₆ r (mem_of_mem hr _), hpres₅ r (mem_of_mem hr calleeSaved), k₄ r (mem_of_mem hr _),
        k₃ r (mem_of_mem hr _), ρ₂ r hr]
    · have hv := hpost₅.value
      rw [x10₄, x11₄, x12₄, inv₄.eAt_in hpre hpre.termsStack (a := q + 24)
        (by addr_omega [hqn, hT, hk]) (by addr_omega [hqn, hT, hk]) (by addr_omega [hT]),
        hval t₄ inv₄] at hv
      rw [eAt_congr (b800109f0_mem_same h₆ _) (b800109f0_mem_same h₆ _) (b800109f0_mem_same h₆ _),
        hv, hvq, show monoOf s q = .x iw.toNat by simp [monoOf, h1, hiw]]
      rfl
  · -- `Xy(i, j)`
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800109f4_spec
      (b800109c4_pc_taken h₂ (by rw [htag₁, hx24₁]; exact h1)) trivial
    by_cases hi : iw.toNat < clen s
    swap
    · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (dead_of_fetch (by
        rw [b800109f4_pc_taken h₃ (by rw [hx9₂, hi₂]; simp only [clen] at hi; omega)]; exact trap))⟩
    obtain ⟨hrv, hra, -, hor, hval⟩ := elem iw hi
    have k₃ := b800109f4_keeps h₃
    obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800109f8_spec
      (b800109f4_pc_not_taken h₃ (by rw [hx9₂, hi₂]; simp only [clen] at hi; omega)) (by
        rv_eval [k₃ .x20 (by decide), ρ₂ .x20 (by decide), hx20]
        valid_access hpre.terms [hqn, hT, hk])
    have k₄ := b800109f8_keeps h₄
    have inv₄ := (inv₂.same hpre (b800109f4_mem_same h₃) fun r hr ↦ k₃ r (mem_of_mem hr _)).same
      hpre (b800109f8_mem_same h₄) fun r hr ↦ k₄ r (mem_of_mem hr _)
    have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 112 := by
      rw [b800109f8_x10 h₄, k₃ .x2 (by decide), hx2₂]; rv_eval []
    have x11₄ : t₄.getReg .x11 = q + 24 := by
      rw [b800109f8_x11 h₄, k₃ .x20 (by decide), ρ₂ .x20 (by decide), hx20]
    have x12₄ : t₄.getReg .x12 = s.getReg .x13 + BitVec.ofNat 64 (24 * iw.toNat) := by
      rw [b800109f8_x12 h₄, k₃ .x18 (by decide), k₃ .x10 (by decide), hx18₂, hi₂, offset24]
    have x25₄ : t₄.getReg .x25 = s.getMem (q + 16) := by
      rw [b800109f8_x25 h₄, k₃ .x20 (by decide), ρ₂ .x20 (by decide), hx20,
        show q + 24 - 8 = q + 16 by rv_eval [], b800109f4_mem_same h₃, hm₂, tq16]
    obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hdead⟩ := hMul.call
      (hr₁.trans (hr₂.trans (hr₃.trans hr₄))) (b800109f8_pc h₄)
      (mulPre hpre inv₄ (Or.inr x10₄) (by rw [x11₄]; exact hlv) (by rw [x12₄]; exact hrv)
        (by rw [x10₄, x11₄]; addr_omega [hqn, hT, hk, hts, hsb]) (by rw [x10₄, x12₄]; exact hor)
        (by rw [x11₄]; exact hla) (by rw [x12₄]; exact hra))
    swap
    · exact ⟨t₅, hr₅, Or.inr hdead⟩
    have inv₅ := inv₄.mul hpre (Or.inr x10₄) hpres₅ hpost₅
    have hprod : eAt t₅ (s.getReg .x2 - 112) = eAt s (q + 24) * (column s).getD iw.toNat 0 := by
      have hv := hpost₅.value
      rw [x10₄, x11₄, x12₄, inv₄.eAt_in hpre hpre.termsStack (a := q + 24)
        (by addr_omega [hqn, hT, hk]) (by addr_omega [hqn, hT, hk]) (by addr_omega [hT]),
        hval t₄ inv₄] at hv
      exact hv
    obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80010a1c_spec
      (by rw [hpc₅, returnAddress_eq, b800109f8_x1 h₄]; decide) trivial
    have x9₅ : t₅.getReg .x9 = s.getReg .x14 := by
      rw [hpres₅.reg .x9, k₄ .x9 (by decide), k₃ .x9 (by decide), hx9₂]
    have x25₅ : t₅.getReg .x25 = s.getMem (q + 16) := by rw [hpres₅.reg .x25, x25₄]
    by_cases hj : (s.getMem (q + 16)).toNat < clen s
    swap
    · exact ⟨t₆, hr₅.trans hr₆, Or.inr (dead_of_fetch (by
        rw [b80010a1c_pc_taken h₆ (by rw [x9₅, x25₅]; simp only [clen] at hj; omega)]; exact trap))⟩
    obtain ⟨hrv', hra', hor', -, hval'⟩ := elem _ hj
    obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80010a20_spec
      (b80010a1c_pc_not_taken h₆ (by rw [x9₅, x25₅]; simp only [clen] at hj; omega)) trivial
    have k₆ := b80010a1c_keeps h₆
    have k₇ := b80010a20_keeps h₇
    have inv₇ := (inv₅.same hpre (b80010a1c_mem_same h₆) fun r hr ↦ k₆ r (mem_of_mem hr _)).same
      hpre (b80010a20_mem_same h₇) fun r hr ↦ k₇ r (mem_of_mem hr _)
    have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 144 := inv₅.sp
    have x10₇ : t₇.getReg .x10 = s.getReg .x2 - 136 := by
      rw [b80010a20_x10 h₇, k₆ .x2 (by decide), x2₅]; rv_eval []
    have x11₇ : t₇.getReg .x11 = s.getReg .x2 - 112 := by
      rw [b80010a20_x11 h₇, k₆ .x2 (by decide), x2₅]; rv_eval []
    have x12₇ : t₇.getReg .x12 = s.getReg .x13 + BitVec.ofNat 64 (24 * (s.getMem (q + 16)).toNat) := by
      rw [b80010a20_x12 h₇, k₆ .x18 (by decide), k₆ .x25 (by decide), hpres₅.reg .x18, x25₅,
        k₄ .x18 (by decide), k₃ .x18 (by decide), hx18₂, offset24]
    obtain ⟨t₈, hr₈, ⟨hpc₈, hpres₈, hpost₈⟩ | hdead⟩ := hMul.call
      (hr₆.trans hr₇) (b80010a20_pc h₇)
      (mulPre hpre inv₇ (Or.inl x10₇) (by rw [x11₇]; valid_sub hpre.stack.valid [hsb])
        (by rw [x12₇]; exact hrv') (by rw [x10₇, x11₇]; addr_omega [hsb])
        (by rw [x10₇, x12₇]; exact hor') (by rw [x11₇]; addr_omega [hsb]) (by rw [x12₇]; exact hra'))
    swap
    · exact ⟨t₈, hr₅.trans hr₈, Or.inr hdead⟩
    obtain ⟨t₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b80010a40_spec
      (by rw [hpc₈, returnAddress_eq, b80010a20_x1 h₇]; decide) trivial
    have k₉ := b80010a40_keeps h₉
    have inv₈ := inv₇.mul hpre (Or.inl x10₇) hpres₈ hpost₈
    refine ⟨t₉, hr₅.trans (hr₈.trans hr₉), Or.inl ⟨b80010a40_pc h₉,
      inv₈.same hpre (b80010a40_mem_same h₉) fun r hr ↦ k₉ r (mem_of_mem hr _), fun r hr ↦ ?_, ?_⟩⟩
    · rw [k₉ r (mem_of_mem hr _), hpres₈ r (mem_of_mem hr calleeSaved), k₇ r (mem_of_mem hr _),
        k₆ r (mem_of_mem hr _), hpres₅ r (mem_of_mem hr calleeSaved), k₄ r (mem_of_mem hr _),
        k₃ r (mem_of_mem hr _), ρ₂ r hr]
    · have hv := hpost₈.value
      have h112 : eAt t₇ (s.getReg .x2 - 112) = eAt t₅ (s.getReg .x2 - 112) :=
        eAt_congr ((b80010a20_mem_same h₇ _).trans (b80010a1c_mem_same h₆ _))
          ((b80010a20_mem_same h₇ _).trans (b80010a1c_mem_same h₆ _))
          ((b80010a20_mem_same h₇ _).trans (b80010a1c_mem_same h₆ _))
      rw [x10₇, x11₇, x12₇, h112, hprod, hval' t₇ inv₇] at hv
      rw [eAt_congr (b80010a40_mem_same h₉ _) (b80010a40_mem_same h₉ _) (b80010a40_mem_same h₉ _),
        hv, hvq, show monoOf s q = .xy iw.toNat (s.getMem (q + 16)).toNat by
          rw [monoOf, ite_eq_right_of_eq_false _ _ (eq_false h0), ite_eq_right_of_eq_false _ _ (eq_false h1), ← hiw]]
      rfl

/-- The loop is over: at the epilogue with every term added, or at a dead end. -/
def Done (s u t : MachineState) : Prop :=
  (t.pc = 0x80010a50 ∧ FrameInv s u t ∧
    Model.limbs (acc s (len s)) = (t.getReg .x23, t.getReg .x22, t.getReg .x21)) ∨ Dead Image.code t

theorem limbs_zero : Model.limbs (0 : E) = (0, 0, 0) := by decide +kernel

/-- One iteration: term `k` added, then the loop head or the epilogue. -/
theorem body (hMul : MulSpec) {s u : MachineState} (hpre : EvaluatePre s) (t : MachineState)
    (hinv : ∃ k, LoopInv s u t k) :
    (∃ v, Reaches Image.code t v ∧ Done s u v) ∨
      (∃ v, Reaches Image.code t v ∧ (∃ k, LoopInv s u v k) ∧
        (v.getReg .x19).toNat < (t.getReg .x19).toNat) := by
  obtain ⟨k, ht⟩ := hinv
  have hsb := hpre.stack.bounds (by decide) (by decide)
  simp only [evaluateStack, mulStack] at hsb
  have hk := ht.lt
  obtain ⟨v, hrv, ⟨hpc, hinv, hregs, hval⟩ | hdead⟩ := termStep hMul hpre ht
  swap
  · exact Or.inl ⟨v, hrv, Or.inr hdead⟩
  obtain ⟨w, hrw, h⟩ := Sym.BlockSpec.reaches b80010998_spec hpc (by
    rv_eval [hinv.sp]
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have kw := b80010998_keeps h
  have invw := hinv.same hpre (b80010998_mem_same h) fun r hr ↦ kw r (mem_of_mem hr _)
  have hl := limbs_eAt v (s.getReg .x2 - 136)
  rw [hval] at hl
  have x21 := b80010998_x21 h
  have x22 := b80010998_x22 h
  have x23 := b80010998_x23 h
  rw [hinv.sp] at x21 x22 x23
  rv_eval [] at x21 x22 x23
  have hacc : Model.limbs (acc s (k + 1)) = (w.getReg .x23, w.getReg .x22, w.getReg .x21) := by
    rw [acc_succ hk, limbs_add_xor, hl, ht.acc, x21, x22, x23, hregs .x21 (by decide),
      hregs .x22 (by decide), hregs .x23 (by decide)]
    simp only [show s.getReg .x2 - 136 + 8 = s.getReg .x2 - 128 by rv_eval [],
      show s.getReg .x2 - 136 + 16 = s.getReg .x2 - 120 by rv_eval []]
  have x19v : v.getReg .x19 = BitVec.ofNat 64 (len s - k) := (hregs .x19 (by decide)).trans ht.x19
  have hlen := (s.getReg .x12).isLt
  simp only [len] at hk hlen x19v ⊢
  by_cases hlast : k + 1 = (s.getReg .x12).toNat
  · refine Or.inl ⟨w, hrv.trans hrw, Or.inl ⟨b80010998_pc_taken h (by rw [x19v]; addr_omega [hlast, hlen]),
      invw, ?_⟩⟩
    simp only [len, ← hlast]; exact hacc
  · refine Or.inr ⟨w, hrv.trans hrw, ⟨k + 1, {
      toFrameInv := invw
      lt := by simp only [len]; omega
      pc := b80010998_pc_not_taken h (by rw [x19v]; addr_omega [hlast, hk, hlen])
      x9 := by rw [kw .x9 (by decide), hregs .x9 (by decide), ht.x9]
      x18 := by rw [kw .x18 (by decide), hregs .x18 (by decide), ht.x18]
      x19 := by rw [b80010998_x19 h, x19v]; simp only [len]; addr_omega [hk, hlen, hlast]
      x20 := by
        rw [b80010998_x20 h, hregs .x20 (by decide), ht.x20]
        have hT := ValidMemRange.bounds hpre.terms (by omega)
        addr_omega [hT, hk, hlast]
      x24 := by rw [kw .x24 (by decide), hregs .x24 (by decide), ht.x24]
      acc := hacc }⟩, ?_⟩
    rw [b80010998_x19 h, x19v, ht.x19]
    addr_omega [hk, hlen, hlast]

/-- The prologue: the epilogue for an empty form, else the loop head. -/
theorem setup {s : MachineState} (hpc : s.pc = 0x80010924) (hpre : EvaluatePre s) :
    ∃ u, b80010924.Holds s u ∧ ∃ t, Reaches Image.code s t ∧
      ((t.pc = 0x80010a50 ∧ FrameInv s u t ∧
        Model.limbs (acc s (len s)) = (t.getReg .x23, t.getReg .x22, t.getReg .x21)) ∨
        ∃ k, LoopInv s u t k) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  simp only [evaluateStack, mulStack] at hsb
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010924_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b80010924_keeps h₁
  have hm₁ := b80010924_frame h₁ (by addr_omega [hsb])
  have inv₁ : FrameInv s u u := {
    sp := b80010924_x2 h₁
    out := b80010924_x8 h₁
    kept := fun r hr ↦ k₁ r (mem_of_mem hr _)
    top := fun _ _ ↦ rfl
    mem := hm₁.mono fun a ha ↦ by addr_omega [ha, hsb] }
  refine ⟨u, h₁, ?_⟩
  by_cases h0 : s.getReg .x12 = 0
  · obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b80010a44_spec (b80010924_pc_taken h₁ h0) trivial
    have kt := b80010a44_keeps h
    refine ⟨t, hr₁.trans hr, Or.inl ⟨b80010a44_pc h,
      inv₁.same hpre (b80010a44_mem_same h) fun r hr ↦ kt r (mem_of_mem hr _), ?_⟩⟩
    rw [b80010a44_x21 h, b80010a44_x22 h, b80010a44_x23 h,
      show len s = 0 by simp [len, h0], acc_zero]
    exact limbs_zero
  · obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b8001095c_spec (b80010924_pc_not_taken h₁ h0) trivial
    have kt := b8001095c_keeps h
    refine ⟨t, hr₁.trans hr, Or.inr ⟨0, {
      toFrameInv := inv₁.same hpre (b8001095c_mem_same h) fun r hr ↦ kt r (mem_of_mem hr _)
      lt := by simp only [len]; rcases Nat.eq_zero_or_pos (s.getReg .x12).toNat with h' | h'
               · exact absurd (BitVec.eq_of_toNat_eq h') h0
               · exact h'
      pc := b8001095c_pc h
      x9 := by rw [b8001095c_x9 h, k₁ .x14 (by decide)]
      x18 := by rw [b8001095c_x18 h, k₁ .x13 (by decide)]
      x19 := by rw [b8001095c_x19 h, k₁ .x12 (by decide)]; simp [len]
      x20 := by rw [b8001095c_x20 h, k₁ .x11 (by decide)]; simp
      x24 := b8001095c_x24 h
      acc := by rw [b8001095c_x21 h, b8001095c_x22 h, b8001095c_x23 h, acc_zero]; exact limbs_zero }⟩⟩

/-- **`Form::evaluate` meets its contract**, given `mul`'s. -/
theorem evaluate_spec (hMul : MulSpec) : EvaluateSpec := by
  intro s hpc hpre
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hos := hpre.outStack
  have hob := ValidMemRange.bounds hpre.out (by decide)
  simp only [evaluateStack, mulStack] at hsb hos
  obtain ⟨u, h₁, t, hst, ht⟩ := setup hpc hpre
  obtain ⟨v, hsv, hv⟩ : ∃ v, Reaches Image.code s v ∧ Done s u v := by
    rcases ht with ht | ht
    · exact ⟨t, hst, Or.inl ht⟩
    · obtain ⟨v, htv, hv⟩ := Reaches.loop (fun t ↦ ∃ k, LoopInv s u t k) (fun t ↦ (t.getReg .x19).toNat)
        (Done s u) (body hMul hpre) t ht
      exact ⟨v, hst.trans htv, hv⟩
  rcases hv with ⟨hpc', hinv, hacc⟩ | hdead
  swap
  · exact ⟨v, hsv, Or.inr hdead⟩
  obtain ⟨w, hrw, h⟩ := Sym.BlockSpec.reaches b80010a50_spec hpc' (by
    rv_eval [hinv.sp, hinv.out]
    and_intros <;> first
      | valid_access hpre.stack.valid [hsb]
      | valid_access hpre.out [hob]
      | addr_omega [hsb, hos, hob])
  have k := b80010a50_keeps h
  have hm := b80010a50_frame h (by rw [hinv.out]; addr_omega [hob])
  rw [hinv.out] at hm
  have pc := b80010a50_pc h
  have r1 := b80010a50_x1 h
  have r2 := b80010a50_x2 h
  have r8 := b80010a50_x8 h
  have r9 := b80010a50_x9 h
  have r18 := b80010a50_x18 h
  have r19 := b80010a50_x19 h
  have r20 := b80010a50_x20 h
  have r21 := b80010a50_x21 h
  have r22 := b80010a50_x22 h
  have r23 := b80010a50_x23 h
  have r24 := b80010a50_x24 h
  have r25 := b80010a50_x25 h
  rw [hinv.sp] at pc r1 r2 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25
  rv_eval [] at pc r1 r2 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25
  have top (a : Word) (h1 : (s.getReg .x2).toNat - 88 ≤ a.toNat) (h2 : a.toNat < (s.getReg .x2).toNat) :
      v.getMem a = u.getMem a := hinv.top a (by addr_omega [h1, h2, hsb])
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n8 h₁] at pc r1
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n16 h₁] at r8
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n24 h₁] at r9
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n32 h₁] at r18
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n40 h₁] at r19
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n48 h₁] at r20
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n56 h₁] at r21
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n64 h₁] at r22
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n72 h₁] at r23
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n80 h₁] at r24
  rw [top _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80010924_m_x2_n88 h₁] at r25
  refine ⟨w, hsv.trans hrw, Or.inl ⟨pc.trans (returnAddress_eq s).symm,
    preserves_of r2 r8 r9 r18 r19 fun r hr ↦ ?_, ?_, fun a h1 h2 ↦ ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r20
    · exact r21
    · exact r22
    · exact r23
    · exact r24
    · exact r25
    · rw [k .x26 (by decide)]; exact hinv.kept .x26 (by decide)
    · rw [k .x27 (by decide)]; exact hinv.kept .x27 (by decide)
  · show eAt w _ = FormRust.evaluate ⟨termsOf s (s.getReg .x11) (len s)⟩ (column s)
    rw [← acc_len]
    apply eAt_eq_of_limbs
    have m0 := b80010a50_m_x8_0 h
    have m8 := b80010a50_m_x8_8 h
    have m16 := b80010a50_m_x8_16 h
    rw [hinv.out] at m0 m8 m16
    rw [m0, m8, m16]
    exact hacc.symm
  · exact (hm a h1).trans (hinv.mem a h2)

end Rv64Verifier.Layout.Evaluate
