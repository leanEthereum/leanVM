import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Blocks.F73

/-!
# `E::pow`

```rust
pub fn pow(self, exponent: u64) -> Self {
    let (mut base, mut out, mut n) = (self, ONE, exponent);
    while n != 0 {
        if n & 1 == 1 {
            out *= base;
        }
        base = base.square();
        n >>= 1;
    }
    out
}
```

compiled at `0x8000ef7c` (`Blocks/F73.lean`): `a0` is the return slot, `a1` the caller's copy of
`self`, which holds `base` (`s2`), `a2` the exponent (`s1`). The 80-byte frame (`F`, `sp - 80`)
holds `out` at `F`, the callees' result at `F + 24` and the saved registers at `F + 48`.
`0x8000ef7c` sets `out = ONE` and goes to the epilogue `0x8000f01c` for a zero exponent; the loop
head `0x8000efe4` tests the low bit; `0x8000efec` calls `<E as Mul>::mul` (`EMulSpec`), and
`0x8000f000` copies the product to `out`; `0x8000efb4` calls `E::square` (`ESquareSpec`), and
`0x8000efc4` copies the square to `base`, shifts `n`, and loops or leaves.

The invariant is `out * base ^ n = self ^ exponent` (`LoopInv`), the loop `Reaches.loop` on `n`.
-/

namespace Rv64Verifier.Proofs.Field.Pow
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F73
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The entry's `self`. -/
def x0 (s : MachineState) : E := eAt s (s.getReg .x11)

/-- The callee-saved registers `pow` never touches. -/
def kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem mem_of_kept {r : Reg} (h : r ∈ kept) (l : List Reg)
    (hl : ∀ r ∈ kept, r ∈ l := by decide) : r ∈ l :=
  hl r h

/-- Inside the frame: registers, saved registers, and memory outside `self` and the stack. -/
structure Saved (s t : MachineState) : Prop where
  sp : t.getReg .x2 = s.getReg .x2 - 80
  out : t.getReg .x8 = s.getReg .x10
  kept : ∀ r ∈ kept, t.getReg r = s.getReg r
  ra : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : t.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : t.getMem (s.getReg .x2 - 32) = s.getReg .x18
  mem : ∀ a, ¬ Within a (s.getReg .x11) 24 → ¬ Within a (stackLo s powStack) powStack →
    t.getMem a = s.getMem a

/-- `Saved`, and `s2` holds `self`'s address. -/
structure FrameInv (s t : MachineState) : Prop extends Saved s t where
  base : t.getReg .x18 = s.getReg .x11

/-- At the loop head with `n` left: `out * base ^ n = self ^ exponent`. -/
structure LoopInv (s t : MachineState) (n : Word) : Prop extends FrameInv s t where
  pc : t.pc = 0x8000efe4
  x9 : t.getReg .x9 = n
  ne : n ≠ 0
  value : eAt t (s.getReg .x2 - 80) * eAt t (s.getReg .x11) ^ n.toNat =
    x0 s ^ (s.getReg .x12).toNat

/-- At the epilogue with `out` the power, or at a dead end. -/
def Done (s t : MachineState) : Prop :=
  (t.pc = 0x8000f01c ∧ Saved s t ∧ eAt t (s.getReg .x2 - 80) = x0 s ^ (s.getReg .x12).toNat) ∨
    Dead Image.code t

/-- `sp` and the operands as numbers. -/
structure Facts (s : MachineState) : Prop where
  sp : 32 + powStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
    (s.getReg .x2).toNat % 16 = 0 ∧
    (stackLo s powStack).toNat = (s.getReg .x2).toNat - powStack
  out : 32 ≤ (s.getReg .x10).toNat ∧ (s.getReg .x10).toNat % 8 = 0 ∧
    (s.getReg .x10).toNat + 8 * 3 ≤ 0xc0000008
  base : 32 ≤ (s.getReg .x11).toNat ∧ (s.getReg .x11).toNat % 8 = 0 ∧
    (s.getReg .x11).toNat + 8 * 3 ≤ 0xc0000008

theorem facts {s : MachineState} (h : PowPre s) : Facts s :=
  ⟨h.stack.bounds (by decide) (by decide), ValidMemRange.bounds h.out (by decide),
    ValidMemRange.bounds h.base (by decide)⟩

/-- An `E` whose three words are unchanged. -/
theorem eAt_of {s t : MachineState} {p : Word} (h : ∀ k ∈ [0, 8, 16], t.getMem (p + k) =
    s.getMem (p + k)) : eAt t p = eAt s p := by
  have h0 : t.getMem p = s.getMem p := by simpa using h 0 (by simp)
  unfold eAt
  rw [h0, h 8 (by simp), h 16 (by simp)]

/-! ## The calls -/

/-- `out *= base`: from `0x8000efec` to `0x8000efb4`. -/
theorem mulStep (hMul : EMulSpec) {s t : MachineState} (hpre : PowPre s) (ht : FrameInv s t)
    (hpc : t.pc = 0x8000efec) :
    ∃ w, Reaches Image.code t w ∧ ((w.pc = 0x8000efb4 ∧ FrameInv s w ∧
      w.getReg .x9 = t.getReg .x9 ∧
      eAt w (s.getReg .x2 - 80) = eAt t (s.getReg .x2 - 80) * eAt t (s.getReg .x11) ∧
      eAt w (s.getReg .x11) = eAt t (s.getReg .x11)) ∨ Dead Image.code w) := by
  have hf := facts hpre
  have hsp := hf.sp
  have hB := hf.base
  have hBs := hpre.baseStack
  have hBP := hpre.basePool
  have hP := hpre.pool.apart
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000efec_spec hpc trivial
  have k₁ := b8000efec_keeps h₁
  have hc2 : c.getReg .x2 = s.getReg .x2 - 80 := (k₁ .x2 (by decide)).trans ht.sp
  have hc10 : c.getReg .x10 = s.getReg .x2 - 80 + 24 := by rw [b8000efec_x10 h₁, ht.sp]
  have hc11 : c.getReg .x11 = s.getReg .x2 - 80 := by rw [b8000efec_x11 h₁, ht.sp]
  have hc12 : c.getReg .x12 = s.getReg .x11 := by rw [b8000efec_x12 h₁, ht.base]
  have hcm := b8000efec_mem_same h₁
  have hpre' : MulArgs c ∧ PoolOk c mulStack := ⟨{
    out := by rw [hc10]; valid_sub hpre.stack.valid [hsp]
    lhs := by rw [hc11]; valid_sub hpre.stack.valid [hsp]
    rhs := by rw [hc12]; exact hpre.base
    stack := ⟨by valid_sub hpre.stack.valid [hsp, hc2], by addr_omega [hsp, hc2]⟩
    outLhs := by addr_omega [hsp, hc10, hc11]
    outRhs := by addr_omega [hsp, hc10, hc12, hB, hBs]
    outStack := by addr_omega [hsp, hc10, hc2]
    lhsStack := by addr_omega [hsp, hc11, hc2]
    rhsStack := by addr_omega [hsp, hc12, hc2, hB, hBs] }, {
    word := by
      rw [hcm, ht.mem _ (by addr_omega [hBP, hB]) (by addr_omega [hP, hsp])]
      exact hpre.pool.word
    apart := by addr_omega [hP, hsp, hc2] }⟩
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ := hMul.call hr₁ (b8000efec_pc h₁) hpre'
  swap
  · exact ⟨v, hr₂, Or.inr hdead⟩
  have hv2 : v.getReg .x2 = s.getReg .x2 - 80 := (hpres.reg .x2).trans hc2
  have hprod := hpost.value
  rw [hc10, hc11, hc12] at hprod
  have hvold (a : Word) (h₁ : ¬ Within a (s.getReg .x2 - 80 + 24) 24)
      (h₂ : ¬ Within a (s.getReg .x2 - 1104) 1024) : v.getMem a = t.getMem a := by
    rw [hpost.frame a (by rw [hc10]; exact h₁) (by addr_omega [h₂, hc2, hsp]), hcm]
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f000_spec
    (by rw [hvpc, returnAddress_eq, b8000efec_x1 h₁]; decide +kernel) (by
      rv_eval [hv2]
      and_intros <;> valid_access hpre.stack.valid [hsp])
  have k₃ := b8000f000_keeps h₃
  have w₀ := b8000f000_m_x2_0 h₃
  have w₁ := b8000f000_m_x2_8 h₃
  have w₂ := b8000f000_m_x2_16 h₃
  have hm₃ := b8000f000_frame h₃ (by rw [hv2]; addr_omega [hsp])
  rw [hv2] at hm₃
  rv_eval [hv2] at w₀ w₁ w₂
  have hwold (a : Word) (h₀ : ¬ Within a (s.getReg .x2 - 80) 48)
      (h₂ : ¬ Within a (s.getReg .x2 - 1104) 1024) : w.getMem a = t.getMem a := by
    rw [hm₃ a (by addr_omega [h₀, hsp]), hvold a (by addr_omega [h₀, hsp]) h₂]
  refine ⟨w, hr₂.trans hr₃, Or.inl ⟨b8000f000_pc h₃, {
    sp := (k₃ .x2 (by decide)).trans hv2
    out := by rw [k₃ .x8 (by decide), hpres.reg .x8, k₁ .x8 (by decide), ht.out]
    base := by rw [k₃ .x18 (by decide), hpres.reg .x18, k₁ .x18 (by decide), ht.base]
    kept := fun r hr ↦ by
      rw [k₃ r (mem_of_kept hr _), hpres r (mem_of_kept hr _), k₁ r (mem_of_kept hr _),
        ht.kept r hr]
    ra := by rw [hwold _ (by addr_omega [hsp]) (by addr_omega [hsp]), ht.ra]
    s0 := by rw [hwold _ (by addr_omega [hsp]) (by addr_omega [hsp]), ht.s0]
    s1 := by rw [hwold _ (by addr_omega [hsp]) (by addr_omega [hsp]), ht.s1]
    s2 := by rw [hwold _ (by addr_omega [hsp]) (by addr_omega [hsp]), ht.s2]
    mem := fun a h₁ h₂ ↦ by
      rw [hwold a (by addr_omega [h₂, hsp]) (by addr_omega [h₂, hsp]), ht.mem a h₁ h₂] },
    by rw [k₃ .x9 (by decide), hpres.reg .x9, k₁ .x9 (by decide)], ?_, ?_⟩⟩
  · have : eAt w (s.getReg .x2 - 80) = eAt v (s.getReg .x2 - 80 + 24) := by
      unfold eAt; rv_eval [w₀, w₁, w₂]
    rw [this, hprod]
    congr 1
    · exact eAt_of fun k hk ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> rw [hcm]
    · exact eAt_of fun k hk ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> rw [hcm]
  · exact eAt_of fun k hk ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;>
        exact hwold _ (by addr_omega [hsp, hB, hBs]) (by addr_omega [hsp, hB, hBs])

/-- `base = base.square(); n >>= 1`: from `0x8000efb4` to the loop head or the epilogue. -/
theorem squareStep (hSq : ESquareSpec) {s t : MachineState} (hpre : PowPre s) (ht : FrameInv s t)
    (hpc : t.pc = 0x8000efb4) :
    ∃ w, Reaches Image.code t w ∧ ((FrameInv s w ∧ w.getReg .x9 = t.getReg .x9 >>> 1 ∧
      (w.pc = if t.getReg .x9 >>> 1 = 0 then 0x8000f01c else 0x8000efe4) ∧
      eAt w (s.getReg .x2 - 80) = eAt t (s.getReg .x2 - 80) ∧
      eAt w (s.getReg .x11) = eAt t (s.getReg .x11) * eAt t (s.getReg .x11)) ∨
        Dead Image.code w) := by
  have hf := facts hpre
  have hsp := hf.sp
  have hB := hf.base
  have hBs := hpre.baseStack
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000efb4_spec hpc trivial
  have k₁ := b8000efb4_keeps h₁
  have hc10 : c.getReg .x10 = s.getReg .x2 - 80 + 24 := by rw [b8000efb4_x10 h₁, ht.sp]
  have hc11 : c.getReg .x11 = s.getReg .x11 := by rw [b8000efb4_x11 h₁, ht.base]
  have hcm := b8000efb4_mem_same h₁
  have hpre' : ESquarePre c := {
    out := by rw [hc10]; valid_sub hpre.stack.valid [hsp]
    arg := by rw [hc11]; exact hpre.base }
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ := hSq.call hr₁ (b8000efb4_pc h₁) hpre'
  swap
  · exact ⟨v, hr₂, Or.inr hdead⟩
  have hv2 : v.getReg .x2 = s.getReg .x2 - 80 := by
    rw [hpres.reg .x2, k₁ .x2 (by decide), ht.sp]
  have hv18 : v.getReg .x18 = s.getReg .x11 := by
    rw [hpres.reg .x18, k₁ .x18 (by decide), ht.base]
  have hsq := hpost.value
  rw [hc10, hc11] at hsq
  have hvold (a : Word) (h₁ : ¬ Within a (s.getReg .x2 - 80 + 24) 24) :
      v.getMem a = t.getMem a := by
    rw [hpost.frame a (by rw [hc10]; exact h₁), hcm]
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000efc4_spec
    (by rw [hvpc, returnAddress_eq, b8000efb4_x1 h₁]; decide +kernel) (by
      rv_eval [hv2, hv18]
      and_intros <;> first
        | valid_access hpre.stack.valid [hsp]
        | valid_access hpre.base [hB])
  have k₃ := b8000efc4_keeps h₃
  have w₀ := b8000efc4_m_x18_0 h₃
  have w₁ := b8000efc4_m_x18_8 h₃
  have w₂ := b8000efc4_m_x18_16 h₃
  have hm₃ := b8000efc4_frame h₃ (by rw [hv18]; addr_omega [hB])
  rv_eval [hv18, hv2] at w₀ w₁ w₂
  rw [hv18] at hm₃
  have hwold (a : Word) (h₀ : ¬ Within a (s.getReg .x11) 24)
      (h₁ : ¬ Within a (s.getReg .x2 - 80 + 24) 24) : w.getMem a = t.getMem a := by
    rw [hm₃ a h₀, hvold a h₁]
  have hx9 : w.getReg .x9 = t.getReg .x9 >>> 1 := by
    rw [b8000efc4_x9 h₃, hpres.reg .x9, k₁ .x9 (by decide)]
  refine ⟨w, hr₂.trans hr₃, Or.inl ⟨{
    sp := (k₃ .x2 (by decide)).trans hv2
    out := by rw [k₃ .x8 (by decide), hpres.reg .x8, k₁ .x8 (by decide), ht.out]
    base := (k₃ .x18 (by decide)).trans hv18
    kept := fun r hr ↦ by
      rw [k₃ r (mem_of_kept hr _), hpres r (mem_of_kept hr _), k₁ r (mem_of_kept hr _),
        ht.kept r hr]
    ra := by rw [hwold _ (by addr_omega [hsp, hB, hBs]) (by addr_omega [hsp]), ht.ra]
    s0 := by rw [hwold _ (by addr_omega [hsp, hB, hBs]) (by addr_omega [hsp]), ht.s0]
    s1 := by rw [hwold _ (by addr_omega [hsp, hB, hBs]) (by addr_omega [hsp]), ht.s1]
    s2 := by rw [hwold _ (by addr_omega [hsp, hB, hBs]) (by addr_omega [hsp]), ht.s2]
    mem := fun a h₁ h₂ ↦ by
      rw [hwold a h₁ (by addr_omega [h₂, hsp]), ht.mem a h₁ h₂] }, hx9, ?_, ?_, ?_⟩⟩
  · rw [← k₁ .x9 (by decide), ← hpres.reg .x9]
    split
    · exact b8000efc4_pc_taken h₃ (by assumption)
    · exact b8000efc4_pc_not_taken h₃ (by assumption)
  · exact eAt_of fun k hk ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;>
        exact hwold _ (by addr_omega [hsp, hB, hBs]) (by addr_omega [hsp])
  · have : eAt w (s.getReg .x11) = eAt v (s.getReg .x2 - 80 + 24) := by
      unfold eAt; rv_eval [w₀, w₁, w₂]
    rw [this, hsq]
    congr 1 <;> exact eAt_of fun k hk ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> rw [hcm]

/-! ## The loop -/

theorem pow_step (a b : E) (n : Word) :
    a * (if n &&& 1 = 0 then 1 else b) * (b * b) ^ (n >>> 1).toNat = a * b ^ n.toNat := by
  have hdiv : (n >>> 1).toNat = n.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hbit : (n &&& 1).toNat = n.toNat % 2 := by
    rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]
  have hb : (if n &&& 1 = 0 then 1 else b) = b ^ (n.toNat % 2) := by
    split
    · rename_i h; rw [show n.toNat % 2 = 0 by rw [← hbit, h]; rfl, pow_zero]
    · rename_i h
      rw [show n.toNat % 2 = 1 by
        have : (n &&& 1).toNat ≠ 0 := fun h0 ↦ h (BitVec.eq_of_toNat_eq h0)
        omega, pow_one]
  rw [hb, hdiv, ← sq, ← pow_mul, mul_assoc, ← pow_add,
    show n.toNat % 2 + 2 * (n.toNat / 2) = n.toNat by omega]

def measure (t : MachineState) : Nat := (t.getReg .x9).toNat

theorem body (hMul : EMulSpec) (hSq : ESquareSpec) {s : MachineState} (hpre : PowPre s)
    (t : MachineState) (hinv : ∃ n, LoopInv s t n) :
    (∃ u, Reaches Image.code t u ∧ Done s u) ∨
      (∃ u, Reaches Image.code t u ∧ (∃ n, LoopInv s u n) ∧ measure u < measure t) := by
  obtain ⟨n, ht⟩ := hinv
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000efe4_spec ht.pc trivial
  have k₁ := b8000efe4_keeps h₁
  have hm₁ := b8000efe4_mem_same h₁
  have hf₁ : FrameInv s u := {
    sp := (k₁ .x2 (by decide)).trans ht.sp
    out := (k₁ .x8 (by decide)).trans ht.out
    base := (k₁ .x18 (by decide)).trans ht.base
    kept := fun r hr ↦ (k₁ r (mem_of_kept hr _)).trans (ht.kept r hr)
    ra := (hm₁ _).trans ht.ra
    s0 := (hm₁ _).trans ht.s0
    s1 := (hm₁ _).trans ht.s1
    s2 := (hm₁ _).trans ht.s2
    mem := fun a h₁ h₂ ↦ (hm₁ a).trans (ht.mem a h₁ h₂) }
  have hu9 : u.getReg .x9 = n := (k₁ .x9 (by decide)).trans ht.x9
  have hu_e (p : Word) : eAt u p = eAt t p := by unfold eAt; simp only [hm₁]
  -- `out *= base` on a set bit, then the square
  obtain ⟨w, hr₂, hw⟩ : ∃ w, Reaches Image.code u w ∧ ((w.pc = 0x8000efb4 ∧ FrameInv s w ∧
      w.getReg .x9 = n ∧
      eAt w (s.getReg .x2 - 80) = eAt t (s.getReg .x2 - 80) *
        (if n &&& 1 = 0 then 1 else eAt t (s.getReg .x11)) ∧
      eAt w (s.getReg .x11) = eAt t (s.getReg .x11)) ∨ Dead Image.code w) := by
    by_cases hbit : n &&& 1 = 0
    · refine ⟨u, Reaches.refl _, Or.inl ⟨b8000efe4_pc_taken h₁ (by rw [ht.x9]; exact hbit), hf₁,
        hu9, ?_, hu_e _⟩⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hbit), mul_one, hu_e]
    · obtain ⟨w, hr, hw | hd⟩ := mulStep hMul hpre hf₁
        (b8000efe4_pc_not_taken h₁ (by rw [ht.x9]; exact hbit))
      · refine ⟨w, hr, Or.inl ⟨hw.1, hw.2.1, hw.2.2.1.trans hu9, ?_, ?_⟩⟩
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hbit), hw.2.2.2.1, hu_e, hu_e]
        · rw [hw.2.2.2.2, hu_e]
      · exact ⟨w, hr, Or.inr hd⟩
  rcases hw with ⟨hwpc, hfw, hw9, hwout, hwbase⟩ | hd
  swap
  · exact Or.inl ⟨w, hr₁.trans hr₂, Or.inr hd⟩
  obtain ⟨z, hr₃, ⟨hfz, hz9, hzpc, hzout, hzbase⟩ | hd⟩ := squareStep hSq hpre hfw hwpc
  swap
  · exact Or.inl ⟨z, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  rw [hw9] at hz9 hzpc
  have hval : eAt z (s.getReg .x2 - 80) * eAt z (s.getReg .x11) ^ (n >>> 1).toNat =
      x0 s ^ (s.getReg .x12).toNat := by
    rw [hzout, hzbase, hwout, hwbase, pow_step, ht.value]
  by_cases hz : n >>> 1 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hz)] at hzpc
    refine Or.inl ⟨z, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨hzpc, hfz.toSaved, ?_⟩⟩
    rw [← hval, hz]
    simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hz)] at hzpc
    refine Or.inr ⟨z, hr₁.trans (hr₂.trans hr₃), ⟨n >>> 1, { hfz with
      pc := hzpc, x9 := hz9, ne := hz, value := hval }⟩, ?_⟩
    simp only [measure, hz9, ht.x9]
    have : n.toNat ≠ 0 := fun h ↦ ht.ne (BitVec.eq_of_toNat_eq (by simpa using h))
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega

/-! ## Entry and exit -/

theorem setup {s : MachineState} (hpc : s.pc = 0x8000ef7c) (hpre : PowPre s) :
    ∃ t, Reaches Image.code s t ∧
      ((t.pc = 0x8000f01c ∧ Saved s t ∧
        eAt t (s.getReg .x2 - 80) = x0 s ^ (s.getReg .x12).toNat) ∨ ∃ n, LoopInv s t n) := by
  have hf := facts hpre
  have hsp := hf.sp
  have hB := hf.base
  have hBs := hpre.baseStack
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000ef7c_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsp])
  have k₀ := b8000ef7c_keeps h₀
  have m₀ := b8000ef7c_m_x2_n80 h₀
  have m₁ := b8000ef7c_m_x2_n72 h₀
  have m₂ := b8000ef7c_m_x2_n64 h₀
  have hm₀ := b8000ef7c_frame h₀ (by addr_omega [hsp])
  have hold (a : Word) (h : ¬ Within a (s.getReg .x2 - 80) 80) : t₀.getMem a = s.getMem a :=
    hm₀ a h
  have hf₀ : Saved s t₀ := {
    sp := b8000ef7c_x2 h₀
    out := b8000ef7c_x8 h₀
    kept := fun r hr ↦ k₀ r (mem_of_kept hr _)
    ra := b8000ef7c_m_x2_n8 h₀
    s0 := b8000ef7c_m_x2_n16 h₀
    s1 := b8000ef7c_m_x2_n24 h₀
    s2 := b8000ef7c_m_x2_n32 h₀
    mem := fun a _ h₂ ↦ hold a (by addr_omega [h₂, hsp]) }
  have hone : eAt t₀ (s.getReg .x2 - 80) = 1 := by
    apply eAt_eq_of_limbs
    rw [limbs_one]
    rv_eval [m₀, m₁, m₂]
  have hbase : eAt t₀ (s.getReg .x11) = x0 s :=
    eAt_of fun k hk ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hold _ (by addr_omega [hsp, hB, hBs])
  by_cases he : s.getReg .x12 = 0
  · refine ⟨t₀, hr₀, Or.inl ⟨b8000ef7c_pc_taken h₀ he, hf₀, ?_⟩⟩
    rw [hone, he]
    simp
  · obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000efa8_spec
      (b8000ef7c_pc_not_taken h₀ he) trivial
    have k₁ := b8000efa8_keeps h₁
    have hm₁ := b8000efa8_mem_same h₁
    have he₁ (p : Word) : eAt t₁ p = eAt t₀ p := by unfold eAt; simp only [hm₁]
    refine ⟨t₁, hr₀.trans hr₁, Or.inr ⟨s.getReg .x12, {
      sp := (k₁ .x2 (by decide)).trans hf₀.sp
      out := (k₁ .x8 (by decide)).trans hf₀.out
      base := by rw [b8000efa8_x18 h₁, k₀ .x11 (by decide)]
      kept := fun r hr ↦ (k₁ r (mem_of_kept hr _)).trans (hf₀.kept r hr)
      ra := (hm₁ _).trans hf₀.ra
      s0 := (hm₁ _).trans hf₀.s0
      s1 := (hm₁ _).trans hf₀.s1
      s2 := (hm₁ _).trans hf₀.s2
      mem := fun a h₁ h₂ ↦ (hm₁ a).trans (hf₀.mem a h₁ h₂)
      pc := b8000efa8_pc h₁
      x9 := by rw [b8000efa8_x9 h₁, k₀ .x12 (by decide)]
      ne := he
      value := by rw [he₁, he₁, hone, hbase, one_mul] }⟩⟩

theorem exit {s t : MachineState} (hpre : PowPre s) (hpc : t.pc = 0x8000f01c) (ht : Saved s t)
    (hval : eAt t (s.getReg .x2 - 80) = x0 s ^ (s.getReg .x12).toNat) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧ PowPost s u := by
  have hf := facts hpre
  have hsp := hf.sp
  have hO := hf.out
  have hOs := hpre.outStack
  have hOB := hpre.outBase
  have hB := hf.base
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b8000f01c_spec hpc (by
    rv_eval [ht.sp, ht.out]
    and_intros <;> first
      | addr_omega [hsp, hO, hOs]
      | valid_access hpre.stack.valid [hsp]
      | valid_access hpre.out [hO])
  have k := b8000f01c_keeps h
  have pc := b8000f01c_pc h
  have x2 := b8000f01c_x2 h
  have x8 := b8000f01c_x8 h
  have x9 := b8000f01c_x9 h
  have x18 := b8000f01c_x18 h
  have m₀ := b8000f01c_m_x8_0 h
  have m₁ := b8000f01c_m_x8_8 h
  have m₂ := b8000f01c_m_x8_16 h
  have hm := b8000f01c_frame h (by rw [ht.out]; addr_omega [hO])
  rv_eval [ht.sp, ht.out, ht.ra, ht.s0, ht.s1, ht.s2] at pc x2 x8 x9 x18 m₀ m₁ m₂ hm
  have hrest : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
      u.getReg r = s.getReg r := by
    intro r hr
    have h1 : r ∈ kept := by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
    rw [k r (mem_of_kept h1 _), ht.kept r h1]
  refine ⟨u, hr, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 (by rw [k .x19 (by decide), ht.kept .x19 (by decide)]) hrest,
    ⟨?_, fun a h₁ h₂ h₃ ↦ ?_⟩⟩
  · show eAt u (s.getReg .x10) = x0 s ^ (s.getReg .x12).toNat
    rw [← hval]
    unfold eAt
    rv_eval [m₀, m₁, m₂]
  · rw [hm a h₁, ht.mem a h₂ h₃]

/-- **`E::pow` raises to the power**, given `mul`'s and `E::square`'s contracts. -/
theorem pow_spec (hMul : EMulSpec) (hSq : ESquareSpec) : PowSpec := by
  intro s hpc hpre
  obtain ⟨t, hst, ht⟩ := setup hpc hpre
  obtain ⟨u, hsu, hu⟩ : ∃ u, Reaches Image.code s u ∧ Done s u := by
    rcases ht with ht | ht
    · exact ⟨t, hst, Or.inl ht⟩
    · obtain ⟨u, htu, hu⟩ := Reaches.loop (fun t ↦ ∃ n, LoopInv s t n) measure (Done s)
        (body hMul hSq hpre) t ht
      exact ⟨u, hst.trans htu, hu⟩
  rcases hu with ⟨hpc', hfu, hval⟩ | hdead
  · obtain ⟨v, huv, hvpc, hpres, hpost⟩ := exit hpre hpc' hfu hval
    exact ⟨v, hsu.trans huv, Or.inl ⟨hvpc, hpres, hpost⟩⟩
  · exact ⟨u, hsu, Or.inr hdead⟩

end Rv64Verifier.Proofs.Field.Pow
