module

public import NativeVm.Field.KInv

/-!
# `E` on the machine

An `E` element in registers is two words, limb `0` then limb `1` (`eOf`). The kernels work on
`A = (r9, r10)` and `B = (r11, r12)` and leave their result in `A`:

* `eadd`: `A := A + B`;
* `emul`: `A := A · B`, by three products in `K` (Karatsuba), `y² = x·y + 1` folding the product
  of the `y` limbs into both; `B` is kept;
* `esq`: `A := A²`, two squarings in `K`: `(c₀ + c₁y)² = c₀² + c₁² + x·c₁²·y`;
* `escale`: `A := A · ofK b`, `b` the lane in `r11`;
* `esqn`: `A := A^(2^rdx)`, `rdx` squarings (the Frobenius `x ↦ x^(2^k)`);
* `epow`: `A := A^r13`, by squaring and multiplying, `r13`'s bits from the lowest.
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters

/-! ## Sum and product -/

/-- `A := A + B`. -/
def eadd : Stmt := blk [I (.xor .r9 .r11), I (.xor .r10 .r12)]

theorem eadd_spec (s : QState) {E : QState → Prop} :
    WP eadd s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
      eOf (s.reg .r9) (s.reg .r10) + eOf (s.reg .r11) (s.reg .r12) ∧
      s'.mem = s.mem ∧ RegsFrame [.r9, .r10] s s') E := by
  unfold eadd
  fstep; fstep; fdone
  exact ⟨eOf_add _ _ _ _, trivial, by rf_tac⟩

/-- The registers `emul` writes. -/
abbrev eRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10]

/-- `A := A · B`: `p₀ = a₀b₀` in `rdx`, `p₁ = a₁b₁` in `r10`, `p₂ = (a₀ + a₁)(b₀ + b₁)` in
`rax`; then `c₀ = p₀ + p₁` and `c₁ = p₂ + p₀ + p₁ + x·p₁`. -/
def emul : Stmt := blk [
  I (.mov .rax .r9), I (.mov .rbx .r11), kmul, I (.mov .rdx .rax),
  I (.mov .rax .r10), I (.mov .rbx .r12), kmul,
  I (.xor .r9 .r10), I (.mov .r10 .rax),
  I (.mov .rax .r9), I (.mov .rbx .r11), I (.xor .rbx .r12), kmul,
  I (.mov .r9 .rdx), I (.xor .r9 .r10), I (.xor .rax .r9),
  I (.mov .r8 .r10), I (.sari .r8 63), I (.andi .r8 0x1B), I (.shli .r10 1), I (.xor .r10 .r8),
  I (.xor .r10 .rax)]

/-- The product in `E` from the three products in `K`. -/
theorem eOf_mul_karatsuba {a0 a1 b0 b1 p0 p1 p2 : K} (h0 : p0 = a0 * b0) (h1 : p1 = a1 * b1)
    (h2 : p2 = (a0 + a1) * (b0 + b1)) :
    E.ofLimbs (p0 + p1) (g * p1 + (p2 + (p0 + p1))) = E.ofLimbs a0 a1 * E.ofLimbs b0 b1 := by
  rw [mul_limbs]
  congr 1
  · rw [h0, h1]
  · rw [h0, h1, h2]
    linear_combination (a0 * b0 + a1 * b1) * (CharTwo.two_eq_zero : (2 : K) = 0)

/-- **`emul` multiplies in `E`.** -/
theorem emul_spec (s : QState) {E : QState → Prop} :
    WP emul s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
      eOf (s.reg .r9) (s.reg .r10) * eOf (s.reg .r11) (s.reg .r12) ∧
      s'.mem = s.mem ∧ RegsFrame eRegs s s') E := by
  unfold emul
  fstep; fstep
  refine WP.then (kmul_spec _) fun t1 ⟨h1, m1, f1⟩ ↦ ?_
  rsimp at h1
  have g1 : ∀ r ∉ kRegs, t1.reg r = s.reg r := fun r hr ↦ by
    rw [f1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1]
  fstep; fstep; fstep
  refine WP.then (kmul_spec _) fun t2 ⟨h2, m2, f2⟩ ↦ ?_
  rsimp at h2
  rw [g1 .r10 (by decide), g1 .r12 (by decide)] at h2
  have g2 : ∀ r ∉ kRegs, r ≠ .rdx → t2.reg r = s.reg r := fun r hr hd ↦ by
    rw [f2 r hr, ← g1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hd]
  have d2 : t2.reg .rdx = t1.reg .rax := by rw [f2 .rdx (by decide)]; rsimp
  fstep; fstep; fstep; fstep; fstep
  refine WP.then (kmul_spec _) fun t3 ⟨h3, m3, f3⟩ ↦ ?_
  rsimp at h3
  rw [g2 .r9 (by decide) (by decide), g2 .r10 (by decide) (by decide),
    g2 .r11 (by decide) (by decide), g2 .r12 (by decide) (by decide)] at h3
  have e10 : t3.reg .r10 = t2.reg .rax := by rw [f3 .r10 (by decide)]; rsimp
  have ed : t3.reg .rdx = t1.reg .rax := by rw [f3 .rdx (by decide)]; rsimp; exact d2
  fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep
  fdone
  refine ⟨?_, m3.trans (m2.trans m1), ?_⟩
  · rw [mulXW_unfold]
    simp only [eOf, ofLane_xor, ofLane_mulXW, ed, e10, h1, h2, h3]
    exact eOf_mul_karatsuba rfl rfl rfl
  · intro r hr
    simp only [eRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ha, hb, hc, hd, h8, h9, h10⟩ := hr
    have hk : r ∉ kRegs := by simp [kRegs, *]
    simp only [QState.setReg_reg, ha, hb, hd, h8, h9, h10, ↓reduceIte, f3 r hk, f2 r hk,
      f1 r hk]

/-! ## Squares and scaling -/

/-- `A := A²`: `c₁²` in `r10`, then `c₀ = a₀² + a₁²` and `c₁ = x·a₁²`. -/
def esq : Stmt := blk [
  I (.mov .rax .r10), ksq, I (.mov .r10 .rax),
  I (.mov .rax .r9), ksq, I (.xor .rax .r10), I (.mov .r9 .rax),
  I (.mov .r8 .r10), I (.sari .r8 63), I (.andi .r8 0x1B), I (.shli .r10 1), I (.xor .r10 .r8)]

/-- The registers `esq` and `escale` write. -/
abbrev sqRegs : List Reg64 := [.rax, .rbx, .rcx, .r8, .r9, .r10]

theorem eOf_sq_limbs {a0 a1 q0 q1 : K} (h0 : q0 = a0 ^ 2) (h1 : q1 = a1 ^ 2) :
    E.ofLimbs (q0 + q1) (g * q1) = E.ofLimbs a0 a1 ^ 2 := by
  rw [sq, mul_limbs]
  congr 1
  · rw [h0, h1, sq, sq]
  · rw [h1, mul_comm a1 a0, CharTwo.add_self_eq_zero, zero_add, sq]

/-- **`esq` squares in `E`.** -/
theorem esq_spec (s : QState) {E : QState → Prop} :
    WP esq s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = eOf (s.reg .r9) (s.reg .r10) ^ 2 ∧
      s'.mem = s.mem ∧ RegsFrame sqRegs s s') E := by
  unfold esq
  fstep
  refine WP.then (ksq_spec _) fun t1 ⟨h1, m1, f1⟩ ↦ ?_
  rsimp at h1
  have g1 : ∀ r ∉ kRegs, t1.reg r = s.reg r := fun r hr ↦ by
    rw [f1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1]
  fstep; fstep
  refine WP.then (ksq_spec _) fun t2 ⟨h2, m2, f2⟩ ↦ ?_
  rsimp at h2
  rw [g1 .r9 (by decide)] at h2
  have e10 : t2.reg .r10 = t1.reg .rax := by rw [f2 .r10 (by decide)]; rsimp
  fstep; fstep; fstep; fstep; fstep; fstep; fstep
  fdone
  refine ⟨?_, m2.trans m1, ?_⟩
  · rw [mulXW_unfold, eOf, eOf, ofLane_xor, ofLane_mulXW, e10, h1, h2]
    exact eOf_sq_limbs rfl rfl
  · intro r hr
    simp only [sqRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ha, hb, hc, h8, h9, h10⟩ := hr
    have hk : r ∉ kRegs := by simp [kRegs, *]
    simp only [QState.setReg_reg, ha, h8, h9, h10, ↓reduceIte, f2 r hk, f1 r hk]

/-- `A := A · ofK b`, `b` the lane in `r11`: each limb times `b` in `K`. -/
def escale : Stmt := blk [
  I (.mov .rax .r9), I (.mov .rbx .r11), kmul, I (.mov .r9 .rax),
  I (.mov .rax .r10), I (.mov .rbx .r11), kmul, I (.mov .r10 .rax)]

/-- **`escale` multiplies by an element of `K`.** -/
theorem escale_spec (s : QState) {E : QState → Prop} :
    WP escale s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
      eOf (s.reg .r9) (s.reg .r10) * ofK (K.ofLane (s.reg .r11)) ∧
      s'.mem = s.mem ∧ RegsFrame sqRegs s s') E := by
  unfold escale
  fstep; fstep
  refine WP.then (kmul_spec _) fun t1 ⟨h1, m1, f1⟩ ↦ ?_
  rsimp at h1
  have g1 : ∀ r ∉ kRegs, t1.reg r = s.reg r := fun r hr ↦ by
    rw [f1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1]
  fstep; fstep; fstep
  refine WP.then (kmul_spec _) fun t2 ⟨h2, m2, f2⟩ ↦ ?_
  rsimp at h2
  rw [g1 .r10 (by decide), g1 .r11 (by decide)] at h2
  have e9 : t2.reg .r9 = t1.reg .rax := by rw [f2 .r9 (by decide)]; rsimp
  fstep
  fdone
  refine ⟨?_, m2.trans m1, ?_⟩
  · rw [eOf, eOf, e9, h1, h2, ofK_eq_ofLimbs, mul_limbs]
    congr 1 <;> ring
  · intro r hr
    simp only [sqRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ha, hb, hc, h8, h9, h10⟩ := hr
    have hk : r ∉ kRegs := by simp [kRegs, *]
    simp only [QState.setReg_reg, ha, hb, h9, h10, ↓reduceIte, f2 r hk, f1 r hk]

end NativeVm.Field
