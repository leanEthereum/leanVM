module

public import NativeVm.Field.E

/-!
# Powers in `E`

`esqn`: `A := A^(2^rdx)`, `rdx` squarings (the Frobenius `x ↦ x^(2^k)`, `frobenius_8`'s
squarings); `epow`: `A := A^r13`, by squaring and multiplying over `r13`'s bits from the lowest,
the product so far in `(rsi, rbp)` and the squared base in `B`.
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters

/-- `A := A^(2^rdx)`: `rdx` squarings, counting `rdx` down to zero. -/
def esqn : Stmt := .loop (.test false .rdx (.reg .rdx)) (blk [esq, I (.subi .rdx 1)])

/-- **`esqn` raises to `2^rdx`.** It writes `eRegs`. -/
theorem esqn_spec (s : QState) {E : QState → Prop} :
    WP esqn s (fun s' ↦
      eOf (s'.reg .r9) (s'.reg .r10) = eOf (s.reg .r9) (s.reg .r10) ^ 2 ^ (s.reg .rdx).toNat ∧
      s'.reg .rdx = 0 ∧ s'.mem = s.mem ∧ RegsFrame eRegs s s') E := by
  unfold esqn
  apply WP.loop (fun t ↦ eOf (t.reg .r9) (t.reg .r10) ^ 2 ^ (t.reg .rdx).toNat =
      eOf (s.reg .r9) (s.reg .r10) ^ 2 ^ (s.reg .rdx).toNat ∧ t.mem = s.mem ∧ RegsFrame eRegs s t)
    (fun t ↦ (t.reg .rdx).toNat)
  · exact ⟨rfl, rfl, RegsFrame.refl _ _⟩
  · intro t ⟨hI, hm, hf⟩ hc
    have hne : t.reg .rdx ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hpos : (t.reg .rdx).toNat ≠ 0 := fun h0 ↦ hne (UInt64.toNat_inj.mp (by simpa using h0))
    refine WP.then (esq_spec _) fun t₁ ⟨h1, h2, h3⟩ ↦ ?_
    have hd : t₁.reg .rdx = t.reg .rdx := h3 .rdx (by simp)
    fstep
    fdone
    refine ⟨⟨?_, h2.trans hm, ?_⟩, ?_⟩
    · rw [hd, toNat_sub_one hne, h1, ← pow_mul, ← pow_succ', Nat.sub_add_cancel (by omega), hI]
    · exact RegsFrame.setReg (RegsFrame.trans hf (RegsFrame.mono h3 (by simp))) (by simp) _
    · rw [hd, toNat_sub_one hne]
      omega
  · intro t ⟨hI, hm, hf⟩ hc
    have h0 : t.reg .rdx = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    refine ⟨?_, h0, hm, hf⟩
    rw [← hI, h0]
    simp

/-- `A := A^r13`: the product so far in `(rsi, rbp)`, the base squared at each bit in `B`. -/
def epow : Stmt := blk [
  I (.mov .r11 .r9), I (.mov .r12 .r10), I (.movi .rsi 1), I (.movi .rbp 0),
  .loop (.test false .r13 (.reg .r13)) (blk [
    .ite (.test false .r13 (.imm 1))
      (blk [I (.mov .r9 .rsi), I (.mov .r10 .rbp), emul, I (.mov .rsi .r9), I (.mov .rbp .r10)])
      .skip,
    I (.mov .r9 .r11), I (.mov .r10 .r12), esq, I (.mov .r11 .r9), I (.mov .r12 .r10),
    I (.shri .r13 1)]),
  I (.mov .r9 .rsi), I (.mov .r10 .rbp)]

/-- The registers `epow` writes. -/
abbrev epowRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13]

theorem toNat_and_one (n : UInt64) : (n &&& 1).toNat = n.toNat % 2 := by
  rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]

theorem toNat_bit (n : UInt64) :
    n.toNat = 2 * (n >>> 1).toNat + (n &&& 1).toNat := by
  rw [UInt64.toNat_shiftRight, toNat_and_one]
  simp only [Nat.shiftRight_eq_div_pow]
  change n.toNat = 2 * (n.toNat / 2) + n.toNat % 2
  omega

/-- **`epow` raises to `r13`.** -/
theorem epow_spec (s : QState) {E : QState → Prop} :
    WP epow s (fun s' ↦
      eOf (s'.reg .r9) (s'.reg .r10) = eOf (s.reg .r9) (s.reg .r10) ^ (s.reg .r13).toNat ∧
      s'.mem = s.mem ∧ RegsFrame epowRegs s s') E := by
  unfold epow
  fstep; fstep; fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ eOf (t.reg .rsi) (t.reg .rbp) * eOf (t.reg .r11) (t.reg .r12) ^
      (t.reg .r13).toNat = eOf (s.reg .r9) (s.reg .r10) ^ (s.reg .r13).toNat ∧ t.mem = s.mem ∧
      RegsFrame epowRegs s t)
    (fun t ↦ (t.reg .r13).toNat)
  · refine ⟨?_, rfl, by rf_tac⟩
    rsimp
    rw [eOf_one, one_mul]
  · intro t ⟨hI, hm, hf⟩ hc
    have hne : t.reg .r13 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    -- After the conditional product: `(rsi, rbp)` times `B ^ bit`, `B` and `r13` kept.
    have hbit : WP (.ite (.test false .r13 (.imm 1))
        (blk [I (.mov .r9 .rsi), I (.mov .r10 .rbp), emul, I (.mov .rsi .r9), I (.mov .rbp .r10)])
        .skip) t (fun t₁ ↦ eOf (t₁.reg .rsi) (t₁.reg .rbp) = eOf (t.reg .rsi) (t.reg .rbp) *
          eOf (t.reg .r11) (t.reg .r12) ^ (t.reg .r13 &&& 1).toNat ∧
          t₁.reg .r11 = t.reg .r11 ∧ t₁.reg .r12 = t.reg .r12 ∧ t₁.reg .r13 = t.reg .r13 ∧
          t₁.mem = t.mem ∧ RegsFrame epowRegs t t₁) E := by
      apply WP.ite
      by_cases hb : t.reg .r13 &&& 1 = 0
      · have : (Cond.test false .r13 (.imm 1)).eval t = false := by
          simp [Cond.eval, Rhs.eval, int64One_toUInt64, hb]
        rw [this]
        refine WP.skip ⟨?_, rfl, rfl, rfl, rfl, RegsFrame.refl _ _⟩
        rw [hb]
        simp
      · have h1 : t.reg .r13 &&& 1 = 1 := by
          apply UInt64.toNat_inj.mp
          have : (t.reg .r13 &&& 1).toNat ≠ 0 := fun h0 ↦
            hb (UInt64.toNat_inj.mp (by simpa using h0))
          rw [toNat_and_one] at this ⊢
          simp only [UInt64.toNat_one]
          omega
        have : (Cond.test false .r13 (.imm 1)).eval t = true := by
          simp [Cond.eval, Rhs.eval, int64One_toUInt64, h1]
        rw [this]
        fstep; fstep
        refine WP.then (emul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
        rsimp at e1
        fstep; fstep; fdone
        have k : ∀ r ∉ eRegs, t₁.reg r = t.reg r := fun r hr ↦ by
          rw [e3 r hr]
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
        refine ⟨?_, k .r11 (by decide), k .r12 (by decide), k .r13 (by decide), e2, ?_⟩
        · rw [e1, h1]
          simp
        · intro r hr
          simp only [epowRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          have hk : r ∉ eRegs := by simp [eRegs, *]
          simp only [QState.setReg_reg, hr.2.2.2.2.1, hr.2.2.2.2.2.1, ↓reduceIte]
          exact k r hk
    apply WP.blk_cons
    refine WP.mono hbit (fun t₁ ⟨b1, b11, b12, b13, bm, bf⟩ ↦ ?_) (fun _ h ↦ h)
    fstep; fstep
    refine WP.then (esq_spec _) fun t₂ ⟨q1, q2, q3⟩ ↦ ?_
    rsimp at q1
    have k : ∀ r ∉ sqRegs, t₂.reg r = t₁.reg r := fun r hr ↦ by
      rw [q3 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.2.2.2.2.1, hr.2.2.2.2.2]
    fstep; fstep; fstep; fdone
    refine ⟨⟨?_, q2.trans (bm.trans hm), ?_⟩, ?_⟩
    · rw [q1, k .rsi (by decide), k .rbp (by decide), k .r13 (by decide), b1, b11, b12, b13,
        ← hI, ← pow_mul, mul_assoc, ← pow_add, toNat_bit (t.reg .r13)]
      congr 2
      ring
    · intro r hr
      simp only [epowRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      have hk : r ∉ sqRegs := by simp [sqRegs, *]
      simp only [QState.setReg_reg, hr.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2, ↓reduceIte]
      rw [k r hk, bf r (by simp [epowRegs, *]), hf r (by simp [epowRegs, *])]
    · rw [k .r13 (by decide), b13, toNat_bit (t.reg .r13)]
      have : (t.reg .r13).toNat ≠ 0 := fun h0 ↦ hne (UInt64.toNat_inj.mp (by simpa using h0))
      have := toNat_bit (t.reg .r13)
      omega
  · intro t ⟨hI, hm, hf⟩ hc
    have h0 : t.reg .r13 = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    fstep; fstep; fdone
    refine ⟨?_, hm, ?_⟩
    · rw [← hI, h0]
      simp
    · exact RegsFrame.setReg (RegsFrame.setReg hf (by simp) _) (by simp) _

end NativeVm.Field
