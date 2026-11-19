module

public import NativeVm.Field.Fold

/-!
# Powers

`epowers`: writes `powers b n = [1, b, b², …]` (`n` terms) at `r14`, `b` in `B`, `n` in `r15`;
the power so far in `A`.
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters LeanVM.Protocol.Verifier

theorem powersFrom_length (acc base : E) : ∀ n, (powersFrom acc base n).length = n
  | 0 => rfl
  | n + 1 => by rw [powersFrom, List.length_cons, powersFrom_length _ _ n]

theorem powersFrom_getD (acc base : E) : ∀ n k, k < n →
    (powersFrom acc base n).getD k 0 = acc * base ^ k
  | 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, 0, _ => by rw [powersFrom, List.getD_cons_zero, pow_zero, mul_one]
  | n + 1, k + 1, hk => by
    rw [powersFrom, List.getD_cons_succ, powersFrom_getD _ _ n k (by omega), pow_succ', mul_assoc]

/-- `powers b n` at `r14`, `b` in `B`, `n` in `r15`. -/
def epowers : Stmt := blk [
  I (.movi .r9 1), I (.movi .r10 0),
  .loop (.test false .r15 (.reg .r15)) (blk [
    I (.store (at_ .r14 0) .r9), I (.store (at_ .r14 8) .r10), emul,
    I (.addi .r14 16), I (.subi .r15 1)])]

/-- The registers `epowers` writes. -/
abbrev powRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r14, .r15]

variable {s : QState} {F : QState → Prop}

/-- **`epowers` writes `powers`.** -/
theorem epowers_spec {n : Nat} {dst : UInt64} (h14 : s.reg .r14 = dst)
    (hn : s.reg .r15 = n.toUInt64) (hlen : n < 2 ^ 60)
    (hdom : ∀ k < 2 * n, (s.mem (ew dst k)).isSome) :
    WP epowers s (fun s' ↦ EArr s'.mem dst (powers (eOf (s.reg .r11) (s.reg .r12)) n) ∧
      (∀ a, (∀ k < 2 * n, a ≠ ew dst k) → s'.mem a = s.mem a) ∧
      (∀ k < 2 * n, (s'.mem (ew dst k)).isSome) ∧ RegsFrame powRegs s s') F := by
  set b := eOf (s.reg .r11) (s.reg .r12) with hb_def
  unfold epowers
  fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ i ≤ n, t.reg .r14 = ew dst (2 * i) ∧ t.reg .r15 = (n - i).toUInt64 ∧
      eOf (t.reg .r9) (t.reg .r10) = b ^ i ∧ (∀ k < i, EW t.mem dst k (b ^ k)) ∧
      (∀ a, (∀ k < 2 * n, a ≠ ew dst k) → t.mem a = s.mem a) ∧
      (∀ k < 2 * n, (t.mem (ew dst k)).isSome) ∧ RegsFrame powRegs s t)
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, fun k hk ↦ absurd hk (Nat.not_lt_zero _),
      fun _ _ ↦ rfl, hdom, by rf_tac⟩ <;> rsimp
    · rw [h14, Nat.mul_zero, ew_zero]
    · rw [hn, Nat.sub_zero]
    · rw [eOf_one, pow_zero]
  · intro t ⟨i, hi, t14, t15, hA, hD, hF, hW, hf⟩ hc
    have hne : t.reg .r15 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hin : i < n := by
      by_contra h
      exact hne (by rw [t15, show n - i = 0 by omega]; rfl)
    have w0 : t.reg .r14 + 0 = ew dst (2 * i) := by rw [t14]; uring
    have w1 : t.reg .r14 + 8 = ew dst (2 * i + 1) := by rw [t14]; uring
    refine WP.store_at (by rsimp; rw [w0]; exact hW _ (by omega)) ?_
    refine WP.store_at (by
      rsimp; rw [w1]
      exact isSome_setMem (hW _ (by omega)) _ _) ?_
    refine WP.then (emul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1 e2
    have k : ∀ q ∉ eRegs, t₁.reg q = t.reg q := fun q hq ↦ by rw [e3 q hq]; rsimp
    fstep; fstep; fdone
    rw [w0, w1] at e2
    obtain ⟨v0, v1⟩ := eOf_eq_iff.mp hA
    have n01 : ew dst (2 * i) ≠ ew dst (2 * i + 1) := ew_ne _ (by omega) (by omega) (by omega)
    have hm : ∀ a, t₁.mem a = if a = ew dst (2 * i + 1) then some (t.reg .r10) else
        if a = ew dst (2 * i) then some (t.reg .r9) else t.mem a := fun a ↦ by
      rw [e2]
      simp only [QState.setMem_mem]
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [k .r14 (by decide), t14]; uring
    · rw [k .r15 (by decide), t15, show n - i = n - (i + 1) + 1 by omega, toUInt64_succ_sub]
    · rw [e1, hA, pow_succ, hf .r11 (by decide), hf .r12 (by decide)]
    · intro q hq
      simp only [EW, hm]
      by_cases hqi : q < i
      · obtain ⟨d0, d1⟩ := hD q hqi
        have m0 : ew dst (2 * q) ≠ ew dst (2 * i) := ew_ne _ (by omega) (by omega) (by omega)
        have m1 : ew dst (2 * q) ≠ ew dst (2 * i + 1) := ew_ne _ (by omega) (by omega) (by omega)
        have m2 : ew dst (2 * q + 1) ≠ ew dst (2 * i) := ew_ne _ (by omega) (by omega) (by omega)
        have m3 : ew dst (2 * q + 1) ≠ ew dst (2 * i + 1) :=
          ew_ne _ (by omega) (by omega) (by omega)
        simp only [m0, m1, m2, m3, ite_false]
        exact ⟨d0, d1⟩
      · obtain rfl : q = i := by omega
        simp only [n01, ite_false, ite_true, v0, v1]
        exact ⟨trivial, trivial⟩
    · intro a ha
      have m0 := ha (2 * i) (by omega)
      have m1 := ha (2 * i + 1) (by omega)
      simp only [hm, m0, m1, ite_false]
      exact hF a ha
    · intro q hq
      simp only [hm]
      split
      · rfl
      · split
        · rfl
        · exact hW q hq
    · intro q hq
      have hq' := hq
      simp only [powRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq'
      obtain ⟨_, _, _, _, _, h9, h10, h14', h15'⟩ := hq'
      have hk : q ∉ eRegs := by simp [eRegs, *]
      simp only [QState.setReg_reg, h14', h15', ↓reduceIte, k q hk]
      exact hf q hq
    · rw [k .r15 (by decide), t15, show n - i = n - (i + 1) + 1 by omega, toUInt64_succ_sub,
        toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hi, _, t15, _, hD, hF, hW, hf⟩ hc
    have h0 : t.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hin : i = n := by
      have := toUInt64_inj (a := n - i) (b := 0) (by omega) (by norm_num) (by rw [← t15, h0]; rfl)
      omega
    subst hin
    refine WP.blk_nil ⟨?_, hF, hW, hf⟩
    rw [EArr_iff_EW, powers, powersFrom_length]
    intro k hk
    rw [powersFrom_getD _ _ _ _ hk, one_mul]
    exact hD k hk

end NativeVm.Field
