module

public import NativeVm.Field.Arrays

/-!
# One fold of a table

`efold`: from the table `xs` at `r13`, `r15 = |xs| / 2` pairs, it writes `foldPairs r xs` at `r14`,
`r` in `B`: element `i` is `a + r·(a + b)` for the pair `(a, b) = (xs[2i], xs[2i+1])`, which is
`a·(1 + r) + b·r`. It reads a pair before writing element `i`, and element `i` is written after
every pair before it was read, so `r14` may be `r13` (`FoldSep.self`) or any area that does not
overlap the pairs still to read (`FoldSep`).
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## `foldPairs` -/

theorem foldPairs_cons_cons (r a b : E) (rest : List E) :
    foldPairs r (a :: b :: rest) = (a * (1 + r) + b * r) :: foldPairs r rest := (rfl)

theorem foldPairs_length (r : E) : ∀ xs : List E, (foldPairs r xs).length = xs.length / 2
  | [] => rfl
  | [_] => by simp [foldPairs]
  | a :: b :: rest => by
    rw [foldPairs_cons_cons, List.length_cons, foldPairs_length r rest]
    simp only [List.length_cons]
    omega

theorem foldPairs_getD (r : E) : ∀ (xs : List E) (k : Nat), k < xs.length / 2 →
    (foldPairs r xs).getD k 0 = xs.getD (2 * k) 0 * (1 + r) + xs.getD (2 * k + 1) 0 * r
  | [], _, hk => absurd hk (by simp)
  | [_], _, hk => absurd hk (by simp)
  | a :: b :: rest, 0, _ => by simp [foldPairs_cons_cons]
  | a :: b :: rest, k + 1, hk => by
    rw [foldPairs_cons_cons, List.getD_cons_succ,
      foldPairs_getD r rest k (by simp only [List.length_cons] at hk; omega),
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring, show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 1 + 1 from rfl,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]

/-! ## Where the fold may write -/

/-- Writing element `k` at `dst` clobbers no pair still to read from `src`, of `n` elements. -/
def FoldSep (src dst : UInt64) (n : Nat) : Prop :=
  ∀ k j l l', 2 * k + 2 ≤ j → j < n → l < 2 → l' < 2 → ew dst (2 * k + l) ≠ ew src (2 * j + l')

/-- A fold in place. -/
theorem FoldSep.self (p : UInt64) {n : Nat} (hn : n < 2 ^ 60) : FoldSep p p n :=
  fun _ _ _ _ hkj hj hl hl' ↦ ew_ne p (by omega) (by omega) (by omega)

/-! ## `efold` -/

/-- `foldPairs r xs` at `r14` from `xs` at `r13`, `r15` pairs, `r` in `B`. -/
def efold : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.load .r9 (at_ .r13 0)), I (.load .rdx (at_ .r13 16)), I (.xor .r9 .rdx),
  I (.load .r10 (at_ .r13 8)), I (.load .rdx (at_ .r13 24)), I (.xor .r10 .rdx),
  emul,
  I (.load .rdx (at_ .r13 0)), I (.xor .r9 .rdx), I (.load .rdx (at_ .r13 8)), I (.xor .r10 .rdx),
  I (.store (at_ .r14 0) .r9), I (.store (at_ .r14 8) .r10),
  I (.addi .r13 32), I (.addi .r14 16), I (.subi .r15 1)])

/-- The registers `efold` writes. -/
abbrev foldRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r13, .r14, .r15]

theorem toUInt64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a.toUInt64 = b.toUInt64) :
    a = b := by
  have := congrArg UInt64.toNat h
  rwa [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem toNat_toUInt64 {a : Nat} (ha : a < 2 ^ 64) : a.toUInt64.toNat = a := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha]

variable {s : QState} {F : QState → Prop}

/-- **`efold` writes `foldPairs`.** -/
theorem efold_spec {xs : List E} {src dst : UInt64} (h13 : s.reg .r13 = src)
    (h14 : s.reg .r14 = dst) (hx : EArr s.mem src xs) (hn : s.reg .r15 = (xs.length / 2).toUInt64)
    (hlen : xs.length < 2 ^ 60) (hdom : ∀ k < 2 * (xs.length / 2), (s.mem (ew dst k)).isSome)
    (hsep : FoldSep src dst xs.length) :
    WP efold s (fun s' ↦ EArr s'.mem dst (foldPairs (eOf (s.reg .r11) (s.reg .r12)) xs) ∧
      (∀ a, (∀ k < 2 * (xs.length / 2), a ≠ ew dst k) → s'.mem a = s.mem a) ∧
      (∀ k < 2 * (xs.length / 2), (s'.mem (ew dst k)).isSome) ∧
      s'.reg .r13 = ew src (4 * (xs.length / 2)) ∧ s'.reg .r14 = ew dst (2 * (xs.length / 2)) ∧
      RegsFrame foldRegs s s') F := by
  set n := xs.length with hn_def
  set c := n / 2 with hc_def
  set r := eOf (s.reg .r11) (s.reg .r12) with hr_def
  rw [EArr_iff_EW] at hx
  unfold efold
  apply WP.loop (fun t ↦ ∃ i ≤ c, t.reg .r13 = ew src (4 * i) ∧ t.reg .r14 = ew dst (2 * i) ∧
      t.reg .r15 = (c - i).toUInt64 ∧
      (∀ k < i, EW t.mem dst k ((foldPairs r xs).getD k 0)) ∧
      (∀ j, 2 * i ≤ j → j < n → EW t.mem src j (xs.getD j 0)) ∧
      (∀ a, (∀ k < 2 * c, a ≠ ew dst k) → t.mem a = s.mem a) ∧
      (∀ k < 2 * c, (t.mem (ew dst k)).isSome) ∧ RegsFrame foldRegs s t)
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, fun k hk ↦ absurd hk (Nat.not_lt_zero _),
      fun j _ hj ↦ hx j hj, fun _ _ ↦ rfl, hdom, RegsFrame.refl _ _⟩
    · rw [h13, Nat.mul_zero, ew_zero]
    · rw [h14, Nat.mul_zero, ew_zero]
    · rw [hn, Nat.sub_zero]
  · intro t ⟨i, hi, t13, t14, t15, hD, hS, hF, hW, hf⟩ hc
    have hne : t.reg .r15 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hic : i < c := by
      by_contra h
      exact hne (by rw [t15, show c - i = 0 by omega]; rfl)
    obtain ⟨a0, a1⟩ := hS (2 * i) le_rfl (by omega)
    obtain ⟨b0, b1⟩ := hS (2 * i + 1) (by omega) (by omega)
    have ad0 : t.reg .r13 + 0 = ew src (2 * (2 * i)) := by rw [t13]; uring
    have ad8 : t.reg .r13 + 8 = ew src (2 * (2 * i) + 1) := by rw [t13]; uring
    have ad16 : t.reg .r13 + 16 = ew src (2 * (2 * i + 1)) := by rw [t13]; uring
    have ad24 : t.reg .r13 + 24 = ew src (2 * (2 * i + 1) + 1) := by rw [t13]; uring
    refine WP.load_at (by rsimp; rw [ad0]; exact a0) ?_
    refine WP.load_at (by rsimp; rw [ad16]; exact b0) ?_
    fstep
    refine WP.load_at (by rsimp; rw [ad8]; exact a1) ?_
    refine WP.load_at (by rsimp; rw [ad24]; exact b1) ?_
    fstep
    refine WP.then (emul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1 e2
    have k : ∀ q ∉ eRegs, t₁.reg q = t.reg q := fun q hq ↦ by
      rw [e3 q hq]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp [hq.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2]
    have k13 : t₁.reg .r13 = t.reg .r13 := k .r13 (by decide)
    refine WP.load_at (by rsimp; rw [k13, e2, ad0]; exact a0) ?_
    fstep
    refine WP.load_at (by rsimp; rw [k13, e2, ad8]; exact a1) ?_
    fstep
    have w0 : t₁.reg .r14 + 0 = ew dst (2 * i) := by rw [k .r14 (by decide), t14]; uring
    have w1 : t₁.reg .r14 + 8 = ew dst (2 * i + 1) := by rw [k .r14 (by decide), t14]; uring
    refine WP.store_at (by rsimp; rw [w0, e2]; exact hW _ (by omega)) ?_
    refine WP.store_at (by
      rsimp; rw [w1]
      exact isSome_setMem (by rsimp; rw [e2]; exact hW _ (by omega)) _ _) ?_
    fstep; fstep; fstep
    fdone
    rw [w0, w1]
    simp only [QState.setMem_mem, QState.setReg_mem, e2]
    -- The element written.
    have hv : eOf (t₁.reg .r9 ^^^ ((xs.getD (2 * i) 0).limb 0).lane)
        (t₁.reg .r10 ^^^ ((xs.getD (2 * i) 0).limb 1).lane) = (foldPairs r xs).getD i 0 := by
      have h11 : t.reg .r11 = s.reg .r11 := hf .r11 (by decide)
      have h12 : t.reg .r12 = s.reg .r12 := hf .r12 (by decide)
      rw [eOf_add, e1, eOf_add, eOf_lanes, eOf_lanes, h11, h12,
        foldPairs_getD r xs i (by omega)]
      ring
    obtain ⟨v0, v1⟩ := eOf_eq_iff.mp hv
    have n01 : ew dst (2 * i) ≠ ew dst (2 * i + 1) := ew_ne _ (by omega) (by omega) (by omega)
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [k13, t13]; uring
    · rw [k .r14 (by decide), t14]; uring
    · rw [k .r15 (by decide), t15, show c - i = c - (i + 1) + 1 by omega, toUInt64_succ_sub]
    · intro q hq
      by_cases hqi : q < i
      · obtain ⟨d0, d1⟩ := hD q hqi
        have m0 : ew dst (2 * q) ≠ ew dst (2 * i) := ew_ne _ (by omega) (by omega) (by omega)
        have m1 : ew dst (2 * q) ≠ ew dst (2 * i + 1) := ew_ne _ (by omega) (by omega) (by omega)
        have m2 : ew dst (2 * q + 1) ≠ ew dst (2 * i) := ew_ne _ (by omega) (by omega) (by omega)
        have m3 : ew dst (2 * q + 1) ≠ ew dst (2 * i + 1) :=
          ew_ne _ (by omega) (by omega) (by omega)
        simp only [EW, QState.setMem_mem, QState.setReg_mem, e2, m0, m1, m2, m3, ite_false]
        exact ⟨d0, d1⟩
      · obtain rfl : q = i := by omega
        simp only [EW, QState.setMem_mem, QState.setReg_mem, n01, ite_false, ite_true, v0, v1]
        exact ⟨trivial, trivial⟩
    · intro j hj hjn
      obtain ⟨d0, d1⟩ := hS j (by omega) hjn
      have s0 := fun l' (hl' : l' < 2) ↦ hsep i j 0 l' (by omega) hjn (by omega) hl'
      have s1 := fun l' (hl' : l' < 2) ↦ hsep i j 1 l' (by omega) hjn (by omega) hl'
      have m0 := Ne.symm (s0 0 (by omega))
      have m1 := Ne.symm (s1 0 (by omega))
      have m2 := Ne.symm (s0 1 (by omega))
      have m3 := Ne.symm (s1 1 (by omega))
      simp only [Nat.add_zero] at m0 m1 m2 m3
      simp only [EW, QState.setMem_mem, QState.setReg_mem, e2, m0, m1, m2, m3, ite_false]
      exact ⟨d0, d1⟩
    · intro a ha
      have m0 := ha (2 * i) (by omega)
      have m1 := ha (2 * i + 1) (by omega)
      simp only [m0, m1, ite_false]
      exact hF a ha
    · intro q hq
      split
      · rfl
      · split
        · rfl
        · exact hW q hq
    · intro q hq
      have hq' := hq
      simp only [foldRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq'
      obtain ⟨_, _, _, hdx, _, h9, h10, h13', h14', h15'⟩ := hq'
      have hk : q ∉ eRegs := by simp [eRegs, *]
      simp only [QState.setMem_reg, QState.setReg_reg, hdx, h9, h10, h13', h14', h15',
        ↓reduceIte, k q hk]
      exact hf q hq
    · rw [k .r15 (by decide), t15, show c - i = c - (i + 1) + 1 by omega, toUInt64_succ_sub,
        toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨i, hi, t13, t14, t15, hD, _, hF, hW, hf⟩ hc
    have h0 : t.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hic : i = c := by
      have := toUInt64_inj (a := c - i) (b := 0) (by omega) (by norm_num) (by rw [← t15, h0]; rfl)
      omega
    subst hic
    refine ⟨?_, hF, hW, t13, t14, hf⟩
    rw [EArr_iff_EW, foldPairs_length]
    exact hD

end NativeVm.Field
