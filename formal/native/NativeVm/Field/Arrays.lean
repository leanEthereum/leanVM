module

public import NativeVm.Field.E
public import Statement.LeanVmVerifier
public import Mathlib.Data.UInt

/-!
# Kernels over lists of `E` in memory

A list of `E` elements is held at a pointer, element `i` at `16 i` bytes from it (`EArr`). The
kernels read their lists through `r13` and `r14`, take their count in `r15` and leave their
result in `A = (r9, r10)`:

* `edot`: `A := dot xs ys` (`LeanVM.Protocol.Verifier.dot`), the sum so far in `(rsi, rbp)`;
* `eeqEval`: `A := eqEval xs ys`, the factor `1 + x + y` in `B`;
* `epolyEval`: `A := polyEval cs b` for `b` in `B`, by Horner's rule from the last coefficient;

They write no memory.
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## Loads and stores at a register -/

theorem eval_at (r : Reg64) (d : Int64) (s : QState) : (at_ r d).eval s = s.reg r + d.toUInt64 := by
  simp [Addr.eval, at_]

variable {s : QState} {P F : QState → Prop} {xs : List Stmt}

theorem WP.load_at {d r : Reg64} {disp : Int64} {v : UInt64}
    (h : s.mem (s.reg r + disp.toUInt64) = some v) (k : WP (blk xs) (s.setReg d v) P F) :
    WP (blk (I (.load d (at_ r disp)) :: xs)) s P F :=
  WP.blk_cons (WP.ins (by simp [QInstr.step, eval_at, h]) k)

theorem WP.store_at {r src : Reg64} {disp : Int64} (h : (s.mem (s.reg r + disp.toUInt64)).isSome)
    (k : WP (blk xs) (s.setMem (s.reg r + disp.toUInt64) (s.reg src)) P F) :
    WP (blk (I (.store (at_ r disp) src) :: xs)) s P F := by
  refine WP.blk_cons (WP.ins ?_ k)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  simp [QInstr.step, eval_at, hv]

theorem toUInt64_eq_zero {n : Nat} (h : n < 2 ^ 64) (h0 : n.toUInt64 = 0) : n = 0 := by
  have := congrArg UInt64.toNat h0
  rwa [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h] at this

theorem toUInt64_succ_sub (n : Nat) : (n + 1).toUInt64 - 1 = n.toUInt64 := by
  rw [Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.ofNat_add]
  simp

/-! ## Folds -/

theorem foldl_add (L : List E) (a : E) : L.foldl (· + ·) a = a + L.foldl (· + ·) 0 := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + x), zero_add, add_assoc]

theorem foldl_mul (L : List E) (a : E) : L.foldl (· * ·) a = a * L.foldl (· * ·) 1 := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (1 * x), one_mul, mul_assoc]

theorem dot_cons (x y : E) (xs ys : List E) : dot (x :: xs) (y :: ys) = x * y + dot xs ys := by
  rw [dot, dot, List.zipWith_cons_cons, List.foldl_cons, foldl_add, zero_add]

theorem eqEval_cons (x y : E) (xs ys : List E) :
    eqEval (x :: xs) (y :: ys) = (1 + x + y) * eqEval xs ys := by
  rw [eqEval, eqEval, List.zipWith_cons_cons, List.foldl_cons, foldl_mul, one_mul]

/-! ## `edot` -/

/-- `A := dot xs ys`, `xs` at `r13`, `ys` at `r14`, `r15` elements; the sum in `(rsi, rbp)`. -/
def edot : Stmt := blk [
  I (.movi .rsi 0), I (.movi .rbp 0),
  .loop (.test false .r15 (.reg .r15)) (blk [
    I (.load .r9 (at_ .r13 0)), I (.load .r10 (at_ .r13 8)),
    I (.load .r11 (at_ .r14 0)), I (.load .r12 (at_ .r14 8)),
    emul,
    I (.xor .rsi .r9), I (.xor .rbp .r10),
    I (.addi .r13 16), I (.addi .r14 16), I (.subi .r15 1)]),
  I (.mov .r9 .rsi), I (.mov .r10 .rbp)]

/-- The registers the list kernels may write: all but `rdi` and `rsp`. -/
abbrev arrRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- **`edot` computes `dot`.** -/
theorem edot_spec {xs ys : List E} (hx : EArr s.mem (s.reg .r13) xs)
    (hy : EArr s.mem (s.reg .r14) ys) (hl : ys.length = xs.length)
    (hn : s.reg .r15 = xs.length.toUInt64) (hlen : xs.length < 2 ^ 64) :
    WP edot s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = dot xs ys ∧ s'.mem = s.mem ∧
      RegsFrame arrRegs s s') F := by
  unfold edot
  fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ xs' ys', EArr s.mem (t.reg .r13) xs' ∧ EArr s.mem (t.reg .r14) ys' ∧
      ys'.length = xs'.length ∧ t.reg .r15 = xs'.length.toUInt64 ∧ xs'.length < 2 ^ 64 ∧
      eOf (t.reg .rsi) (t.reg .rbp) + dot xs' ys' = dot xs ys ∧ t.mem = s.mem ∧
      RegsFrame arrRegs s t)
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨xs, ys, ?_, ?_, hl, ?_, hlen, ?_, rfl, by rf_tac⟩ <;> rsimp
    · exact hx
    · exact hy
    · exact hn
    · rw [eOf_zero, zero_add]
  · intro t ⟨xs', ys', hx', hy', hl', hn', hlen', hI, hm, hf⟩ hc
    have hne : t.reg .r15 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    obtain ⟨x, xs'', rfl⟩ : ∃ x xs'', xs' = x :: xs'' := by
      cases xs' with
      | nil => exact absurd hn' hne
      | cons x xs'' => exact ⟨x, xs'', rfl⟩
    obtain ⟨y, ys'', rfl⟩ : ∃ y ys'', ys' = y :: ys'' := by
      cases ys' with
      | nil => simp at hl'
      | cons y ys'' => exact ⟨y, ys'', rfl⟩
    rw [EArr.cons_iff] at hx' hy'
    obtain ⟨⟨x0, x1⟩, hx''⟩ := hx'
    obtain ⟨⟨y0, y1⟩, hy''⟩ := hy'
    refine WP.load_at (by rw [hm, int64Zero_toUInt64, UInt64.add_zero]; exact x0) ?_
    refine WP.load_at (by rsimp; rw [hm]; exact x1) ?_
    refine WP.load_at (by rsimp; rw [hm, UInt64.add_zero]; exact y0) ?_
    refine WP.load_at (by rsimp; rw [hm]; exact y1) ?_
    refine WP.then (emul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1
    have k : ∀ r ∉ eRegs, r ≠ .r11 → r ≠ .r12 → t₁.reg r = t.reg r := fun r hr h11 h12 ↦ by
      rw [e3 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, h11, h12]
    fstep; fstep; fstep; fstep; fstep; fdone
    simp only [List.length_cons] at hl' hn' hlen'
    refine ⟨⟨xs'', ys'', ?_, ?_, by omega, ?_, by omega, ?_, e2.trans hm, ?_⟩, ?_⟩
    · rw [k .r13 (by decide) (by decide) (by decide)]; exact hx''
    · rw [k .r14 (by decide) (by decide) (by decide)]; exact hy''
    · rw [k .r15 (by decide) (by decide) (by decide), hn', toUInt64_succ_sub]
    · rw [← hI, k .rsi (by decide) (by decide) (by decide),
        k .rbp (by decide) (by decide) (by decide), eOf_add, e1, eOf_lanes, eOf_lanes,
        dot_cons, add_assoc]
    · intro r hr
      have hr' := hr
      simp only [arrRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨_, _, _, _, hsi, hbp, _, _, _, h11, h12, h13, h14, h15⟩ := hr'
      have hk : r ∉ eRegs := by simp [eRegs, *]
      simp only [QState.setReg_reg, hsi, hbp, h13, h14, h15, ↓reduceIte, k r hk h11 h12]
      exact hf r hr
    · rw [k .r15 (by decide) (by decide) (by decide), hn', toUInt64_succ_sub]
      simp only [UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · intro t ⟨xs', ys', _, _, hl', hn', hlen', hI, hm, hf⟩ hc
    have h0 : t.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hx0 : xs' = [] := List.eq_nil_of_length_eq_zero (toUInt64_eq_zero hlen' (hn' ▸ h0))
    have hy0 : ys' = [] := List.eq_nil_of_length_eq_zero (by rw [hl', hx0]; rfl)
    subst hx0 hy0
    fstep; fstep; fdone
    refine ⟨?_, hm, ?_⟩
    · rw [← hI]
      simp [dot]
    · exact RegsFrame.setReg (RegsFrame.setReg hf (by simp) _) (by simp) _

/-! ## `eeqEval` -/

/-- `A := eqEval xs ys`, `xs` at `r13`, `ys` at `r14`, `r15` elements; each factor `1 + x + y`
in `B`. -/
def eeqEval : Stmt := blk [
  I (.movi .r9 1), I (.movi .r10 0),
  .loop (.test false .r15 (.reg .r15)) (blk [
    I (.load .r11 (at_ .r13 0)), I (.load .rdx (at_ .r14 0)), I (.xor .r11 .rdx),
    I (.xori .r11 1),
    I (.load .r12 (at_ .r13 8)), I (.load .rdx (at_ .r14 8)), I (.xor .r12 .rdx),
    emul,
    I (.addi .r13 16), I (.addi .r14 16), I (.subi .r15 1)])]

/-- The registers `eeqEval` writes. -/
abbrev eqRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem eOf_xor_one (a b : UInt64) : eOf (a ^^^ 1) b = eOf a b + 1 := by
  rw [← eOf_one, ← eOf_add, UInt64.xor_zero]

/-- **`eeqEval` computes `eqEval`.** -/
theorem eeqEval_spec {xs ys : List E} (hx : EArr s.mem (s.reg .r13) xs)
    (hy : EArr s.mem (s.reg .r14) ys) (hl : ys.length = xs.length)
    (hn : s.reg .r15 = xs.length.toUInt64) (hlen : xs.length < 2 ^ 64) :
    WP eeqEval s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = eqEval xs ys ∧ s'.mem = s.mem ∧
      RegsFrame eqRegs s s') F := by
  unfold eeqEval
  fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ xs' ys', EArr s.mem (t.reg .r13) xs' ∧ EArr s.mem (t.reg .r14) ys' ∧
      ys'.length = xs'.length ∧ t.reg .r15 = xs'.length.toUInt64 ∧ xs'.length < 2 ^ 64 ∧
      eOf (t.reg .r9) (t.reg .r10) * eqEval xs' ys' = eqEval xs ys ∧ t.mem = s.mem ∧
      RegsFrame eqRegs s t)
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨xs, ys, ?_, ?_, hl, ?_, hlen, ?_, rfl, by rf_tac⟩ <;> rsimp
    · exact hx
    · exact hy
    · exact hn
    · rw [eOf_one, one_mul]
  · intro t ⟨xs', ys', hx', hy', hl', hn', hlen', hI, hm, hf⟩ hc
    have hne : t.reg .r15 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    obtain ⟨x, xs'', rfl⟩ : ∃ x xs'', xs' = x :: xs'' := by
      cases xs' with
      | nil => exact absurd hn' hne
      | cons x xs'' => exact ⟨x, xs'', rfl⟩
    obtain ⟨y, ys'', rfl⟩ : ∃ y ys'', ys' = y :: ys'' := by
      cases ys' with
      | nil => simp at hl'
      | cons y ys'' => exact ⟨y, ys'', rfl⟩
    rw [EArr.cons_iff] at hx' hy'
    obtain ⟨⟨x0, x1⟩, hx''⟩ := hx'
    obtain ⟨⟨y0, y1⟩, hy''⟩ := hy'
    refine WP.load_at (by rw [hm, int64Zero_toUInt64, UInt64.add_zero]; exact x0) ?_
    refine WP.load_at (by rsimp; rw [hm, UInt64.add_zero]; exact y0) ?_
    fstep; fstep
    refine WP.load_at (by rsimp; rw [hm]; exact x1) ?_
    refine WP.load_at (by rsimp; rw [hm]; exact y1) ?_
    fstep
    refine WP.then (emul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1
    have k : ∀ r ∉ eRegs, r ≠ .r11 → r ≠ .r12 → t₁.reg r = t.reg r := fun r hr h11 h12 ↦ by
      rw [e3 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.2.2.2.1, h11, h12]
    fstep; fstep; fstep; fdone
    simp only [List.length_cons] at hl' hn' hlen'
    refine ⟨⟨xs'', ys'', ?_, ?_, by omega, ?_, by omega, ?_, e2.trans hm, ?_⟩, ?_⟩
    · rw [k .r13 (by decide) (by decide) (by decide)]; exact hx''
    · rw [k .r14 (by decide) (by decide) (by decide)]; exact hy''
    · rw [k .r15 (by decide) (by decide) (by decide), hn', toUInt64_succ_sub]
    · rw [← hI, e1, eOf_xor_one, eOf_add, eOf_lanes, eOf_lanes, eqEval_cons]
      ring
    · intro r hr
      have hr' := hr
      simp only [eqRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨_, _, _, _, _, _, _, h11, h12, h13, h14, h15⟩ := hr'
      have hk : r ∉ eRegs := by simp [eRegs, *]
      simp only [QState.setReg_reg, h13, h14, h15, ↓reduceIte, k r hk h11 h12]
      exact hf r hr
    · rw [k .r15 (by decide) (by decide) (by decide), hn', toUInt64_succ_sub]
      simp only [UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · intro t ⟨xs', ys', _, _, hl', hn', hlen', hI, hm, hf⟩ hc
    have h0 : t.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hx0 : xs' = [] := List.eq_nil_of_length_eq_zero (toUInt64_eq_zero hlen' (hn' ▸ h0))
    have hy0 : ys' = [] := List.eq_nil_of_length_eq_zero (by rw [hl', hx0]; rfl)
    subst hx0 hy0
    refine WP.blk_nil ⟨?_, hm, hf⟩
    rw [← hI]
    simp [eqEval]

/-! ## `epolyEval` -/

/-- `A := polyEval cs b`, `cs` at `r13`, `r15` coefficients, `b` in `B`: Horner's rule from the
last coefficient, `r13` stepping back from the end. -/
def epolyEval : Stmt := blk [
  I (.movi .r9 0), I (.movi .r10 0),
  I (.lea .r13 { base := .r13, idx := some (.r15, .W64) }),
  I (.lea .r13 { base := .r13, idx := some (.r15, .W64) }),
  .loop (.test false .r15 (.reg .r15)) (blk [
    emul,
    I (.subi .r13 16),
    I (.load .rdx (at_ .r13 0)), I (.xor .r9 .rdx), I (.load .rdx (at_ .r13 8)),
    I (.xor .r10 .rdx),
    I (.subi .r15 1)])]

/-- The registers `epolyEval` writes. -/
abbrev polyRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r13, .r15]


/-- **`epolyEval` computes `polyEval`.** -/
theorem epolyEval_spec {cs : List E} (hc : EArr s.mem (s.reg .r13) cs)
    (hn : s.reg .r15 = cs.length.toUInt64) (hlen : cs.length < 2 ^ 64) :
    WP epolyEval s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
      polyEval cs (eOf (s.reg .r11) (s.reg .r12)) ∧ s'.mem = s.mem ∧
      RegsFrame polyRegs s s') F := by
  set b := eOf (s.reg .r11) (s.reg .r12)
  unfold epolyEval
  fstep; fstep; fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ pre, EArr s.mem (s.reg .r13) pre ∧
      t.reg .r13 = s.reg .r13 + (16 * pre.length).toUInt64 ∧
      t.reg .r15 = pre.length.toUInt64 ∧ pre.length < 2 ^ 64 ∧
      pre.foldr (fun c acc ↦ acc * b + c) (eOf (t.reg .r9) (t.reg .r10)) = polyEval cs b ∧
      t.mem = s.mem ∧ RegsFrame polyRegs s t)
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨cs, hc, ?_, ?_, hlen, ?_, rfl, by rf_tac⟩
    · simp only [Addr.eval, QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hn, Width.bytes,
        int64Zero_toUInt64, Nat.toUInt64_eq, UInt64.ofNat_mul, UInt64.reduceOfNat]
      open scoped UInt64.CommRing in ring
    · rsimp
      exact hn
    · rsimp
      rw [eOf_zero]
      rfl
  · intro t ⟨pre, hpre, h13, hn', hlen', hI, hm, hf⟩ hc'
    have hne : t.reg .r15 ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc'
    obtain ⟨pre', c, rfl⟩ : ∃ pre' c, pre = pre' ++ [c] := by
      rcases List.eq_nil_or_concat' pre with h | ⟨L, c, h⟩
      · subst h; exact absurd hn' hne
      · exact ⟨L, c, h⟩
    rw [EArr.append_iff, EArr.cons_iff] at hpre
    obtain ⟨hpre', ⟨c0, c1⟩, _⟩ := hpre
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add] at h13 hn' hlen'
    refine WP.then (emul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    have k : ∀ r ∉ eRegs, t₁.reg r = t.reg r := e3
    have hb : eOf (t.reg .r11) (t.reg .r12) = b := by
      rw [hf .r11 (by decide), hf .r12 (by decide)]
    have h13' : t₁.reg .r13 - 16 = s.reg .r13 + (16 * pre'.length).toUInt64 := by
      rw [k .r13 (by decide), h13, toUInt64_16_succ]
      open scoped UInt64.CommRing in ring
    fstep
    refine WP.load_at (by rsimp; rw [e2, hm, UInt64.add_zero, h13']; exact c0) ?_
    fstep
    refine WP.load_at (by rsimp; rw [e2, hm, h13']; exact c1) ?_
    fstep; fstep; fdone
    refine ⟨⟨pre', hpre', h13', ?_, by omega, ?_, e2.trans hm, ?_⟩, ?_⟩
    · rw [k .r15 (by decide), hn', toUInt64_succ_sub]
    · rw [← hI, List.foldr_append, List.foldr_cons, List.foldr_nil, eOf_add, e1, hb, eOf_lanes]
    · intro r hr
      have hr' := hr
      simp only [polyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨_, _, _, hd, _, h9, h10, h13, h15⟩ := hr'
      have hk : r ∉ eRegs := by simp [eRegs, *]
      simp only [QState.setReg_reg, hd, h9, h10, h13, h15, ↓reduceIte, k r hk]
      exact hf r hr
    · rw [k .r15 (by decide), hn', toUInt64_succ_sub]
      simp only [UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · intro t ⟨pre, _, _, hn', hlen', hI, hm, hf⟩ hc'
    have h0 : t.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hc'
    have hp0 : pre = [] := List.eq_nil_of_length_eq_zero (toUInt64_eq_zero hlen' (hn' ▸ h0))
    subst hp0
    exact WP.blk_nil ⟨hI, hm, hf⟩

end NativeVm.Field
