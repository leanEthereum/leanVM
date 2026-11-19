module

public import NativeVm.Code.Phase3.LayoutCode

/-!
# Phase 3's placements and selectors: small facts

The addresses `aW`, `aI`, `aH` from the working area's address in `r15`; immediates; comparisons
of small numbers; reads through stores to other words.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

variable {s : QState}

theorem eval_aW {p : UInt64} (h : s.reg .r15 = p) (k : Nat) : (aW k).eval s = wd p k := by
  rw [eval_wd (j := 0) (by rw [h, wd_zero]), Nat.zero_add]

theorem eval_aI {p : UInt64} {ix : Reg64} {i : Nat} (h : s.reg .r15 = p)
    (hi : s.reg ix = i.toUInt64) (k : Nat) : (aI ix k).eval s = wd p (i + k) := by
  rw [eval_idx64 (j := 0) (by rw [h, wd_zero]) hi, Nat.zero_add]

theorem eval_aH {p : UInt64} {ix : Reg64} {i : Nat} (h : s.reg .r15 = p)
    (hi : s.reg ix = (2 * i).toUInt64) (k : Nat) : (aH ix k).eval s = wd p (i + k) := by
  simp only [Addr.eval, h, hi, wdisp_toUInt64]
  rw [show Width.W32.bytes.toUInt64 = 4 from rfl, ← wd_add p i k]
  congr 1
  unfold wd
  congr 1
  simp only [Nat.toUInt64_eq, UInt64.ofNat_mul]
  rw [UInt64.mul_comm, ← UInt64.mul_assoc]
  rfl

theorem ofNat_toUInt64 (n : Nat) : (Int64.ofNat n).toUInt64 = n.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp

/-- `a ≠ b` of numbers below `2^63` as words. -/
theorem cmp_ne_lit {r : Reg64} {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63)
    (h : s.reg r = a.toUInt64) :
    (Cond.cmp .ne r (.imm (Int64.ofNat b))).eval s = !decide (a = b) := by
  rw [cond_ne, rhs_imm, h, ofNat_toUInt64 b]
  by_cases e : a = b
  · subst e; simp
  · simp only [e, decide_false, Bool.not_false, bne_iff_ne, ne_eq]
    rw [toUInt64_inj (by omega) (by omega)]
    exact e

theorem cmp_ne_zero {r : Reg64} {a : Nat} (ha : a < 2 ^ 64) (h : s.reg r = a.toUInt64) :
    (Cond.cmp .ne r (.imm 0)).eval s = !decide (a = 0) := by
  rw [cond_ne, rhs_imm, h, Field.int64Zero_toUInt64]
  by_cases e : a = 0
  · subst e; simp
  · simp only [e, decide_false, Bool.not_false, bne_iff_ne, ne_eq]
    rw [show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, toUInt64_inj ha (by omega)]
    exact e

theorem cmp_ltu_reg {r q : Reg64} {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h1 : s.reg r = a.toUInt64) (h2 : s.reg q = b.toUInt64) :
    (Cond.cmp .ltu r (.reg q)).eval s = decide (a < b) := by
  rw [cond_ltu, rhs_reg, h1, h2]
  exact decide_eq_decide.mpr (toUInt64_lt ha hb)

theorem cmp_geu_reg {r q : Reg64} {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h1 : s.reg r = a.toUInt64) (h2 : s.reg q = b.toUInt64) :
    (Cond.cmp .geu r (.reg q)).eval s = decide (b ≤ a) := by
  rw [cond_geu, rhs_reg, h1, h2]
  exact decide_eq_decide.mpr (toUInt64_le hb ha)

theorem toUInt64_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ ((toUInt64_le (by omega) ha).mpr h), toNat_toUInt64 ha,
    toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]

theorem toUInt64_sub_one {a : Nat} (h : 1 ≤ a) (ha : a < 2 ^ 64) :
    a.toUInt64 - 1 = (a - 1).toUInt64 := toUInt64_sub (b := 1) h ha

theorem toUInt64_add_two (a : Nat) : a.toUInt64 + 2 = (a + 2).toUInt64 := toUInt64_add a 2

/-- `1 << (a & 63)` is `2^a` for `a < 64`. -/
theorem one_shl {a : Nat} (h : a < 64) :
    (1 : UInt64) <<< (a.toUInt64 &&& 63) = (2 ^ a).toUInt64 := by
  have e : a.toUInt64 &&& 63 = a.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, toNat_toUInt64 (by omega)]
    show a &&& 63 = a
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [e, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, toUInt64_shl _ _ h, Nat.mul_one]

/-- The key `a · 1024 + 1023 - 2 j`. -/
theorem key_eq {a j : Nat} (ha : a < 2 ^ 40) (hj : j < 512) :
    a.toUInt64 <<< (10 : Nat).toUInt64 + 1023 - (2 * j).toUInt64 =
      (a * 1024 + 1023 - 2 * j).toUInt64 := by
  rw [toUInt64_shl _ _ (by omega), show (1023 : UInt64) = (1023 : Nat).toUInt64 from rfl,
    toUInt64_add, toUInt64_sub (by omega) (by omega)]
  congr 1
  omega

/-- A store to a word of an area keeps its other words. -/
theorem setMem_other {p : UInt64} {a b : Nat} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (h : b ≠ a)
    (v : UInt64) : (s.setMem (wd p a) v).mem (wd p b) = s.mem (wd p b) := by
  rw [QState.setMem_mem, ite_eq_right_of_eq_false _ _ (eq_false fun e ↦ h ((wd_inj hb ha).mp e))]

theorem setMem_same {p : UInt64} (a : Nat) (v : UInt64) :
    (s.setMem (wd p a) v).mem (wd p a) = some v := by
  simp

theorem isSome_setMem' {a : UInt64} (v : UInt64) (b : UInt64) :
    ((s.setMem a v).mem b).isSome = true ↔ (s.setMem a v).mem b ≠ none := by
  simp [Option.isSome_iff_ne_none]

/-- Which words exist, through a store to a word that exists. -/
theorem dom_setMem {a : UInt64} (h : (s.mem a).isSome) (v : UInt64) (b : UInt64) :
    ((s.setMem a v).mem b).isSome = (s.mem b).isSome := by
  rw [QState.setMem_mem]
  split
  · subst b; rw [h]; rfl
  · rfl

/-- Read words and registers through register and memory updates, word indices compared by
`omega`. -/
syntax "p3wsimp" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| p3wsimp $[$loc]?) => `(tactic|
      simp (disch := omega) only [QState.setReg_mem, QState.setMem_reg, QState.setReg_reg,
        setMem_wd_ne, setMem_wd_eq, reduceCtorEq, ↓reduceIte, int64_toUInt64,
        Field.int64Zero_toUInt64] $[$loc]?)

/-- A register frame through updates of the frame's registers and of memory. -/
theorem rf_of {l : List Reg64} {s s' : QState} (h : ∀ r, r ∉ l → s'.reg r = s.reg r) :
    RegsFrame l s s' := h

theorem wp_ite_of {c : Cond} {t e : Stmt} {P E : QState → Prop} {b : Bool} (hc : c.eval s = b)
    (ht : b = true → WP t s P E) (he : b = false → WP e s P E) : WP (.ite c t e) s P E := by
  cases b
  · exact WP.ite (by rw [hc]; exact he rfl)
  · exact WP.ite (by rw [hc]; exact ht rfl)

end NativeVm.Code.P3
