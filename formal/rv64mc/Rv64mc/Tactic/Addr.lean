/-
  Rv64mc.Tactic.Addr

  Addresses as a base plus a constant offset, `t + c`, the form `rv_sym` keeps them in, and the facts about them
  a proof needs, each with the arithmetic on the constants as a Boolean the kernel evaluates (`offLe`, `offLt`),
  so that no `omega` runs on a goal with the program's state in it. A base is bounded by literals, `L ≤ t.toNat`
  and `t.toNat ≤ H`, as a contract's precondition bounds the stack pointer; offsets are read as signed.

  ## Main results

  * `add_ne_add`, `ne_add`, `add_ne`: two offsets from one base are different addresses
  * `add_le_add`, `le_add`, `add_le`: an offset at most another, from a bounded base
  * `ne_add_of_le`, `add_le_of_le`: an address at or above the base, against one below it
-/

namespace Rv64mc.Tactic

/-- Offsets `c1 ≤ c2` (signed) from any base in `[L, H]` that wrap neither below zero nor above `2^64`. -/
def offLe (L H : Nat) (c1 c2 : BitVec 64) : Bool :=
  decide (0 ≤ (L : Int) + c1.toInt ∧ (H : Int) + c2.toInt < 2 ^ 64 ∧ c1.toInt ≤ c2.toInt)

/-- A negative offset `c` (signed) from any base at least `L` that does not wrap below zero. -/
def offLt (L : Nat) (c : BitVec 64) : Bool :=
  decide (0 ≤ (L : Int) + c.toInt ∧ c.toInt < 0)

/-- The value of a base plus an offset that does not wrap. -/
theorem toNat_add_off {t c : BitVec 64} (h0 : 0 ≤ (t.toNat : Int) + c.toInt) (h1 : (t.toNat : Int) + c.toInt < 2 ^ 64) :
    ((t + c).toNat : Int) = t.toNat + c.toInt := by
  rw [BitVec.toNat_add]
  have := c.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h0 h1 ⊢
  by_cases hc : 2 * c.toNat < 2 ^ 64 <;> simp only [hc, ite_true, ite_false] at h0 h1 ⊢ <;> omega

theorem add_le_add {t c1 c2 : BitVec 64} {L H : Nat} (hL : L ≤ t.toNat) (hH : t.toNat ≤ H)
    (h : offLe L H c1 c2 = true) : t + c1 ≤ t + c2 := by
  simp only [offLe, decide_eq_true_eq] at h
  have e1 := toNat_add_off (t := t) (c := c1) (by omega) (by omega)
  have e2 := toNat_add_off (t := t) (c := c2) (by omega) (by omega)
  rw [BitVec.le_def]; omega

theorem le_add {t c : BitVec 64} {L H : Nat} (hL : L ≤ t.toNat) (hH : t.toNat ≤ H)
    (h : offLe L H 0#64 c = true) : t ≤ t + c := by
  simpa using add_le_add hL hH h

theorem add_le {t c : BitVec 64} {L H : Nat} (hL : L ≤ t.toNat) (hH : t.toNat ≤ H)
    (h : offLe L H c 0#64 = true) : t + c ≤ t := by
  simpa using add_le_add hL hH h

theorem add_ne_add {t c1 c2 : BitVec 64} (h : (c1 != c2) = true) : t + c1 ≠ t + c2 := by
  intro e; simp_all

theorem ne_add {t c : BitVec 64} (h : (c != 0#64) = true) : t ≠ t + c := by
  intro e; simp_all

theorem add_ne {t c : BitVec 64} (h : (c != 0#64) = true) : t + c ≠ t := by
  intro e; simp_all

/-- An address at or above a base is not one below it. -/
theorem ne_add_of_le {t a c : BitVec 64} {L : Nat} (hL : L ≤ t.toNat) (ha : t ≤ a) (h : offLt L c = true) :
    a ≠ t + c := by
  simp only [offLt, decide_eq_true_eq] at h
  have e := toNat_add_off (t := t) (c := c) (by omega) (by have := t.isLt; omega)
  rw [BitVec.le_def] at ha
  intro he; subst he; omega

/-- An address below a base is below every address at or above it. -/
theorem add_le_of_le {t a c : BitVec 64} {L : Nat} (hL : L ≤ t.toNat) (ha : t ≤ a) (h : offLt L c = true) :
    t + c ≤ a := by
  simp only [offLt, decide_eq_true_eq] at h
  have e := toNat_add_off (t := t) (c := c) (by omega) (by have := t.isLt; omega)
  rw [BitVec.le_def] at ha ⊢; omega

/-- A literal below every base in `[L, H]` plus an offset, `k ≤ t + c`. -/
def litLe (L H k : Nat) (c : BitVec 64) : Bool :=
  decide (0 ≤ (L : Int) + c.toInt ∧ (H : Int) + c.toInt < 2 ^ 64 ∧ (k : Int) ≤ L + c.toInt ∧ k < 2 ^ 64)

/-- A literal above every base in `[L, H]` plus an offset, `t + c ≤ k`. -/
def leLit (L H k : Nat) (c : BitVec 64) : Bool :=
  decide (0 ≤ (L : Int) + c.toInt ∧ (H : Int) + c.toInt ≤ k ∧ k < 2 ^ 64)

theorem lit_le_add {t c : BitVec 64} {L H k : Nat} (hL : L ≤ t.toNat) (hH : t.toNat ≤ H)
    (h : litLe L H k c = true) : BitVec.ofNat 64 k ≤ t + c := by
  simp only [litLe, decide_eq_true_eq] at h
  have e := toNat_add_off (t := t) (c := c) (by omega) (by omega)
  rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem add_le_lit {t c : BitVec 64} {L H k : Nat} (hL : L ≤ t.toNat) (hH : t.toNat ≤ H)
    (h : leLit L H k c = true) : t + c ≤ BitVec.ofNat 64 k := by
  simp only [leLit, decide_eq_true_eq] at h
  have e := toNat_add_off (t := t) (c := c) (by omega) (by omega)
  rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

example : offLe (0x10000#64).toNat (0x7fffffffffffffff#64).toNat 0xffffffffffffffb0#64 0xfffffffffffffff8#64 = true := by
  rfl
example (t : BitVec 64) (hl : 0x10000#64 ≤ t) (hh : t ≤ 0x7fffffffffffffff#64) :
    t + 0xffffffffffffffb0#64 ≤ t + 0xfffffffffffffff8#64 := add_le_add hl hh rfl

end Rv64mc.Tactic
