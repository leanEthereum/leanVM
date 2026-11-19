module

public import NativeVm.Code.Phase7.RingStore

/-!
# Small register steps and lists in memory

`minReg a b` (`a := min a b`) and `subSat a b` (`a := a - b`, `0` below), on numbers below `2^64`;
`EArr.take`, `EArr.drop` for a list's prefix and suffix; `ew_ew`, `ew_inj` for words of a small
buffer.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier

variable {s : QState} {F : QState → Prop}

/-! ## Registers -/

theorem toUInt64_lt_iff {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    x.toUInt64 < y.toUInt64 ↔ x < y := by
  rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64 hx, toNat_toUInt64 hy]

theorem toUInt64_sub {x y : Nat} (h : y ≤ x) : x.toUInt64 - y.toUInt64 = (x - y).toUInt64 := by
  rw [Nat.toUInt64_eq, Nat.toUInt64_eq, Nat.toUInt64_eq, ← UInt64.ofNat_sub h]

/-- `a := min a b`. -/
def minReg (a b : Reg64) : Stmt := .ite (.cmp .ltu b (.reg a)) (blk [I (.mov a b)]) (blk [])

theorem minReg_spec {a b : Reg64} {x y : Nat} (ha : s.reg a = x.toUInt64)
    (hb : s.reg b = y.toUInt64) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    WP (minReg a b) s (fun s' ↦ s' = s.setReg a (min x y).toUInt64) F := by
  unfold minReg
  apply WP.ite
  by_cases h : y < x
  · have hc : (Cond.cmp .ltu b (.reg a)).eval s = true := by
      simp [Cond.eval, Rhs.eval, ha, hb, toUInt64_lt_iff hy hx, h]
    simp only [hc, ↓reduceIte]
    fstep; fdone
    rw [hb, Nat.min_eq_right (by omega)]
  · have hc : (Cond.cmp .ltu b (.reg a)).eval s = false := by
      simp [Cond.eval, Rhs.eval, ha, hb, toUInt64_lt_iff hy hx, h]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    refine WP.blk_nil ?_
    rw [Nat.min_eq_left (by omega), ← ha]
    cases s
    simp [QState.setReg]

/-- `a := a - b`, `0` when `b` is larger. -/
def subSat (a b : Reg64) : Stmt :=
  .ite (.cmp .ltu a (.reg b)) (blk [I (.movi a 0)]) (blk [I (.sub a b)])

theorem subSat_spec {a b : Reg64} {x y : Nat} (ha : s.reg a = x.toUInt64)
    (hb : s.reg b = y.toUInt64) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    WP (subSat a b) s (fun s' ↦ s' = s.setReg a (x - y).toUInt64) F := by
  unfold subSat
  apply WP.ite
  by_cases h : x < y
  · have hc : (Cond.cmp .ltu a (.reg b)).eval s = true := by
      simp [Cond.eval, Rhs.eval, ha, hb, toUInt64_lt_iff hx hy, h]
    simp only [hc, ↓reduceIte]
    fstep; fdone
    rw [show x - y = 0 by omega]
    rfl
  · have hc : (Cond.cmp .ltu a (.reg b)).eval s = false := by
      simp [Cond.eval, Rhs.eval, ha, hb, toUInt64_lt_iff hx hy, h]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    fstep; fdone
    rw [ha, hb, toUInt64_sub (by omega)]

/-! ## Words of a buffer -/

theorem ew_ew (b : UInt64) (i j : Nat) : ew (ew b i) j = ew b (i + j) := by uring

theorem ew_inj {b : UInt64} {i j : Nat} (hi : i < 2 ^ 61) (hj : j < 2 ^ 61) :
    ew b i = ew b j ↔ i = j :=
  ⟨fun e ↦ by_contra fun h ↦ ew_ne b hi hj h e, fun h ↦ h ▸ rfl⟩

theorem add16 (p : UInt64) (i : Nat) : p + (16 * i).toUInt64 = ew p (2 * i) := by uring

/-! ## Prefixes and suffixes -/

theorem EArr.take {mem : UInt64 → Option UInt64} {p : UInt64} {L : List E} (h : EArr mem p L)
    (k : Nat) : EArr mem p (L.take k) := by
  have e := List.take_append_drop k L
  rw [← e] at h
  exact (EArr.append_iff.mp h).1

theorem EArr.drop {mem : UInt64 → Option UInt64} {p : UInt64} {L : List E} (h : EArr mem p L)
    {k : Nat} (hk : k ≤ L.length) : EArr mem (ew p (2 * k)) (L.drop k) := by
  have e := List.take_append_drop k L
  rw [← e] at h
  have := (EArr.append_iff.mp h).2
  rwa [List.length_take, Nat.min_eq_left hk, add16] at this

end NativeVm.Code.Ring
