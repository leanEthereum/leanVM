/-
  LeanVM.Guest.Packed.PMap

  A finite map `ℕ → ℕ` packed in one `ℕ`, a slot of fixed width per key.
-/

module

public import LeanVM.Guest.Packed.Lanes

/-!
# Packed maps

A map with slots of `w` bits is one number `m`: its low 64 bits are a **salt**, and above them key
`k`'s slot is lane `k` (`slot w m k`), holding `v + 1` for the value `v` and `0` for none. `get`
reads a slot with one shift and a remainder, and `set` writes one with a single `xor` on the whole
number. A value is at most `2^w - 2`; `set` keeps the other slots whatever the value
(`get_set_ne`), and stores it when it fits (`get_set_eq`).

Each `get` or `set` copies the number above the slot, and the kernel keeps every copy in its
caches until the declaration is checked: a `PMap` is a map of a few kilobits, and a larger map is
a `PTree` of them (`PTree.lean`).

The salt is a counter that `set` steps: the kernel hashes a literal by its low 64 bits, so the
versions of a map along a chain of updates, which differ only in their high slots, would share
one hash and collide in the kernel's caches. `get` never reads it, so no spec mentions it.

For maps of `n` slots whose stored values are below `2^(w-1)` (`fits` and `guarded` of the slots,
`m >>> 64`), `sub` and `inter` compare all slots at once by the guard bits of `Lanes`'s
`nonzero`, as `Trie.sub` and `Trie.inter` (`LeanVM/Guest/ExecCore.lean`) do key by key.
-/

namespace LeanVM.Guest.Packed.PMap

open LeanVM.Guest.Packed

@[expose] public section

/-- The empty map. -/
def empty : ℕ := 0

/-- The salt's mask, `2^64 - 1`. -/
def saltMask : ℕ := Nat.sub (Nat.pow 2 64) 1

/-- Key `k`'s slot in `m`, slots of `w` bits: `v + 1` for the value `v`, `0` for none. -/
def slot (w m k : ℕ) : ℕ := Nat.mod (Nat.shiftRight m (Nat.add 64 (Nat.mul w k))) (Nat.pow 2 w)

/-- The value at key `k`. -/
def get (w m k : ℕ) : Option ℕ :=
  match slot w m k with
  | 0 => none
  | x + 1 => some x

/-- `m` with the value `v` at key `k`, and the next salt. -/
def set (w m k v : ℕ) : ℕ :=
  Nat.xor m (Nat.lor
    (Nat.shiftLeft (Nat.xor (slot w m k) (Nat.mod (Nat.add v 1) (Nat.pow 2 w))) (Nat.add 64 (Nat.mul w k)))
    (Nat.xor (Nat.land m saltMask) (Nat.land (Nat.add (Nat.land m saltMask) 1) saltMask)))

/-- Every entry of `a` is one of `b`, for maps of `n` slots below `2^(w-1)`. -/
def sub (w n a b : ℕ) : Bool :=
  Nat.beq (Nat.land (nonzero w n (Nat.shiftRight a 64))
    (nonzero w n (Nat.xor (Nat.shiftRight a 64) (Nat.shiftRight b 64)))) 0

/-- The entries on which `a` and `b` agree, for maps of `n` slots below `2^(w-1)`, with `a`'s next
salt. -/
def inter (w n a b : ℕ) : ℕ :=
  Nat.lor (Nat.shiftLeft (Nat.xor (Nat.shiftRight a 64) (Nat.land (Nat.shiftRight a 64)
      (Nat.mul (Nat.shiftRight (nonzero w n (Nat.xor (Nat.shiftRight a 64) (Nat.shiftRight b 64)))
        (Nat.sub w 1)) (Nat.sub (Nat.pow 2 w) 1)))) 64)
    (Nat.land (Nat.add (Nat.land a saltMask) 1) saltMask)

end

variable {w n m k v : ℕ}

public theorem slot_eq (w m k : ℕ) : slot w m k = lane (m >>> 64) w k := by
  show (m >>> (64 + w * k)) % 2 ^ w = (m >>> 64 >>> (w * k)) % 2 ^ w
  rw [Nat.shiftRight_add]

public theorem slot_lt (w m k : ℕ) : slot w m k < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)

public theorem get_eq_none : get w m k = none ↔ slot w m k = 0 := by
  unfold get; split <;> simp_all

public theorem get_eq_some {x : ℕ} : get w m k = some x ↔ slot w m k = x + 1 := by
  unfold get; split <;> simp_all

/-- `get` reads the slot: maps agree at a key when their slots do. -/
public theorem get_eq_get_iff {a b : ℕ} : get w a k = get w b k ↔ slot w a k = slot w b k := by
  unfold get; split <;> split <;> simp_all

@[simp] public theorem get_empty (w k : ℕ) : get w empty k = none := by
  rw [get_eq_none, slot_eq]; simp [empty]

theorem saltMask_eq : saltMask = 2 ^ 64 - 1 := rfl

/-- Bits from `64` on are the slots: the salt `s < 2^64` beside `y <<< 64` is dropped by `>>> 64`. -/
theorem shiftLeft_lor_shiftRight (y s : ℕ) (hs : s < 2 ^ 64) : (y <<< 64 ||| s) >>> 64 = y := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_shiftRight, Nat.testBit_lor, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega)))]
  simp

theorem salt_lt (a b : ℕ) : a &&& saltMask ^^^ b &&& saltMask < 2 ^ 64 :=
  Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ (by decide)) (Nat.and_lt_two_pow _ (by decide))

public theorem slot_set (w m k v k' : ℕ) :
    slot w (set w m k v) k' = if k' = k then (v + 1) % 2 ^ w else slot w m k' := by
  apply Nat.eq_of_testBit_eq; intro b
  rw [slot_eq]
  show (lane ((m ^^^ ((slot w m k ^^^ (v + 1) % 2 ^ w) <<< (64 + w * k) |||
    (m &&& saltMask ^^^ ((m &&& saltMask) + 1) &&& saltMask))) >>> 64) w k').testBit b = _
  have hs : (m &&& saltMask ^^^ ((m &&& saltMask) + 1) &&& saltMask).testBit (64 + (w * k' + b)) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le (salt_lt _ _) (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [testBit_lane, Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_lor, hs, Bool.or_false,
    Nat.testBit_shiftLeft]
  by_cases hb : b < w
  · have hsl : (slot w m k).testBit b = m.testBit (64 + (w * k + b)) := by
      rw [slot_eq, testBit_lane, Nat.testBit_shiftRight]; simp [hb]
    split_ifs with hk
    · subst hk
      simp only [hb, decide_true, Bool.true_and, ge_iff_le, Nat.add_le_add_iff_left,
        Nat.le_add_right, Nat.add_sub_add_left, Nat.add_sub_cancel_left, Nat.testBit_xor, hsl]
      cases m.testBit (64 + (w * k' + b)) <;> simp
    · rw [slot_eq w m k', testBit_lane, Nat.testBit_shiftRight]
      rcases Nat.lt_or_gt_of_ne hk with hk | hk
      · have : ¬ 64 + (w * k' + b) ≥ 64 + w * k := by
          have := (mul_add_lt_mul hb (i := k') (j := k)).2 hk; omega
        simp [this]
      · have hge : w ≤ w * k' + b - w * k := by
          have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hk); rw [Nat.mul_succ] at this; omega
        have : (slot w m k ^^^ (v + 1) % 2 ^ w).testBit (64 + (w * k' + b) - (64 + w * k)) = false := by
          apply Nat.testBit_lt_two_pow
          refine lt_of_lt_of_le (Nat.xor_lt_two_pow (slot_lt ..) (Nat.mod_lt _ (Nat.two_pow_pos w))) ?_
          exact Nat.pow_le_pow_right (by omega) (by omega)
        simp [this]
  · have hlt : ∀ x < 2 ^ w, x.testBit b = false := fun x hx ↦
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    split_ifs
    · simp [hb, hlt _ (Nat.mod_lt _ (Nat.two_pow_pos w))]
    · simp [hb, hlt _ (lane_lt ..), slot_eq]

public theorem get_set_eq (w m k v : ℕ) (h : v + 1 < 2 ^ w) : get w (set w m k v) k = some v := by
  rw [get_eq_some, slot_set]; simp [Nat.mod_eq_of_lt h]

public theorem get_set_ne (w m k v : ℕ) {k' : ℕ} (h : k' ≠ k) : get w (set w m k v) k' = get w m k' := by
  rw [get_eq_get_iff, slot_set]; simp [h]

/-! ## Whole-map comparisons -/

section Compare

variable {a b : ℕ}

theorem slot_eq_zero_of_ge (hm : m >>> 64 < 2 ^ (w * n)) (hk : n ≤ k) : slot w m k = 0 := by
  rw [slot_eq, ← pack_lane hm, lane_pack (fun i _ ↦ lane_lt ..)]; simp [Nat.not_lt.2 hk]

theorem lane_diff (hw : 0 < w) (ha : a >>> 64 < 2 ^ (w * n)) (hb : b >>> 64 < 2 ^ (w * n))
    (ga : ∀ k < n, slot w a k < 2 ^ (w - 1)) (gb : ∀ k < n, slot w b k < 2 ^ (w - 1)) (i : ℕ) :
    lane (nonzero w n (a >>> 64 ^^^ b >>> 64)) w i =
      if i < n ∧ slot w a i ≠ slot w b i then 2 ^ (w - 1) else 0 := by
  rw [lane_nonzero hw (Nat.xor_lt_two_pow ha hb)
    (fun i hi ↦ by rw [lane_xor, ← slot_eq, ← slot_eq]; exact Nat.xor_lt_two_pow (ga i hi) (gb i hi)),
    lane_xor]
  simp only [ne_eq, xor_eq_zero_iff, ← slot_eq]

variable (hw : 0 < w) (ha : a >>> 64 < 2 ^ (w * n)) (hb : b >>> 64 < 2 ^ (w * n))
  (ga : ∀ k < n, slot w a k < 2 ^ (w - 1)) (gb : ∀ k < n, slot w b k < 2 ^ (w - 1))
include hw ha hb ga gb

public theorem sub_iff : sub w n a b = true ↔ ∀ k x, get w a k = some x → get w b k = some x := by
  show Nat.beq (nonzero w n (a >>> 64) &&& nonzero w n (a >>> 64 ^^^ b >>> 64)) 0 = true ↔ _
  rw [Nat.beq_eq, eq_zero_iff_lanes hw]
  simp only [get_eq_some]
  refine forall_congr' fun k ↦ ?_
  rw [lane_land, lane_diff hw ha hb ga gb, lane_nonzero hw ha fun i hi ↦ slot_eq w a i ▸ ga i hi]
  by_cases hk : k < n
  · by_cases h0 : slot w a k = 0
    · simp only [← slot_eq, h0]; simp
    · by_cases he : slot w a k = slot w b k
      · simp only [← slot_eq, he]; simp
      · simp only [← slot_eq]
        simp only [hk, ne_eq, h0, not_false_eq_true, and_self, ↓reduceIte, he, Nat.and_self,
          (Nat.two_pow_pos _).ne', false_iff, not_forall]
        exact ⟨slot w a k - 1, by omega, by omega⟩
  · simp only [hk, false_and, ↓reduceIte, Nat.and_zero, true_iff]
    intro x hx; rw [slot_eq_zero_of_ge ha (by omega)] at hx; omega

public theorem get_inter (k : ℕ) :
    get w (inter w n a b) k = if get w a k = get w b k then get w a k else none := by
  have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  -- The guard bits of the differing slots, shifted to each lane's bottom and spread over it.
  have hd : nonzero w n (a >>> 64 ^^^ b >>> 64) >>> (w - 1) * (2 ^ w - 1) =
      pack (fun i ↦ if slot w a i ≠ slot w b i then 2 ^ w - 1 else 0) w n := by
    have hlt : ∀ i < n, (if slot w a i ≠ slot w b i then 2 ^ (w - 1) else 0) < 2 ^ w := fun i _ ↦ by
      split_ifs
      · exact Nat.pow_lt_pow_right (by omega) (by omega)
      · exact Nat.two_pow_pos _
    have : nonzero w n (a >>> 64 ^^^ b >>> 64) =
        pack (fun i ↦ if slot w a i ≠ slot w b i then 2 ^ (w - 1) else 0) w n := by
      rw [lane_ext (nonzero_lt hw) (pack_lt hlt)]
      intro i hi
      rw [lane_diff hw ha hb ga gb, lane_pack hlt]; simp [hi]
    rw [this, Nat.shiftRight_eq_div_pow,
      pack_congr (g := fun i ↦ (if slot w a i ≠ slot w b i then 1 else 0) * 2 ^ (w - 1))
        fun i _ ↦ by split_ifs <;> simp,
      ← pack_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _), pack_mul]
    exact pack_congr fun i _ ↦ by split_ifs <;> simp
  have hslot : slot w (inter w n a b) k = if slot w a k = slot w b k then slot w a k else 0 := by
    rw [slot_eq]
    show lane ((((a >>> 64) ^^^ ((a >>> 64) &&& (nonzero w n (a >>> 64 ^^^ b >>> 64) >>> (w - 1) *
      (2 ^ w - 1)))) <<< 64 ||| (((a &&& saltMask) + 1) &&& saltMask)) >>> 64) w k = _
    rw [shiftLeft_lor_shiftRight _ _ (Nat.and_lt_two_pow _ (by decide)), hd, lane_xor, lane_land,
      lane_pack fun i _ ↦ by split_ifs <;> omega, ← slot_eq]
    by_cases hk : k < n
    · by_cases he : slot w a k = slot w b k
      · simp [hk, he]
      · simp only [hk, ne_eq, he, not_false_eq_true, ↓reduceIte]
        rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (slot_lt ..),
          Nat.xor_self]
    · have := slot_eq_zero_of_ge ha (k := k) (by omega)
      have := slot_eq_zero_of_ge hb (k := k) (by omega)
      simp_all
  split_ifs with he
  · exact get_eq_get_iff.2 (by rw [hslot]; simp [get_eq_get_iff.1 he])
  · rw [get_eq_none, hslot]; simp [mt get_eq_get_iff.2 he]

end Compare

end LeanVM.Guest.Packed.PMap
