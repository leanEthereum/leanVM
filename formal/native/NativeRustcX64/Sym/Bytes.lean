module

public import NativeRustcX64.Sym.Basic
import all Kraken.Mem

/-!
# Bytes of stored and loaded values

The bytes Kraken stores for a value of `n ≤ 8` bytes are the `byteOf`s of the 64-bit value it is
the low bytes of (`toBytes_setWidth`); the integer Kraken loads from the bytes `byteOf x (t + i)`,
`i < n`, is the `n` bytes of `x` from byte `t` (`ofBytes_byteOf`). Kraken's memory: a load of bytes
that are all there (`loadInt_of_get?`), the bytes after a store (`get?_storeInt`).
-/

namespace NativeRustcX64.Sym

public section

/-! ## Bytes of integers -/

theorem toBytes_getElem? (n : Nat) (v : Int) (t : Nat) (ht : t < n) :
    (Int.toBytes n v)[t]? = some (UInt8.ofNat ((v / 2 ^ (8 * t)) % 256).toNat) := by
  induction n generalizing v t with
  | zero => omega
  | succ n ih =>
    cases t with
    | zero =>
      simp only [Int.toBytes, List.getElem?_cons_zero, Nat.mul_zero, Int.pow_zero, Int.ediv_one,
        Int.take]
      rfl
    | succ t =>
      simp only [Int.toBytes, List.getElem?_cons_succ]
      rw [ih (v / 256) t (by omega), Int.ediv_ediv_of_nonneg (by decide)]
      congr 4
      rw [show 8 * (t + 1) = 8 + 8 * t by omega, Int.pow_add]
      rfl

theorem byteOf_mod (x : BitVec 64) (t : Nat) :
    byteOf x t = UInt8.ofNat (x.toNat / 2 ^ (8 * t) % 256) := by
  unfold byteOf
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat']
  omega

/-- A value congruent to `X` modulo `2 ^ (8 * n)` has `X`'s bytes below `n`. -/
theorem byte_of_cong (v : Int) (X q : Int) (n t : Nat) (ht : t < n) (hv : v = X + q * 2 ^ (8 * n)) :
    (v / 2 ^ (8 * t)) % 256 = (X / 2 ^ (8 * t)) % 256 := by
  have hp : (2 : Int) ^ (8 * n) = (q.sign * 0 + 256 * 2 ^ (8 * (n - t - 1))) * 2 ^ (8 * t) := by
    rw [Int.mul_zero, Int.zero_add, show (256 : Int) = 2 ^ 8 from rfl, ← Int.pow_add,
      ← Int.pow_add]
    congr 1
    omega
  rw [hv, hp, Int.mul_zero, Int.zero_add, ← Int.mul_assoc, Int.add_mul_ediv_right _ _ (by
    exact Int.ne_of_gt (Int.pow_pos (by decide))), Int.mul_comm q, Int.mul_assoc,
    Int.add_mul_emod_self_left]

theorem natCast_div_mod (N a : Nat) :
    ((N / 2 ^ a % 256 : Nat) : Int) = (N : Int) / 2 ^ a % 256 := by
  rw [Int.natCast_emod, Int.natCast_ediv, Int.natCast_pow]
  rfl

theorem toBytes_setWidth (x : BitVec 64) (n t : Nat) (ht : t < n) :
    (Int.toBytes n (x.setWidth (8 * n)).toInt)[t]? = some (byteOf x t) := by
  rw [toBytes_getElem? n _ t ht, byteOf_mod]
  congr 1
  have hX : (x.setWidth (8 * n)).toNat = x.toNat % 2 ^ (8 * n) := BitVec.toNat_setWidth _ _
  have key : ((x.setWidth (8 * n)).toInt / 2 ^ (8 * t)) % 256 =
      ((x.toNat % 2 ^ (8 * n) : Nat) : Int) / 2 ^ (8 * t) % 256 := by
    rw [BitVec.toInt_eq_toNat_cond, hX]
    split
    · rfl
    · apply byte_of_cong _ _ (-1) n t ht
      rw [Int.natCast_pow, Int.sub_eq_add_neg, Int.neg_one_mul]
      rfl
  rw [key, ← natCast_div_mod, Int.toNat_natCast]
  congr 1
  rw [show 8 * n = 8 * t + 8 * (n - t) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd]
  exact ⟨2 ^ (8 * (n - t) - 8), by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]
    congr 1
    omega⟩

theorem ofBytes_natCast (bs : List UInt8) : Int.ofBytes bs = (Nat.ofBytes bs : Int) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [Int.ofBytes_cons, ih]
    show _ = ((Nat.ofBytes bs * 256 + b.toNat : Nat) : Int)
    rw [Int.natCast_add, Int.natCast_mul]
    rfl

theorem natOfBytes_append_single (l : List UInt8) (b : UInt8) :
    Nat.ofBytes (l ++ [b]) = Nat.ofBytes l + 256 ^ l.length * b.toNat := by
  induction l with
  | nil => simp [Nat.ofBytes]
  | cons a l ih =>
    show Nat.ofBytes (l ++ [b]) * 256 + a.toNat = (Nat.ofBytes l * 256 + a.toNat) + _
    rw [ih, List.length_cons, Nat.pow_succ, Nat.add_mul,
      show 256 ^ l.length * 256 * b.toNat = 256 ^ l.length * b.toNat * 256 by
        rw [Nat.mul_assoc, Nat.mul_comm 256, ← Nat.mul_assoc]]
    omega

theorem ofBytes_byteOf (x : BitVec 64) (t n : Nat) :
    Int.ofBytes ((List.range n).map fun i => byteOf x (t + i)) =
      ((x.toNat / 2 ^ (8 * t) % 2 ^ (8 * n) : Nat) : Int) := by
  rw [ofBytes_natCast]
  congr 1
  induction n with
  | zero => simp [Nat.ofBytes, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, natOfBytes_append_single, ih,
      List.length_map, List.length_range, byteOf_mod, UInt8.toNat_ofNat',
      show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add, Nat.mod_mul,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, show 8 * t + 8 * n = 8 * (t + n) by omega,
      show (256 : Nat) ^ n = 2 ^ (8 * n) by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul],
      Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 256)]

theorem ofBytes_nonneg_lt (bs : List UInt8) :
    0 ≤ Int.ofBytes bs ∧ Int.ofBytes bs < 2 ^ (8 * bs.length) := by
  refine ⟨Int.ofBytes_ge_zero bs, ?_⟩
  have := Int.ofBytes_lt bs
  rwa [show (2 : Int) ^ (8 * bs.length) = 256 ^ bs.length by
    rw [Int.pow_mul]
    rfl]

/-! ## Kraken's memory -/

theorem mapM_some {α β : Type} (l : List α) (g : α → Option β) (f : α → β)
    (h : ∀ i ∈ l, g i = some (f i)) : (l.map g).mapM id = some (l.map f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.mapM_cons, id, h a List.mem_cons_self,
      ih (fun i hi => h i (List.mem_cons_of_mem a hi))]
    rfl

theorem loadInt_of_get? (d : DataMem) (a : BitVec 64) (n : Nat) (f : Nat → UInt8)
    (h : ∀ i < n, d.get? (a + BitVec.ofNat 64 i) = some (f i)) :
    Mem.loadInt d a n = some (Int.ofBytes ((List.range n).map f)) := by
  unfold Mem.loadInt Mem.loadBytes
  rw [mapM_some (List.range n) _ f (fun i hi => h i (List.mem_range.mp hi))]
  rfl

theorem get?_storeInt (d : DataMem) (a k : BitVec 64) (n : Nat) (v : Int) (hn : n ≤ 8) :
    (Mem.storeInt d a n v).get? k =
      if (k - a).toNat < n then (Int.toBytes n v)[(k - a).toNat]? else d.get? k := by
  unfold Mem.storeInt Mem.storeBytes
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union,
    get?_At _ _ _ (by rw [Int.toBytes_length]; omega), Std.ExtHashMap.get?_eq_getElem?]
  split
  · rename_i h
    rw [List.getElem?_eq_getElem (by rw [Int.toBytes_length]; exact h)]
    rfl
  · rename_i h
    rw [List.getElem?_eq_none (by rw [Int.toBytes_length]; omega)]
    rfl

/-- `Mem.loadInt` reads only the bytes it loads. -/
theorem loadInt_congr {d d' : DataMem} {a : BitVec 64} {n : Nat}
    (h : ∀ i < n, d'.get? (a + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i)) :
    Mem.loadInt d' a n = Mem.loadInt d a n := by
  unfold Mem.loadInt Mem.loadBytes
  rw [List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))]

theorem loadInt_isSome_of_get? (d : DataMem) (a : BitVec 64) (n : Nat)
    (h : ∀ i < n, (d.get? (a + BitVec.ofNat 64 i)).isSome) : (Mem.loadInt d a n).isSome := by
  rw [loadInt_of_get? d a n (fun i => (d.get? (a + BitVec.ofNat 64 i)).getD 0)]
  · rfl
  · intro i hi
    have := h i hi
    revert this
    cases d.get? (a + BitVec.ofNat 64 i) <;> simp

/-! ## Addresses -/

theorem toNat_add_ofNat (b : BitVec 64) (i : Nat) (h : b.toNat + i < 2 ^ 64) :
    (b + BitVec.ofNat 64 i).toNat = b.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_sub_of_le (k a : BitVec 64) (h : a.toNat ≤ k.toNat) :
    (k - a).toNat = k.toNat - a.toNat := by
  rw [BitVec.toNat_sub]
  have := k.isLt
  omega

theorem le_toNat_sub (k a : BitVec 64) (n : Nat) (hA : a.toNat + n ≤ 2 ^ 64)
    (h : k.toNat < a.toNat ∨ a.toNat + n ≤ k.toNat) : n ≤ (k - a).toNat := by
  rw [BitVec.toNat_sub]
  have := k.isLt
  have := a.isLt
  rcases h with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show 2 ^ 64 - a.toNat + k.toNat = (k.toNat - a.toNat) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega

end

end NativeRustcX64.Sym
