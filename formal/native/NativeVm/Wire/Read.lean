module

public import NativeVm.Wire.Model

/-!
# The model's reads are the wire's reads

Reading at byte position `c` of `B` is reading `B.drop c` (`readU32_drop`, `readU32s_drop`,
`readWords_drop`, `readDigest_drop`, `readDigests_drop`, `readRows_drop`): the same values, and
the rest is `B.drop` of the new position. A little-endian lane of bytes is their little-endian
number (`littleEndianLane_eq_sum`).
-/

@[expose] public section

namespace NativeVm.Wire

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open Native.Keccak.Proof

/-! ## Little-endian numbers -/

theorem byte_lt (b : UInt8) : b.toNat < 256 := b.toNat_lt

/-- The little-endian number of `m` bytes is below `256 ^ m`. -/
theorem sum_bytes_lt (f : Nat → UInt8) (m : Nat) :
    ∑ k ∈ Finset.range m, (f k).toNat * 256 ^ k < 256 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have := byte_lt (f m)
    have : (f m).toNat * 256 ^ m ≤ 255 * 256 ^ m := Nat.mul_le_mul_right _ (by omega)
    omega

theorem leNat_lt (B : List UInt8) (p n : Nat) : leNat B p n < 256 ^ n :=
  sum_bytes_lt (fun k ↦ B.getD (p + k) 0) n

/-- Bit `t` of a little-endian number of bytes. -/
theorem testBit_sum_bytes (f : Nat → UInt8) (m t : Nat) :
    (∑ k ∈ Finset.range m, (f k).toNat * 256 ^ k).testBit t =
      (decide (t < 8 * m) && (f (t / 8)).toNat.testBit (t % 8)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hlt := sum_bytes_lt f m
    rw [Finset.sum_range_succ, show (f m).toNat * 256 ^ m = 2 ^ (8 * m) * (f m).toNat by
      rw [pow_mul]; ring, add_comm, Nat.testBit_two_pow_mul_add _ (by rw [pow_mul]; simpa using hlt)]
    split
    · rw [ih]; simp [*, show t < 8 * (m + 1) by omega]
    · by_cases h2 : t < 8 * m + 8
      · have hq : t / 8 = m := by omega
        have hr : t % 8 = t - 8 * m := by omega
        simp [hq, hr, show t < 8 * (m + 1) by omega]
      · simp [show ¬ t < 8 * (m + 1) by omega, testBit_byte _ (show 8 ≤ t - 8 * m by omega)]

/-- **A lane is the little-endian number of its bytes.** -/
theorem laneOf_toNat (f : Nat → UInt8) :
    (laneOf f).toNat = ∑ k ∈ Finset.range 8, (f k).toNat * 256 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_laneOf, testBit_sum_bytes]

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem littleEndianLane_eq_sum (bytes : List UInt8) (i : Nat) :
    littleEndianLane bytes i =
      (∑ k ∈ Finset.range 8, (bytes.getD (8 * i + k) 0).toNat * 256 ^ k).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [littleEndianLane_eq, laneOf_toNat, toNat_toUInt64]
  exact lt_of_lt_of_le (sum_bytes_lt _ 8) (by norm_num)

/-! ## Reading at a position -/

variable {B : List UInt8}

theorem getD_take_drop (B : List UInt8) (c n j : Nat) :
    ((B.drop c).take n).getD j 0 = if j < n then B.getD (c + j) 0 else 0 := by
  rw [getD_take, getD_drop]

theorem readBytes_drop {c : Nat} (hc : c ≤ B.length) (n : Nat) :
    readBytes n (B.drop c) =
      if c + n ≤ B.length then some ((B.drop c).take n, B.drop (c + n)) else none := by
  unfold readBytes
  rw [List.length_drop, List.drop_drop]
  by_cases h : c + n ≤ B.length
  · simp only [show n ≤ B.length - c by omega, h, ite_true]
  · simp only [show ¬ n ≤ B.length - c by omega, h, ite_false]

/-- Lane `i` of the `n` bytes at `c`, for `8 i + 8 ≤ n`, is the word at `c + 8 i`. -/
theorem lane_take_drop (B : List UInt8) (c n i : Nat) (h : 8 * i + 8 ≤ n) :
    littleEndianLane ((B.drop c).take n) i = leAt B (c + 8 * i) 8 := by
  rw [littleEndianLane_eq_sum, leAt, leNat]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [getD_take_drop, Nat.add_assoc]
  simp only [show 8 * i + k < n by omega, ite_true]

theorem readU32_drop {c : Nat} (hc : c ≤ B.length) :
    readU32 (B.drop c) = (rdU32 B c).map fun (v, c') ↦ (v, B.drop c') := by
  unfold readU32 rdU32
  rw [readBytes_drop hc]
  by_cases h : c + 4 ≤ B.length
  · simp only [h, ite_true]
    simp only [Option.map_some]
    congr
    rw [littleEndianLane_eq_sum, toNat_toUInt64 (lt_of_lt_of_le (sum_bytes_lt _ 8) (by norm_num)),
      leNat]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, getD_take_drop]
    simp
  · simp only [h, ite_false]
    rfl

theorem rdU32_le {c v c' : Nat} (h : rdU32 B c = some (v, c')) : c' ≤ B.length := by
  unfold rdU32 at h
  split at h
  · cases h; assumption
  · cases h

theorem rdU32_lt {c v c' : Nat} (h : rdU32 B c = some (v, c')) : v < 2 ^ 32 := by
  unfold rdU32 at h
  split at h
  · cases h; exact lt_of_lt_of_le (leNat_lt B c 4) (by norm_num)
  · cases h

theorem readU32s_drop (n : Nat) : ∀ {c : Nat}, c ≤ B.length →
    readU32s n (B.drop c) = (rdU32s B n c).map fun (v, c') ↦ (v, B.drop c') := by
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    simp only [readU32s, rdU32s, readU32_drop hc]
    cases h : rdU32 B c with
    | none => rfl
    | some p =>
      obtain ⟨v, c'⟩ := p
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rw [ih (rdU32_le h)]
      cases rdU32s B n c' with
      | none => rfl
      | some q => rfl

theorem rdU32s_le (n : Nat) : ∀ {c c' : Nat} {vs : List Nat}, c ≤ B.length →
    rdU32s B n c = some (vs, c') → c' ≤ B.length := by
  induction n with
  | zero => intro c c' vs hc h; cases h; exact hc
  | succ n ih =>
    intro c c' vs hc h
    simp only [rdU32s, Option.bind_eq_bind] at h
    cases h1 : rdU32 B c with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨v, c1⟩ := p
      simp only [h1, Option.bind_some] at h
      cases h2 : rdU32s B n c1 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨vs', c2⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        exact h.2 ▸ ih (rdU32_le h1) h2

theorem readWords_drop {c : Nat} (hc : c ≤ B.length) (n : Nat) :
    readWords n (B.drop c) = (rdWords B n c).map fun (v, c') ↦ (v, B.drop c') := by
  unfold readWords rdWords
  rw [readBytes_drop hc]
  by_cases h : c + 8 * n ≤ B.length
  · simp only [h, ite_true]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    refine List.map_congr_left fun i hi ↦ ?_
    rw [List.mem_range] at hi
    rw [lane_take_drop _ _ _ _ (by omega)]
  · simp only [h, ite_false]
    rfl

theorem rdWords_le {c n c' : Nat} {v : List K} (h : rdWords B n c = some (v, c')) :
    c' ≤ B.length := by
  unfold rdWords at h
  split at h
  · cases h; assumption
  · cases h

theorem digest_take_drop (B : List UInt8) (c : Nat) :
    #v[littleEndianLane ((B.drop c).take 32) 0, littleEndianLane ((B.drop c).take 32) 1,
      littleEndianLane ((B.drop c).take 32) 2, littleEndianLane ((B.drop c).take 32) 3] =
    (#v[leAt B c 8, leAt B (c + 8) 8, leAt B (c + 16) 8, leAt B (c + 24) 8] : Digest) := by
  have h0 := lane_take_drop B c 32 0 (by omega)
  have h1 := lane_take_drop B c 32 1 (by omega)
  have h2 := lane_take_drop B c 32 2 (by omega)
  have h3 := lane_take_drop B c 32 3 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show 8 * 2 = 16 from rfl,
    show 8 * 3 = 24 from rfl] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]

theorem readDigest_drop {c : Nat} (hc : c ≤ B.length) :
    readDigest (B.drop c) = (rdDigest B c).map fun (v, c') ↦ (v, B.drop c') := by
  unfold readDigest rdDigest
  rw [readBytes_drop hc]
  by_cases h : c + 32 ≤ B.length
  · simp only [h, ite_true, Option.map_some, digest_take_drop]
  · simp only [h, ite_false, Option.map_none]

theorem rdDigest_le {c c' : Nat} {v : Digest} (h : rdDigest B c = some (v, c')) :
    c' ≤ B.length := by
  unfold rdDigest at h
  split at h
  · cases h; assumption
  · cases h

theorem readRows_drop (w n : Nat) : ∀ {c : Nat}, c ≤ B.length →
    readRows w n (B.drop c) = (rdRows B w n c).map fun (v, c') ↦ (v, B.drop c') := by
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    simp only [readRows, rdRows, readWords_drop hc]
    cases h : rdWords B w c with
    | none => rfl
    | some p =>
      obtain ⟨v, c'⟩ := p
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rw [ih (rdWords_le h)]
      cases rdRows B w n c' with
      | none => rfl
      | some q => rfl

theorem rdRows_le (w n : Nat) : ∀ {c c' : Nat} {vs : List (List K)}, c ≤ B.length →
    rdRows B w n c = some (vs, c') → c' ≤ B.length := by
  induction n with
  | zero => intro c c' vs hc h; cases h; exact hc
  | succ n ih =>
    intro c c' vs hc h
    simp only [rdRows, Option.bind_eq_bind] at h
    cases h1 : rdWords B w c with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨v, c1⟩ := p
      simp only [h1, Option.bind_some] at h
      cases h2 : rdRows B w n c1 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨vs', c2⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        exact h.2 ▸ ih (rdWords_le h1) h2

theorem rdRows_length (w n : Nat) : ∀ {c c' : Nat} {vs : List (List K)},
    rdRows B w n c = some (vs, c') → vs.length = n ∧ ∀ r ∈ vs, r.length = w := by
  induction n with
  | zero => intro c c' vs h; cases h; simp
  | succ n ih =>
    intro c c' vs h
    simp only [rdRows, Option.bind_eq_bind] at h
    cases h1 : rdWords B w c with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨v, c1⟩ := p
      simp only [h1, Option.bind_some] at h
      cases h2 : rdRows B w n c1 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨vs', c2⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨hl, hw⟩ := ih h2
        refine ⟨by simp [hl], ?_⟩
        intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        · unfold rdWords at h1
          split at h1
          · cases h1; simp
          · cases h1
        · exact hw r hr

end NativeVm.Wire
