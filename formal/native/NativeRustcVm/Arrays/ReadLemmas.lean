module

public import NativeRustcVm.Arrays.Read

/-!
# Reading arrays back

What the readers of `NativeRustcVm.Arrays.Read` give where memory holds known values: a word's
bytes read back as the word (`wordOf_of_wordAt`), arrays as their elements (`wordsOf_of_wordsAt`,
`ewsOf_of_ewsAt`); the readers' elements (`getElem_ewsOf`) and their dependence on the bytes read
only (`ewsOf_congr`); arrays in memory one element at a time (`ewsAt_append`, `ewsAt_getElem`).
-/

namespace NativeRustcVm

open NativeVm.Model

public section

theorem addr_add (a : BitVec 64) (i j : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Words -/

theorem leNat_cons (b : UInt8) (bs : List UInt8) : leNat (b :: bs) = b.toNat + 256 * leNat bs :=
  rfl

/-- The little-endian number of the `n` low bytes of `x`. -/
theorem leNat_bytes (n x : Nat) :
    leNat ((List.range n).map fun k ↦ UInt8.ofNat (x / 2 ^ (8 * k))) = x % 2 ^ (8 * n) := by
  induction n generalizing x with
  | zero => simp [leNat, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, leNat_cons]
    have h := ih (x / 256)
    have hf : ((fun k ↦ UInt8.ofNat (x / 2 ^ (8 * k))) ∘ Nat.succ) =
        fun k ↦ UInt8.ofNat (x / 256 / 2 ^ (8 * k)) := by
      funext k
      simp only [Function.comp, Nat.div_div_eq_div_mul]
      congr 2
      rw [show 8 * (k + 1) = 8 + 8 * k by omega, Nat.pow_add]
    rw [hf, h, Nat.mul_zero, Nat.pow_zero, Nat.div_one, UInt8.toNat_ofNat',
      show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add, Nat.mod_mul]

theorem wordBytes_eq (w : UInt64) :
    wordBytes w = (List.range 8).map fun k ↦ UInt8.ofNat (w.toNat / 2 ^ (8 * k)) := by
  unfold wordBytes LeanVM.Protocol.KeccakHash.wordBytes
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  apply UInt8.toNat.inj
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt8.toNat_ofNat']
  have h8 : (8 * k).toUInt64.toNat % 64 = 8 * k := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [h8, Nat.shiftRight_eq_div_pow]

theorem leNat_wordBytes (w : UInt64) : leNat (wordBytes w) = w.toNat := by
  rw [wordBytes_eq, leNat_bytes]
  exact Nat.mod_eq_of_lt w.toNat_lt

theorem length_wordBytes (w : UInt64) : (wordBytes w).length = 8 := by
  simp [wordBytes, LeanVM.Protocol.KeccakHash.wordBytes]

theorem length_ewBytes (x : EW) : (ewBytes x).length = 16 := by
  simp [ewBytes, length_wordBytes]

/-- The bytes read where they are `bs`. -/
theorem bytesFrom_of_bytesAt {d : Mem 64} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d a bs) : bytesFrom d a bs.length = bs := by
  apply List.ext_getElem (by simp [bytesFrom])
  intro i h1 h2
  simp only [bytesFrom, List.getElem_map, List.getElem_range]
  rw [h i h2]
  rfl

theorem wordOf_of_wordAt {d : Mem 64} {a : BitVec 64} {w : UInt64} (h : WordAt d a w) :
    wordOf d a = w := by
  have := bytesFrom_of_bytesAt h
  rw [length_wordBytes] at this
  rw [wordOf, this, leNat_wordBytes]
  exact UInt64.ofNat_toNat

/-! ## Arrays in memory -/

theorem bytesAt_append {d : Mem 64} {a : BitVec 64} {l₁ l₂ : List UInt8} :
    BytesAt d a (l₁ ++ l₂) ↔ BytesAt d a l₁ ∧ BytesAt d (a + BitVec.ofNat 64 l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · rw [addr_add, h _ (by simp; omega), List.getElem_append_right (by omega)]
      simp
  · intro ⟨h₁, h₂⟩ i hi
    by_cases hi1 : i < l₁.length
    · rw [h₁ i hi1, List.getElem_append_left hi1]
    · have := h₂ (i - l₁.length) (by simp at hi; omega)
      rw [addr_add, Nat.add_sub_cancel' (by omega)] at this
      rw [this, List.getElem_append_right (by omega)]

theorem ewsAt_nil (d : Mem 64) (a : BitVec 64) : EWsAt d a [] := fun _ h ↦ absurd h (by simp)

theorem ewsAt_append {d : Mem 64} {a : BitVec 64} {xs ys : List EW} :
    EWsAt d a (xs ++ ys) ↔ EWsAt d a xs ∧ EWsAt d (a + BitVec.ofNat 64 (16 * xs.length)) ys := by
  unfold EWsAt
  rw [List.flatMap_append, bytesAt_append]
  have : (xs.flatMap ewBytes).length = 16 * xs.length := by
    rw [List.length_flatMap]
    simp [length_ewBytes, Nat.mul_comm]
  rw [this]

theorem ewsAt_singleton {d : Mem 64} {a : BitVec 64} {x : EW} :
    EWsAt d a [x] ↔ EWAt d a x := by
  simp [EWsAt, EWAt]

theorem ewAt_iff {d : Mem 64} {a : BitVec 64} {x : EW} :
    EWAt d a x ↔ WordAt d a x.c0 ∧ WordAt d (a + 8#64) x.c1 := by
  unfold EWAt ewBytes WordAt
  rw [bytesAt_append, length_wordBytes]

theorem ewsAt_getElem {d : Mem 64} {a : BitVec 64} {xs : List EW} (h : EWsAt d a xs) {i : Nat}
    (hi : i < xs.length) : EWAt d (a + BitVec.ofNat 64 (16 * i)) xs[i] := by
  have hx : xs = xs.take i ++ ([xs[i]] ++ xs.drop (i + 1)) := by simp
  rw [hx, ewsAt_append, ewsAt_append, ewsAt_singleton] at h
  have hl : (xs.take i).length = i := by simp; omega
  rw [hl] at h
  exact h.2.1

/-! ## The readers -/

@[simp] theorem length_ewsOf (d : Mem 64) (a : BitVec 64) (n : Nat) : (ewsOf d a n).length = n := by
  simp [ewsOf]

@[simp] theorem getElem_ewsOf (d : Mem 64) (a : BitVec 64) (n i : Nat) (h : i < (ewsOf d a n).length) :
    (ewsOf d a n)[i] = ewOf d (a + BitVec.ofNat 64 (16 * i)) := by
  simp [ewsOf]

@[simp] theorem length_wordsOf (d : Mem 64) (a : BitVec 64) (n : Nat) :
    (wordsOf d a n).length = n := by
  simp [wordsOf]

@[simp] theorem getElem_wordsOf (d : Mem 64) (a : BitVec 64) (n i : Nat)
    (h : i < (wordsOf d a n).length) :
    (wordsOf d a n)[i] = wordOf d (a + BitVec.ofNat 64 (8 * i)) := by
  simp [wordsOf]

theorem ewOf_of_ewAt {d : Mem 64} {a : BitVec 64} {x : EW} (h : EWAt d a x) : ewOf d a = x := by
  rw [ewAt_iff] at h
  rw [ewOf, wordOf_of_wordAt h.1, wordOf_of_wordAt h.2]

theorem ewsOf_of_ewsAt {d : Mem 64} {a : BitVec 64} {xs : List EW} (h : EWsAt d a xs) :
    ewsOf d a xs.length = xs := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [getElem_ewsOf, ewOf_of_ewAt (ewsAt_getElem h h2)]

theorem wordsAt_append {d : Mem 64} {a : BitVec 64} {xs ys : List UInt64} :
    WordsAt d a (xs ++ ys) ↔ WordsAt d a xs ∧ WordsAt d (a + BitVec.ofNat 64 (8 * xs.length)) ys := by
  unfold WordsAt
  rw [List.flatMap_append, bytesAt_append]
  have : (xs.flatMap wordBytes).length = 8 * xs.length := by
    rw [List.length_flatMap]
    simp [length_wordBytes, Nat.mul_comm]
  rw [this]

theorem wordsAt_nil (d : Mem 64) (a : BitVec 64) : WordsAt d a [] := fun _ h ↦ absurd h (by simp)

theorem wordsAt_singleton {d : Mem 64} {a : BitVec 64} {x : UInt64} :
    WordsAt d a [x] ↔ WordAt d a x := by
  simp [WordsAt, WordAt]

theorem wordsAt_getElem {d : Mem 64} {a : BitVec 64} {xs : List UInt64} (h : WordsAt d a xs)
    {i : Nat} (hi : i < xs.length) : WordAt d (a + BitVec.ofNat 64 (8 * i)) xs[i] := by
  have hx : xs = xs.take i ++ ([xs[i]] ++ xs.drop (i + 1)) := by simp
  rw [hx, wordsAt_append, wordsAt_append, wordsAt_singleton] at h
  have hl : (xs.take i).length = i := by simp; omega
  rw [hl] at h
  exact h.2.1

theorem wordsOf_of_wordsAt {d : Mem 64} {a : BitVec 64} {xs : List UInt64} (h : WordsAt d a xs) :
    wordsOf d a xs.length = xs := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [getElem_wordsOf, wordOf_of_wordAt (wordsAt_getElem h h2)]

/-- A word read depends on its eight bytes only. -/
theorem wordOf_congr {d d' : Mem 64} {a : BitVec 64}
    (h : ∀ i < 8, d'.get? (a + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i)) :
    wordOf d' a = wordOf d a := by
  unfold wordOf bytesFrom
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem ewOf_congr {d d' : Mem 64} {a : BitVec 64}
    (h : ∀ i < 16, d'.get? (a + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i)) :
    ewOf d' a = ewOf d a := by
  unfold ewOf
  rw [wordOf_congr (d := d) (fun i hi ↦ h i (by omega)),
    wordOf_congr (d := d) (a := a + 8#64) fun i hi ↦ by
      rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add]
      exact h _ (by omega)]

/-- The elements read depend on their bytes only. -/
theorem ewsOf_congr {d d' : Mem 64} {a : BitVec 64} {n : Nat}
    (h : ∀ i < 16 * n, d'.get? (a + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i)) :
    ewsOf d' a n = ewsOf d a n := by
  unfold ewsOf
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact ewOf_congr fun j hj ↦ by rw [addr_add]; exact h _ (by omega)

theorem wordsOf_congr {d d' : Mem 64} {a : BitVec 64} {n : Nat}
    (h : ∀ i < 8 * n, d'.get? (a + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i)) :
    wordsOf d' a n = wordsOf d a n := by
  unfold wordsOf
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact wordOf_congr fun j hj ↦ by rw [addr_add]; exact h _ (by omega)

/-! ## Mapped memory read back -/

/-- The bytes of the word of eight bytes are they. -/
theorem wordBytes_ofNat_leNat_eight {bs : List UInt8} (h : bs.length = 8) :
    wordBytes (UInt64.ofNat (leNat bs)) = bs := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
    simp only [leNat, wordBytes, LeanVM.Protocol.KeccakHash.wordBytes, List.range_succ,
      List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, List.cons_append, List.cons.injEq, and_true]
    simp only [← UInt8.toNat_inj]
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    omega

/-- Mapped bytes hold the word `wordOf` reads. -/
theorem wordAt_of_mapped {d : Mem 64} {a : BitVec 64} (h : Mapped d a 8) :
    WordAt d a (wordOf d a) := by
  have hl : (bytesFrom d a 8).length = 8 := by simp [bytesFrom]
  unfold WordAt wordOf
  rw [wordBytes_ofNat_leNat_eight hl]
  intro i hi
  simp only [bytesFrom, List.getElem_map, List.getElem_range]
  have := h i (by rw [hl] at hi; exact hi)
  revert this
  cases d.get? (a + BitVec.ofNat 64 i) <;> simp

/-- Mapped bytes hold the `E` element `ewOf` reads. -/
theorem ewAt_of_mapped {d : Mem 64} {a : BitVec 64} (h : Mapped d a 16) : EWAt d a (ewOf d a) :=
  ewAt_iff.mpr ⟨wordAt_of_mapped fun i hi ↦ h i (by omega), wordAt_of_mapped fun i hi ↦ by
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add]; exact h _ (by omega)⟩

/-- Mapped bytes hold the `E` elements `ewsOf` reads. -/
theorem ewsAt_of_mapped {d : Mem 64} {a : BitVec 64} {n : Nat} (h : Mapped d a (16 * n)) :
    EWsAt d a (ewsOf d a n) := by
  induction n with
  | zero => exact ewsAt_nil d a
  | succ n ih =>
    have e : ewsOf d a (n + 1) = ewsOf d a n ++ [ewOf d (a + BitVec.ofNat 64 (16 * n))] := by
      simp [ewsOf, List.range_succ]
    rw [e, ewsAt_append, ewsAt_singleton, length_ewsOf]
    exact ⟨ih fun i hi ↦ h i (by omega), ewAt_of_mapped fun i hi ↦ by
      rw [addr_add]; exact h _ (by omega)⟩

/-- Mapped bytes hold the words `wordsOf` reads. -/
theorem wordsAt_of_mapped {d : Mem 64} {a : BitVec 64} {n : Nat} (h : Mapped d a (8 * n)) :
    WordsAt d a (wordsOf d a n) := by
  induction n with
  | zero => exact wordsAt_nil d a
  | succ n ih =>
    have e : wordsOf d a (n + 1) = wordsOf d a n ++ [wordOf d (a + BitVec.ofNat 64 (8 * n))] := by
      simp [wordsOf, List.range_succ]
    rw [e, wordsAt_append, wordsAt_singleton, length_wordsOf]
    exact ⟨ih fun i hi ↦ h i (by omega), wordAt_of_mapped fun i hi ↦ by
      rw [addr_add]; exact h _ (by omega)⟩

end

end NativeRustcVm
