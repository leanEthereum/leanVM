module

public import LeanVMCircuits.Rec.Tables

@[expose] public section

/-!
What the recursion builder's row patterns mean, from the table theorems.

Each builder operation emits one row and holds some of its slots equal to other wires, which the bus's copy cycles
enforce. These theorems take those equalities as hypotheses on the row's slot values and state the operation's
meaning: an inverse, a sum, a packed word, the casts between digests, `E` elements and words, a hash row's
challenge, and a Merkle node's placement of its child.
-/

namespace LeanVMCircuits.Rec

/-- The four limbs slot `s` of a table carries on a row. -/
noncomputable def limbs (table : List (List Form)) (s : ℕ) (row : ℕ → K) (i : ℕ) : K :=
  ((table.getD s []).getD i .zero).eval row

theorem slotE_limbs (table : List (List Form)) (s : ℕ) (row : ℕ → K) :
    slotE row (table.getD s []) = toE (limbs table s row 0) (limbs table s row 1) (limbs table s row 2) := rfl

/-- `inv`: an `EMUL` row `a · i + 0` whose result is held to the constant one makes `i` the inverse of `a`, the
only one. -/
theorem inverse_row (row : ℕ → K)
    (hd : limbs emul arithD row 0 = 0 ∧ limbs emul arithD row 1 = 0 ∧ limbs emul arithD row 2 = 0)
    (hc : limbs emul arithC row 0 = 1 ∧ limbs emul arithC row 1 = 0 ∧ limbs emul arithC row 2 = 0) :
    slotE row (emul.getD arithA []) * slotE row (emul.getD arithB []) = 1 ∧
      ∀ j : E, slotE row (emul.getD arithA []) * j = 1 → j = slotE row (emul.getD arithB []) := by
  simp only [arithA, arithB, arithC, arithD] at hd hc ⊢
  have hspec := (emul_spec row).1
  have hd0 : slotE row (emul.getD 2 []) = 0 := by
    rw [slotE_limbs, hd.1, hd.2.1, hd.2.2]; simp [toE, emb_zero]
  have hc1 : slotE row (emul.getD 3 []) = 1 := by
    rw [slotE_limbs, hc.1, hc.2.1, hc.2.2]; simp [toE, emb, map_one]
  rw [hd0, add_zero, hc1] at hspec
  refine ⟨hspec.symm, fun j hj => ?_⟩
  calc j = 1 * j := (one_mul j).symm
    _ = (slotE row (emul.getD 1 []) * slotE row (emul.getD 0 [])) * j := by
      rw [mul_comm (slotE row (emul.getD 1 [])), ← hspec]
    _ = slotE row (emul.getD 1 []) := by rw [mul_assoc, hj, mul_one]

/-- `add`: an `EMUL` row whose second factor is held to one sums the other two slots. -/
theorem add_row (row : ℕ → K)
    (hb : limbs emul arithB row 0 = 1 ∧ limbs emul arithB row 1 = 0 ∧ limbs emul arithB row 2 = 0) :
    slotE row (emul.getD arithC []) = slotE row (emul.getD arithA []) + slotE row (emul.getD arithD []) := by
  simp only [arithA, arithB, arithC, arithD] at hb ⊢
  have hspec := (emul_spec row).1
  have hb1 : slotE row (emul.getD 1 []) = 1 := by
    rw [slotE_limbs, hb.1, hb.2.1, hb.2.2]; simp [toE, emb, map_one]
  rw [hspec, hb1, mul_one]

/-- `pack`: a `SPLIT` row whose bits past `n` are held to zero makes the word the number its first `n` bits spell. -/
theorem pack_row (row : ℕ → K) (hid : ∀ id ∈ splitIdentities, id.eval row = 0) (n : ℕ)
    (hzero : ∀ i, n ≤ i → i < 64 → row (1 + i) = 0) :
    (∀ i < 64, row (1 + i) = 0 ∨ row (1 + i) = 1) ∧ toWord (row 0) = num (bitsOf row) 64 ∧
      toWord (row 0) < 2 ^ n := by
  obtain ⟨hbits, hword⟩ := split_spec row hid
  refine ⟨hbits, hword, ?_⟩
  rw [hword]
  have hhigh : ∀ i, n ≤ i → (num (bitsOf row) 64).testBit i = false := by
    intro i hi
    by_cases h64 : i < 64
    · rw [testBit_num _ _ _ h64, bitsOf, hzero i hi h64]
      simp
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (num_lt _ 64) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  exact Nat.lt_pow_two_of_testBit _ hhigh

/-- The `CAST` row's views: one digest is the `E` element of its first three words, two 128-bit halves with a zero
top limb, and four words. -/
theorem cast_views (row : ℕ → K) :
    (∀ i : Fin 4, limbs cast castDigest row i = row i) ∧
      (∀ i : Fin 3, limbs cast castElement row i = row i) ∧ limbs cast castElement row 3 = 0 ∧
      (limbs cast castHalves row 0 = row 0 ∧ limbs cast castHalves row 1 = row 1 ∧ limbs cast castHalves row 2 = 0 ∧ limbs cast castHalves row 3 = 0) ∧
      (limbs cast (castHalves + 1) row 0 = row 2 ∧ limbs cast (castHalves + 1) row 1 = row 3 ∧ limbs cast (castHalves + 1) row 2 = 0 ∧ limbs cast (castHalves + 1) row 3 = 0) ∧
      ∀ w : Fin 4, limbs cast (castWords + w) row 0 = row w := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro i; fin_cases i <;> rfl)
    | (simp [castElement, castHalves, limbs, cast, dSlot, eSlot, kSlot, Form.eval, Form.zero, ofWord_zero])

/-- A hash row's challenge is the `E` element of its output's first three words, and its output slot the digest of
its four output words. -/
theorem hash_outputs (row : ℕ → K) :
    (∀ i : Fin 4, limbs hash hashSlotOut row i = row (hashO + i)) ∧ (∀ i : Fin 3, limbs hash hashSlotCh row i = row (hashO + i)) ∧
      limbs hash hashSlotCh row 3 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (intro i; fin_cases i <;> rfl)
    | (simp [hashSlotCh, limbs, hash, dSlot, eSlot, Form.eval, Form.zero, ofWord_zero])

/-- `node`: when a hash row's mux slot is held to the digest `acc`, `acc` is the message's first half at bit 0 and
its second half at bit 1. -/
theorem node_row (row : ℕ → K) (hid : ∀ id ∈ hashIdentities, id.eval row = 0) (acc : Fin 4 → K)
    (hmux : ∀ i : Fin 4, limbs hash hashSlotMux row i = acc i) :
    (row hashSel = 0 ∧ ∀ i : Fin 4, row (hashM + i) = acc i) ∨
      (row hashSel = 1 ∧ ∀ i : Fin 4, row (hashM + 4 + i) = acc i) := by
  have hb := (hash_mux row hid 0 (by norm_num)).2
  rcases hb with h | h
  · refine Or.inl ⟨h, fun i => ?_⟩
    have := (hash_mux row hid i i.isLt).1
    rw [h, if_pos rfl] at this
    rw [← this]; exact hmux i
  · refine Or.inr ⟨h, fun i => ?_⟩
    have := (hash_mux row hid i i.isLt).1
    rw [h, if_neg one_ne_zero] at this
    rw [← this]; exact hmux i

end LeanVMCircuits.Rec
