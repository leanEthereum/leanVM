import LeanDa.Scheme

/-!
# The Merkle commitment to the cells

For every hash function `H`. An honest opening verifies (`verifyCell_openCell`). Two openings of
one commitment at one position to two different cells give an `H` collision, which
`findCollision` computes: climb both openings' hash inputs from the cells' bytes up to the root's
`rowRoot ‖ colRoot`, and return the first pair of inputs that differ while their hashes agree
(`findCollision_spec`). The cells' bytes differ because a cell's encoding is injective
(`cellBytes_injective`), and the roots' inputs hash alike, so such a level exists.
-/

namespace LeanDa

variable (H : List UInt8 → Digest)

/-! ## Byte encodings are injective -/

theorem pairBytes_injective {a b c d : Digest} (h : pairBytes a b = pairBytes c d) :
    a = c ∧ b = d := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, Vector.toList_inj.mp h2⟩

theorem length_kBytes (a : K) : (kBytes a).length = 8 := by simp [kBytes]

theorem testBit_kBytes (a : K) {t j : ℕ} (ht : t < 8) (hj : j < 8) :
    ((((kBytes a)[t]'(by simp [kBytes, ht])).toNat).testBit j) = a.toBitVec.toNat.testBit (8 * t + j) := by
  simp only [kBytes, List.getElem_map, List.getElem_range, Nat.toUInt8_eq, UInt8.toNat_ofNat']
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hj]

theorem kBytes_injective : Function.Injective kBytes := by
  intro a b h
  apply BF64.ext
  apply BitVec.eq_of_toNat_eq
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  by_cases hi : i < 64
  · have ht : i / 8 < 8 := by omega
    have hj : i % 8 < 8 := by omega
    have hab := congrArg (fun l ↦ ((l[i / 8]?).getD 0).toNat.testBit (i % 8)) h
    rw [List.getElem?_eq_getElem (by simp [kBytes, ht]), List.getElem?_eq_getElem (by simp [kBytes, ht]),
      Option.getD_some, Option.getD_some, testBit_kBytes a ht hj, testBit_kBytes b ht hj] at hab
    rwa [show 8 * (i / 8) + i % 8 = i by omega] at hab
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le a.toBitVec.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b.toBitVec.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem flatMap_kBytes_injective {l₁ l₂ : List K} (hl : l₁.length = l₂.length)
    (h : l₁.flatMap kBytes = l₂.flatMap kBytes) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a as ih =>
    cases l₂ with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.flatMap_cons] at h
      obtain ⟨hab, hrest⟩ := List.append_inj h (by rw [length_kBytes, length_kBytes])
      rw [kBytes_injective hab, ih (by simpa using hl) hrest]

theorem cellBytes_injective : Function.Injective cellBytes := by
  intro x y h
  exact List.ofFn_injective (flatMap_kBytes_injective (by rw [List.length_ofFn, List.length_ofFn]) h)

/-! ## Completeness -/

theorem walk_merklePath (d : ℕ) (f : ℕ → Digest) (idx : ℕ) (h : idx < 2 ^ d) :
    walk H idx (f idx) (merklePath H d f idx) = merkleRoot H d f := by
  induction d generalizing f idx with
  | zero =>
    obtain rfl : idx = 0 := by simpa using h
    rfl
  | succ d ih =>
    rw [merklePath, walk, merkleRoot, ← ih (up H f) (idx / 2) (by rw [pow_succ] at h; omega)]
    congr 1
    unfold up sibling
    rcases Nat.mod_two_eq_zero_or_one idx with h2 | h2
    · simp only [h2, ↓reduceIte]
      rw [show 2 * (idx / 2) = idx by omega]
    · have h2' : ¬idx % 2 = 0 := by omega
      simp only [h2', ↓reduceIte]
      rw [show 2 * (idx / 2) + 1 = idx by omega, show 2 * (idx / 2) = idx - 1 by omega]

theorem length_merklePath (d : ℕ) (f : ℕ → Digest) (idx : ℕ) :
    (merklePath H d f idx).length = d := by
  induction d generalizing f idx with
  | zero => rfl
  | succ d ih => simp [merklePath, ih]

theorem le_nPad (r : ℕ) : r ≤ nPad r := Nat.le_pow_clog (by norm_num) r

theorem colLeaves_colIndex {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    colLeaves H c (colIndex p) = cellDigest H (c p) := by
  have hr := le_nPad r
  have hrow : (posRow p : ℕ) < nPad r := lt_of_lt_of_le (posRow p).isLt hr
  have hmod : colIndex p % nPad r = posRow p := by
    rw [colIndex, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrow]
  have hdiv : colIndex p / nPad r = posCell p := by
    rw [colIndex, Nat.add_comm, Nat.add_mul_div_right _ _ (by unfold nPad; positivity),
      Nat.div_eq_of_lt hrow, Nat.zero_add]
  have h1 : (posRow p : ℕ) < r := (posRow p).isLt
  have h2 : (posCell p : ℕ) < 128 := (posCell p).isLt
  rw [colLeaves, hmod, hdiv]
  simp only [paddedCell, h1, h2, and_self, ↓reduceDIte]
  congr 2
  apply Fin.ext
  simp only [pos, posRow, posCell]
  omega

theorem colIndex_lt {r : ℕ} (p : Fin (r * 128)) : colIndex p < 2 ^ (7 + logPad r) := by
  have hrow : (posRow p : ℕ) < nPad r := lt_of_lt_of_le (posRow p).isLt (le_nPad r)
  have hcell := (posCell p).isLt
  rw [pow_add, colIndex]
  unfold nPad at hrow ⊢
  nlinarith

/-- **An honest opening verifies.** -/
theorem verifyCell_openCell {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    verifyCell H r (commitCells H c) p (c p) (openCell H c p) = true := by
  simp only [verifyCell, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨length_merklePath H _ _ _, ?_⟩
  simp only [openCell]
  rw [← colLeaves_colIndex H c p, walk_merklePath H _ _ _ (colIndex_lt p)]
  rfl

/-! ## Collisions from two openings -/

/-- The hash inputs from a cell's bytes `a` at index `idx` up to the root, the last one
`rowRoot ‖ colRoot`. -/
def hashInputs : ℕ → List UInt8 → List Digest → Digest → List (List UInt8)
  | _, a, [], rr => [a, pairBytes rr (H a)]
  | idx, a, s :: rest, rr =>
    a :: hashInputs (idx / 2) (if idx % 2 = 0 then pairBytes (H a) s else pairBytes s (H a)) rest rr

/-- The first pair of inputs, level by level, that differ and hash alike. -/
def findCollision : List (List UInt8) → List (List UInt8) → List UInt8 × List UInt8
  | a :: as, b :: bs => if a ≠ b ∧ H a = H b then (a, b) else findCollision as bs
  | _, _ => ([], [])

theorem findCollision_spec (idx : ℕ) (a b : List UInt8) (p q : List Digest) (rp rq : Digest)
    (hlen : p.length = q.length) (hab : a ≠ b)
    (hroot : H (pairBytes rp (walk H idx (H a) p)) = H (pairBytes rq (walk H idx (H b) q))) :
    (findCollision H (hashInputs H idx a p rp) (hashInputs H idx b q rq)).1 ≠
        (findCollision H (hashInputs H idx a p rp) (hashInputs H idx b q rq)).2 ∧
      H (findCollision H (hashInputs H idx a p rp) (hashInputs H idx b q rq)).1 =
        H (findCollision H (hashInputs H idx a p rp) (hashInputs H idx b q rq)).2 := by
  induction p generalizing idx a b q with
  | nil =>
    obtain rfl : q = [] := List.eq_nil_of_length_eq_zero hlen.symm
    simp only [hashInputs, findCollision]
    by_cases hH : H a = H b
    · simp [hab, hH]
    · have hne : pairBytes rp (H a) ≠ pairBytes rq (H b) := fun h ↦ hH (pairBytes_injective h).2
      simp only [walk] at hroot
      simp [hab, hH, hne, hroot]
  | cons s rest ih =>
    obtain ⟨s', rest', rfl⟩ : ∃ s' rest', q = s' :: rest' := by
      cases q with
      | nil => simp at hlen
      | cons s' rest' => exact ⟨s', rest', rfl⟩
    simp only [hashInputs, findCollision]
    by_cases hH : H a = H b
    · simp [hab, hH]
    · simp only [hH, and_false, ↓reduceIte]
      refine ih (idx / 2) _ _ rest' (by simpa using hlen) ?_ ?_
      · intro h
        split_ifs at h
        · exact hH (pairBytes_injective h).1
        · exact hH (pairBytes_injective h).2
      · simp only [walk] at hroot
        rwa [← apply_ite H, ← apply_ite H] at hroot

/-- The collision two openings of one position give. -/
def openingsCollision (r : ℕ) (p : Fin (r * 128)) (x : Cell) (τ : Opening) (x' : Cell)
    (τ' : Opening) : List UInt8 × List UInt8 :=
  findCollision H (hashInputs H (colIndex p) (cellBytes x) τ.path τ.rowRoot)
    (hashInputs H (colIndex p) (cellBytes x') τ'.path τ'.rowRoot)

/-- **Two verifying openings of one position to different cells give a collision.** -/
theorem openingsCollision_spec {r : ℕ} {com : Digest} {p : Fin (r * 128)} {x x' : Cell}
    {τ τ' : Opening} (hx : x ≠ x') (hτ : verifyCell H r com p x τ = true)
    (hτ' : verifyCell H r com p x' τ' = true) :
    (openingsCollision H r p x τ x' τ').1 ≠ (openingsCollision H r p x τ x' τ').2 ∧
      H (openingsCollision H r p x τ x' τ').1 = H (openingsCollision H r p x τ x' τ').2 := by
  simp only [verifyCell, Bool.and_eq_true, decide_eq_true_eq] at hτ hτ'
  exact findCollision_spec H _ _ _ _ _ _ _ (hτ.1.trans hτ'.1.symm)
    (fun h ↦ hx (cellBytes_injective h)) (hτ.2.trans hτ'.2.symm)

end LeanDa
