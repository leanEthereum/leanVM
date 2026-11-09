module

public import LeanDa.Scheme
public import LeanDa.Defs
public import LeanDa.WithHash
public import LeanDa.Commitment

@[expose] public section

/-!
# The Merkle commitment to the cells

For every hash function `H`. An honest opening verifies (`verifyCell_openCell`). Two openings of
one commitment at one position to two different cells give an `H` collision, which
`findCollision` computes: climb both openings' hash inputs from the cells' bytes up to the root's,
and return the first pair of inputs that differ while their hashes agree
(`findCollision_spec`). The cells' bytes differ because a cell's encoding is injective
(`cellBytes_injective`), and the roots' inputs hash alike, so such a level exists.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

namespace LeanDa

variable (H : List UInt8 → Common.DigestBytes)

/-! ## Byte encodings are injective -/

theorem pairBytes_injective {a b c d : Common.DigestBytes} (h : pairBytes a b = pairBytes c d) :
    a = c ∧ b = d := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, Vector.toList_inj.mp h2⟩

theorem length_kBytes (a : K) : (LeanVM.Parameters.K.toBytes a).length = 8 := by simp [toBytes_eq_shift]

theorem testBit_kBytes (a : K) {t j : ℕ} (ht : t < 8) (hj : j < 8) :
    ((((LeanVM.Parameters.K.toBytes a)[t]'(by simp [toBytes_eq_shift, ht])).toNat).testBit j) = a.toBitVec.toNat.testBit (8 * t + j) := by
  simp only [toBytes_eq_shift, List.getElem_map, List.getElem_range, Nat.toUInt8_eq, UInt8.toNat_ofNat']
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hj]

theorem kBytes_injective : Function.Injective LeanVM.Parameters.K.toBytes := by
  intro a b h
  apply BF64.ext
  apply BitVec.eq_of_toNat_eq
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  by_cases hi : i < 64
  · have ht : i / 8 < 8 := by omega
    have hj : i % 8 < 8 := by omega
    have hab := congrArg (fun l ↦ ((l[i / 8]?).getD 0).toNat.testBit (i % 8)) h
    rw [List.getElem?_eq_getElem (by simp [toBytes_eq_shift, ht]), List.getElem?_eq_getElem (by simp [toBytes_eq_shift, ht]),
      Option.getD_some, Option.getD_some, testBit_kBytes a ht hj, testBit_kBytes b ht hj] at hab
    rwa [show 8 * (i / 8) + i % 8 = i by omega] at hab
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le a.toBitVec.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b.toBitVec.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem flatMap_kBytes_injective {l₁ l₂ : List K} (hl : l₁.length = l₂.length)
    (h : l₁.flatMap LeanVM.Parameters.K.toBytes = l₂.flatMap LeanVM.Parameters.K.toBytes) : l₁ = l₂ := by
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

theorem walk_merklePath (d : ℕ) (f : ℕ → Common.DigestBytes) (idx : ℕ) (h : idx < 2 ^ d) :
    walk H idx (f idx) (merklePathWithHash H d f idx) = merkleRootWithHash H d f := by
  induction d generalizing f idx with
  | zero =>
    obtain rfl : idx = 0 := by simpa using h
    rfl
  | succ d ih =>
    rw [merklePathWithHash, walk, merkleRootWithHash, ← ih (upWithHash H f) (idx / 2) (by rw [pow_succ] at h; omega)]
    congr 1
    unfold upWithHash sibling
    rcases Nat.mod_two_eq_zero_or_one idx with h2 | h2
    · simp only [h2, ↓reduceIte]
      rw [show 2 * (idx / 2) = idx by omega]
    · have h2' : ¬idx % 2 = 0 := by omega
      simp only [h2', ↓reduceIte]
      rw [show 2 * (idx / 2) + 1 = idx by omega, show 2 * (idx / 2) = idx - 1 by omega]

theorem length_merklePath (d : ℕ) (f : ℕ → Common.DigestBytes) (idx : ℕ) :
    (merklePathWithHash H d f idx).length = d := by
  induction d generalizing f idx with
  | zero => rfl
  | succ d ih => simp [merklePathWithHash, ih]


/-- A climb reads the index's low bits only, one per sibling. -/
theorem walk_mod : ∀ (path : List Common.DigestBytes) (idx : ℕ) (node : Common.DigestBytes),
    walk H idx node path = walk H (idx % 2 ^ path.length) node path
  | [], _, _ => rfl
  | s :: rest, idx, node => by
    have h2 : idx % 2 ^ (rest.length + 1) % 2 = idx % 2 := by
      rw [pow_succ, Nat.mod_mul_left_mod]
    have hd : idx % 2 ^ (rest.length + 1) / 2 % 2 ^ rest.length = idx / 2 % 2 ^ rest.length := by
      rw [pow_succ', Nat.mod_mul_right_div_self, Nat.mod_mod]
    rw [List.length_cons, walk, walk, h2, walk_mod rest (idx / 2), walk_mod rest (idx % _ / 2), hd]

/-- A climb along two paths in turn. -/
theorem walk_append : ∀ (l₁ l₂ : List Common.DigestBytes) (idx : ℕ) (node : Common.DigestBytes),
    walk H idx node (l₁ ++ l₂) = walk H (idx / 2 ^ l₁.length) (walk H idx node l₁) l₂
  | [], _, _, _ => by simp [walk]
  | s :: rest, l₂, idx, node => by
    rw [List.cons_append, walk, walk, walk_append rest l₂, List.length_cons, pow_succ',
      Nat.div_div_eq_div_mul]

theorem cellLeaves_position {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    cellLeavesWithHash H c (positionRow p) (positionCell p) = cellDigestWithHash H (c p) := by
  have h1 : (positionRow p : ℕ) < r := (positionRow p).isLt
  have h2 : (positionCell p : ℕ) < 128 := (positionCell p).isLt
  rw [cellLeavesWithHash]
  simp only [paddedCell, h1, h2, and_self, ↓reduceDIte]
  congr 2
  apply Fin.ext
  simp only [cellPosition, positionRow, positionCell]
  omega

/-- **An honest opening verifies.** -/
theorem verifyCell_openCell {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    verifyCell H r (commitCellsWithHash H c) p (c p) (openCellWithHash H c p) = true := by
  simp only [verifyCell, Bool.and_eq_true, decide_eq_true_eq]
  have hrow : (positionRow p : ℕ) < 2 ^ logPaddedRowCount r :=
    lt_of_lt_of_le (positionRow p).isLt (le_nPad r)
  refine ⟨by simp only [openCellWithHash, List.length_append, length_merklePath], ?_⟩
  simp only [openCellWithHash]
  rw [walk_append, length_merklePath, walk_mod H (merklePathWithHash H 7 _ _) (p : ℕ), length_merklePath,
    show (p : ℕ) % 2 ^ 7 = positionCell p from rfl, ← cellLeaves_position H c p,
    walk_merklePath H _ _ _ (positionCell p).isLt, show (p : ℕ) / 2 ^ 7 = positionRow p from rfl]
  exact walk_merklePath H _ (blobRootWithHash H c) _ hrow

/-! ## Collisions from two openings -/

theorem findCollision_spec (idx : ℕ) (a b : List UInt8) (p q : List Common.DigestBytes)
    (hlen : p.length = q.length) (hab : a ≠ b)
    (hroot : walk H idx (H a) p = walk H idx (H b) q) :
    (findCollision H (hashInputs H idx a p) (hashInputs H idx b q)).1 ≠
        (findCollision H (hashInputs H idx a p) (hashInputs H idx b q)).2 ∧
      H (findCollision H (hashInputs H idx a p) (hashInputs H idx b q)).1 =
        H (findCollision H (hashInputs H idx a p) (hashInputs H idx b q)).2 := by
  induction p generalizing idx a b q with
  | nil =>
    obtain rfl : q = [] := List.eq_nil_of_length_eq_zero hlen.symm
    simp only [walk] at hroot
    simp [hashInputs, findCollision, hab, hroot]
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

/-- **Two verifying openings of one position to different cells give a collision.** -/
theorem openingsCollision_spec {r : ℕ} {com : Common.DigestBytes} {p : Fin (r * 128)} {x x' : Cell}
    {τ τ' : CellOpening} (hx : x ≠ x') (hτ : verifyCell H r com p x τ = true)
    (hτ' : verifyCell H r com p x' τ' = true) :
    (openingsCollision H r p x τ x' τ').1 ≠ (openingsCollision H r p x τ x' τ').2 ∧
      H (openingsCollision H r p x τ x' τ').1 = H (openingsCollision H r p x τ x' τ').2 := by
  simp only [verifyCell, Bool.and_eq_true, decide_eq_true_eq] at hτ hτ'
  exact findCollision_spec H _ _ _ _ _ (hτ.1.trans hτ'.1.symm)
    (fun h ↦ hx (cellBytes_injective h)) (hτ.2.trans hτ'.2.symm)

end LeanDa
