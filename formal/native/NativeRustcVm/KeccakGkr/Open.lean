module

public import NativeVm.Math.Keccak.Facts

/-!
# `keccak_open`'s in-place fold is `keccakOpen`'s

`keccakOpen` folds the 64 slot rows by the slot's challenges into ever shorter arrays
(`openStep`); the Rust folds them in place, rows `i < size / 2` becoming the fold of rows `2 i` and
`2 i + 1` (`foldRow`), which no earlier write of the round touched (`2 i ≥ i`). Row by row
(`openRows c t`, the rows after the first `t` challenges): `openRows_succ_getD`.

And the slot weights end to end (`rowsFlat`): entry `64 r + z` is `slotRow`'s
(`rowsFlat_slotWeights`).
-/

namespace NativeRustcVm.KeccakGkr

open NativeVm.Model NativeVm.Math.Keccak

@[expose] public section

/-- Two rows folded by a challenge: `lo + c (lo + hi)`, entry by entry. -/
def foldRow (c : EW) (lo hi : Array EW) : Array EW :=
  Array.zipWith (fun lo hi ↦ lo + c * (lo + hi)) lo hi

/-- One round of `keccakOpen`'s fold. -/
def openStep (rows : Array (Array EW)) (c : EW) : Array (Array EW) :=
  (Array.range (rows.size / 2)).map fun i ↦ foldRow c (rows.getD (2 * i) #[]) (rows.getD (2 * i + 1) #[])

/-- The rows after the first `t` challenges of `slot`. -/
def openRows (slot : Array EW) (rows : Array (Array EW)) (t : Nat) : Array (Array EW) :=
  (slot.toList.take t).foldl openStep rows

end

public section

theorem openRows_zero (slot : Array EW) (rows : Array (Array EW)) :
    openRows slot rows 0 = rows := by
  simp [openRows]

theorem openRows_succ (slot : Array EW) (rows : Array (Array EW)) {t : Nat} (ht : t < slot.size) :
    openRows slot rows (t + 1) = openStep (openRows slot rows t) (slot.getD t 0) := by
  rw [openRows, openRows, List.take_add_one, List.foldl_append]
  rw [List.getElem?_eq_getElem (by simpa using ht)]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]

theorem openStep_size (rows : Array (Array EW)) (c : EW) :
    (openStep rows c).size = rows.size / 2 := by
  simp [openStep]

theorem openRows_size (slot : Array EW) (rows : Array (Array EW)) {t : Nat} (ht : t ≤ slot.size) :
    (openRows slot rows t).size = rows.size / 2 ^ t := by
  induction t with
  | zero => simp [openRows_zero]
  | succ t ih =>
    rw [openRows_succ _ _ (by omega), openStep_size, ih (by omega), Nat.pow_succ,
      Nat.div_div_eq_div_mul]

/-- **A round, row by row**: row `i` below half the rows is the fold of rows `2 i`, `2 i + 1`. -/
theorem openRows_succ_getD (slot : Array EW) (rows : Array (Array EW)) {t i : Nat}
    (ht : t < slot.size) (hi : i < (openRows slot rows t).size / 2) :
    (openRows slot rows (t + 1)).getD i #[] =
      foldRow (slot.getD t 0) ((openRows slot rows t).getD (2 * i) #[])
        ((openRows slot rows t).getD (2 * i + 1) #[]) := by
  rw [openRows_succ _ _ ht, openStep, getD_map_range _ _ _ hi]

/-- `keccakOpen`'s rows are the fold. -/
theorem keccakOpen_rows (slot : Array EW) (rows : Array (Array EW)) :
    slot.foldl (fun rows challenge ↦ (Array.range (rows.size / 2)).map fun i ↦
      Array.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) #[])
        (rows.getD (2 * i + 1) #[])) rows = openRows slot rows slot.size := by
  rw [openRows, List.take_of_length_le (by simp), Array.foldl_toList]
  rfl

/-- A row of a fold: entry `z` of two rows of 64 entries folded. -/
theorem foldRow_getD (c : EW) {lo hi : Array EW} (hlo : lo.size = 64) (hhi : hi.size = 64)
    {z : Nat} (hz : z < 64) :
    (foldRow c lo hi).getD z 0 = lo.getD z 0 + c * (lo.getD z 0 + hi.getD z 0) := by
  rw [foldRow, zipWith_getD _ _ _ (by omega) (by omega)]

theorem foldRow_size {c : EW} {lo hi : Array EW} (hlo : lo.size = 64) (hhi : hi.size = 64) :
    (foldRow c lo hi).size = 64 := by
  simp [foldRow, hlo, hhi]

/-- Every row of a fold of rows of 64 entries has 64 entries. -/
theorem openRows_row_size (slot : Array EW) (rows : Array (Array EW))
    (hw : ∀ r < rows.size, (rows.getD r #[]).size = 64) {t : Nat} (ht : t ≤ slot.size) :
    ∀ r < (openRows slot rows t).size, ((openRows slot rows t).getD r #[]).size = 64 := by
  induction t with
  | zero => simpa [openRows_zero] using hw
  | succ t ih =>
    intro r hr
    have hr' : r < (openRows slot rows t).size / 2 := by
      rw [openRows_succ _ _ (by omega), openStep_size] at hr; exact hr
    rw [openRows_succ_getD _ _ (by omega) hr']
    exact foldRow_size (ih (by omega) _ (by omega)) (ih (by omega) _ (by omega))

/-- An entry of lists of `k` entries end to end. -/
theorem flatMap_getElem? {α β : Type} (f : α → List β) (k : Nat) :
    ∀ (L : List α), (∀ x ∈ L, (f x).length = k) → ∀ r z, z < k →
      (L.flatMap f)[k * r + z]? = L[r]?.bind fun x ↦ (f x)[z]?
  | [], _, r, z, _ => by simp
  | x :: L, h, r, z, hz => by
    have hx := h x List.mem_cons_self
    rw [List.flatMap_cons]
    cases r with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by omega)]
      simp
    | succ r =>
      rw [List.getElem?_append_right (by rw [hx, Nat.mul_succ]; omega), hx,
        show k * (r + 1) + z - k = k * r + z by rw [Nat.mul_succ]; omega,
        flatMap_getElem? f k L (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)) r z hz]
      simp

/-- **The slot weights end to end**: entry `64 r + z` is entry `z` of row `r`. -/
theorem rowsFlat_getElem? (rows : Array (Array EW)) (hw : ∀ r < rows.size, (rows.getD r #[]).size = 64)
    {r z : Nat} (hr : r < rows.size) (hz : z < 64) :
    (rows.toList.flatMap (·.toList))[64 * r + z]? = some ((rows.getD r #[]).getD z 0) := by
  rw [flatMap_getElem? _ 64 _ (fun x hx ↦ by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := hw i (by simpa using hi)
    simpa [Array.getD_eq_getD_getElem?, show i < rows.size by simpa using hi] using this) r z hz]
  have hr' := hw r hr
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hr, Option.getD_some] at hr' ⊢
  simp [Array.getElem?_toList, Array.getElem?_eq_getElem hr, Array.getElem?_eq_getElem (show z < rows[r].size by omega)]

theorem rowsFlat_length (rows : Array (Array EW)) (hw : ∀ r < rows.size, (rows.getD r #[]).size = 64) :
    (rows.toList.flatMap (·.toList)).length = 64 * rows.size := by
  rw [List.length_flatMap]
  have : ∀ x ∈ rows.toList, x.toList.length = 64 := fun x hx ↦ by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := hw i (by simpa using hi)
    simpa [Array.getD_eq_getD_getElem?, show i < rows.size by simpa using hi] using this
  rw [List.map_congr_left this, List.map_const', List.sum_replicate, Array.length_toList, smul_eq_mul,
    Nat.mul_comm]

end

end NativeRustcVm.KeccakGkr
