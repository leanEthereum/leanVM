module

public import LeanVM.Cost.Decoder.GuestTables
public import LeanVM.Cost.Decoder.GuestLanes

/-!
# The guest's frame cells, packed four to a number

The decoder program holds the guest's frame cells (`guestLocs`, `GuestTables.lean`, every cell
below `2^16`) as one literal (`guestLocsLit`, `Rule.literalNatArrays`), packed: the functions in
groups of four (`guestLaneGroups`, `GuestLanes.lean`), group `g`'s row of the table (row `g + 1`)
the numbers whose lane `k`, bits `16k … 16k + 15`, is function `groups[g][k]`'s cell at the same
position (`packLanes`), and row `0` each function's slot `4·(g + 1) + k` (`guestSlotsList`). Cell
`i` of function `j` (`locAt`) is read with two lookups of `j` and one of `i`, and arithmetic on the
slot alone: the price of a read does not depend on `i`, which may be any number. Packing within a
function's row instead would divide `i`, whose limbs a reader does not bound.

`LanesCheck.lean` proves `locAt j i` the cell of `guestLocs`, function by function.
-/

namespace LeanVM.Cost.Decoder

@[expose] public section

/-- Numbers as the lanes of one, `16` bits each, the first lowest. -/
def lanesWord : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 65536 * lanesWord l

/-- The rows' entries `0 … n - 1` packed: entry `i`'s lanes the rows' entries `i` (`0` past a
row's end). -/
def packLanesN : ℕ → List (List ℕ) → List ℕ
  | 0, _ => []
  | n + 1, rows => lanesWord (rows.map (·.headD 0)) :: packLanesN n (rows.map List.tail)

/-- The longest row's length. -/
def maxLength (rows : List (List ℕ)) : ℕ := (rows.map List.length).foldr max 0

/-- The rows packed, as many entries as the longest. -/
def packLanes (rows : List (List ℕ)) : List ℕ := packLanesN (maxLength rows) rows

/-- **The packed table**: the slots, then each group's rows packed. -/
def guestLanesList : List (List ℕ) :=
  guestSlotsList :: guestLaneGroups.map fun g ↦ packLanes (g.map fun j ↦ guestLocsList.getD j [])

/-- The packed table, as arrays: the decoder's literal (reducible: the compiler's literal rule
reads its list). -/
abbrev guestLocsLit : Array (Array ℕ) := (guestLanesList.map List.toArray).toArray

/-- The packed table (`Cost/Decoder/Witness.lean` compiles its uses as calls of one function
holding the literal). -/
def guestLanes : Array (Array ℕ) := guestLocsLit

/-- **Function `j`'s frame cell `i`**: its slot `s` (row `0`), lane `s % 4` of row `s / 4`'s entry
`i`. -/
def locAt (j i : ℕ) : ℕ :=
  let t := guestLanes
  let s := (t.getD 0 #[]).getD j 0
  ((t.getD (s / 4) #[]).getD i 0 >>> (16 * (s % 4))) % 65536

theorem locAt_lt (j i : ℕ) : locAt j i < 2 ^ 16 := Nat.mod_lt _ (by norm_num)

/-! ## The lanes -/

theorem lanesWord_cell (l : List ℕ) (h : ∀ x ∈ l, x < 65536) (k : ℕ) :
    (lanesWord l >>> (16 * k)) % 65536 = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp [lanesWord]
  | cons a l ih =>
    have ha := h a (by simp)
    cases k with
    | zero => simp only [lanesWord, Nat.mul_zero, Nat.shiftRight_zero, List.getD_cons_zero]; omega
    | succ k =>
      rw [List.getD_cons_succ, ← ih (fun x hx ↦ h x (by simp [hx])) k, Nat.mul_succ, Nat.add_comm,
        Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (lanesWord (a :: l)) 16]
      congr 2
      simp only [lanesWord]
      omega

theorem lanesWord_lt (l : List ℕ) (h : ∀ x ∈ l, x < 65536) : lanesWord l < 65536 ^ l.length := by
  induction l with
  | nil => simp [lanesWord]
  | cons a l ih =>
    have ha := h a (by simp)
    have := ih (fun x hx ↦ h x (by simp [hx]))
    simp only [lanesWord, List.length_cons, Nat.pow_succ]
    omega

theorem packLanesN_getD (n : ℕ) (rows : List (List ℕ)) (i : ℕ) :
    (packLanesN n rows).getD i 0 = if i < n then lanesWord (rows.map (·.getD i 0)) else 0 := by
  induction n generalizing rows i with
  | zero => simp [packLanesN]
  | succ n ih =>
    cases i with
    | zero =>
      simp only [packLanesN, List.getD_cons_zero, Nat.zero_lt_succ, ite_true]
      congr 1
      apply List.map_congr_left
      intro r _
      cases r <;> rfl
    | succ i =>
      simp only [packLanesN, List.getD_cons_succ, ih, List.map_map, Nat.succ_lt_succ_iff]
      split
      · congr 1
        apply List.map_congr_left
        intro r _
        cases r <;> simp
      · rfl

theorem packLanesN_length (n : ℕ) (rows : List (List ℕ)) : (packLanesN n rows).length = n := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih => simp [packLanesN, ih]

theorem length_le_maxLength {rows : List (List ℕ)} {r : List ℕ} (h : r ∈ rows) :
    r.length ≤ maxLength rows := by
  induction rows with
  | nil => simp at h
  | cons x rows ih =>
    simp only [maxLength, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

theorem getD_mem_or_nil (rows : List (List ℕ)) (k : ℕ) : rows.getD k [] ∈ rows ∨ rows.getD k [] = [] := by
  rw [List.getD_eq_getElem?_getD]
  cases h : rows[k]? with
  | none => exact Or.inr rfl
  | some r => exact Or.inl (List.mem_of_getElem? h)

theorem getD_lt_of_all {r : List ℕ} {B : ℕ} (hB : 0 < B) (h : ∀ x ∈ r, x < B) (i : ℕ) :
    r.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : r[i]? with
  | none => exact hB
  | some x => exact h x (List.mem_of_getElem? hi)

/-- **A lane of the packed rows**: lane `k` of entry `i` is row `k`'s entry `i`, the rows' entries
below `2^16`. -/
theorem packLanes_cell (rows : List (List ℕ)) (h : ∀ r ∈ rows, ∀ x ∈ r, x < 65536) (i k : ℕ) :
    ((packLanes rows).getD i 0 >>> (16 * k)) % 65536 = (rows.getD k []).getD i 0 := by
  rw [packLanes, packLanesN_getD]
  split
  · rw [lanesWord_cell _ (fun x hx ↦ ?_)]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD (l := rows)]
      cases rows[k]? <;> simp
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      exact getD_lt_of_all (by norm_num) (h r hr) i
  · rename_i hi
    rw [Nat.zero_shiftRight, Nat.zero_mod]
    rcases getD_mem_or_nil rows k with hr | hr
    · have := length_le_maxLength hr
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    · rw [hr]; rfl

/-- Every packed number of at most four rows below `2^16` is one limb. -/
theorem packLanes_lt (rows : List (List ℕ)) (h : ∀ r ∈ rows, ∀ x ∈ r, x < 65536)
    (hl : rows.length ≤ 4) (i : ℕ) : (packLanes rows).getD i 0 < 2 ^ 64 := by
  rw [packLanes, packLanesN_getD]
  split
  · have h1 := lanesWord_lt (rows.map (·.getD i 0)) (fun x hx ↦ by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      exact getD_lt_of_all (by norm_num) (h r hr) i)
    rw [List.length_map] at h1
    have h2 : 65536 ^ rows.length ≤ 65536 ^ 4 := Nat.pow_le_pow_right (by norm_num) hl
    have h3 : (65536 : ℕ) ^ 4 = 2 ^ 64 := by norm_num
    omega
  · norm_num

theorem packLanes_length (rows : List (List ℕ)) : (packLanes rows).length = maxLength rows :=
  packLanesN_length _ _

end

end LeanVM.Cost.Decoder
