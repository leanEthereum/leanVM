/-
  LeanVM.Guest.B1.Selectors.SharedHonest

  A selector run's honest nibble tables, as `verify_tables` allocates them: padded blocks at their
  strides, and the run's tables' sizes.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTables
public import LeanVM.Guest.B1.Selectors.ColumnSelector
public import LeanVM.Guest.B1.Selectors.TableLemmas

/-!
# A run's honest tables

`ssEqTab zs zs1 n`, `ssGTab gs n`: nibble `j`'s eq levels at `32j` and its `g` table at `16j`
(`padTo`), within the sizes `verify_tables` allocates (`ssEqW n = 32 (n / 4 + 1)`, `ssGW n =
16 (n / 4 + 1)` words); `runTables_of`: they give `RunTables`. `tbReadsAt_chunks`: a buffer of
padded blocks holds each block at its stride.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The eq table's size, in words: `q + 1` nibbles of `SEL_TAB_EQ_STRIDE = 32`. -/
def ssEqW (n : ℕ) : ℕ := 32 * (n / 4 + 1)

/-- The `g` table's size. -/
def ssGW (n : ℕ) : ℕ := 16 * (n / 4 + 1)

/-! ## Strided buffers -/

/-- `l` padded with zeros to `S` words. -/
def padTo (S : ℕ) (l : List E) : List E := l ++ List.replicate (S - l.length) 0

theorem padTo_length {S : ℕ} {l : List E} (h : l.length ≤ S) : (padTo S l).length = S := by
  simp [padTo]; omega

theorem getD_flatMap_const {S : ℕ} (f : ℕ → List E) (hf : ∀ i, (f i).length = S) :
    ∀ (m i k : ℕ), i < m → k < S →
      ((List.range m).flatMap f).getD (S * i + k) 0 = (f i).getD k 0
  | 0, _, _, hi, _ => absurd hi (by omega)
  | m + 1, i, k, hi, hk => by
    rw [List.range_succ, List.flatMap_append]
    have hlen : ((List.range m).flatMap f).length = S * m := by
      rw [List.length_flatMap]
      simp [hf, List.sum_replicate, Nat.mul_comm]
    rcases Nat.lt_or_ge i m with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact getD_flatMap_const f hf m i k h hk
    · obtain rfl : i = m := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp

theorem length_flatMap_padTo {S m : ℕ} (blk : ℕ → List E) (hb : ∀ i, (blk i).length ≤ S) :
    ((List.range m).flatMap fun i ↦ padTo S (blk i)).length = S * m := by
  rw [List.length_flatMap]
  simp [padTo_length (hb _), List.sum_replicate, Nat.mul_comm]

/-- **A buffer of padded blocks holds each block at its stride.** -/
theorem tbReadsAt_chunks {rd : Reader} {p : E} {S m : ℕ} (blk : ℕ → List E)
    (hb : ∀ i, (blk i).length ≤ S) (h : TbReadsAt rd p ((List.range m).flatMap fun i ↦ padTo S (blk i)))
    {i : ℕ} (hi : i < m) : TbReadsAt rd (p * gen ^ (S * i)) (blk i) := by
  intro k hk
  rw [tb_loadHolds_mul_gen_pow]
  have hS : k < S := lt_of_lt_of_le hk (hb i)
  have hidx : S * i + k < S * m := by nlinarith
  have := h (S * i + k) (by rw [length_flatMap_padTo blk hb]; exact hidx)
  rw [← List.getD_eq_getElem _ 0,
    getD_flatMap_const (fun i ↦ padTo S (blk i)) (fun i ↦ padTo_length (hb i)) m i k hi hS] at this
  rwa [padTo, List.getD_append _ _ _ _ hk, List.getD_eq_getElem _ _ hk] at this

/-! ## The honest tables -/

/-- The eq levels' table: nibble `j`'s eq levels at `32j`. -/
def ssEqTab (zs zs1 : List E) (n : ℕ) : List E :=
  (List.range ((n + 3) / 4)).flatMap fun j ↦ padTo 32 (eqLevels (nib zs j) (nib zs1 j))

/-- The `g` tables' table: nibble `j`'s `g`-power table at `16j`. -/
def ssGTab (gs : List E) (n : ℕ) : List E :=
  (List.range ((n + 3) / 4)).flatMap fun j ↦ padTo 16 (gTable (nib gs j))

theorem ss_nib_length {l : List E} {n : ℕ} (h : l.length = n) (j : ℕ) :
    (nib l j).length = min 4 (n - 4 * j) := by
  simp [nib, h]

theorem eqLevels_nib_le {zs zs1 : List E} {n : ℕ} (hz : zs.length = n) (hz1 : zs1.length = n)
    (j : ℕ) : (eqLevels (nib zs j) (nib zs1 j)).length ≤ 32 := by
  rw [eqLevels_length (ss_nib_length hz j) (ss_nib_length hz1 j)]
  have : min 4 (n - 4 * j) ≤ 4 := min_le_left _ _
  have : 2 ^ (min 4 (n - 4 * j) + 1) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem gTable_nib_le {gs : List E} {n : ℕ} (hg : gs.length = n) (j : ℕ) :
    (gTable (nib gs j)).length ≤ 16 := by
  rw [gTable_length (ss_nib_length hg j)]
  have : min 4 (n - 4 * j) ≤ 4 := min_le_left _ _
  have : 2 ^ min 4 (n - 4 * j) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
  simpa using this

theorem ssEqTab_le {zs zs1 : List E} {n : ℕ} (hz : zs.length = n) (hz1 : zs1.length = n) :
    (ssEqTab zs zs1 n).length ≤ ssEqW n := by
  rw [ssEqTab, length_flatMap_padTo _ (eqLevels_nib_le hz hz1), ssEqW]; omega

theorem ssGTab_le {gs : List E} {n : ℕ} (hg : gs.length = n) : (ssGTab gs n).length ≤ ssGW n := by
  rw [ssGTab, length_flatMap_padTo _ (gTable_nib_le hg), ssGW]; omega

/-- **The tables give `RunTables`.** -/
theorem runTables_of {rd : Reader} {eqt gt : E} {n : ℕ} {zs zs1 gs : List E}
    (hz : zs.length = n) (hz1 : zs1.length = n) (hg : gs.length = n)
    (he : TbReadsAt rd eqt (ssEqTab zs zs1 n)) (hgt : TbReadsAt rd gt (ssGTab gs n)) :
    RunTables rd eqt gt n zs zs1 gs := fun _ hj ↦
  ⟨tbReadsAt_chunks _ (eqLevels_nib_le hz hz1) he hj, tbReadsAt_chunks _ (gTable_nib_le hg) hgt hj⟩

end
end LeanVM.Guest.B1.Tables
