/-
  LeanVM.Guest.B1.Place.OsKidsSp3

  open_stacked's queries' value on the honest trace: `opening_queries`' chain is the level's
  enforced sum.
-/

module

public import LeanVM.Guest.B1.Place.OsKidsSp2
public import LeanVM.Guest.B1.Whir.QueriesBlk
public import LeanVM.Guest.B1.Whir.BrCaps

/-!
# The queries' value

`wp_val`: the honest row weights `wpC` entry by entry. **`q_ret`**: `opening_queries`' return on
level `l`'s honest openings and row weights, `oqChain … λ⁻¹ ⋯ · λ^q`, is the level's enforced sum
(`oqChain_powers`, `enforcedSum_eq`, `rowDot_level0`, `rowDot_deeper`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {c : OsCfg} {tr : OsTr}

theorem wp_val {l k : ℕ} (hk : k < c.maxIl) :
    (wpC c tr l).getD k 0 =
      if k < 2 ^ rwLo (lvAt c l).folds then
        (eqKernel ((tr.L l).chs.take (rwLo (lvAt c l).folds))).getD
          (rwSlot (rwLo (lvAt c l).folds) (if l = 0 then 1 else 0) k) 0
      else if k < 2 ^ rwLo (lvAt c l).folds + 2 ^ ((lvAt c l).folds - rwLo (lvAt c l).folds) then
        (eqKernel ((tr.L l).chs.drop (rwLo (lvAt c l).folds))).getD
          (rwSlot ((lvAt c l).folds - rwLo (lvAt c l).folds) (if l = 0 then 1 else 0)
            (k - 2 ^ rwLo (lvAt c l).folds)) 0
      else 0 := by
  rw [wpC, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

/-- **`opening_queries`' return on level `l`'s honest openings is its enforced sum.** -/
theorem q_ret {l : ℕ} (hrow : RowShape l (lvAt c l))
    (hil : rowLo (lvAt c l).interleave + (lvAt c l).interleave / rowLo (lvAt c l).interleave ≤
      c.maxIl)
    (hidx : (tr.L l).index = l) (hch : (tr.L l).chs.length = (lvAt c l).folds)
    (hql : (tr.L l).qs.length = (lvAt c l).queries) (hos : (tr.L l).os.length = (tr.L l).qs.length)
    (hlam : (tr.L l).lam ≠ 0)
    (hleaf : ∀ k < (lvAt c l).queries, ((tr.L l).os.getD k default).leaf.length =
      lvWidth l (lvAt c l)) :
    oqChain ((lvAt c l).queries % 2 * (if l = 0 then 1 else 0)) (if l = 0 then 1 else 0)
        (tr.L l).lam⁻¹
        (fun k ↦ rowDot (if l = 0 then 1 else 0) (lvAt c l).interleave
          ((tr.L l).os.getD k default).leaf fun i ↦ (wpC c tr l).getD i 0)
        ((lvAt c l).queries / (1 + if l = 0 then 1 else 0)) * (tr.L l).lam ^ (lvAt c l).queries =
      (tr.L l).enforced := by
  have hodd : (lvAt c l).queries % 2 * (if l = 0 then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  have hb : (if l = 0 then 1 else 0) = 1 ∨
      ((if l = 0 then 1 else 0) = 0 ∧ (lvAt c l).queries % 2 * (if l = 0 then 1 else 0) = 0) := by
    split_ifs <;> simp
  have h1 := oqChain_powers hlam hodd hb (fun k ↦ rowDot (if l = 0 then 1 else 0)
    (lvAt c l).interleave ((tr.L l).os.getD k default).leaf fun i ↦ (wpC c tr l).getD i 0)
    ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))
  rw [oqCount_q] at h1
  rw [h1]
  have hrl : (tr.L l).rows.length = (tr.L l).qs.length := by
    unfold SpLv.rows; split_ifs <;> simp [hos]
  unfold SpLv.enforced
  rw [← hrl, enforcedSum_eq, hrl, hql]
  unfold powSum
  refine congrArg (List.foldl _ 0) (List.map_congr_left fun k hk ↦ ?_)
  have hk' : k < (lvAt c l).queries := List.mem_range.mp hk
  refine congrArg ((tr.L l).lam ^ k * ·) ?_
  have hko : k < (tr.L l).os.length := by omega
  have hrowk : (tr.L l).rows.getD k [] = specRow l ((tr.L l).os.getD k default).leaf := by
    have e : (tr.L l).rows = ((tr.L l).os.map (·.leaf)).map (specRow l) := by
      unfold SpLv.rows specRow
      rw [hidx]
      by_cases h0 : l = 0
      · simp only [h0, ↓reduceIte]
      · simp only [h0, ↓reduceIte]
    rw [e, List.getD_eq_getElem _ _ (by simpa using hko), List.getElem_map, List.getElem_map,
      List.getD_eq_getElem _ _ hko]
  beta_reduce
  rw [hrowk]
  have hlen := hleaf k hk'
  obtain ⟨hf, hI⟩ := hrow
  unfold lvWidth at hlen
  by_cases h0 : l = 0
  · subst h0
    simp only [↓reduceIte] at hf hI hlen ⊢
    rw [hI] at hlen hil ⊢
    rw [hf] at hch
    rw [rowLo_64] at hil
    simp only [specRow, ↓reduceIte]
    refine rowDot_level0 hlen hch (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · rw [wp_val (by omega), hf]
      simp [rwSlot, hi, show rwLo 6 = 3 from rfl]
    · rw [wp_val (by omega), hf]
      simp only [rwSlot, show rwLo 6 = 3 from rfl] at *
      have p3 : (2 : ℕ) ^ 3 = 8 := rfl
      simp only [↓reduceIte, p3, show ¬ 8 + i < 8 by omega, show 8 + i < 8 + 8 by omega]
      congr 1
      omega
  · simp only [h0, ↓reduceIte] at hf hI hlen ⊢
    rw [hI] at hlen hil ⊢
    rw [hf] at hch
    rw [rowLo_16] at hil
    simp only [specRow, h0, ↓reduceIte]
    refine rowDot_deeper (by simpa using hlen) hch (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · rw [wp_val (by omega), hf]
      simp [rwSlot, hi, h0, show rwLo 4 = 3 from rfl]
    · rw [wp_val (by omega), hf]
      simp only [rwSlot, show rwLo 4 = 3 from rfl] at *
      have p3 : (2 : ℕ) ^ 3 = 8 := rfl
      have p1 : (2 : ℕ) ^ (4 - 3) = 2 := rfl
      simp only [h0, ↓reduceIte, p3, p1, show ¬ 8 + i < 8 by omega, show 8 + i < 8 + 2 by omega,
        zero_ne_one, Nat.add_sub_cancel_left]

end
end LeanVM.Guest.B1
