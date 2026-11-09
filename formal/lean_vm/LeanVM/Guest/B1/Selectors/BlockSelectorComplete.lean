/-
  LeanVM.Guest.B1.Selectors.BlockSelectorComplete

  `block_selector` is complete: for `n < 34` bits pinned in memory, with complements and weights,
  their products are an outcome of `block_selector__L{n}`.
-/

module

public import LeanVM.Guest.B1.Selectors.BlockSelector

/-!
# `block_selector` is complete (TRIAGE G #50)

For bits `bs` at `sel_bits` (as `0/1` words), complements `zs1` and weights `cs`, the valuation
`bsVal` gives every value of `block_selector__L{n}`'s body what the body computes: block `k`'s
bit, its square (the bit again, which the write-once store then reads), the complement, the sum,
the running eq product (`bsEqV`), the one, the weight, the product, the sum and the running
`g`-power product (`bsRbV`); the final copies are the last running products.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Bit `k` as a word. -/
def bsB (bs : List Bool) (k : ℕ) : E := bitE (bs.getD k false)

/-- The running eq product after block `k`. -/
def bsEqV (bs : List Bool) (zs1 : List E) : ℕ → E
  | 0 => bsB bs 0 + zs1.getD 0 0
  | k + 1 => bsEqV bs zs1 k * (bsB bs (k + 1) + zs1.getD (k + 1) 0)

/-- The running `g`-power product after block `k`. -/
def bsRbV (bs : List Bool) (cs : List E) : ℕ → E
  | 0 => 1 + bsB bs 0 * cs.getD 0 0
  | k + 1 => bsRbV bs cs k * (1 + bsB bs (k + 1) * cs.getD (k + 1) 0)

/-- Value `r < 10` of block `k ≥ 1`, at `10k + 1 + r`. -/
def bsBlkV (bs : List Bool) (zs1 cs : List E) (k r : ℕ) : E :=
  [bsB bs k, bsB bs k * bsB bs k, zs1.getD k 0, bsB bs k + zs1.getD k 0, bsEqV bs zs1 k, 1,
    cs.getD k 0, bsB bs k * cs.getD k 0, 1 + bsB bs k * cs.getD k 0, bsRbV bs cs k].getD r 0

/-- Block `0`'s values, at `3 .. 10`. -/
def bsBlk0V (bs : List Bool) (zs1 cs : List E) : List E :=
  [bsB bs 0, bsB bs 0 * bsB bs 0, zs1.getD 0 0, bsEqV bs zs1 0, 1, cs.getD 0 0,
    bsB bs 0 * cs.getD 0 0, bsRbV bs cs 0]

/-- Value `k` of `block_selector__L{n}`. -/
def bsVal (n : ℕ) (sb z1 ic : E) (bs : List Bool) (zs1 cs : List E) (k : ℕ) : E :=
  if k = 0 then sb else if k = 1 then z1 else if k = 2 then ic
  else if n = 0 then 1
  else if k = 10 * n + 1 then bsEqV bs zs1 (n - 1)
  else if k = 10 * n + 2 then bsRbV bs cs (n - 1)
  else if k < 11 then (bsBlk0V bs zs1 cs).getD (k - 3) 0
  else bsBlkV bs zs1 cs ((k - 1) / 10) ((k - 1) % 10)

theorem bsVal_blk {n : ℕ} (sb z1 ic : E) (bs : List Bool) (zs1 cs : List E) {k r : ℕ}
    (hk1 : 1 ≤ k) (hkn : k < n) (hr : r < 10) :
    bsVal n sb z1 ic bs zs1 cs (10 * k + 1 + r) = bsBlkV bs zs1 cs k r := by
  have h1 : (10 * k + 1 + r - 1) / 10 = k := by omega
  have h2 : (10 * k + 1 + r - 1) % 10 = r := by omega
  simp only [bsVal, show 10 * k + 1 + r ≠ 0 by omega, show 10 * k + 1 + r ≠ 1 by omega,
    show 10 * k + 1 + r ≠ 2 by omega, show n ≠ 0 by omega, show 10 * k + 1 + r ≠ 10 * n + 1 by omega,
    show 10 * k + 1 + r ≠ 10 * n + 2 by omega, show ¬ 10 * k + 1 + r < 11 by omega, ↓reduceIte,
    h1, h2]

theorem bsVal_blk0 {n : ℕ} (sb z1 ic : E) (bs : List Bool) (zs1 cs : List E) (hn : n ≠ 0)
    {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 11) :
    bsVal n sb z1 ic bs zs1 cs k = (bsBlk0V bs zs1 cs).getD (k - 3) 0 := by
  simp only [bsVal, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, hn,
    show k ≠ 10 * n + 1 by omega, show k ≠ 10 * n + 2 by omega, hk, ↓reduceIte]

/-- The running eq product's value. -/
theorem bsVal_eq {n : ℕ} (sb z1 ic : E) (bs : List Bool) (zs1 cs : List E) (hn : n ≠ 0)
    {k : ℕ} (hk : k < n) : bsVal n sb z1 ic bs zs1 cs (bsEq k) = bsEqV bs zs1 k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [bsEq, ↓reduceIte]
    rw [bsVal_blk0 sb z1 ic bs zs1 cs hn (by norm_num) (by norm_num)]; rfl
  · simp only [bsEq, show k ≠ 0 by omega, ↓reduceIte]
    rw [show 10 * k + 5 = 10 * k + 1 + 4 by omega, bsVal_blk sb z1 ic bs zs1 cs hk0 hk
      (by norm_num)]; rfl

/-- The running `g`-power product's value. -/
theorem bsVal_rb {n : ℕ} (sb z1 ic : E) (bs : List Bool) (zs1 cs : List E) (hn : n ≠ 0)
    {k : ℕ} (hk : k < n) : bsVal n sb z1 ic bs zs1 cs (bsRb k) = bsRbV bs cs k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [bsRb, ↓reduceIte]
    rw [bsVal_blk0 sb z1 ic bs zs1 cs hn (by norm_num) (by norm_num)]; rfl
  · simp only [bsRb, show k ≠ 0 by omega, ↓reduceIte]
    rw [show 10 * k + 10 = 10 * k + 1 + 9 by omega, bsVal_blk sb z1 ic bs zs1 cs hk0 hk
      (by norm_num)]; rfl

theorem bs_zip_range {α β : Type} (l1 : List α) (l2 : List β) (d1 : α) (d2 : β)
    (h : l1.length = l2.length) :
    List.zip l1 l2 = (List.range l1.length).map fun k ↦ (l1.getD k d1, l2.getD k d2) := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
  have hi : i < l1.length := by simpa using h2
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)]

theorem bsEqV_eq (bs : List Bool) (zs1 : List E) : ∀ k, bsEqV bs zs1 k =
    ((List.range (k + 1)).map fun j ↦ bsB bs j + zs1.getD j 0).prod
  | 0 => by simp [bsEqV]
  | k + 1 => by rw [bsEqV, bsEqV_eq bs zs1 k, tb_prod_map_range_succ' _ (k + 1)]

theorem bsRbV_eq (bs : List Bool) (cs : List E) : ∀ k, bsRbV bs cs k =
    ((List.range (k + 1)).map fun j ↦ 1 + bsB bs j * cs.getD j 0).prod
  | 0 => by simp [bsRbV]
  | k + 1 => by rw [bsRbV, bsRbV_eq bs cs k, tb_prod_map_range_succ' _ (k + 1)]

/-- **`block_selector` is complete** at its 34 specializations. -/
theorem block_selector_complete_holds : block_selector_complete_Spec := by
  intro n hn rd args rets h
  match args, rets, h with
  | [sb, z1, ic], [eq, rb], ⟨bs, zs1, cs, hbl, hzl, hcl, hbr, hzr, hcr, heq, hrb⟩ =>
    obtain ⟨fn, hf, hp, hb⟩ := bsFound hn
    set F := bsVal n sb z1 ic bs zs1 cs with hF
    have f0 : F 0 = sb := by simp [hF, bsVal]
    have f1 : F 1 = z1 := by simp [hF, bsVal]
    have f2 : F 2 = ic := by simp [hF, bsVal]
    refine (tb_rel_pre hf hb (bsPre_noRet n) [sb, z1, ic] [eq, rb]).mpr ⟨fun x ↦ F x.idx,
      by rw [hp]; simp only [List.map_cons, List.map_nil]; rw [f0, f1, f2], ?_, ?_⟩
    · by_cases h0 : n = 0
      · subst h0
        simp only [bsPre, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
        simp [hF, bsVal, tb_word_one]
      · simp only [bsPre, h0, ↓reduceIte]
        rw [holdsList_append, holdsList_flatten _ (fun b hb ↦ by
          obtain ⟨t, -, rfl⟩ := List.mem_map.mp hb; exact bsBlk_noRet t)]
        refine ⟨fun b hb ↦ ?_, ?_⟩
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
          have hk := List.mem_range.mp hk
          have lb : LoadHolds rd sb k (bsB bs k) := by
            have := hbr k (by simp; omega)
            rwa [List.getElem_map, ← List.getD_eq_getElem _ false] at this
          have lb2 : LoadHolds rd sb k (bsB bs k * bsB bs k) := by
            rw [bsB, bitE_mul_self]; exact lb
          have lz : LoadHolds rd z1 k (zs1.getD k 0) := by
            have := hzr k (by omega)
            rwa [← List.getD_eq_getElem _ 0] at this
          have lc : LoadHolds rd ic k (cs.getD k 0) := by
            have := hcr k (by omega)
            rwa [← List.getD_eq_getElem _ 0] at this
          rcases Nat.eq_zero_or_pos k with rfl | hk0
          · have e : ∀ j, 3 ≤ j → j < 11 → F j = (bsBlk0V bs zs1 cs).getD (j - 3) 0 :=
              fun j h3 h11 ↦ bsVal_blk0 sb z1 ic bs zs1 cs h0 h3 h11
            simp only [bsBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
            rw [e 3 le_rfl (by norm_num), e 4 (by norm_num) (by norm_num),
              e 5 (by norm_num) (by norm_num), e 6 (by norm_num) (by norm_num),
              e 7 (by norm_num) (by norm_num), e 8 (by norm_num) (by norm_num),
              e 9 (by norm_num) (by norm_num), e 10 (by norm_num) (by norm_num), f0, f1, f2]
            simp only [bsBlk0V, Nat.reduceSub, List.getD_cons_zero, List.getD_cons_succ,
              bsEqV, bsRbV, tb_word_one]
            refine ⟨lb, ?_, lb2, lz, ?_, ?_, lc, ?_, ?_⟩ <;> trivial
          · have e : ∀ r, r < 10 → F (10 * k + 1 + r) = bsBlkV bs zs1 cs k r :=
              fun r hr ↦ bsVal_blk sb z1 ic bs zs1 cs hk0 hk hr
            simp only [bsBlk, show k ≠ 0 by omega, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
              Atom.Holds, and_true]
            rw [show F (bsEq (k - 1)) = bsEqV bs zs1 (k - 1) from
                bsVal_eq sb z1 ic bs zs1 cs h0 (by omega),
              show F (bsRb (k - 1)) = bsRbV bs cs (k - 1) from
                bsVal_rb sb z1 ic bs zs1 cs h0 (by omega),
              show 10 * k + 1 = 10 * k + 1 + 0 from rfl, e 0 (by norm_num), e 1 (by norm_num),
              e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num), e 5 (by norm_num),
              e 6 (by norm_num), e 7 (by norm_num), e 8 (by norm_num), e 9 (by norm_num), f0, f1,
              f2]
            obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            simp only [bsBlkV, List.getD_cons_zero, List.getD_cons_succ, bsEqV, bsRbV,
              tb_word_one, Nat.add_sub_cancel]
            refine ⟨lb, ?_, lb2, lz, ?_, ?_, ?_, lc, ?_, ?_, ?_⟩ <;> trivial
        · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
          rw [show F (bsEq (n - 1)) = bsEqV bs zs1 (n - 1) from
              bsVal_eq sb z1 ic bs zs1 cs h0 (by omega),
            show F (bsRb (n - 1)) = bsRbV bs cs (n - 1) from
              bsVal_rb sb z1 ic bs zs1 cs h0 (by omega)]
          simp [hF, bsVal, h0]
    · show (bsRet n).map (fun x ↦ F x.idx) = [eq, rb]
      by_cases h0 : n = 0
      · subst h0
        obtain rfl := List.length_eq_zero_iff.mp hbl
        obtain rfl := List.length_eq_zero_iff.mp hzl
        obtain rfl := List.length_eq_zero_iff.mp hcl
        simp [heq, hrb, bsRet, hF, bsVal]
      · simp only [bsRet, h0, ↓reduceIte, List.map_cons, List.map_nil]
        have e1 : F (10 * n + 1) = bsEqV bs zs1 (n - 1) := by simp [hF, bsVal, h0]
        have e2 : F (10 * n + 2) = bsRbV bs cs (n - 1) := by simp [hF, bsVal, h0]
        rw [e1, e2, heq, hrb, bsEqV_eq, bsRbV_eq, show n - 1 + 1 = n by omega,
          bs_zip_range bs zs1 false 0 (by omega), bs_zip_range bs cs false 0 (by omega), hbl,
          List.map_map, List.map_map]
        rfl
  | [], _, h => simp [BlockSelOut] at h
  | [_], _, h => simp [BlockSelOut] at h
  | [_, _], _, h => simp [BlockSelOut] at h
  | _ :: _ :: _ :: _ :: _, _, h => simp [BlockSelOut] at h
  | [_, _, _], [], h => simp [BlockSelOut] at h
  | [_, _, _], [_], h => simp [BlockSelOut] at h
  | [_, _, _], _ :: _ :: _ :: _, h => simp [BlockSelOut] at h

end
end LeanVM.Guest.B1.Tables
