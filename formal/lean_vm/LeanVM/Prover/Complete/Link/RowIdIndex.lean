/-
  LeanVM.Prover.Complete.Link.RowIdIndex

  The index side's tables at the index point `r`, as sums over the executed rows.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdJump
public import LeanVM.Prover.Complete.Link.State
public import LeanVM.Prover.Complete.Link.BalanceArrays

/-!
# The index side at `r`

The index side bound at `r` reads each of its arrays' extensions `M_f` (`index_value`). Paired
with `Z = eq(r, ·)`, the scattered arrays are sums over the executed rows (the state helper's
`sum_stateScatter`, the balance helper's `pair_scattered` and `pair_step_*`): the states at their
cycles, the accesses at their cells, the word reads, the rows' weights at their instructions. The
payload sits at index `0` (`M_pay`), and the memory's words read `M_1` (`M_words`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset

/-- The two equality weights agree on `E`. -/
theorem eqAt_keccak : ∀ (p : List E) (j : ℕ),
    LeanVM.Protocol.KeccakGkr.eqAt p j = LeanVM.Protocol.Hotwire.eqAt p j
  | [], _ => rfl
  | z :: p, j => by
    rw [LeanVM.Protocol.KeccakGkr.eqAt_cons, LeanVM.Protocol.Hotwire.eqAt_cons, eqAt_keccak p,
      CharTwo.sub_eq_add]

/-- The index side's array `f` at the point `r`. -/
noncomputable def idxM (W : Witness) (ch : LinkChallenges) (r : List E) (f : ℕ) : E :=
  mleA ((indexArrays W ch).getD f #[]) r

/-- **The index side's value at `r`.** -/
theorem index_value (W : Witness) (ch : LinkChallenges) (r : List E) :
    (r.foldl Prods.fold (indexProds W ch)).value =
      idxM W ch r 6 * idxM W ch r 0 + idxM W ch r 7 * idxM W ch r 1 +
        ch.etaMem * idxM W ch r 2 * idxM W ch r 3 + idxM W ch r 4 * idxM W ch r 5 +
        idxM W ch r 8 + ch.etaMem * idxM W ch r 9 * idxM W ch r 10 +
        idxM W ch r 11 * idxM W ch r 12 := by
  rw [value_foldl]
  simp [indexProds, idxM]

theorem at_index (W : Witness) (ch : LinkChallenges) (r : List E) (f : ℕ) :
    (r.foldl Prods.fold (indexProds W ch)).at f = idxM W ch r f := foldl_fold_at r _ f

section Index

variable (W : Witness) (ch : LinkChallenges) (r : List E)
  (hT : Tabs W.chunks.width (indexProds W ch)) (hr : r.length = W.chunks.width)
include hT hr

theorem idxM_eq_sum {f : ℕ} (hf : f < 13) :
    idxM W ch r f = ∑ j ∈ range (2 ^ W.chunks.width),
      LeanVM.Protocol.Hotwire.eqAt r j * idxAt W ch f j := by
  have hsz : ((indexArrays W ch).getD f #[]).size = 2 ^ r.length := by
    rw [hr]
    have hs : (indexArrays W ch).size = 13 := by simp [indexArrays]
    refine hT.1 _ ?_
    simp only [indexProds, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega : f < (indexArrays W ch).size), Option.getD_some]
    exact Array.getElem_mem _
  rw [idxM, mleA_eq_sum _ _ hsz, hr]
  rfl

theorem idxM_pair {f : ℕ} (hf : f < 13) :
    idxM W ch r f = pair (2 ^ W.chunks.width) ((indexArrays W ch).getD f #[])
      (LeanVM.Protocol.Hotwire.eqAt r) := by
  rw [idxM_eq_sum W ch r hT hr hf, pair]
  exact sum_congr rfl fun j _ ↦ mul_comm _ _

/-- The states (`k = 0`) or successors (`k = 1`) at their cycles. -/
theorem idxM_state {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex) {k : ℕ} (hk : k < 2) :
    idxM W ch r k = ∑ t ∈ range nTables, ∑ u ∈ range (W.rows.getD t 0),
      LeanVM.Protocol.Hotwire.eqAt r (rowCycle (traceSteps ex) t u) * stateWeight W ch k t u := by
  rw [idxM_eq_sum W ch r hT hr (by omega), ← sum_stateScatter hW hv ch k _ nTables le_rfl]
  refine sum_congr rfl fun j _ ↦ ?_
  congr 1
  unfold idxAt
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · rw [indexArrays_zero]
  · rw [indexArrays_one]

/-- The accesses' weights at their cells. -/
theorem idxM_mem (hS : ScatterOK W) :
    idxM W ch r 2 = ∑ t ∈ range nTables, ∑ u ∈ range (W.rows.getD t 0),
      (((tables.getD t default).links.memory.zip (ch.mu.getD t [])).map fun am ↦
        gateOf (colAt W t u) am.1 * (am.2 * omegaRow W ch t u) *
          LeanVM.Protocol.Hotwire.eqAt r (ptrAt W t am.1.pointer u + am.1.shift)).sum := by
  rw [idxM_pair W ch r hT hr (by omega)]
  exact pair_scattered W ch 2 (by omega) _ _ fun t ht acc hacc ↦
    pair_step_mem W ch hS ht _ acc (hacc 2)

/-- The word reads' weights at their cells. -/
theorem idxM_word (hS : ScatterOK W) :
    idxM W ch r 9 = ∑ t ∈ range nTables, ∑ u ∈ range (W.rows.getD t 0),
      ((wordReads (tables.getD t default).links (ch.mu.getD t []) (ch.gammaMem.getD 1 0)).map fun pf ↦
        pf.2.evaluate (colAt W t u) * omegaRow W ch t u *
          LeanVM.Protocol.Hotwire.eqAt r (ptrAt W t pf.1 u)).sum := by
  rw [idxM_pair W ch r hT hr (by omega)]
  exact pair_scattered W ch 3 (by omega) _ _ fun t ht acc hacc ↦
    pair_step_word W ch hS ht _ acc (hacc 3)

/-- The rows' weights at their instructions. -/
theorem idxM_bc (hS : ScatterOK W) :
    idxM W ch r 4 = ∑ t ∈ range nTables, ∑ u ∈ range (W.rows.getD t 0), omegaRow W ch t u *
      LeanVM.Protocol.Hotwire.eqAt r (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u) := by
  rw [idxM_pair W ch r hT hr (by omega)]
  exact pair_scattered W ch 4 (by omega) _ _ fun t ht acc hacc ↦
    pair_step_bc W ch hS ht _ acc (hacc 4)

/-- The rows' weights times `fp` at their instructions. -/
theorem idxM_fp (hS : ScatterOK W) :
    idxM W ch r 11 = ∑ t ∈ range nTables, ∑ u ∈ range (W.rows.getD t 0), omegaRow W ch t u *
      colAt W t u (tables.getD t default).links.stateLink.fp *
      LeanVM.Protocol.Hotwire.eqAt r (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u) := by
  rw [idxM_pair W ch r hT hr (by omega)]
  exact pair_scattered W ch 5 (by omega) _ _ fun t ht acc hacc ↦
    pair_step_fp W ch hS ht _ acc (hacc 5)

/-- The payload, at index `0`. -/
theorem idxM_pay :
    idxM W ch r 8 = LeanVM.Protocol.Hotwire.eqAt r 0 *
      ∑ t ∈ range nTables, ∑ u ∈ range (W.rows.getD t 0), omegaRow W ch t u *
        ((payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).1.evaluate (colAt W t u) +
          gatedVal (colAt W t u) (colAt W t u)
            (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).2) := by
  have hz : ∀ j ∈ range (2 ^ W.chunks.width), j ≠ 0 → idxAt W ch 8 j = 0 := by
    intro j _ hj
    have h8 : idxAt W ch 8 j = ((Array.replicate (2 ^ W.chunks.width) (0 : E)).set! 0
        (sumE ((List.range nTables).map fun t ↦ tablePayload ch t (W.rows.getD t 0) (W.tableCols t)
          (omegaTable (ch.theta.getD t 0) ch.tau (W.layout.tableLogHeights.getD t 0)
            (W.rows.getD t 0))))).getD j 0 := rfl
    rw [h8]
    simp only [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hj),
      Array.getElem?_replicate]
    split_ifs <;> rfl
  have h0 : 0 ∈ range (2 ^ W.chunks.width) := mem_range.mpr (Nat.two_pow_pos _)
  rw [idxM_eq_sum W ch r hT hr (by omega), ← sum_payload,
    sum_eq_single 0 (fun j hj hne ↦ by rw [hz j hj hne, mul_zero]) (fun h ↦ absurd h0 h),
    sum_eq_single 0 (fun j hj hne ↦ hz j hj hne) (fun h ↦ absurd h0 h)]

end Index

/-- `eq(p, 0)`, the product of `1 + p_i`. -/
theorem eqAt_zero_prodE : ∀ p : List E,
    LeanVM.Protocol.Hotwire.eqAt p 0 = prodE (p.map (1 + ·))
  | [] => by simp [prodE]
  | z :: p => by
    rw [LeanVM.Protocol.Hotwire.eqAt_cons, eqAt_zero_prodE p, prodE_eq_prod, prodE_eq_prod]
    simp [CharTwo.sub_eq_add]

/-- **The memory's words at `r` are `M_1`.** -/
theorem idxM_words (W : Witness) (ch : LinkChallenges) (r : List E)
    (hr : r.length = W.chunks.width) (hL : W.layout.logMemory ≤ W.chunks.width)
    (h0 : (W.cols.getD memory0 #[]).size = 2 ^ W.layout.logMemory)
    (h1 : (W.cols.getD memory1 #[]).size = 2 ^ W.layout.logMemory)
    (hT : Tabs W.chunks.width (indexProds W ch)) :
    idxM W ch r 10 = honestM1 W r := by
  have htl : (r.take W.layout.logMemory).length = W.layout.logMemory := by simp [hr, hL]
  rw [idxM_eq_sum W ch r hT hr (by omega), ← sum_range_add_sum_Ico _ (Nat.pow_le_pow_right
    (by norm_num) hL), sum_eq_zero (s := Ico _ _) fun j hj ↦ by
      rw [idxAt_ten, Keccak.getD_ofFn' _ (mem_Ico.mp hj).2]
      have hnot : ¬ j < 2 ^ W.layout.logMemory := by have := (mem_Ico.mp hj).1; omega
      simp [hnot], add_zero]
  unfold honestM1 mleK
  rw [min_eq_left hL, ← eqAt_zero_prodE]
  dsimp only
  rw [mleA_eq_sum _ _ (by rw [Array.size_map, h0, htl]), mleA_eq_sum _ _ (by rw [Array.size_map, h1, htl]), htl, mul_sum,
    ← sum_add_distrib, sum_mul]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' := mem_range.mp hj
  rw [idxAt_ten, Keccak.getD_ofFn' _ (lt_of_lt_of_le hj' (Nat.pow_le_pow_right (by norm_num) hL))]
  simp only [hj', ↓reduceIte]
  conv_lhs => rw [← List.take_append_drop W.layout.logMemory r]
  rw [LeanVM.Protocol.Hotwire.eqAt_append, htl, Nat.div_eq_of_lt hj']
  rw [getD_map_ofK, getD_map_ofK]
  ring


end LeanVM.Prover.Complete.RowId

end
