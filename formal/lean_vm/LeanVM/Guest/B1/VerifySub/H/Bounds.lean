/-
  LeanVM.Guest.B1.VerifySub.H.Bounds

  An honest layout's sizes: the push side's total is at most the stack's (plus one), so the bus
  depth is at most the stack's log plus one.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Front

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem colKappa_list : (List.range Tables.nCommittedCols).map
    (fun c ↦ (Tables.colKappaSrc c, Tables.colKappaAdj c)) =
    List.replicate 4 (1, 0) ++ [(0, 19), (7, 6)] ++ List.replicate 15 (2, 0) ++
      List.replicate 15 (3, 0) ++ List.replicate 8 (4, 0) ++ List.replicate 15 (5, 0) ++
      List.replicate 14 (6, 0) ++ List.replicate 28 (7, 0) := by decide

/-- **The stack's total**, column by column. -/
theorem stackTotal_eq (lm h0 h1 h2 h3 h4 h5 : ℕ) :
    Tables.stackTotal (columnKappas lm 19 [h0, h1, h2, h3, h4, h5]) =
      4 * 2 ^ lm + 2 ^ 19 + 64 * 2 ^ h5 + 15 * 2 ^ h0 + 15 * 2 ^ h1 + 8 * 2 ^ h2 +
        15 * 2 ^ h3 + 14 * 2 ^ h4 + 28 * 2 ^ h5 := by
  unfold Tables.stackTotal
  rw [Tables.committedKappas_columnKappas lm _ rfl]
  have e : (List.range Tables.nCommittedCols).map (fun c ↦
      ([0, lm, h0, h1, h2, h3, h4, h5].getD (Tables.colKappaSrc c) 0 + Tables.colKappaAdj c)) =
      ((List.range Tables.nCommittedCols).map
        (fun c ↦ (Tables.colKappaSrc c, Tables.colKappaAdj c))).map
        (fun p ↦ [0, lm, h0, h1, h2, h3, h4, h5].getD p.1 0 + p.2) := by
    rw [List.map_map]; rfl
  rw [e, colKappa_list]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.getD_cons_succ,
    List.getD_cons_zero, smul_eq_mul, Nat.add_zero, pow_add]
  ring

/-- **The push side's total**, block by block. -/
theorem pushTotal_eq (lm h0 h1 h2 h3 h4 h5 : ℕ) :
    pushTotal lm [h0, h1, h2, h3, h4, h5] =
      1 + 2 ^ lm + 2 ^ 19 + 5 * 2 ^ h0 + 5 * 2 ^ h1 + 3 * 2 ^ h2 + 5 * 2 ^ h3 + 5 * 2 ^ h4 +
        28 * 2 ^ h5 := by
  unfold pushTotal
  rw [show (List.range 54).map (fun b ↦ 2 ^ pushKappa lm [h0, h1, h2, h3, h4, h5] b) =
    ((List.range 54).map (pushKappa lm [h0, h1, h2, h3, h4, h5])).map (2 ^ ·) from
    (List.map_map ..).symm, pushKappas_eq]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, smul_eq_mul]
  ring

/-- **The push side fits the stack**: its total is at most the stack's plus one. -/
theorem pushTotal_le_stack (lm : ℕ) {hs : List ℕ} (hl : hs.length = 6) :
    pushTotal lm hs ≤ Tables.stackTotal (columnKappas lm 19 hs) + 1 := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    rw [pushTotal_eq, stackTotal_eq]
    omega

/-- **An honest bus depth**: at most `29`, at least `20`, the memory's log and the heights. -/
theorem vsH_depth {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem : ℕ}
    {rowsN : List ℕ} (hrl : rowsN.length = 6)
    (h28 : (Tables.layoutOf bytecode logMem rowsN).stackLog ≤ 28) :
    log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) ≤ 29 ∧
      pushTotal logMem (Tables.tableHeightsOf rowsN) ≤ 2 ^ 28 + 1 := by
  have hsl := tableHeights_length rowsN hrl
  rw [stackLog_eq hbl] at h28
  have hst : Tables.stackTotal (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)) ≤ 2 ^ 28 :=
    log2Ceil_le_iff.mp (by omega)
  have hp := pushTotal_le_stack logMem hsl
  refine ⟨log2Ceil_le_iff.mpr (by
    calc _ ≤ 2 ^ 28 + 1 := by omega
      _ ≤ 2 ^ 29 := by norm_num), by omega⟩

end
end LeanVM.Guest.B1.VerifySub
