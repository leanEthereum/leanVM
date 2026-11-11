/-
  LeanVM.Guest.B1.VerifySub.H.Bounds

  An honest layout's sizes: twice the push side's total is at most the stack's plus `2^19`, so the
  bus depth is at most the stack's log.
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

/-- **The push side fits the stack**: twice its total is at most the stack's plus `2^19`. -/
theorem pushTotal_le_stack {lm : ℕ} (hlm : 1 ≤ lm) {hs : List ℕ} (hl : hs.length = 6) :
    2 * pushTotal lm hs ≤ Tables.stackTotal (columnKappas lm 19 hs) + 2 ^ 19 := by
  have h2 : 2 ≤ 2 ^ lm := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ lm := Nat.pow_le_pow_right (by norm_num) hlm
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    rw [pushTotal_eq, stackTotal_eq]
    omega

/-- **An honest bus depth**: at most `32`, the stack's log bound. -/
theorem vsH_depth {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem : ℕ}
    {rowsN : List ℕ} (hrl : rowsN.length = 6) (hlm : 1 ≤ logMem)
    (h32 : (Tables.layoutOf bytecode logMem rowsN).stackLog ≤ 32) :
    log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) ≤ 32 ∧
      pushTotal logMem (Tables.tableHeightsOf rowsN) ≤ 2 ^ 32 := by
  have hsl := tableHeights_length rowsN hrl
  rw [stackLog_eq hbl] at h32
  have hst : Tables.stackTotal (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)) ≤ 2 ^ 32 :=
    log2Ceil_le_iff.mp (by omega)
  have hp := pushTotal_le_stack hlm hsl
  have hle : pushTotal logMem (Tables.tableHeightsOf rowsN) ≤ 2 ^ 32 := by omega
  exact ⟨log2Ceil_le_iff.mpr hle, hle⟩

end
end LeanVM.Guest.B1.VerifySub
