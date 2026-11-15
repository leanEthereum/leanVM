module

public import LeanVM.Cost.Bounds.Guest.Readers
public import LeanVM.Cost.Decoder.Da

/-!
# Bounds on the guest decoder's prices: the DA matrix

`da_verify`'s witness off its callees' frames (`Cost/Decoder/Da.lean`: each blob's region base
computed once and passed to its row, each cell's loop frame a closure read four times, the powers of
`g` in `K`), in the price `S` of an application of `da_verify`'s valuation `σ` and the price `F` of
an application of the frame map `Vn` (a frame's valuation at a variable), the blobs `r ≤ 2^k`,
`k ≤ 34` (`r < 2^34`, `gLogD_lt`):

* a blob-loop valuation (`dvBlobLW_cost`), a blob's base (`dvBlobBase_cost`);
* a cell-loop valuation (`dvCellVW_cost`), a cell's `256` symbols at it (`cellSymsAt_cost`), a cell
  (`dvSymsCell_cost`), a blob's row (`dvRowOf_cost`, `dvRowAt_cost`);
* the witness (`dvWitNAt_cost`: at most `dvWitNRowsPrice k F S = (33283·F + 519·S + 146·k +
  2303726)·2^k + 19`);
* **`dvWitN_cost_1024`**: one logarithm (`GLogBound P D G`), the count clamped to `1024`
  (`daRowCount`, `daRowCount_cost`: `7`), the rows: at most `S + G + dvWitNRowsPrice 10 F S + 22`
  on every input; `dvWitN_cost`: below `S + G + dvWitNAtPrice F S + 14`, `dvWitNAtPrice F S =
  dvWitNRowsPrice 34 F S`; `dvWitN_cost_of_le`: at a clamped count `≤ 2^k`,
  `S + G + dvWitNRowsPrice k F S + 22`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main LeanVM.Guest.Fast

public section

variable (P : MachineProgram) {G : ℕ}

/-- The rows' count clamped to `1024` (`daRowCountC`): `7`. -/
theorem daRowCount_cost (hP : Includes P Decoder.daRowCountC.costDeps) (r : ℕ) (hr : r < 2 ^ 64) :
    machineCost P Decoder.daRowCountC.costIdx [encodeValue r] ≤ 7 := by
  rw [Decoder.daRowCountC.costEq P hP, limbs_of_lt hr]; split_ifs <;> omega

theorem length_dvSymsCell (σ : Val) (Vn : NFrames) (base : E) (h : ℕ) :
    (Decoder.dvSymsCell σ Vn base h).length = 256 := by
  unfold Decoder.dvSymsCell Decoder.cellSymsAt Da.cellSymsOf
  rw [List.length_map, List.length_range]

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

/-- **A cell's `256` symbols at a cell-loop valuation** (`cellSymsAtC`), the valuation a closure
`cellV` of price at most `Rw`: `4·Rw + 256·F + 12871`. -/
theorem cellSymsAt_cost (hP : Includes P Decoder.cellSymsAtC.costDeps) {cell : Val}
    {cellV : MachineValue} (hcell : ∀ v : V, RunsApp P cellV [encodeValue v] (encodeValue (cell v)))
    {Rw : ℕ} (hRw : ∀ v : V, appCost P cellV [encodeValue v] ≤ Rw) :
    machineCost P Decoder.cellSymsAtC.costIdx [VnV, cellV] ≤ 4 * Rw + 256 * F + 12871 := by
  rw [Decoder.cellSymsAtC.costEq P hP Vn VnV hVn cell cellV hcell]
  set a := [cell (.n 5), cell (.n 6), cell (.n 7)]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.cellSymsAtC.lam0.costIdx
      [VnV, encodeValue a, encodeValue [cell (.n 4)]]) [encodeValue v]
      (encodeValue (Vn (fn_idx% da_verify_cell) [cell (.n 4)] a v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.cellSymsAtC.lam0.costSpec P (by includes) Vn VnV hVn a
      [cell (.n 4)] v)
  rw [Decoder.cellSymsOfC.costEq P (by includes) _ _ hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.cellSymsOfC.lam0.costIdx
      [.closure Decoder.cellSymsAtC.lam0.costIdx [VnV, encodeValue a, encodeValue [cell (.n 4)]]])
    (fun j ↦ RunsApp.of_spec (Decoder.cellSymsOfC.lam0.costSpec P
      (by includes) _ _ hσ j))
    (F + 22) 256 256 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.cellSymsOfC.lam0.costEq P (by includes) _ _ hσ,
        limbs_of_lt (by omega : j < 2 ^ 64), limbs_of_lt (by omega : j + 1 < 2 ^ 64), appCost_fn, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        Decoder.cellSymsAtC.lam0.costEq P (by includes) Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := hF (fn_idx% da_verify_cell) [cell (.n 4)] a (.n (j + 1)) (by norm_num) (by simp [a])
      omega)
  have := hRw (.n 4); have := hRw (.n 5); have := hRw (.n 6); have := hRw (.n 7)
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- **Blob `i`'s blob-loop valuation** (`dvBlobLWC`) at `a`, `i < 2^k`, `0 < k ≤ 34`:
`F + 3·S + 73·k + 59`. -/
theorem dvBlobLW_cost (hP : Includes P Decoder.dvBlobLWC.costDeps) (k i : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hi : i < 2 ^ k) (a : V) :
    machineCost P Decoder.dvBlobLWC.costIdx [σV, VnV, encodeValue i, encodeValue a] ≤
      F + 3 * S + 73 * k + 59 := by
  rw [Decoder.dvBlobLWC.costEq P hP σ σV hσ Vn VnV hVn]
  have := powSqK_cost_lt P (by includes) Parameters.g i k hk0 (by omega) hi
  have := hS (.n 1); have := hS (.n 14); have := hS (.n 17)
  have := hF (fn_idx% da_verify_loop0) [ofK (Parameters.g ^ i), σ (.n 1), σ (.n 14), σ (.n 17)] [] a
    (by norm_num) (by simp)
  omega

/-- **Blob `i`'s base** (`dvBlobBaseC`), `i < 2^k`, `0 < k ≤ 34`: `3·F + 7·S + 146·k + 170`. -/
theorem dvBlobBase_cost (hP : Includes P Decoder.dvBlobBaseC.costDeps) (k i : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hi : i < 2 ^ k) :
    machineCost P Decoder.dvBlobBaseC.costIdx [σV, VnV, encodeValue i] ≤
      3 * F + 7 * S + 146 * k + 170 := by
  rw [Decoder.dvBlobBaseC.costEq P hP σ σV hσ Vn VnV hVn]
  have := dvBlobLW_cost P hVn hF hσ hS (by includes) k i hk0 hk hi (.n 4)
  have := dvBlobLW_cost P hVn hF hσ hS (by includes) k i hk0 hk hi (.n 5)
  have := hS (.n 14)
  have := hF (fn_idx% da_verify_blob) [σ (.n 14)]
    [Decoder.dvBlobLW σ Vn i (.n 4), Decoder.dvBlobLW σ Vn i (.n 5)] (.n 1) (by norm_num) (by simp)
  omega

/-- **Cell `h`'s cell-loop valuation** (`dvCellVWC`) at `a`, any base, `h < 128`:
`F + S + 550`. -/
theorem dvCellVW_cost (hP : Includes P Decoder.dvCellVWC.costDeps) (base : E) (h : ℕ)
    (hh : h < 128) (a : V) :
    machineCost P Decoder.dvCellVWC.costIdx
      [σV, VnV, encodeValue base, encodeValue h, encodeValue a] ≤ F + S + 550 := by
  rw [Decoder.dvCellVWC.costEq P hP σ σV hσ Vn VnV hVn]
  have := powSqK_cost_lt P (by includes) Parameters.g h 7 (by norm_num) (by norm_num) (by omega)
  have := hS (.n 14)
  have := hF (fn_idx% da_verify_blob_loop0) [ofK (Parameters.g ^ h), σ (.n 14), base] [] a
    (by norm_num) (by simp)
  omega

/-- **Cell `h`'s symbols** (`dvSymsCellC`), any base, `h < 128`: `260·F + 4·S + 15130`. -/
theorem dvSymsCell_cost (hP : Includes P Decoder.dvSymsCellC.costDeps) (base : E) (h : ℕ)
    (hh : h < 128) :
    machineCost P Decoder.dvSymsCellC.costIdx [σV, VnV, encodeValue base, encodeValue h] ≤
      260 * F + 4 * S + 15130 := by
  rw [Decoder.dvSymsCellC.costEq P hP σ σV hσ Vn VnV hVn]
  have hcell : ∀ v : V, RunsApp P (.closure Decoder.dvSymsCellC.lam0.costIdx
      [σV, VnV, encodeValue base, encodeValue h]) [encodeValue v]
      (encodeValue (Decoder.dvCellVW σ Vn base h v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.dvSymsCellC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn
      base h v)
  have hRw : ∀ v : V, appCost P (.closure Decoder.dvSymsCellC.lam0.costIdx
      [σV, VnV, encodeValue base, encodeValue h]) [encodeValue v] ≤ F + S + 562 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append,
      Decoder.dvSymsCellC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := dvCellVW_cost P hVn hF hσ hS (by includes) base h hh v
    omega
  have := cellSymsAt_cost P hVn hF (by includes) hcell hRw
  omega

/-- **A blob's row** (`dvRowOfC`), any base: `33280·F + 512·S + 2303511`. -/
theorem dvRowOf_cost (hP : Includes P Decoder.dvRowOfC.costDeps) (base : E) :
    machineCost P Decoder.dvRowOfC.costIdx [σV, VnV, encodeValue base] ≤
      33280 * F + 512 * S + 2303511 := by
  rw [Decoder.dvRowOfC.costEq P hP σ σV hσ Vn VnV hVn]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.dvRowOfC.lam0.costIdx [σV, VnV, encodeValue base])
    (fun h ↦ RunsApp.of_spec (Decoder.dvRowOfC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn
      base h))
    (260 * F + 4 * S + 15141) 128 128 le_rfl (by norm_num) (fun h hh ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.dvRowOfC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn, List.length_cons,
        List.length_cons, List.length_cons, List.length_nil]
      have := dvSymsCell_cost P hVn hF hσ hS (by includes) base h hh
      omega)
  have hf := flatten_map_cost P (by includes) 256 (fun h ↦ Decoder.dvSymsCell σ Vn base h)
    (List.range 128) (fun h _ ↦ (length_dvSymsCell σ Vn base h).le)
  simp only [List.length_range] at hf
  omega

/-- **Blob `i`'s row** (`dvRowAtC`), its base computed once, `i < 2^k`, `0 < k ≤ 34`:
`33283·F + 519·S + 146·k + 2303688`. -/
theorem dvRowAt_cost (hP : Includes P Decoder.dvRowAtC.costDeps) (k i : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hi : i < 2 ^ k) :
    machineCost P Decoder.dvRowAtC.costIdx [σV, VnV, encodeValue i] ≤
      33283 * F + 519 * S + 146 * k + 2303688 := by
  rw [Decoder.dvRowAtC.costEq P hP σ σV hσ Vn VnV hVn]
  have := dvBlobBase_cost P hVn hF hσ hS (by includes) k i hk0 hk hi
  have := dvRowOf_cost P hVn hF hσ hS (by includes) (Decoder.dvBlobBase σ Vn i)
  omega

/-- The witness's price at `r ≤ 2^k` blobs. -/
@[expose] def dvWitNRowsPrice (k F S : ℕ) : ℕ :=
  (33283 * F + 519 * S + 146 * k + 2303726) * 2 ^ k + 19

/-- The witness's price at `r ≤ 2^34` blobs. -/
@[expose] def dvWitNAtPrice (F S : ℕ) : ℕ := dvWitNRowsPrice 34 F S

/-- **`da_verify`'s witness at `r ≤ 2^k` blobs** (`dvWitNAtC`), `0 < k ≤ 34`: each blob's row,
its base computed once: at most `dvWitNRowsPrice k F S`. -/
theorem dvWitNAt_cost (hP : Includes P Decoder.dvWitNAtC.costDeps) (k r : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hr : r ≤ 2 ^ k) :
    machineCost P Decoder.dvWitNAtC.costIdx [encodeValue r, σV, VnV] ≤ dvWitNRowsPrice k F S := by
  have h2 : 2 ^ k ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hk
  rw [Decoder.dvWitNAtC.costEq P hP r σ σV hσ Vn VnV hVn]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.dvWitNAtC.lam0.costIdx [σV, VnV])
    (fun i ↦ RunsApp.of_spec (Decoder.dvWitNAtC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn i))
    (33283 * F + 519 * S + 146 * k + 2303698) r (2 ^ k) hr (by omega) (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.dvWitNAtC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn, List.length_cons,
        List.length_cons, List.length_nil]
      have := dvRowAt_cost P hVn hF hσ hS (by includes) k i hk0 hk (by omega)
      omega)
  have e : (33283 * F + 519 * S + 146 * k + 2303698 + 28) * 2 ^ k + 8 + 11 =
      dvWitNRowsPrice k F S := by
    unfold dvWitNRowsPrice; ring
  omega

/-- **`da_verify`'s witness at `r ≤ 2^k` rows** (`dvWitNC`), the logarithm's tables `D` given:
one logarithm, the count clamped to `1024` (`daRowCount`), then the rows: at most
`S + G + dvWitNRowsPrice k F S + 22`. -/
theorem dvWitN_cost_of_le (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.dvWitNC.costDeps) (hG : GLogBound P D G) (k : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hr : Decoder.daRowCount (Decoder.gLogD D (σ (.n 1))) ≤ 2 ^ k) :
    machineCost P Decoder.dvWitNC.costIdx [encodeValue D, σV, VnV] ≤
      S + G + dvWitNRowsPrice k F S + 22 := by
  rw [Decoder.dvWitNC.costEq P hP D σ σV hσ Vn VnV hVn]
  have := hG (σ (.n 1))
  have := hS (.n 1)
  have := daRowCount_cost P (by includes) (Decoder.gLogD D (σ (.n 1)))
    (by have := gLogD_lt D (σ (.n 1)); omega)
  have := dvWitNAt_cost P hVn hF hσ hS (by includes) k _ hk0 hk hr
  omega

/-- **`da_verify`'s witness** (`dvWitNC`), the logarithm's tables `D` given: one logarithm, the
rows at most `1024` (`daRowCount_le`, on every input): at most
`S + G + dvWitNRowsPrice 10 F S + 22`. -/
theorem dvWitN_cost_1024 (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.dvWitNC.costDeps) (hG : GLogBound P D G) :
    machineCost P Decoder.dvWitNC.costIdx [encodeValue D, σV, VnV] ≤
      S + G + dvWitNRowsPrice 10 F S + 22 :=
  dvWitN_cost_of_le P hVn hF hσ hS D hP hG 10 (by norm_num) (by norm_num)
    ((Decoder.daRowCount_le _).trans (by norm_num))

/-- **`da_verify`'s witness** (`dvWitNC`), the logarithm's tables `D` given: at most
`S + G + dvWitNAtPrice F S + 14` (`dvWitN_cost_1024`, below the price at `2^34` rows). -/
theorem dvWitN_cost (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.dvWitNC.costDeps) (hG : GLogBound P D G) :
    machineCost P Decoder.dvWitNC.costIdx [encodeValue D, σV, VnV] ≤
      S + G + dvWitNAtPrice F S + 14 := by
  have := dvWitN_cost_1024 P hVn hF hσ hS D hP hG
  have e : dvWitNRowsPrice 10 F S + 8 ≤ dvWitNAtPrice F S := by
    unfold dvWitNAtPrice dvWitNRowsPrice
    norm_num
    nlinarith
  omega

end Val

end Frames

end

end LeanVM.Cost.Bounds.Guest
