module

public import LeanVM.Cost.Bounds.Guest.Readers
public import LeanVM.Cost.Decoder.Da

/-!
# Bounds on the guest decoder's prices: the DA matrix

`da_verify`'s witness off its callees' frames (`Cost/Decoder/Da.lean`: each column's frame looked
up once, its two words kept in an array of the `128` columns; each cell's blob-loop frame looked
up once; the powers of `g` in `K`), in the price `S` of an application of `da_verify`'s valuation
`σ` and the price `F` of an application of the frame map `Vn` (a frame's valuation at a variable),
the matrix's rows `r ≤ 2^k`, `k ≤ 34` (`r < 2^34`, `gLogD_lt`):

* a column's valuation (`dvColVN_cost`), its two words (`dvColWords_cost`), **the `128` columns'
  words** (`dvCols_cost`: `256·F + 2048·S + 1131026`);
* a blob-loop valuation (`dvRowVW_cost`), a cell's `256` symbols at it (`cellSymsAt_cost`), a cell
  (`dvSymsCell_cost`), a cell of the padded matrix (`dvSymsCols_cost`); the rows (`daRows_cost`,
  any symbols);
* the witness, its columns' words given (`dvWitNCols_cost`: `dvWitNColsPrice`), and built
  (`dvWitNAt_cost`: at most `dvWitNRowsPrice k F S = (33152·F + 1152·S + 28032·k +
  2257970)·2^k + 256·F + 2048·S + 1131200`);
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

theorem length_dvSymsCols (r : ℕ) (σ : Val) (Vn : NFrames) (cols : Array (E × E)) (i j : ℕ) :
    (Decoder.dvSymsCols r σ Vn cols i j).length = 256 := by
  unfold Decoder.dvSymsCols Decoder.dvSymsCell Decoder.cellSymsAt Da.cellSymsOf
  split_ifs
  · rw [List.length_map, List.length_range]
  · rw [List.length_replicate]

/-- **The rows** (`daRowsC`), any symbols: `r ≤ M` rows of `128` cells, each cell's price at
most `D` and its symbols at most `256`: at most `((D + 34)·128 + 361906)·M + 15`. -/
theorem daRows_cost (hP : Includes P Decoder.daRowsC.costDeps)
    (syms : ℕ → ℕ → List K) (symsV : MachineValue)
    (hsyms : ∀ a b, RunsApp P symsV [encodeValue a, encodeValue b] (encodeValue (syms a b)))
    (D r M : ℕ) (hr : r ≤ M) (hM : M < 2 ^ 64)
    (hD : ∀ i < r, ∀ j < 128, appCost P symsV [encodeValue i, encodeValue j] ≤ D)
    (hlen : ∀ i j, (syms i j).length ≤ 256) :
    machineCost P Decoder.daRowsC.costIdx [encodeValue r, symsV] ≤
      ((D + 34) * 128 + 361906) * M + 15 := by
  rw [Decoder.daRowsC.costEq P hP r syms symsV hsyms]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.daRowsC.lam0.costIdx [symsV])
    (fun i ↦ RunsApp.of_spec (Decoder.daRowsC.lam0.costSpec P (by includes)
      syms symsV hsyms i))
    ((D + 34) * 128 + 361878) r M hr hM (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.daRowsC.lam0.costEq P (by includes) syms symsV hsyms, List.length_cons, List.length_nil]
      have m' := rangeMap_le P (by includes) (by includes) _
        (.closure Decoder.daRowsC.lam0.lam0.costIdx [symsV, encodeValue i])
        (fun j ↦ RunsApp.of_spec (Decoder.daRowsC.lam0.lam0.costSpec P
          (by includes) syms symsV hsyms i j))
        (D + 6) 128 128 le_rfl (by norm_num) (fun j hj ↦ by
          rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
            Decoder.daRowsC.lam0.lam0.costEq P (by includes) syms symsV hsyms, List.length_cons, List.length_cons, List.length_nil]
          have := hD i hi j hj
          omega)
      have hf := flatten_map_cost P (by includes) 256 (syms i) (List.range 128)
        (fun j _ ↦ hlen i j)
      simp only [List.length_range] at hf
      omega)
  nlinarith

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

/-- **A cell's `256` symbols at a row's valuation** (`cellSymsAtC`), the row's valuation a closure
`rowV` of price at most `Rw`: `3·Rw + 256·F + 12863`. -/
theorem cellSymsAt_cost (hP : Includes P Decoder.cellSymsAtC.costDeps) (c13 : E) {row : Val}
    {rowV : MachineValue} (hrow : ∀ v : V, RunsApp P rowV [encodeValue v] (encodeValue (row v)))
    {Rw : ℕ} (hRw : ∀ v : V, appCost P rowV [encodeValue v] ≤ Rw) :
    machineCost P Decoder.cellSymsAtC.costIdx [VnV, encodeValue c13, rowV] ≤
      3 * Rw + 256 * F + 12863 := by
  rw [Decoder.cellSymsAtC.costEq P hP Vn VnV hVn c13 row rowV hrow]
  set a := [row (.n 6), row (.n 7), row (.n 8)]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.cellSymsAtC.lam0.costIdx
      [VnV, encodeValue a, encodeValue [c13]]) [encodeValue v] (encodeValue (Vn (fn_idx% da_verify_cell) [c13] a v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.cellSymsAtC.lam0.costSpec P (by includes) Vn VnV hVn a [c13] v)
  rw [Decoder.cellSymsOfC.costEq P (by includes) _ _ hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.cellSymsOfC.lam0.costIdx
      [.closure Decoder.cellSymsAtC.lam0.costIdx [VnV, encodeValue a, encodeValue [c13]]])
    (fun j ↦ RunsApp.of_spec (Decoder.cellSymsOfC.lam0.costSpec P
      (by includes) _ _ hσ j))
    (F + 22) 256 256 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.cellSymsOfC.lam0.costEq P (by includes) _ _ hσ,
        limbs_of_lt (by omega : j < 2 ^ 64), limbs_of_lt (by omega : j + 1 < 2 ^ 64), appCost_fn, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        Decoder.cellSymsAtC.lam0.costEq P (by includes) Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := hF (fn_idx% da_verify_cell) [c13] a (.n (j + 1)) (by norm_num) (by simp [a])
      omega)
  have := hRw (.n 6); have := hRw (.n 7); have := hRw (.n 8)
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

omit hVn hF in
/-- Column `j`'s arguments (`dvColArgsC`), `j < 128`: `8·S + 4364`. -/
theorem dvColArgs_cost (hP : Includes P Decoder.dvColArgsC.costDeps) (j : ℕ)
    (hj : j < 128) :
    machineCost P Decoder.dvColArgsC.costIdx [σV, encodeValue j] ≤
      8 * S + 4364 := by
  rw [Decoder.dvColArgsC.costEq P hP σ σV hσ]
  have := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen j 7 (by norm_num)
    (by norm_num) (by omega)
  have := hS (.n 1); have := hS (.n 22); have := hS (.n 6); have := hS (.n 7)
  have := hS (.n 8); have := hS (.n 9)
  omega

/-- **Column `j`'s valuation** (`dvColVNC`) at `a`, `j < 128`: `F + 8·S + 4378`. -/
theorem dvColVN_cost (hP : Includes P Decoder.dvColVNC.costDeps) (j : ℕ) (hj : j < 128) (a : V) :
    machineCost P Decoder.dvColVNC.costIdx [σV, VnV, encodeValue j, encodeValue a] ≤
      F + 8 * S + 4378 := by
  rw [Decoder.dvColVNC.costEq P hP σ σV hσ Vn VnV hVn]
  have := dvColArgs_cost P hσ hS (by includes) j hj
  have := hF (fn_idx% da_verify_column) (Da.dvColArgs σ j) [] a (by norm_num) (by simp [Da.dvColArgs])
  omega

/-- **Column `j`'s two words** (`dvColWordsC`), its frame looked up once per word, `j < 128`:
`2·F + 16·S + 8801`. -/
theorem dvColWords_cost (hP : Includes P Decoder.dvColWordsC.costDeps) (j : ℕ) (hj : j < 128) :
    machineCost P Decoder.dvColWordsC.costIdx [σV, VnV, encodeValue j] ≤
      2 * F + 16 * S + 8801 := by
  have hv : ∀ v : V, RunsApp P (.closure Decoder.dvColWordsC.lam0.costIdx
      [σV, VnV, encodeValue j]) [encodeValue v] (encodeValue (dvColVN σ Vn j v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.dvColWordsC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn
      j v)
  rw [Decoder.dvColWordsC.costEq P hP σ σV hσ Vn VnV hVn,
    Decoder.colWordsOfC.costEq P (by includes) _ _ hv]
  have h : ∀ v : V, appCost P (.closure Decoder.dvColWordsC.lam0.costIdx
      [σV, VnV, encodeValue j]) [encodeValue v] ≤ F + 8 * S + 4386 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.dvColWordsC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := dvColVN_cost P hVn hF hσ hS (by includes) j hj v
    omega
  have := h (.n 13); have := h (.n 14)
  omega

/-- **The `128` columns' words** (`dvColsC`), each column's frame looked up once:
`256·F + 2048·S + 1131026`. -/
theorem dvCols_cost (hP : Includes P Decoder.dvColsC.costDeps) :
    machineCost P Decoder.dvColsC.costIdx [σV, VnV] ≤ 256 * F + 2048 * S + 1131026 := by
  rw [Decoder.dvColsC.costEq P hP σ σV hσ Vn VnV hVn, List.length_map, List.length_range]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.dvColsC.lam0.costIdx [σV, VnV])
    (fun j ↦ RunsApp.of_spec (Decoder.dvColsC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn j))
    (2 * F + 16 * S + 8807) 128 128 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.dvColsC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn, List.length_cons, List.length_cons, List.length_nil]
      have := dvColWords_cost P hVn hF hσ hS (by includes) j hj
      omega)
  omega

/-- **Row `i`'s valuation in column `j`** (`dvRowVWC`) at `a`, the column's words `cw` given,
`i < 2^k`, `k ≤ 34`, `j < 128`: `F + 3·S + 73·k + 607`. -/
theorem dvRowVW_cost (hP : Includes P Decoder.dvRowVWC.costDeps) (cw : E × E) (k i j : ℕ)
    (hk0 : 0 < k) (hk : k ≤ 34) (hi : i < 2 ^ k) (hj : j < 128) (a : V) :
    machineCost P Decoder.dvRowVWC.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j, encodeValue a] ≤
        F + 3 * S + 73 * k + 607 := by
  rw [Decoder.dvRowVWC.costEq P hP σ σV hσ Vn VnV hVn]
  have := powSqK_cost_lt P (by includes) Parameters.g i k hk0 (by omega) hi
  have := powSqK_cost_lt P (by includes) Parameters.g j 7 (by norm_num) (by norm_num) (by omega)
  have := hS (.n 1); have := hS (.n 22)
  have := hF (fn_idx% da_verify_column_loop0) [ofK (Parameters.g ^ i), σ (.n 1), cw.1, σ (.n 22), ofK (Parameters.g ^ j),
    cw.2] [] a (by norm_num) (by simp)
  omega

/-- **Cell `(i, j)`'s symbols** (`dvSymsCellC`), the column's words given, its row's frame looked
up once, `i < 2^k`, `k ≤ 34`, `j < 128`: `259·F + 9·S + 219·k + 14735`. -/
theorem dvSymsCell_cost (hP : Includes P Decoder.dvSymsCellC.costDeps) (cw : E × E) (k i j : ℕ)
    (hk0 : 0 < k) (hk : k ≤ 34) (hi : i < 2 ^ k) (hj : j < 128) :
    machineCost P Decoder.dvSymsCellC.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j] ≤
        259 * F + 9 * S + 219 * k + 14735 := by
  rw [Decoder.dvSymsCellC.costEq P hP σ σV hσ Vn VnV hVn]
  have hrow : ∀ v : V, RunsApp P (.closure Decoder.dvSymsCellC.lam0.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j]) [encodeValue v]
      (encodeValue (Decoder.dvRowVW σ Vn cw i j v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.dvSymsCellC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn
      cw i j v)
  have hRw : ∀ v : V, appCost P (.closure Decoder.dvSymsCellC.lam0.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j]) [encodeValue v] ≤
        F + 3 * S + 73 * k + 619 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.cons_append, List.nil_append,
      Decoder.dvSymsCellC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := dvRowVW_cost P hVn hF hσ hS (by includes) cw k i j hk0 hk hi hj v
    omega
  have := cellSymsAt_cost P hVn hF (by includes) cw.1 hrow hRw
  omega

/-- **A cell of the padded matrix** of `r ≤ 2^k` rows (`dvSymsColsC`), `k ≤ 34`, any columns'
words: at most `259·F + 9·S + 219·k + 14768`. -/
theorem dvSymsCols_cost (hP : Includes P Decoder.dvSymsColsC.costDeps) (cols : Array (E × E))
    (k r i j : ℕ) (hk0 : 0 < k) (hk : k ≤ 34) (hr : r ≤ 2 ^ k) (hi : i < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    machineCost P Decoder.dvSymsColsC.costIdx
      [encodeValue r, σV, VnV, encodeValue cols, encodeValue i, encodeValue j] ≤
        259 * F + 9 * S + 219 * k + 14768 := by
  have h2 : 2 ^ k ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hk
  rw [Decoder.dvSymsColsC.costEq P hP r σ σV hσ Vn VnV hVn,
    limbs_of_lt (by omega : r < 2 ^ 64), limbs_of_lt hi, limbs_of_lt hj]
  have := replicate_cost P (by includes) (0 : K) 256 (by norm_num)
  split_ifs with h1 h2'
  · have := dvSymsCell_cost P hVn hF hσ hS (by includes) (cols.getD j (0, 0)) k i j hk0 hk
      (by omega) h2'.2
    omega
  · omega
  · omega
  · omega

/-- The witness's price, its columns' words given, at `r ≤ 2^k` rows. -/
@[expose] def dvWitNColsPrice (k F S : ℕ) : ℕ :=
  (33152 * F + 1152 * S + 28032 * k + 2257970) * 2 ^ k + 100

/-- **`da_verify`'s witness, its columns' words given** (`dvWitNColsC`), `r ≤ 2^k` rows,
`0 < k ≤ 34`: at most `dvWitNColsPrice k F S`. -/
theorem dvWitNCols_cost (hP : Includes P Decoder.dvWitNColsC.costDeps) (cols : Array (E × E))
    (k r : ℕ) (hk0 : 0 < k) (hk : k ≤ 34) (hr : r ≤ 2 ^ k) :
    machineCost P Decoder.dvWitNColsC.costIdx [encodeValue r, σV, VnV, encodeValue cols] ≤
      dvWitNColsPrice k F S := by
  have h2 : 2 ^ k ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hk
  rw [Decoder.dvWitNColsC.costEq P hP r σ σV hσ Vn VnV hVn]
  have hrows := daRows_cost P (by includes) (Decoder.dvSymsCols r σ Vn cols)
    (.closure Decoder.dvWitNColsC.lam0.costIdx [encodeValue r, σV, VnV, encodeValue cols])
    (fun i j ↦ RunsApp.of_spec (Decoder.dvWitNColsC.lam0.costSpec P (by includes) r σ σV hσ Vn
      VnV hVn cols i j))
    (259 * F + 9 * S + 219 * k + 14779) r (2 ^ k) hr (by omega)
    (fun i hi j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.dvWitNColsC.lam0.costEq P (by includes) r σ σV hσ Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := dvSymsCols_cost P hVn hF hσ hS (by includes) cols k r i j hk0 hk hr (by omega)
        (by omega)
      omega)
    (fun i j ↦ (length_dvSymsCols r σ Vn cols i j).le)
  have e : ((259 * F + 9 * S + 219 * k + 14779 + 34) * 128 + 361906) * 2 ^ k =
      (33152 * F + 1152 * S + 28032 * k + 2257970) * 2 ^ k := by ring
  unfold dvWitNColsPrice
  omega

/-- The witness's price at `r ≤ 2^k` rows. -/
@[expose] def dvWitNRowsPrice (k F S : ℕ) : ℕ :=
  (33152 * F + 1152 * S + 28032 * k + 2257970) * 2 ^ k + 256 * F + 2048 * S + 1131200

/-- The witness's price at `r ≤ 2^34` rows. -/
@[expose] def dvWitNAtPrice (F S : ℕ) : ℕ := dvWitNRowsPrice 34 F S

/-- **`da_verify`'s witness at `r ≤ 2^k` rows** (`dvWitNAtC`), `0 < k ≤ 34`: the columns' words
built once, then the witness: at most `dvWitNRowsPrice k F S`. -/
theorem dvWitNAt_cost (hP : Includes P Decoder.dvWitNAtC.costDeps) (k r : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hr : r ≤ 2 ^ k) :
    machineCost P Decoder.dvWitNAtC.costIdx [encodeValue r, σV, VnV] ≤ dvWitNRowsPrice k F S := by
  rw [Decoder.dvWitNAtC.costEq P hP r σ σV hσ Vn VnV hVn]
  have := dvCols_cost P hVn hF hσ hS (by includes)
  have := dvWitNCols_cost P hVn hF hσ hS (by includes) (Decoder.dvCols σ Vn) k r hk0 hk hr
  unfold dvWitNColsPrice at this
  unfold dvWitNRowsPrice
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
