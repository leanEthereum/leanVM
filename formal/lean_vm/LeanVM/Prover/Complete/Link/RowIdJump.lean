/-
  LeanVM.Prover.Complete.Link.RowIdJump

  `JUMP`'s identities vanish on every row of the honest witness's `JUMP` table.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdShare
public import LeanVM.Prover.Complete.Link.ScatterHonest

/-!
# `JUMP`'s identities on the honest rows

`jumpConstraintForm coefs` is `k_0·(b + cond·w) + k_1·(cond + cond·b) + k_2·(pc' + g·pc + b·dest +
g·b·pc) + k_3·(fp' + fp + b·frame + b·fp)` (`jumpForm_eval`). An executed row (`rowOf` of a `JUMP`
step) has `b = 1`, `w = cond⁻¹`, `(pc', fp') = (dest, frame)` when `cond ≠ 0`, and `b = w = 0`,
`(pc', fp') = (g·pc, fp)` otherwise, so each identity is zero in characteristic two
(`jumpForm_rowOf`); a padding row is zero (`jumpForm_zero`). `jumpForm_witness`: on every row of
the honest `JUMP` table.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Extraction Finset

theorem jumpForm_eval (coefs : List E) (col : ℕ → E) :
    (jumpConstraintForm coefs).evaluate col =
      coefs.getD 0 0 * (col 8 + col 2 * col 7) + coefs.getD 1 0 * (col 2 + col 2 * col 8) +
        coefs.getD 2 0 * (col 5 + gpow 1 * col 0 + col 8 * col 3 + gpow 1 * (col 8 * col 0)) +
        coefs.getD 3 0 * (col 6 + col 1 + col 8 * col 4 + col 8 * col 1) := by
  have hc : ∀ s, colIndex jumpColumns s = jumpColumns.idxOf s := fun _ ↦ rfl
  simp only [jumpConstraintForm, Form.evaluate, LeanVM.Protocol.Tables.sumE_eq, hc]
  simp [jumpColumns]
  ring

theorem jumpForm_zero (coefs : List E) : (jumpConstraintForm coefs).evaluate (fun _ ↦ 0) = 0 := by
  rw [jumpForm_eval]; ring

theorem two_E : (2 : E) = 0 := CharTwo.two_eq_zero

/-- **An executed `JUMP` row satisfies `JUMP`'s identities.** -/
theorem jumpForm_rowOf {κ : ℕ} (ctx : FillCtx κ) (k : ℕ) (st : Step)
    (hst : opTableIdx st.ins.opcode = opJump) (coefs : List E) :
    (jumpConstraintForm coefs).evaluate (fun c ↦ ofK ((rowOf ctx k st).getD c 0)) = 0 := by
  obtain ⟨pc, fp, slot, ins⟩ := st
  cases ins with
  | jump oc od of =>
    rw [jumpForm_eval]
    have hg : gpow 1 = ofK g := by rw [LeanVM.Protocol.Relation.gpow_eq_ofK, pow_one]
    have h0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
    have h1 : ofK (1 : K) = 1 := map_one (algebraMap K E)
    by_cases hc : (ctx.limbs (fp * oc))[0] = 0
    · simp [rowOf, hc, hg, ofK_mul, h0]
      linear_combination (coefs[2]?.getD 0 * (ofK pc * ofK g) + coefs[3]?.getD 0 * ofK fp) * two_E
    · have hinv : ofK (ctx.limbs (fp * oc))[0] * ofK (ctx.limbs (fp * oc))[0]⁻¹ = 1 := by
        rw [← ofK_mul, mul_inv_cancel₀ hc, h1]
      simp [rowOf, hc, hg, h1]
      linear_combination (coefs[0]?.getD 0 + coefs[1]?.getD 0 * ofK (ctx.limbs (fp * oc))[0] +
        coefs[2]?.getD 0 * (ofK (ctx.limbs (fp * od))[0] + ofK g * ofK pc) +
        coefs[3]?.getD 0 * (ofK (ctx.limbs (fp * of))[0] + ofK fp)) * two_E + coefs[0]?.getD 0 * hinv
  | _ => simp [opTableIdx, LeanIsaInstruction.opcode, opJump, opXor, opMul, opSet, opDeref,
      opKeccak] at hst

/-- **A padding row's columns are the table's padding row.** -/
theorem pad_witness {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    {t u c : ℕ} (ht : t < nTables) (hu : W.rows.getD t 0 ≤ u)
    (hu' : u < 2 ^ W.layout.tableLogHeights.getD t 0) (hc : c < tableWidths.getD t 0) :
    ((W.tableCols t).getD c #[]).getD u 0 = (paddingRow t).getD c 0 := by
  obtain ⟨hr, hcols, -, -⟩ := witness_steps hW hv
  have hcsize : W.cols.size = nColumns := by rw [hcols]; simp [colsOf]
  obtain ⟨h1, h2, h3⟩ := tableOf_base t ht c hc
  have hlt : c < min (globalColumnBases.getD t 0 + tableWidths.getD t 0) W.cols.size -
      globalColumnBases.getD t 0 := by rw [hcsize]; omega
  have htc : (W.tableCols t).getD c #[] = W.cols.getD (globalColumnBases.getD t 0 + c) #[] := by
    simp only [Witness.tableCols, Array.getD_eq_getD_getElem?, Array.getElem?_extract, hlt,
      ↓reduceIte]
  rw [htc, hcols, colsOf_getD _ _ _ (by rw [← nColumns_eq]; exact h3)]
  have hm0 : globalColumnBases.getD t 0 + c ≠ memory0 := by unfold memory0; omega
  have hm1 : globalColumnBases.getD t 0 + c ≠ memory1 := by unfold memory1; omega
  have hq : globalColumnBases.getD t 0 + c ≠ qkeccak := by unfold qkeccak; omega
  simp only [hm0, hm1, hq, ↓reduceIte, h1, Nat.add_sub_cancel_left]
  rw [Keccak.tableColumn_getD _ _ _ _ hu', rowsOf_getD _ _ ht]
  rw [hr, rowCounts_getD _ ht] at hu
  simp only [List.size_toArray, List.length_map]
  rw [ite_eq_right (by omega)]

theorem paddingRow_jump (c : ℕ) : (paddingRow opJump).getD c 0 = 0 := by
  have hp : (tables.getD opJump default).padding = List.replicate 14 0 := rfl
  simp only [paddingRow, hp, List.map_replicate, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_replicate]
  split <;> simp [LeanVM.Parameters.limb_zero]

/-- **`JUMP`'s identities vanish on every row of the honest `JUMP` table.** -/
theorem jumpForm_witness {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    (coefs : List E) {u : ℕ} (hu : u < 2 ^ W.layout.tableLogHeights.getD opJump 0) :
    (jumpConstraintForm coefs).evaluate (rowValue (W.tableCols opJump) u) = 0 := by
  have ht : opJump < nTables := by decide
  by_cases hn : u < W.rows.getD opJump 0
  · rw [rows_witness hW hv ht] at hn
    rw [rowValue_witness hW hv ht hn]
    exact jumpForm_rowOf _ _ _ (mem_tablePairs (List.getElem_mem hn)) coefs
  · have hz : rowValue (W.tableCols opJump) u = fun _ ↦ 0 := by
      funext c
      unfold rowValue
      by_cases hc : c < tableWidths.getD opJump 0
      · rw [pad_witness hW hv ht (by omega) hu hc, paddingRow_jump]
        exact map_zero (algebraMap K E)
      · have hnone : ((W.tableCols opJump).getD c #[]) = #[] := by
          obtain ⟨-, hcols, -, -⟩ := witness_steps hW hv
          have hcsize : W.cols.size = nColumns := by rw [hcols]; simp [colsOf]
          simp only [Witness.tableCols, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
          rw [ite_eq_right (by rw [hcsize]; omega)]
          rfl
        rw [hnone]
        exact map_zero (algebraMap K E)
    rw [hz]
    exact jumpForm_zero coefs

end LeanVM.Prover.Complete.RowId

end
