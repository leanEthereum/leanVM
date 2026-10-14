module

public import LeanVMCircuits.Rec.Tables

@[expose] public section

/-!
The EXT instruction's three committed field identities. Logical columns are the accumulation bit at 0, the limbs
of `a`, `b`, and the old destination at 1 through 9, and the new destination at 10 through 12. The same identities
are a Clean assertion and the data exported to the production instruction table. No auxiliary witness is assumed.
-/

namespace LeanVMCircuits.ExtensionProduct

open Rec

/-- The exact degree-two identities, including their product order. -/
def rows : List Identity := [
  { linear := [(10, 1)], prods := [(0, 7, 1), (1, 4, 1), (2, 6, 1), (3, 5, 1)] },
  { linear := [(11, 1)], prods := [(0, 8, 1), (1, 5, 1), (2, 4, 1), (2, 6, 1), (3, 5, 1), (3, 6, 1)] },
  { linear := [(12, 1)], prods := [(0, 9, 1), (1, 6, 1), (2, 5, 1), (3, 4, 1), (3, 6, 1)] }
]

/-- The production field constraints authored as a Clean assertion. -/
noncomputable def circuit : FormalAssertion K (fields 13) := identities 13 rows

/-- The checked artifact is exactly the data read by the Clean source, not a second list of equations. -/
theorem source (row : Vector (Expression K) 13) : circuit.main row = assertAll row rows := rfl

noncomputable def a (row : ℕ → K) : E := toE (row 1) (row 2) (row 3)
noncomputable def b (row : ℕ → K) : E := toE (row 4) (row 5) (row 6)
noncomputable def old (row : ℕ → K) : E := toE (row 7) (row 8) (row 9)
noncomputable def out (row : ℕ → K) : E := toE (row 10) (row 11) (row 12)

/-- The extension-field product, plus the old destination scaled by the accumulation column. -/
noncomputable def result (row : ℕ → K) : E := a row * b row + emb (row 0) * old row

noncomputable def c0 (row : ℕ → K) : K :=
  row 0 * row 7 + (row 1 * row 4 + (row 2 * row 6 + row 3 * row 5))
noncomputable def c1 (row : ℕ → K) : K :=
  row 0 * row 8 + (row 1 * row 5 + (row 2 * row 4 + (row 2 * row 6 + (row 3 * row 5 + row 3 * row 6))))
noncomputable def c2 (row : ℕ → K) : K :=
  row 0 * row 9 + (row 1 * row 6 + (row 2 * row 5 + (row 3 * row 4 + row 3 * row 6)))

/-- The three coefficients are the product in the proved cubic extension, not integer multiplication. -/
theorem result_limbs (row : ℕ → K) : result row = toE (c0 row) (c1 row) (c2 row) := by
  unfold result a b old
  rw [mul_comm (emb (row 0)) _, toE_smul, toE_mul, toE_add]
  unfold c0 c1 c2
  congr 1 <;> ring

/-- Every arbitrary row satisfies the exported identities exactly when its new limbs are the specified result. -/
theorem soundness_iff (row : ℕ → K) :
    (∀ id ∈ rows, id.eval row = 0) ↔ out row = result row := by
  have hrows : (∀ id ∈ rows, id.eval row = 0) ↔
      row 10 = c0 row ∧ row 11 = c1 row ∧ row 12 = c2 row := by
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Identity.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      ofWord_one, one_mul, add_zero, add_eq_zero_iff_eq, c0, c1, c2]
  rw [hrows, result_limbs]
  constructor
  · rintro ⟨h0, h1, h2⟩
    simp only [out, h0, h1, h2]
  · intro h
    exact toE_injective _ _ _ _ _ _ h

/-- The actual Clean operations hold exactly when their evaluated ports satisfy the extension instruction. -/
theorem source_holds (env : Environment K) (ports : Vector (Expression K) 13) (offset : ℕ) :
    ConstraintsHold.Soundness env ((circuit.main ports).operations offset) ↔
      out (fun col => (ports.getD col (.const 0)).eval env) =
        result (fun col => (ports.getD col (.const 0)).eval env) := by
  rw [source, assertAll_holds]
  simp_rw [Identity.eval_expr]
  exact soundness_iff _

/-- With a Boolean accumulation column, the identities implement exactly MUL or MAC. -/
theorem instruction_soundness (row : ℕ → K) (holds : ∀ id ∈ rows, id.eval row = 0)
    (bit : row 0 = 0 ∨ row 0 = 1) :
    out row = if row 0 = 0 then a row * b row else a row * b row + old row := by
  rw [(soundness_iff row).mp holds]
  rcases bit with h | h
  · simp [result, h, emb_zero]
  · simp [result, h, emb, map_one]

/-- A base-field operand gives the scalar instruction when its upper limbs are zero. -/
theorem base_operand (row : ℕ → K) (h1 : row 5 = 0) (h2 : row 6 = 0) :
    a row * b row = toE (row 1 * row 4) (row 2 * row 4) (row 3 * row 4) := by
  simp only [a, b, h1, h2, toE_mul, mul_zero, add_zero, zero_add]

/-- Honest result limbs satisfy every identity for every input and accumulation column. -/
theorem completeness (row : ℕ → K) (h0 : row 10 = c0 row) (h1 : row 11 = c1 row)
    (h2 : row 12 = c2 row) : ∀ id ∈ rows, id.eval row = 0 := by
  apply (soundness_iff row).mpr
  rw [result_limbs]
  simp only [out, h0, h1, h2]

/-- Fill only the new destination, leaving every input column untouched. -/
noncomputable def witness (row : ℕ → K) (col : ℕ) : K :=
  if col = 10 then c0 row else if col = 11 then c1 row else if col = 12 then c2 row else row col

theorem witness_inputs (row : ℕ → K) (col : ℕ) (hc : col < 10) : witness row col = row col := by
  simp [witness, show col ≠ 10 by omega, show col ≠ 11 by omega, show col ≠ 12 by omega]

/-- Every arbitrary input assignment has a satisfying extension, without an honest-witness premise. -/
theorem witness_holds (row : ℕ → K) : ∀ id ∈ rows, id.eval (witness row) = 0 := by
  apply completeness <;> simp [witness, c0, c1, c2]

theorem witness_exists (row : ℕ → K) :
    ∃ final : ℕ → K, (∀ col < 10, final col = row col) ∧ ∀ id ∈ rows, id.eval final = 0 :=
  ⟨witness row, witness_inputs row, witness_holds row⟩

end LeanVMCircuits.ExtensionProduct
