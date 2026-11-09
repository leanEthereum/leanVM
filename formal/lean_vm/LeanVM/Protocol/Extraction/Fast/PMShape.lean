module

public import LeanVM.Protocol.Extraction.Fast.LanePM

/-!
# The lane's X-adic problem: the facts its cost proof reads

The data a cost proof of the lanes' approximant-basis interpolation (`Fast/LanePM.lean`,
`Cost/Bounds/PMSolve/`) reads. The interpolation builds the Guruswami–Sudan modular equations
(`buildGSModularDataWithRG`): the moduli `M_b = G^(m−b)`, `b < m` (`G` the vanishing polynomial of
the `n` points, `m` the multiplicity), and the relation matrix, `ℓ + 1` rows and `m` columns, its
column `b` reduced modulo `M_b`. The solver (`certifiedSolutionBasis`, at the bound `W`,
`solveWindow_some`) runs the PM-basis once, on `fullWindowExactNullspaceProblem` at `W`:

* the vanishing polynomial is monic of degree `n` (`monic_vanishingFast`,
  `natDegree_vanishingFast`);
* the relation matrix's entries are reduced (`natDegree_gsRelationMatrix_entry_lt`: the relation
  columns carry a reduced power, `natDegree_gsRelationColumn_lt`), so the lift's second reduction
  takes each remainder's first branch (dividend shorter than the modulus);
* the orders `deg M_b + W + 2` (`gsProblem_orders_toList`), the largest `m·n + W + 2`
  (`gsProblem_maxOrder`).
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Parameters.Whir LeanVM.Extraction
open CompPoly CompPoly.GuruswamiSudan CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open CompPoly.GuruswamiSudan.ApproximantBasis

public section

section Generic

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## The vanishing polynomial and the moduli -/

theorem monic_vanishingFast (xs : Array F) : (vanishingFast xs).toPoly.Monic := by
  rw [vanishingFast_eq]
  exact vanishingPolynomialArray_toPoly_monic xs

/-- The vanishing polynomial of `xs` has degree `|xs|`. -/
theorem natDegree_vanishingFast (xs : Array F) : (vanishingFast xs).natDegree = xs.size := by
  rw [vanishingFast_eq, CPolynomial.natDegree_toPoly, vanishingPolynomialArray_toPoly,
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
  simp

/-! ## The relation matrix is reduced -/

theorem natDegree_C_mul_lt {c : F} {p : CPolynomial F} {D : Nat} (h : p.natDegree < D) :
    (CPolynomial.C c * p).natDegree < D := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul, CPolynomial.C_toPoly]
  rw [CPolynomial.natDegree_toPoly] at h
  exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) h

theorem natDegree_modByMonicWith_lt (modCtx : CPolynomial.ModContext F) (p : CPolynomial F)
    {M : CPolynomial F} (hM : M.toPoly.Monic) (hD : 1 ≤ M.natDegree) :
    (modByMonicWith modCtx p M).natDegree < M.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly M, modByMonicWith_toPoly modCtx hM]
  refine Polynomial.natDegree_modByMonic_lt _ hM fun h1 ↦ ?_
  rw [CPolynomial.natDegree_toPoly, h1, Polynomial.natDegree_one] at hD
  omega

/-- A remainder of a reduced polynomial is itself. -/
theorem modByMonicWith_eq_self (modCtx : CPolynomial.ModContext F) {p M : CPolynomial F}
    (hM : M.toPoly.Monic) (h : p.natDegree < M.natDegree) : modByMonicWith modCtx p M = p := by
  apply CPolynomial.toPoly_injective
  rw [modByMonicWith_toPoly modCtx hM, Polynomial.modByMonic_eq_self_iff hM]
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly M] at h
  exact Polynomial.degree_lt_degree h

/-- A step of `gsRelationColumn`'s loop (CompPoly's, restated). -/
private def colStep (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (reducedR modulus : CPolynomial F) (b : Nat)
    (state : Array (CPolynomial F) × CPolynomial F) (j : Nat) :
    Array (CPolynomial F) × CPolynomial F :=
  (state.1.setIfInBounds j (CPolynomial.C ((j.choose b : F)) * state.2),
   modByMonicWith modCtx (mulCtx.mul state.2 reducedR) modulus)

private theorem gsRelationColumn_eq_colFold (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R modulus : CPolynomial F) (width b : Nat) :
    gsRelationColumn mulCtx modCtx R modulus width b =
      ((List.range' b (width - b)).foldl
        (colStep mulCtx modCtx (modByMonicWith modCtx R modulus) modulus b)
        (Array.replicate width (0 : CPolynomial F), 1)).1 := by
  rw [gsRelationColumn]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl,
    bind_pure_comp, map_pure, Id.run_pure]
  rfl

private theorem colFold_natDegree_lt (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) {reducedR modulus : CPolynomial F} (b : Nat) {D : Nat}
    (hD : 0 < D) (hstep : ∀ p, (modByMonicWith modCtx p modulus).natDegree < D) :
    ∀ (l : List Nat) (col : Array (CPolynomial F)) (pow : CPolynomial F),
      (∀ j, (col.getD j 0).natDegree < D) → pow.natDegree < D →
      ∀ j, ((l.foldl (colStep mulCtx modCtx reducedR modulus b) (col, pow)).1.getD j 0).natDegree
        < D := by
  intro l
  induction l with
  | nil => intro col pow hcol _ j; exact hcol j
  | cons i l ih =>
    intro col pow hcol hpow
    rw [List.foldl_cons]
    refine ih _ _ ?_ (hstep _)
    intro j
    show ((col.setIfInBounds i (CPolynomial.C ((i.choose b : F)) * pow)).getD j 0).natDegree < D
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
    split
    · split
      · exact natDegree_C_mul_lt hpow
      · rw [Option.getD_none, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero,
          Polynomial.natDegree_zero]
        exact hD
    · rw [← Array.getD_eq_getD_getElem?]
      exact hcol j

/-- **A relation column is reduced** modulo a monic modulus of positive degree. -/
theorem natDegree_gsRelationColumn_lt (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R : CPolynomial F) {modulus : CPolynomial F}
    (hM : modulus.toPoly.Monic) (hD : 1 ≤ modulus.natDegree) (width b j : Nat) :
    ((gsRelationColumn mulCtx modCtx R modulus width b).getD j 0).natDegree <
      modulus.natDegree := by
  rw [gsRelationColumn_eq_colFold]
  refine colFold_natDegree_lt mulCtx modCtx b (by omega)
    (fun p ↦ natDegree_modByMonicWith_lt modCtx p hM hD) _ _ _ ?_ ?_ j
  · intro j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> simp only [Option.getD_some, Option.getD_none] <;>
      rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero, Polynomial.natDegree_zero] <;> omega
  · rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one, Polynomial.natDegree_one]
    omega

/-- **The relation matrix is reduced**: entry `(k, b)` has degree below `deg M_b`. -/
theorem natDegree_gsRelationMatrix_entry_lt (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (hG1 : 1 ≤ G.natDegree) {k b : Nat}
    (hk : k < interpolationWidth params) (hb : b < params.multiplicity) :
    (rowGet ((gsRelationMatrixWithModuli mulCtx modCtx R
        (gsModuli mulCtx G params.multiplicity) params).getD k #[]) b).natDegree <
      ((gsModuli mulCtx G params.multiplicity).getD b 0).natDegree := by
  rw [gsRelationMatrixWithModuli_entry _ _ _ _ _ hk hb, gsModuli_getD_one _ _ hb,
    gsModuli_getD _ _ hb]
  have hMon : (G ^ (params.multiplicity - b)).toPoly.Monic := by
    rw [CPolynomial.toPoly_pow]
    exact hG.pow _
  refine natDegree_gsRelationColumn_lt _ _ _ hMon ?_ _ _ _
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_pow, hG.natDegree_pow,
    ← CPolynomial.natDegree_toPoly]
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

/-! ## The problem's sizes and orders -/

omit [BEq F] [LawfulBEq F] in
/-- The window the lanes' solver runs at: the weighted degree `W`. -/
theorem solveWindow_some (equation : ModularEquation F) (shift : Array Nat) (bound : Nat) :
    solveWindow equation shift (some bound) = bound := rfl

omit [BEq F] [LawfulBEq F] in
theorem mem_ofFn_size {rows width : Nat} {e : Nat → Nat → CPolynomial F} {r : PolynomialRow F}
    (h : r ∈ (PolynomialMatrix.ofFn rows width e).toList) : r.size = width := by
  simp only [PolynomialMatrix.ofFn, List.toList_toArray, List.mem_map] at h
  obtain ⟨i, -, rfl⟩ := h
  simp

/-- The orders, as a list: `(i + 1)·deg G + W + 2` for `i < m`, reversed. -/
theorem gsProblem_orders_toList (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (bound : Nat) :
    (fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound).orders.toList =
      ((List.range params.multiplicity).map
        fun i ↦ (i + 1) * G.natDegree + bound + 2).reverse := by
  show ((gsModuli mulCtx G params.multiplicity).map _).toList = _
  rw [gsModuli_eq, Array.toList_map, Array.toList_reverse, List.map_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply]
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_pow, hG.natDegree_pow,
    ← CPolynomial.natDegree_toPoly]

private theorem foldl_max_le {v : Nat} :
    ∀ (l : List Nat) (acc : Nat), acc ≤ v → (∀ x ∈ l, x ≤ v) → l.foldl max acc ≤ v
  | [], _, h, _ => h
  | x :: l, acc, h, hl => by
    rw [List.foldl_cons]
    exact foldl_max_le l _ (max_le h (hl x (by simp))) fun y hy ↦ hl y (by simp [hy])

/-- An element of `l`, or at most the start, is at most `l`'s `foldl max`. -/
theorem le_foldl_max_of_mem_or_le :
    ∀ (l : List Nat) (acc x : Nat), x ∈ l ∨ x ≤ acc → x ≤ l.foldl max acc
  | [], _, _, h => by simpa using h
  | y :: l, acc, x, h => by
    rw [List.foldl_cons]
    refine le_foldl_max_of_mem_or_le l _ x ?_
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (le_max_right _ _)
      · exact Or.inl h
    · exact Or.inr (le_trans h (le_max_left _ _))

/-- An entry of an array of naturals is at most its `foldl max 0`. -/
theorem getD_le_foldl_max (a : Array Nat) (j : Nat) : a.getD j 0 ≤ a.foldl max 0 := by
  rw [← Array.foldl_toList]
  rcases Nat.lt_or_ge j a.size with hj | hj
  · refine le_foldl_max_of_mem_or_le _ _ _ (Or.inl ?_)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
    exact Array.getElem_mem_toList hj
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hj, Option.getD_none]
    exact Nat.zero_le _

/-- **The largest order**: `m·deg G + W + 2`. -/
theorem gsProblem_maxOrder (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (bound : Nat) (hm : 0 < params.multiplicity) :
    maxOrder (fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound) =
      params.multiplicity * G.natDegree + bound + 2 := by
  rw [maxOrder, ← Array.foldl_toList, gsProblem_orders_toList mulCtx modCtx R G params hG]
  refine le_antisymm (foldl_max_le _ _ (Nat.zero_le _) fun x hx ↦ ?_)
    (le_foldl_max_of_mem_or_le _ _ _ ?_)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
    have := Nat.mul_le_mul_right G.natDegree (show i + 1 ≤ params.multiplicity from
      List.mem_range.1 hi)
    omega
  · refine Or.inl (List.mem_reverse.2 (List.mem_map.2 ⟨params.multiplicity - 1,
      List.mem_range.2 (by omega), ?_⟩))
    rw [Nat.sub_add_cancel hm]

end Generic

end

end LeanVM.Extraction.Fast
