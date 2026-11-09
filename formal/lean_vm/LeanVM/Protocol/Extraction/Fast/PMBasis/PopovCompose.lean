module

public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Correctness

/-!
# Ordered weak Popov bases compose

CompPoly's shifted leading position of a row (`rowShiftedLeadingPosition?`, `Shifted.lean`) is the
rightmost entry of largest shifted degree `deg + shift`. A square `n × n` matrix is **ordered weak
Popov** at a shift (`OrderedWeakPopov M s n`) when row `i` has width `n` and shifted leading
position `i`: the pivots are distinct and sorted, and no row is zero.

**`orderedWeakPopov_mulWith`** (the composition lemma): if `P₁` is ordered weak Popov at `s` and
`P₂` at `t = rdeg_s(P₁)` (`updateShiftByRows P₁ s`), then `P₂ · P₁` is ordered weak Popov at `s`,
with `rdeg_s(P₂ · P₁) = rdeg_t(P₂)`. Row `k` of the product, entry `c`, is
`∑ᵢ P₂[k,i]·P₁[i,c]`; each term has `deg + s_c ≤ δ_k = rdeg_t(P₂)[k]`, strictly unless `i = k`
(row `k` of `P₂` has its rightmost maximum at `k`) and `c ≤ i` (row `i` of `P₁` has its rightmost
maximum at `i`); so the entries right of `k` stay below `δ_k`, and entry `k` has exactly the
shifted degree `δ_k`, through its term `i = k` alone (a product of nonzero polynomials over a
field).

Without the ordering the lemma fails (the pivot of row `k` of the product is the largest pivot of
`P₁` among the rows `P₂`'s leading row `k` reaches, which may repeat); the square shape with no
zero row is what CompPoly's PM-basis produces at every level once its leaf fills the pivot slots
(`PopovLeaf.lean`).
-/

namespace LeanVM.Extraction.Fast.Popov

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- **Ordered weak Popov** at shift `s`, size `n`: `n` rows of width `n`, row `i` with shifted
leading position `i`. -/
@[expose] def OrderedWeakPopov (M : PolynomialMatrix F) (s : Array Nat) (n : Nat) : Prop :=
  M.size = n ∧ ∀ i, i < n →
    (M.getD i #[]).size = n ∧ rowShiftedLeadingPosition? (M.getD i #[]) s = some i

omit [BEq F] [LawfulBEq F] in
theorem lt_size_of_rowGet_ne_zero {row : PolynomialRow F} {j : Nat} (h : rowGet row j ≠ 0) :
    j < row.size := by
  by_contra hj
  exact h (rowGet_of_size_le (by omega))

/-- The shifted degree of a row with a leading position is that position's shifted degree. -/
theorem rowShiftedDegree?_of_leadingPosition {row : PolynomialRow F} {s : Array Nat} {i : Nat}
    (h : rowShiftedLeadingPosition? row s = some i) :
    rowShiftedDegree? row s = some ((rowGet row i).natDegree + s.getD i 0) := by
  cases hdeg : rowShiftedDegree? row s with
  | none =>
      unfold rowShiftedLeadingPosition? at h
      rw [hdeg] at h
      cases h
  | some d =>
      have he := rowShiftedLeadingPosition?_entry_eq hdeg h
      rcases shiftedEntryDegree?_eq_some_iff_data.1 he with ⟨_, hd⟩
      rw [hd]

/-- The shifted leading position, characterized: a nonzero entry whose shifted degree bounds
every entry's, strictly to its right. -/
theorem leadingPosition_eq_some_iff {row : PolynomialRow F} {s : Array Nat} {i : Nat} :
    rowShiftedLeadingPosition? row s = some i ↔
      rowGet row i ≠ 0 ∧
      (∀ j, rowGet row j ≠ 0 →
        (rowGet row j).natDegree + s.getD j 0 ≤ (rowGet row i).natDegree + s.getD i 0) ∧
      (∀ j, i < j → rowGet row j ≠ 0 →
        (rowGet row j).natDegree + s.getD j 0 < (rowGet row i).natDegree + s.getD i 0) := by
  constructor
  · intro h
    have hdeg := rowShiftedDegree?_of_leadingPosition h
    have he := rowShiftedLeadingPosition?_entry_eq hdeg h
    refine ⟨(shiftedEntryDegree?_eq_some_iff_data.1 he).1, ?_, ?_⟩
    · intro j hj
      exact rowShiftedDegree?_entry_bound hdeg (lt_size_of_rowGet_ne_zero hj) hj
    · intro j hij hj
      have hle := rowShiftedDegree?_entry_bound hdeg (lt_size_of_rowGet_ne_zero hj) hj
      have hne := rowShiftedLeadingPosition?_no_larger_tie hdeg h
        (lt_size_of_rowGet_ne_zero hj) hij
      rw [shiftedEntryDegree?_eq_some_of_rowGet_ne_zero hj] at hne
      have : (rowGet row j).natDegree + s.getD j 0 ≠
          (rowGet row i).natDegree + s.getD i 0 := fun h' ↦ hne (by rw [h'])
      omega
  · rintro ⟨hi, hle, hlt⟩
    have hdeg : rowShiftedDegree? row s = some ((rowGet row i).natDegree + s.getD i 0) := by
      cases hd : rowShiftedDegree? row s with
      | none =>
          exfalso
          have hz := rowShiftedDegree?_eq_none_iff.1 hd
          exact hi (hz _ (by
            have hlt' := lt_size_of_rowGet_ne_zero hi
            rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt']
            exact Array.getElem_mem_toList hlt'))
      | some d =>
          have h1 := rowShiftedDegree?_le_of_entry_bound (fun k _ hk ↦ hle k hk) hd
          have h2 := rowShiftedDegree?_entry_bound hd (lt_size_of_rowGet_ne_zero hi) hi
          rw [show d = (rowGet row i).natDegree + s.getD i 0 by omega]
    rcases rowShiftedLeadingPosition?_some_of_degree hdeg with ⟨p, hp⟩
    have hge := rowShiftedLeadingPosition?_le_of_entry_eq_degree hdeg hp
      (lt_size_of_rowGet_ne_zero hi) (shiftedEntryDegree?_eq_some_of_rowGet_ne_zero hi)
    have he := rowShiftedLeadingPosition?_entry_eq hdeg hp
    rcases shiftedEntryDegree?_eq_some_iff_data.1 he with ⟨hpne, hpd⟩
    rcases Nat.lt_or_ge i p with hip | hip
    · have := hlt p hip hpne
      omega
    · rw [hp, show p = i by omega]

/-! ## Degree bounds through coefficients -/

/-- `p = 0`, or `deg p + a ≤ d`. -/
@[expose] def Bnd (p : Polynomial F) (a d : Nat) : Prop := p = 0 ∨ p.natDegree + a ≤ d

omit [BEq F] [LawfulBEq F] in
theorem bnd_iff {p : Polynomial F} {a d : Nat} :
    Bnd p a d ↔ ∀ m, d < m + a → p.coeff m = 0 := by
  constructor
  · rintro (rfl | h) m hm
    · simp
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · intro h
    by_cases hp : p = 0
    · exact Or.inl hp
    · refine Or.inr ?_
      by_contra hlt
      exact Polynomial.leadingCoeff_ne_zero.2 hp (h _ (by omega))

omit [BEq F] [LawfulBEq F] in
theorem bnd_sum {ι : Type*} (S : Finset ι) (f : ι → Polynomial F) {a d : Nat}
    (h : ∀ i ∈ S, Bnd (f i) a d) : Bnd (∑ i ∈ S, f i) a d := by
  rw [bnd_iff]
  intro m hm
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_eq_zero fun i hi ↦ bnd_iff.1 (h i hi) m hm

omit [BEq F] [LawfulBEq F] in
theorem bnd_mul {A B : Polynomial F} {a b d : Nat} (hA : Bnd A b d) (hB : Bnd B a b) :
    Bnd (A * B) a d := by
  rcases hA with rfl | hA
  · exact Or.inl (zero_mul B)
  rcases hB with rfl | hB
  · exact Or.inl (mul_zero A)
  refine Or.inr ?_
  have := Polynomial.natDegree_mul_le (p := A) (q := B)
  omega

omit [BEq F] [LawfulBEq F] in
theorem bnd_mono {p : Polynomial F} {a a' d : Nat} (h : Bnd p a d) (ha : a' ≤ a) :
    Bnd p a' d := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

omit [BEq F] [LawfulBEq F] in
theorem bnd_shift {p : Polynomial F} {a d : Nat} (h : Bnd p a d) : Bnd p (a + 1) (d + 1) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem bnd_toPoly_of_le {p : CPolynomial F} {a d : Nat}
    (h : p ≠ 0 → p.natDegree + a ≤ d) : Bnd p.toPoly a d := by
  by_cases hp : p = 0
  · exact Or.inl ((CPolynomial.toPoly_eq_zero_iff p).2 hp)
  · exact Or.inr (by rw [← CPolynomial.natDegree_toPoly]; exact h hp)

/-! ## The composition lemma -/

/-- Row `i < n` of an ordered weak Popov matrix: its entries' shifted degrees are bounded by
`t_i = deg P[i,i] + s_i`, strictly right of `i`. -/
private theorem owp_entry_bnd {P : PolynomialMatrix F} {s : Array Nat} {n i c : Nat}
    (hP : OrderedWeakPopov P s n) (hi : i < n) :
    Bnd (rowGet (P.getD i #[]) c).toPoly (s.getD c 0 + (if i < c then 1 else 0))
      ((rowGet (P.getD i #[]) i).natDegree + s.getD i 0) := by
  rcases leadingPosition_eq_some_iff.1 (hP.2 i hi).2 with ⟨_, hle, hlt⟩
  refine bnd_toPoly_of_le fun hc ↦ ?_
  split
  · have := hlt c (by assumption) hc
    omega
  · have := hle c hc
    omega

/-- The shift update reads the row shifted degrees of an ordered weak Popov matrix. -/
theorem updateShiftByRows_getD {P : PolynomialMatrix F} {s : Array Nat} {n i : Nat}
    (hP : OrderedWeakPopov P s n) (hi : i < n) :
    (updateShiftByRows P s).getD i 0 = (rowGet (P.getD i #[]) i).natDegree + s.getD i 0 := by
  have hi' : i < P.size := hP.1 ▸ hi
  rw [updateShiftByRows, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range hi', Option.map_some, Option.getD_some,
    rowShiftedDegree?_of_leadingPosition (hP.2 i hi).2]

/-- Row `k` of `P₂ · P₁`: width `n`, leading position `k`, and the shifted degree of its
entry `k` is row `k` of `P₂`'s `rdeg_s(P₁)`-degree. -/
private theorem mulWith_row (mulCtx : CPolynomial.MulContext F)
    {P₁ P₂ : PolynomialMatrix F} {s : Array Nat} {n : Nat}
    (h₁ : OrderedWeakPopov P₁ s n) (h₂ : OrderedWeakPopov P₂ (updateShiftByRows P₁ s) n)
    {k : Nat} (hk : k < n) :
    ((mulWith mulCtx P₂ P₁).getD k #[]).size = n ∧
      rowShiftedLeadingPosition? ((mulWith mulCtx P₂ P₁).getD k #[]) s = some k ∧
      (rowGet ((mulWith mulCtx P₂ P₁).getD k #[]) k).natDegree + s.getD k 0 =
        (rowGet (P₂.getD k #[]) k).natDegree + (updateShiftByRows P₁ s).getD k 0 := by
  have hk₂ : k < P₂.size := h₂.1 ▸ hk
  have hn : 0 < n := by omega
  have hwidth : MatrixWidth P₁ = n := by
    refine matrixWidth_eq_of_first_row (by rw [h₁.1]; exact hn) fun r hr ↦ ?_
    rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
    have hi' : i < P₁.size := by simpa [MatrixRows] using hi
    have := (h₁.2 i (h₁.1 ▸ hi')).1
    rw [DenseMatrix.array_getD_of_lt' _ _ hi'] at this
    rw [← hget]
    simpa [MatrixRows, Array.getElem_toList] using this
  rw [mulWith_getD _ _ _ hk₂]
  rcases leadingPosition_eq_some_iff.1 (h₂.2 k hk).2 with ⟨hkk, hle₂, hlt₂⟩
  set r₂ := P₂.getD k #[] with hr₂
  set Q := rowMulMatrixWith mulCtx r₂ P₁ with hQ
  -- `δ`, the row's `t`-degree (`t = rdeg_s(P₁)`), at its leading position `k`.
  set δ := (rowGet r₂ k).natDegree + (updateShiftByRows P₁ s).getD k 0 with hδ
  have hA : ∀ i, i < n → Bnd (rowGet r₂ i).toPoly
      ((rowGet (P₁.getD i #[]) i).natDegree + s.getD i 0 + (if k < i then 1 else 0)) δ := by
    intro i hi
    refine bnd_toPoly_of_le fun hc ↦ ?_
    rw [← updateShiftByRows_getD h₁ hi]
    split
    · have := hlt₂ i (by assumption) hc
      omega
    · have := hle₂ i hc
      omega
  -- Each term of entry `c`.
  have hterm : ∀ i, i < n → ∀ c,
      Bnd ((rowGet r₂ i).toPoly * (rowGet (P₁.getD i #[]) c).toPoly)
        (s.getD c 0 + (if k < i ∨ i < c then 1 else 0)) δ := by
    intro i hi c
    by_cases hki : k < i
    · have hB := bnd_shift (bnd_mono (owp_entry_bnd (c := c) h₁ hi) (Nat.le_add_right _ _))
      have hA' := hA i hi
      rw [ite_eq_left hki] at hA'
      rw [ite_eq_left (Or.inl hki)]
      exact bnd_mul hA' hB
    · have hA' := hA i hi
      rw [ite_eq_right hki, Nat.add_zero] at hA'
      have hB := owp_entry_bnd (c := c) h₁ hi
      by_cases hic : i < c
      · rw [ite_eq_left hic] at hB
        rw [ite_eq_left (Or.inr hic)]
        exact bnd_mul hA' hB
      · rw [ite_eq_right hic, Nat.add_zero] at hB
        rw [ite_eq_right (by omega), Nat.add_zero]
        exact bnd_mul hA' hB
  have hentry : ∀ c, c < n → (rowGet Q c).toPoly =
      ∑ i ∈ Finset.range n, (rowGet r₂ i).toPoly * (rowGet (P₁.getD i #[]) c).toPoly := by
    intro c hc
    rw [hQ, rowGet_rowMulMatrixWith_toPoly mulCtx r₂ P₁ (by rw [hwidth]; exact hc), h₁.1]
  have hQsize : Q.size = n := by rw [hQ, rowMulMatrixWith_size, hwidth]
  -- Every entry has `s`-degree at most `δ`, strictly right of `k`.
  have hbnd : ∀ c, Bnd (rowGet Q c).toPoly (s.getD c 0 + (if k < c then 1 else 0)) δ := by
    intro c
    rcases Nat.lt_or_ge c n with hc | hc
    · rw [hentry c hc]
      refine bnd_sum _ _ fun i hi ↦ bnd_mono (hterm i (Finset.mem_range.1 hi) c) ?_
      split
      · rw [ite_eq_left (by omega)]
      · omega
    · rw [rowGet_of_size_le (by omega), CPolynomial.toPoly_zero]
      exact Or.inl rfl
  -- Entry `k` has `s`-degree exactly `δ`.
  have hkn := lt_size_of_rowGet_ne_zero hkk
  have hdiag₁ : rowGet (P₁.getD k #[]) k ≠ 0 :=
    (leadingPosition_eq_some_iff.1 (h₁.2 k hk).2).1
  set A := (rowGet r₂ k).toPoly with hAdef
  set B := (rowGet (P₁.getD k #[]) k).toPoly with hBdef
  have hA0 : A ≠ 0 := by rw [hAdef, Ne, CPolynomial.toPoly_eq_zero_iff]; exact hkk
  have hB0 : B ≠ 0 := by rw [hBdef, Ne, CPolynomial.toPoly_eq_zero_iff]; exact hdiag₁
  have htk : (updateShiftByRows P₁ s).getD k 0 = B.natDegree + s.getD k 0 := by
    rw [updateShiftByRows_getD h₁ hk, hBdef, CPolynomial.natDegree_toPoly]
  have hAB : (A * B).natDegree + s.getD k 0 = δ := by
    rw [Polynomial.natDegree_mul hA0 hB0, hδ, htk, CPolynomial.natDegree_toPoly, ← hAdef]
    omega
  have hrest : Bnd (∑ i ∈ (Finset.range n).erase k,
      (rowGet r₂ i).toPoly * (rowGet (P₁.getD i #[]) k).toPoly) (s.getD k 0 + 1) δ := by
    refine bnd_sum _ _ fun i hi ↦ ?_
    rcases Finset.mem_erase.1 hi with ⟨hik, hi⟩
    have := hterm i (Finset.mem_range.1 hi) k
    rwa [ite_eq_left (by omega)] at this
  have hsplit := Finset.add_sum_erase (Finset.range n)
    (fun i ↦ (rowGet r₂ i).toPoly * (rowGet (P₁.getD i #[]) k).toPoly)
    (Finset.mem_range.2 hk)
  have hcoeff : ((rowGet Q k).toPoly).coeff (A * B).natDegree = (A * B).leadingCoeff := by
    rw [hentry k hk, ← hsplit, Polynomial.coeff_add,
      bnd_iff.1 hrest _ (by omega), add_zero]
    rfl
  have hQk0 : (rowGet Q k).toPoly ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hcoeff
    exact (mul_ne_zero hA0 hB0) (Polynomial.leadingCoeff_eq_zero.1 hcoeff.symm)
  have hQkdeg : (rowGet Q k).natDegree + s.getD k 0 = δ := by
    rw [CPolynomial.natDegree_toPoly]
    have hle : (rowGet Q k).toPoly.natDegree ≤ (A * B).natDegree := by
      rcases hbnd k with h | h
      · exact absurd h hQk0
      · rw [ite_eq_right (lt_irrefl k), Nat.add_zero] at h
        omega
    have hge : (A * B).natDegree ≤ (rowGet Q k).toPoly.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by
        rw [hcoeff]
        exact Polynomial.leadingCoeff_ne_zero.2 (mul_ne_zero hA0 hB0))
    omega
  refine ⟨hQsize, leadingPosition_eq_some_iff.2 ⟨?_, ?_, ?_⟩, hQkdeg⟩
  · rwa [Ne, ← CPolynomial.toPoly_eq_zero_iff]
  · intro j hj
    rcases hbnd j with h | h
    · exact absurd ((CPolynomial.toPoly_eq_zero_iff _).1 h) hj
    · rw [← CPolynomial.natDegree_toPoly] at h
      split at h <;> omega
  · intro j hkj hj
    rcases hbnd j with h | h
    · exact absurd ((CPolynomial.toPoly_eq_zero_iff _).1 h) hj
    · rw [← CPolynomial.natDegree_toPoly, ite_eq_left hkj] at h
      omega

/-- **The composition lemma.** `P₁` ordered weak Popov at `s`, `P₂` at `rdeg_s(P₁)`: their
product `P₂ · P₁` is ordered weak Popov at `s`. -/
theorem orderedWeakPopov_mulWith (mulCtx : CPolynomial.MulContext F)
    {P₁ P₂ : PolynomialMatrix F} {s : Array Nat} {n : Nat}
    (h₁ : OrderedWeakPopov P₁ s n) (h₂ : OrderedWeakPopov P₂ (updateShiftByRows P₁ s) n) :
    OrderedWeakPopov (mulWith mulCtx P₂ P₁) s n :=
  ⟨by rw [mulWith_size, h₂.1], fun _ hk ↦
    ⟨(mulWith_row mulCtx h₁ h₂ hk).1, (mulWith_row mulCtx h₁ h₂ hk).2.1⟩⟩

omit [LawfulBEq F] in
/-- An ordered weak Popov matrix is shifted weak Popov (distinct leading positions). -/
theorem OrderedWeakPopov.shiftedWeakPopov {M : PolynomialMatrix F} {s : Array Nat} {n : Nat}
    (h : OrderedWeakPopov M s n) : ShiftedWeakPopov M s := by
  intro i j hi hj hij _ _
  rw [(h.2 i (h.1 ▸ hi)).2, (h.2 j (h.1 ▸ hj)).2]
  exact fun h' ↦ hij (Option.some.inj h')

/-- An ordered weak Popov matrix has no zero row. -/
theorem OrderedWeakPopov.rowIsZero_eq_false {M : PolynomialMatrix F} {s : Array Nat} {n : Nat}
    (h : OrderedWeakPopov M s n) {i : Nat} (hi : i < n) : rowIsZero (M.getD i #[]) = false := by
  rcases leadingPosition_eq_some_iff.1 (h.2 i hi).2 with ⟨hne, _, _⟩
  cases hz : rowIsZero (M.getD i #[])
  · rfl
  · exfalso
    have hZ := rowIsZero_iff.1 hz
    have hlt := lt_size_of_rowGet_ne_zero hne
    exact hne (hZ _ (by
      rw [rowGet, DenseMatrix.array_getD_of_lt' _ _ hlt]
      exact Array.getElem_mem_toList hlt))

/-- Zero-row compaction keeps an ordered weak Popov matrix. -/
theorem OrderedWeakPopov.compactNonzeroRows_eq {M : PolynomialMatrix F} {s : Array Nat}
    {n : Nat} (h : OrderedWeakPopov M s n) : compactNonzeroRows M = M := by
  rw [compactNonzeroRows, Array.filter_eq_self]
  intro r hr
  rcases Array.getElem_of_mem hr with ⟨i, hi, rfl⟩
  have := h.rowIsZero_eq_false (i := i) (h.1 ▸ hi)
  rw [DenseMatrix.array_getD_of_lt' _ _ hi] at this
  rw [this]
  rfl

end

end LeanVM.Extraction.Fast.Popov
