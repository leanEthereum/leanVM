module

public import LeanVM.Cost.Bounds.RothRuckenstein
public import LeanVM.Protocol.Extraction.Fast.DecodeAdmissible

/-!
# Sizes along the decoder: the lanes and after

The sizes of the decoder's intermediate values, where they feed the next function's price (pure
facts about the proof-side definitions the extractor runs, `Fast/DecodeAdmissible.lean`):

* the lane's input: `lanePointsS` has `n` points (`lanePointsS_size`), distinct below `2^64`
  columns (`distinct_lanePointsS`); the symbol table `laneTable` has `n` columns, column `v` of the
  word's length (`laneTable_size`, `laneTable_getD_size`);
* the lane's output: **`gsRunDistinctNF_size_le`**, at most `max 1 ℓ` polynomials, each of at most
  `k` coefficients (`gsRunDistinctNF_mem_size_le`). The count is Roth–Ruckenstein's leaves: a node
  of degree `δ` has at most `δ` leaves below it (`prefixesWithFuelFast_size_le`: the children's
  leaves are at most the sum of their roots' multiplicities, `rr_children_leaves_le`);
* after the lane: `toNovelFast` has `2^κ` entries (`toNovelFast_size`), `novelFwd` `2^(κ+R)`
  (`novelFwd_size`); `laneListDistinct` and `laneEncodedDistinct` have at most `max 1 ℓ` entries
  (`laneListDistinct_length_le`, `laneEncodedDistinct_length`), of `2^(κ+1)` coefficients (a
  decoded polynomial's, of degree `< 2^κ + 6`) and `2^(κ+R)` evaluations
  (`mem_laneEncodedDistinct_size`);
* the pruning: `pruneStep` multiplies the number of survivors by at most the lane's list length
  (`pruneStep_length_le`), so after `U` lanes at most `(max 1 ℓ)^U` survivors
  (`pruneUpToDistinct_length_le`), each of `U` coefficient arrays of `2^(κ+1)` entries and at most `n`
  agreeing columns (`pruneUpToDistinct_mem`); `decodeStacksDistinct` has as many stacks
  (`decodeStacksDistinct_length`).

The bound `(max 1 ℓ)^U` is what the code admits without coding theory; the Johnson bound for the
interleaved code (survivors agree jointly on `≥ A` columns) would bound them by the list size `L`.
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.GuruswamiSudan LeanVM.Extraction.Fast LeanVM.Extraction LeanVM.Parameters

public section

/-! ## The lane's input -/

theorem lanePointsS_size (n : ℕ) (S : ℕ → ℕ → K) (u : ℕ) : (lanePointsS n S u).size = n := by
  simp [lanePointsS]

theorem laneTable_size (n : ℕ) (W : ℕ → List K) : (laneTable n W).size = n := by
  simp [laneTable]

/-- Column `v < n` of the table is the word's column `v`, reversed: as many entries. -/
theorem laneTable_getD_size {n v : ℕ} (hv : v < n) (W : ℕ → List K) :
    ((laneTable n W).getD v #[]).size = (W v).length := by
  simp [laneTable, Array.getD_eq_getD_getElem?, hv]

/-! ## Roth–Ruckenstein's leaves -/

theorem foldl_append_size {α β : Type*} (f : α → Array β) (l : List α) (init : Array β) :
    (l.foldl (fun out a ↦ out ++ f a) init).size = init.size + (l.map fun a ↦ (f a).size).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih => simp [ih, Nat.add_assoc]

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- **One level, leaves**: the children of a node, each counted `max 1 (its degree)`, sum to at
most the node's degree. -/
theorem rr_children_leaves_le [CharP F 2] {fr : FieldRootContext F} (hfr : RootsNodup fr)
    (Q : CBivariate F) :
    ((rootsInFieldForNonzeroEquation fr
        (initialCoefficientPolynomial (CBivariate.stripXAdicFactor Q))).toList.map fun a ↦
        max 1 (rrDeg (residualFast (stripFast Q) a))).sum ≤ rrDeg Q := by
  rw [stripFast_eq]
  set Qn := CBivariate.stripXAdicFactor Q
  set P := initialCoefficientPolynomial Qn
  by_cases hP : P = 0
  · rw [hP, rootsInFieldForNonzeroEquation_of_eq_zero]
    simp
  have hroots : rootsInFieldForNonzeroEquation fr P = fr.rootsInField P := by
    simp [rootsInFieldForNonzeroEquation, hP]
  rw [hroots]
  set L := (fr.rootsInField P).toList
  have hL : L.Nodup := hfr P
  rw [← List.sum_toFinset _ hL]
  have hmult : ∀ a ∈ L.toFinset,
      max 1 (rrDeg (residualFast Qn a)) ≤ P.toPoly.rootMultiplicity a := by
    intro a ha
    have hroot : CPolynomial.eval a P = 0 := fr.sound P a (List.mem_toFinset.1 ha)
    have hP' : P.toPoly ≠ 0 := by
      intro h; apply hP; rw [← CPolynomial.toPoly_inj, CPolynomial.toPoly_zero]; exact h
    have hpos : 0 < P.toPoly.rootMultiplicity a := by
      rw [Polynomial.rootMultiplicity_pos hP', Polynomial.IsRoot, ← CPolynomial.eval_toPoly]
      exact hroot
    have h1 : rrDeg (residualFast Qn a) ≤ P.toPoly.rootMultiplicity a :=
      rrDeg_residualFast_le Qn a hP
    omega
  refine (Finset.sum_le_sum hmult).trans ((sum_rootMultiplicity_le _ _).trans ?_)
  rw [rrDeg, ← CPolynomial.natDegree_toPoly]

/-- **Roth–Ruckenstein returns at most `max 1 (rrDeg Q)` prefixes.** -/
theorem prefixesWithFuelFast_size_le [CharP F 2] {fr : FieldRootContext F} (hfr : RootsNodup fr)
    (fuel : ℕ) : ∀ (Q : CBivariate F) (depth : ℕ) (pref : CPolynomial F),
      (prefixesWithFuelFast fr fuel Q depth pref).size ≤ max 1 (rrDeg Q) := by
  induction fuel with
  | zero => intro Q depth pref; simp [prefixesWithFuelFast]
  | succ fuel ih =>
    intro Q depth pref
    rw [prefixesWithFuelFast]
    split
    · simp
    · rw [← Array.foldl_toList, foldl_append_size, Array.size_empty, Nat.zero_add]
      refine le_trans ?_ (le_max_right _ _)
      refine le_trans ?_ (rr_children_leaves_le hfr Q)
      rw [initialCoeffFast_eq, stripFast_eq]
      exact list_sum_map_le fun a _ ↦ ih _ _ _

/-! ## The lane's output -/

/-- The polynomial the lane interpolates, an interpolation witness (on distinct points). -/
theorem interpolateDistinct_valid {points : Array (K × K)} (h : DistinctXCoordinates points)
    {params : GSInterpParams} {Q : CBivariate K} (hQ : interpolateDistinct points params = some Q) :
    ValidInterpolationWitness points params Q :=
  interpContextFast.sound points params Q (by rw [← interpolateDistinct_eq h]; exact hQ)

/-- **The lane returns at most `max 1 ℓ` polynomials** (`ℓ = ⌊W/(k − 1)⌋`), on distinct points. -/
theorem gsRunDistinctNF_size_le {points : Array (K × K)} (h : DistinctXCoordinates points)
    (params : GSInterpParams) (radius : ℕ) (hk : 1 < params.messageDegree) :
    (gsRunDistinctNF points params radius).size ≤ max 1 (interpolationYCap params) := by
  rw [gsRunDistinctNF]
  split
  · simp
  · rename_i Q hQ
    have hv := interpolateDistinct_valid h hQ
    refine Array.size_filter_le.trans ?_
    rw [prefixesNF_eq_truncD hv, prefixesTruncD_eq,
      prefixesTrunc_eq fieldRootCtxFast _ Q _ (fun _ ↦ replayPath Q []) 0 default rfl]
    refine (prefixesWithFuelFast_size_le fieldRootCtxFast_nodup _ _ _ _).trans ?_
    have hd := rrDeg_le (lenLe_of_validInterpolation hv hk).1
    simp only [replayPath, List.foldl_nil, Nat.add_sub_cancel] at hd ⊢
    omega

/-- **Each polynomial the lane returns has at most `k` coefficients** (the degree filter). -/
theorem gsRunDistinctNF_mem_size_le {points : Array (K × K)} {params : GSInterpParams}
    {radius : ℕ} {p : CPolynomial K} (hp : p ∈ gsRunDistinctNF points params radius) :
    p.val.size ≤ params.messageDegree := by
  rw [gsRunDistinctNF] at hp
  split at hp
  · simp at hp
  · rw [Array.mem_filter] at hp
    have := hp.2
    simp only [Bool.and_eq_true, degreeLtBool, decide_eq_true_eq] at this
    exact this.1

/-! ## After the lane -/

theorem novelInv_size (κ : ℕ) (y : Array K) (hy : y.size = 2 ^ κ) :
    (novelInv κ y).size = 2 ^ κ := by
  rw [novelInv]
  generalize List.range κ = l
  induction l generalizing y with
  | nil => exact hy
  | cons i l ih => rw [List.foldl_cons]; exact ih _ (by simp [novelInvStage])

/-- **`toNovelFast` has `2^κ` entries.** -/
theorem toNovelFast_size (κ : ℕ) (p : CPolynomial K) : (toNovelFast κ p).size = 2 ^ κ :=
  novelInv_size κ _ (by simp)

/-- **`novelFwd` has `2^(κ+R)` entries.** -/
theorem novelFwd_size (κ R : ℕ) (c : Array K) : (novelFwd κ R c).size = 2 ^ (κ + R) := by
  rw [novelFwd]
  generalize List.range κ = l
  induction l with
  | nil => simp
  | cons i l _ => rw [List.foldr_cons]; simp [novelFwdStage]

/-- The lane's points are distinct at `κ + R ≤ 64`. -/
theorem lanePointsS_distinct {κ R : ℕ} (h : κ + R ≤ 64) (S : ℕ → ℕ → K) (u : ℕ) :
    DistinctXCoordinates (lanePointsS (2 ^ (κ + R)) S u) :=
  distinct_lanePointsS _ (Nat.pow_le_pow_right (by norm_num) h) S u

/-- **The lane's list has at most `max 1 ℓ` entries** (at `κ + R ≤ 64`, `k > 1`). -/
theorem laneListDistinct_length_le {κ R A : ℕ} (h : κ + R ≤ 64)
    (hk : 1 < (gsParamsFor (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A).interp.messageDegree)
    (S : ℕ → ℕ → K) (u : ℕ) :
    (laneListDistinct κ R A S u).length ≤
      max 1 (interpolationYCap (gsParamsFor (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A).interp) := by
  rw [laneListDistinct, List.length_mergeSort]
  refine (List.dedup_sublist _).length_le.trans ?_
  rw [List.length_map, Array.length_toList, gsLaneDistinct]
  exact gsRunDistinctNF_size_le (lanePointsS_distinct h S u) _ _ hk

/-- The lane's list entries have `2^(κ+1)` coefficients. -/
theorem mem_laneListDistinct_size {κ R A : ℕ} {S : ℕ → ℕ → K} {u : ℕ} {c : Array K}
    (hc : c ∈ laneListDistinct κ R A S u) : c.size = 2 ^ (κ + 1) := by
  rw [laneListDistinct, List.mem_mergeSort, List.mem_dedup, List.mem_map] at hc
  obtain ⟨p, -, rfl⟩ := hc
  exact toNovelFast_size (κ + 1) p

theorem laneEncodedDistinct_length (κ R A : ℕ) (S : ℕ → ℕ → K) (u : ℕ) :
    (laneEncodedDistinct κ R A S u).length = (laneListDistinct κ R A S u).length := by
  rw [laneEncodedDistinct, List.length_map]

/-- **The lane's encoded entries**: `2^(κ+1)` coefficients, `2^(κ+R)` evaluations (`1 ≤ R`). -/
theorem mem_laneEncodedDistinct_size {κ R A : ℕ} (hR : 1 ≤ R) {S : ℕ → ℕ → K} {u : ℕ}
    {e : Array K × Array K} (he : e ∈ laneEncodedDistinct κ R A S u) :
    e.1.size = 2 ^ (κ + 1) ∧ e.2.size = 2 ^ (κ + R) := by
  rw [laneEncodedDistinct, List.mem_map] at he
  obtain ⟨c, hc, rfl⟩ := he
  refine ⟨mem_laneListDistinct_size hc, ?_⟩
  rw [novelFwd_size, show κ + 1 + (R - 1) = κ + R by omega]

/-! ## The pruning -/

/-- **A pruning step multiplies the survivors by at most the lane's list length.** -/
theorem pruneStep_length_le (A : ℕ) (sym : ℕ → K) (L : List (Array K × Array K))
    (st : List (List (Array K) × List ℕ)) :
    (pruneStep A sym L st).length ≤ st.length * L.length := by
  induction st with
  | nil => simp [pruneStep]
  | cons s st ih =>
    rw [pruneStep, List.flatMap_cons, List.length_append]
    rw [pruneStep] at ih
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm (st.length * _)]
    exact Nat.add_le_add (List.length_filterMap_le _ _) ih

/-- A survivor of a pruning step extends a survivor by one entry of the lane's list, its columns
a sublist. -/
theorem mem_pruneStep {A : ℕ} {sym : ℕ → K} {L : List (Array K × Array K)}
    {st : List (List (Array K) × List ℕ)} {s' : List (Array K) × List ℕ}
    (h : s' ∈ pruneStep A sym L st) :
    ∃ s ∈ st, ∃ ce ∈ L, s'.1 = s.1 ++ [ce.1] ∧ s'.2.Sublist s.2 := by
  rw [pruneStep, List.mem_flatMap] at h
  obtain ⟨s, hs, h⟩ := h
  rw [List.mem_filterMap] at h
  obtain ⟨ce, hce, h⟩ := h
  dsimp only at h
  split at h
  · cases h
    exact ⟨s, hs, ce, hce, rfl, List.filter_sublist⟩
  · cases h

/-- **The survivors after `U` lanes**: at most `B^U` (`B` bounding the lanes' list lengths), each
`U` coefficient arrays of `2^(κ+1)` entries, its columns a sublist of the `n` columns. -/
theorem pruneUpToDistinct_bounds {κ R A B : ℕ} (W : ℕ → List K)
    (hB : ∀ u, (laneEncodedDistinct κ R A (tableSymbol (laneTable (2 ^ (κ + R)) W)) u).length ≤ B)
    (U : ℕ) :
    (pruneUpToDistinct κ R A W U).length ≤ B ^ U ∧
      ∀ s ∈ pruneUpToDistinct κ R A W U, s.1.length = U ∧ (∀ c ∈ s.1, c.size = 2 ^ (κ + 1)) ∧
        s.2.Sublist (List.range (2 ^ (κ + R))) := by
  rw [pruneUpToDistinct]
  induction U with
  | zero => simp
  | succ U ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hlen, hmem⟩ := ih
    split
    · simp
    · refine ⟨(pruneStep_length_le _ _ _ _).trans ?_, fun s' hs' ↦ ?_⟩
      · rw [Nat.pow_succ]
        exact Nat.mul_le_mul hlen (hB U)
      · obtain ⟨s, hs, ce, hce, h1, h2⟩ := mem_pruneStep hs'
        obtain ⟨hs1, hs2, hs3⟩ := hmem s hs
        refine ⟨by rw [h1, List.length_append, hs1]; rfl, fun c hc ↦ ?_, h2.trans hs3⟩
        rw [h1, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact hs2 c hc
        · rw [laneEncodedDistinct, List.mem_map] at hce
          obtain ⟨c, hc, rfl⟩ := hce
          exact mem_laneListDistinct_size hc

/-- **The survivors after `U` lanes are at most `(max 1 ℓ)^U`** (at `κ + R ≤ 64`, `k > 1`). -/
theorem pruneUpToDistinct_length_le {κ R A : ℕ} (h : κ + R ≤ 64)
    (hk : 1 < (gsParamsFor (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A).interp.messageDegree)
    (W : ℕ → List K) (U : ℕ) :
    (pruneUpToDistinct κ R A W U).length ≤
      (max 1 (interpolationYCap
        (gsParamsFor (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A).interp)) ^ U :=
  (pruneUpToDistinct_bounds W (fun u ↦ by
    rw [laneEncodedDistinct_length]; exact laneListDistinct_length_le h hk _ u) U).1

/-- The decoded stacks are as many as the survivors of the `2^6` lanes. -/
theorem decodeStacksDistinct_length (μ R : ℕ) (W : ℕ → List K) :
    (decodeStacksDistinct μ R W).length =
      (pruneUpToDistinct (μ - Whir.initialFold) R (johnsonThreshold μ R) W (2 ^ Whir.initialFold)).length := by
  rw [decodeStacksDistinct, List.length_map]

end

end LeanVM.Cost.Bounds
