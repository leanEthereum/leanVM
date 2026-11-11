module

public import LeanVM.Protocol.Extraction.Fast.Extract
public import LeanVM.Protocol.Extraction.Fast.TruncNoFallback
public import LeanVM.Protocol.Extraction.Fast.AfterRoot
public import LeanVM.Protocol.Extraction.Params

/-!
# The decoder at admissible shapes: no full decoder

`gsLaneAtFast` runs `gsRunDistinct` where the final root check is redundant (`checkRedundant`),
and the full decoder (`decodeWithParams gsContextFast`) elsewhere. At the shapes the extractor
decodes, the replay's admissible ones (`Whir.Admissible`: `16 ≤ μ ≤ 32`, `1 ≤ R ≤ 4`, checked by
`readSizesPure`, so by `afterRootDirect`: `admissible_of_afterRootDirect`), it is always
redundant:

* `checkRedundant_of_le`: at most `2^64` columns and an agreement `1 ≤ A ≤ n` make the check
  redundant, as the weighted degree is `W = m·A − 1` and the radius `n − A`, so
  `W < m·(n − radius) = m·A` (`gsMultiplicityAt_pos`: `m ≥ 1`);
* `checkRedundant_johnson`: at every admissible shape, at the Johnson threshold
  (`johnsonThreshold_bounds`: `A ≤ n`, `A² > D·n > 0`).

No evaluation: the window enters only through the bounds on `μ` and `R`.

The lane chain is restated without the branch, and with Roth–Ruckenstein's fallback removed
(`gsRunDistinctNF`, `Fast/TruncNoFallback.lean`) (`gsLaneDistinct`, …, `decodeStacksDistinct`) and
proved equal to the fast chain at admissible shapes (**`decodeStacksDistinct_eq`**); the extractor
the cost machine runs calls it (`Fast/Compiled.lean`).
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Extraction
open CompPoly CompPoly.GuruswamiSudan

public section

/-! ## The check is redundant -/

theorem gsMultiplicityAt_pos (k n A : ℕ) : 1 ≤ gsMultiplicityAt k n A := by
  unfold gsMultiplicityAt
  cases h : (List.range' 1 (gsMultiplicityBoundAt k n A)).find?
      (fun m ↦ gsPass k n (n - A) (gsParamsAt k n A m)) with
  | none => simp [gsMultiplicityBoundAt]
  | some m =>
    have := List.mem_range'.1 (List.mem_of_find?_eq_some h)
    simp only [Option.getD_some]
    omega

/-- **The final root check is redundant** at most `2^64` columns and an agreement `1 ≤ A ≤ n`. -/
theorem checkRedundant_of_le {κ R A : ℕ} (hκR : κ + R ≤ 64) (hA : 1 ≤ A) (hAn : A ≤ 2 ^ (κ + R)) :
    checkRedundant κ R (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A) = true := by
  have hm := gsMultiplicityAt_pos (2 ^ κ) (2 ^ (κ + R)) A
  rw [checkRedundant, Bool.and_eq_true]
  refine ⟨decide_eq_true hκR, decide_eq_true ?_⟩
  show gsMultiplicityAt (2 ^ κ) (2 ^ (κ + R)) A * A - 1 <
    gsMultiplicityAt (2 ^ κ) (2 ^ (κ + R)) A * (2 ^ (κ + R) - (2 ^ (κ + R) - A))
  rw [show 2 ^ (κ + R) - (2 ^ (κ + R) - A) = A by omega]
  have : 1 ≤ gsMultiplicityAt (2 ^ κ) (2 ^ (κ + R)) A * A := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by omega) (by omega))
  omega

/-- **At every admissible shape the final root check is redundant** (at the Johnson threshold). -/
theorem checkRedundant_johnson {μ R : ℕ} (h : Whir.Admissible μ R) :
    checkRedundant (μ - initialFold) R
      (gsParamsFor (2 ^ (μ - initialFold)) (2 ^ (μ - initialFold + R)) (johnsonThreshold μ R)) =
      true := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold Whir.minLogStack at h1
  unfold Whir.maxLogStack at h2
  obtain ⟨hAn, hD⟩ := johnsonThreshold_bounds ⟨h1, h2⟩ ⟨h3, h4⟩
  have hκ : 9 ≤ μ - initialFold := by simp only [initialFold]; omega
  have hD1 : 1 ≤ 2 ^ (μ - initialFold) - 1 := by
    have : 2 ^ 9 ≤ 2 ^ (μ - initialFold) := Nat.pow_le_pow_right (by norm_num) hκ
    omega
  have hn1 : 1 ≤ 2 ^ (μ - initialFold + R) := Nat.one_le_two_pow
  have hA : 1 ≤ johnsonThreshold μ R := by
    rcases Nat.eq_zero_or_pos (johnsonThreshold μ R) with h0 | h0
    · rw [h0, Nat.zero_mul] at hD
      exact absurd hD (Nat.not_lt_zero _)
    · exact h0
  exact checkRedundant_of_le (by simp only [initialFold]; omega) hA hAn

/-! ## The lane chain without the full decoder -/

/-- `gsLaneAtFast` without its branch, and Roth–Ruckenstein without its fallback:
`gsRunDistinctNF` only (`Fast/TruncNoFallback.lean`). -/
@[expose] def gsLaneDistinct (κ R A : ℕ) (S : ℕ → ℕ → K) (u : ℕ) : Array (CPolynomial K) :=
  let params := gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A
  gsRunDistinctNF (lanePointsS (2 ^ (κ + R)) S u) params.interp params.radius

/-- `laneListAtFast` with `gsLaneDistinct`. -/
@[expose] def laneListDistinct (κ R A : ℕ) (S : ℕ → ℕ → K) (u : ℕ) : List (Array K) :=
  (((gsLaneDistinct κ R A S u).toList.map (toNovelFast κ)).dedup).mergeSort coeffsLE

/-- `laneEncodedAtFast` with `laneListDistinct`. -/
@[expose] def laneEncodedDistinct (κ R A : ℕ) (S : ℕ → ℕ → K) (u : ℕ) :
    List (Array K × Array K) :=
  (laneListDistinct κ R A S u).map fun c ↦ (c, novelFwd κ R c)

/-- `pruneUpToFast` with `laneEncodedDistinct`. -/
@[expose] def pruneUpToDistinct (κ R A : ℕ) (W : ℕ → List K) (U : ℕ) :
    List (List (Array K) × List ℕ) :=
  let T := laneTable (2 ^ (κ + R)) W
  (List.range U).foldl
    (fun st u ↦
      if st.isEmpty then []
      else pruneStep A (tableSymbol T u) (laneEncodedDistinct κ R A (tableSymbol T) u) st)
    [([], List.range (2 ^ (κ + R)))]

/-- **The decoded stacks without the full decoder** (`decodeStacksFast`, the lanes by
`gsRunDistinctNF` only). -/
@[expose] def decodeStacksDistinct (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  (pruneUpToDistinct (μ - initialFold) R (johnsonThreshold μ R) W (2 ^ initialFold)).map
    fun s ↦ stackOf μ s.1

theorem gsLaneDistinct_eq {κ R A : ℕ} (h : checkRedundant κ R (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A))
    (S : ℕ → ℕ → K) (u : ℕ) : gsLaneDistinct κ R A S u = gsLaneAtFast κ R A S u := by
  have h64 : κ + R ≤ 64 := by
    rw [checkRedundant, Bool.and_eq_true] at h
    exact of_decide_eq_true h.1
  rw [gsLaneDistinct, gsLaneAtFast]
  simp only [h, ↓reduceIte]
  exact gsRunDistinctNF_eq
    (distinct_lanePointsS _ (Nat.pow_le_pow_right (by norm_num) h64) S u) _ _

theorem pruneUpToDistinct_eq {κ R A : ℕ}
    (h : checkRedundant κ R (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A)) (W : ℕ → List K) (U : ℕ) :
    pruneUpToDistinct κ R A W U = pruneUpToFast κ R A W U := by
  simp only [pruneUpToDistinct, pruneUpToFast, laneEncodedDistinct, laneEncodedAtFast,
    laneListDistinct, laneListAtFast, gsLaneDistinct_eq h]

/-- **At admissible shapes, the decoder without the full decoder is the fast one.** -/
theorem decodeStacksDistinct_eq {μ R : ℕ} (h : Whir.Admissible μ R) (W : ℕ → List K) :
    decodeStacksDistinct μ R W = decodeStacksFast μ R W := by
  rw [decodeStacksDistinct, decodeStacksFast, decodeStacksAtFast,
    pruneUpToDistinct_eq (checkRedundant_johnson h)]

/-! ## The replay's shapes are admissible -/

/-- **The layouts `afterRootDirect` returns are admissible**: `readSizesPure` checks the rate
exponent and the stack size. -/
theorem admissible_of_afterRootDirect {bytecode : List K} {π : Proof} {layout : Layout} {R : ℕ}
    {st : VerifierProgramState} (h : afterRootDirect bytecode π = some ((layout, R), st)) :
    Whir.Admissible layout.stackLog R := by
  unfold afterRootDirect at h
  obtain ⟨r, hr, hc⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨t, -, ht⟩ := Option.map_eq_some_iff.1 hc
  have hr1 : r.1 = (layout, R) := congrArg Prod.fst ht
  obtain ⟨⟨l, R'⟩, s'⟩ := r
  obtain ⟨rfl, rfl⟩ : l = layout ∧ R' = R := Prod.mk.inj hr1
  unfold readSizesPure at hr
  obtain ⟨r', -, hr'⟩ := Option.bind_eq_some_iff.1 hr
  split_ifs at hr' with h1
  dsimp only at hr'
  split_ifs at hr' with h2
  obtain ⟨layout', -, hl⟩ := Option.bind_eq_some_iff.1 hr'
  split_ifs at hl with h3
  simp only [Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
  exact ⟨h3.1, h3.2, h2.1, h2.2⟩

/-- **The lighter layouts `afterRootLite` returns are admissible.** -/
theorem admissible_of_afterRootLite {bytecode : List K} {π : Proof} {layout : LayoutLite} {R : ℕ}
    {st : VerifierProgramState} (h : afterRootLite bytecode π = some ((layout, R), st)) :
    Whir.Admissible layout.stackLog R := by
  rw [afterRootLite_eq, ← afterRootDirect_eq] at h
  obtain ⟨⟨⟨full, R'⟩, st'⟩, hr, hl⟩ := Option.map_eq_some_iff.1 h
  simp only [liteResult, Prod.mk.injEq] at hl
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
  exact admissible_of_afterRootDirect hr

end

end LeanVM.Extraction.Fast
