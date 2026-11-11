module

public import LeanVM.Protocol.Extraction.Extractor
public import LeanVM.Protocol.Extraction.Fast.RothRuckenstein
public import LeanVM.Protocol.Extraction.Lane
public import LeanVM.Protocol.Extraction.Prune
public import LeanVM.Protocol.Extraction.Fast.Karatsuba
public import LeanVM.Protocol.Extraction.Fast.Truncate
public import LeanVM.Protocol.Extraction.Fast.Address
public import LeanVM.Protocol.Extraction.Fast.Order
public import LeanVM.Protocol.Extraction.Fast.RootFinder
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Correctness
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant

/-!
# The extractor, fast

`extractFast` is the knowledge extractor (`LeanVM.Extraction.extract`, `Extraction/Extractor.lean`)
with a faster lane decoder, `gsLaneAtFast`:

* Roth–Ruckenstein's substitution a Taylor shift (`Fast/RothRuckenstein.lean`): `gsContextFast` is
  `gsContext` with `rothRuckensteinRootContextFast`;
* CompPoly's steps whose code costs more than their algorithm, restated and proved equal
  (`Fast/DecoderFast.lean`): Lee–O'Sullivan's normalization and the vanishing polynomial
  (`interpContext` is `interpContextFast`), the root finder (`fieldRootCtxFast`,
  `Fast/RootFinder.lean`);
* the lane decoder's points distinct, so the interpolation skips its distinctness check, and the
  distance filter evaluating by Horner's rule (`gsRunDistinct`);
* the word's columns reversed once (`laneTable`), the lanes' symbols read from the table
  (`tableSymbol`, `pruneUpToFast`, `fastStacksFast`);
* without the final root check where the parameters make it redundant (`gsRunNoCheck`,
  `checkRedundant`: at most `2^64` columns and `W < m·(n − radius)`, as at every shape the
  statement decodes, `W = m·A − 1`, `radius = n − A`);
* the interpolation: Lee–O'Sullivan's (`interpContext`) at every shape (the compiled decoder's is
  the approximant basis, `Fast/LanePM.lean`). Another interpolation may return another
  polynomial, so another list in another order: what the list holds does not depend on it
  (`mem_gsRunNoCheck`: the polynomials of degree `< k` within the radius), and the statement sorts
  each lane's list (`laneListAt`), so the
  sorted lists are equal (`laneListAtFast_eq`).

The definitions from the lane decoder up to the extractor are copied with it (a `@[csimp]` lemma
acts where code is compiled, and the statement's definitions are compiled in `Statement/`), each
proved equal to its original: **`extractFast_eq`**: `extractFast = extract`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash LeanVM.Extraction
open CompPoly CompPoly.GuruswamiSudan

public section

/-- The list decoder's interpolation (`gsContext`'s): Lee–O'Sullivan, Mulders–Storjohann, with
the fast normalization and vanishing polynomial (`interpContextFast`, `Fast/DecoderFast.lean`). -/
@[expose] def interpContext : GSInterpContext K :=
  interpContextFast

theorem interpContext_eq : interpContext =
    LeeOSullivan.leeOSullivanInterpContext CPolynomial.VanishingPolynomialContext.direct
      (CPolynomial.BatchEvalContext.horner K)
      (PolynomialMatrix.muldersStorjohannFastReducerContext K) :=
  interpContextFast_eq

/-- The list decoder's context with Roth–Ruckenstein's fast substitution, and the restated root
finder (`fieldRootCtxFast`). -/
@[expose] def gsContextFast : GSFilteredCoreContext K :=
  filteredCoreContextOfInterpRootContexts interpContext
    (rothRuckensteinRootContextFast fieldRootCtxFast)

theorem gsContextFast_eq : gsContextFast = gsContext := by
  rw [gsContextFast, fieldRootCtxFast_eq, rothRuckensteinRootContextFast_eq, gsContext,
    interpContext_eq]

/-! ## The final root check, dropped

Roth–Ruckenstein's prefixes are filtered twice: by `isRootYDegreeLtBool` (degree `< k` and
`Q(X, p(X)) = 0`, a Horner evaluation of `Q` at `p`: about `ℓ·(W + ℓ·k)²` operations per
candidate), then by the distance filter (`passesCandidateDistance`: at most `radius` mismatches).
When `W < m·(n − radius)` and the points are distinct, a candidate of degree `< k` that passes the
distance filter matches on at least `n − radius` points, so `Q(X, p(X)) = 0` already
(`composeY_eq_zero_of_enough_matching_multiplicity_points`, CompPoly's Guruswami–Sudan lemma):
the root check is redundant, and `gsRunNoCheck` keeps the degree check and the distance filter. -/

/-- **The list decoder without the final root check**: the fast Roth–Ruckenstein prefixes of
the interpolated `Q` (truncated, `prefixesTruncD`) of degree `< k` that pass the distance
filter. -/
@[expose] def gsRunNoCheck (I : GSInterpContext K) (points : Array (K × K))
    (params : GSInterpParams) (radius : ℕ) : Array (CPolynomial K) :=
  match I.interpolate points params with
  | none => #[]
  | some Q =>
    (prefixesTruncD fieldRootCtxFast params.messageDegree
        (CBivariate.truncateX Q params.messageDegree) params.messageDegree Q [] 0
        default).filter fun p ↦
      degreeLtBool p params.messageDegree && passesCandidateDistance points radius p

theorem candidateMismatchCount_add_matchingPointCount (points : Array (K × K))
    (p : CPolynomial K) :
    candidateMismatchCount points p + matchingPointCount points p = points.size := by
  rw [candidateMismatchCount, matchingPointCount, ← Array.foldl_toList, ← Array.foldl_toList,
    ← Array.length_toList]
  generalize points.toList = l
  have h : ∀ a b : ℕ,
      l.foldl (fun count point ↦
          if CPolynomial.eval point.1 p == point.2 then count else count + 1) a +
        l.foldl (fun count point ↦
          if CPolynomial.eval point.1 p == point.2 then count + 1 else count) b =
        a + b + l.length := by
    induction l with
    | nil => simp
    | cons q l ih =>
      intro a b
      simp only [List.foldl_cons, List.length_cons]
      split <;> rw [ih] <;> omega
  simpa using h 0 0

theorem gsRunNoCheck_eq (I : GSInterpContext K) (points : Array (K × K))
    (params : GSInterpParams) (radius : ℕ) (hdist : DistinctXCoordinates points)
    (hW : params.weightedDegreeBound < params.multiplicity * (points.size - radius)) :
    gsRunNoCheck I points params radius =
      gsFilteredCore points I (rothRuckensteinRootContext K fieldRootCtx) params radius := by
  rw [gsRunNoCheck, fieldRootCtxFast_eq, gsFilteredCore, gsCore]
  cases hQ : I.interpolate points params with
  | none => rfl
  | some Q =>
    have hvalid := I.sound points params Q hQ
    dsimp only
    rw [prefixesTruncD_eq, prefixesTrunc_eq fieldRootCtx params.messageDegree Q params.messageDegree
      (fun _ ↦ replayPath Q []) 0 default rfl]
    simp only [replayPath, List.foldl_nil]
    simp only [rothRuckensteinRootContext, rothRuckensteinRootsYDegreeLt,
      transformedRothRuckensteinRootsYDegreeLt, transformedRothRuckensteinRootPrefixes,
      prefixesWithFuelFast_eq, Array.filter_filter]
    rw [← Array.toList_inj, Array.toList_filter, Array.toList_filter]
    refine List.filter_congr fun p _ ↦ ?_
    simp only [isRootYDegreeLtBool]
    by_cases hd : degreeLtBool p params.messageDegree = true
    · by_cases hp : passesCandidateDistance points radius p = true
      · have hmis : candidateMismatchCount points p ≤ radius := by
          simpa [passesCandidateDistance] using hp
        have hsum := candidateMismatchCount_add_matchingPointCount points p
        have hmatches : params.weightedDegreeBound <
            params.multiplicity * matchingPointCount points p :=
          lt_of_lt_of_le hW (Nat.mul_le_mul_left _ (by omega))
        have hroot := composeYHorner_eq_zero_of_composeY
          (composeY_eq_zero_of_enough_matching_multiplicity_points hvalid
            (degreeLt_of_degreeLtBool hd) hdist hmatches)
        simp [hd, hp, hroot]
      · simp [hp]
    · simp [hd]

/-- **What the run lists does not depend on the interpolation**: the polynomials of degree `< k`
within the radius, if the points have an interpolation polynomial. -/
theorem mem_gsRunNoCheck (I : GSInterpContext K) (points : Array (K × K))
    (params : GSInterpParams) (radius : ℕ) (hdist : DistinctXCoordinates points)
    (hW : params.weightedDegreeBound < params.multiplicity * (points.size - radius))
    (p : CPolynomial K) :
    p ∈ (gsRunNoCheck I points params radius).toList ↔
      (∃ Q, ValidInterpolationWitness points params Q) ∧ degreeLt p params.messageDegree ∧
        candidateMismatchCount points p ≤ radius := by
  rw [gsRunNoCheck_eq I points params radius hdist hW]
  let C := filteredCoreContextOfInterpRootContexts I (rothRuckensteinRootContext K fieldRootCtx)
  change p ∈ (C.run points params radius).toList ↔ _
  constructor
  · intro h
    obtain ⟨Q, hv, hd, _, hm⟩ := C.sound h
    exact ⟨⟨Q, hv⟩, hd, hm⟩
  · rintro ⟨hex, hd, hm⟩
    have hsum := candidateMismatchCount_add_matchingPointCount points p
    exact C.complete hex hdist hd (lt_of_lt_of_le hW (Nat.mul_le_mul_left _ (by omega)))
      (by simpa [passesCandidateDistance] using hm)

/-- **`gsRunNoCheck interpContext` on distinct points**: without the interpolation's distinctness
check (`interpolateDistinct`), the distance filter evaluating by Horner's rule
(`passesDistanceFast`). -/
@[expose] def gsRunDistinct (points : Array (K × K)) (params : GSInterpParams) (radius : ℕ) :
    Array (CPolynomial K) :=
  match interpolateDistinct points params with
  | none => #[]
  | some Q =>
    (prefixesTruncD fieldRootCtxFast params.messageDegree
        (CBivariate.truncateX Q params.messageDegree) params.messageDegree Q [] 0
        default).filter fun p ↦
      degreeLtBool p params.messageDegree && passesDistanceFast points radius p

theorem gsRunDistinct_eq {points : Array (K × K)} (h : DistinctXCoordinates points)
    (params : GSInterpParams) (radius : ℕ) :
    gsRunDistinct points params radius = gsRunNoCheck interpContext points params radius := by
  rw [gsRunDistinct, gsRunNoCheck, interpolateDistinct_eq h, passesDistanceFast_eq]
  rfl

/-- The lane decoder's points are distinct below `2^64` columns. -/
theorem distinct_lanePoints (n : ℕ) (hn : n ≤ 2 ^ 64) (W : ℕ → List K) (u : ℕ) :
    DistinctXCoordinates (lanePoints n W u) := by
  rw [DistinctXCoordinates, lanePoints, Array.toList_ofFn, List.map_ofFn]
  exact List.nodup_ofFn.2 (LaneProofs.domainEmb n hn).injective

/-- Whether the final root check is redundant at a shape: at most `2^64` columns, and
`W < m·(n − radius)`. -/
@[expose] def checkRedundant (κ R : ℕ) (params : GSExecParams) : Bool :=
  decide (κ + R ≤ 64) &&
    decide (params.interp.weightedDegreeBound <
      params.interp.multiplicity * (2 ^ (κ + R) - params.radius))

/-! ## The word's symbols, read once

The statement reads lane `u`'s symbol at column `v` as `(W v).reverse.getD u 0` (`laneSymbol`): a
reversal of the column's `64` entries per read, and the pruning reads a symbol per survivor, list
entry and column. The fast decoder reverses each column once (`laneTable`, the columns `v < n`)
and reads entries (`tableSymbol`); the pruning reads only columns `v < n` (`colsLt_pruneStep`), so
the two agree where they are read (`pruneStep_congr`). -/

/-- The word's columns `v < n`, each reversed, as arrays. -/
@[expose] def laneTable (n : ℕ) (W : ℕ → List K) : Array (Array K) :=
  Array.ofFn fun v : Fin n ↦ (W v.val).reverse.toArray

/-- Lane `u`'s symbol at column `v`, read from the table. -/
@[expose] def tableSymbol (T : Array (Array K)) (u v : ℕ) : K := (T.getD v #[]).getD u 0

theorem tableSymbol_laneTable {n v : ℕ} (hv : v < n) (W : ℕ → List K) (u : ℕ) :
    tableSymbol (laneTable n W) u v = laneSymbol W u v := by
  simp [tableSymbol, laneTable, laneSymbol, Array.getD_eq_getD_getElem?, hv,
    List.getD_eq_getElem?_getD]

/-- `lanePoints`, the symbols read from `S` (`S u v`: lane `u` at column `v`). -/
@[expose] def lanePointsS (n : ℕ) (S : ℕ → ℕ → K) (u : ℕ) : Array (K × K) :=
  Array.ofFn fun v : Fin n ↦ (K.ofBits v.val, S u v.val)

theorem lanePointsS_eq {n u : ℕ} {S : ℕ → ℕ → K} {W : ℕ → List K}
    (hS : ∀ v < n, S u v = laneSymbol W u v) : lanePointsS n S u = lanePoints n W u := by
  rw [lanePointsS, lanePoints]
  congr 1
  funext v
  rw [hS v v.isLt]

/-- A pruning step reads the symbols only at its survivors' columns. -/
theorem pruneStep_congr {A : ℕ} {sym sym' : ℕ → K} {L : List (Array K × Array K)}
    {st : List (List (Array K) × List ℕ)} (h : ∀ s ∈ st, ∀ v ∈ s.2, sym v = sym' v) :
    pruneStep A sym L st = pruneStep A sym' L st := by
  unfold pruneStep
  refine List.flatMap_congr fun s hs ↦ List.filterMap_congr fun ce _ ↦ ?_
  have hf : (s.2.filter fun v ↦ decide (ce.2.getD v 0 = sym v)) =
      s.2.filter fun v ↦ decide (ce.2.getD v 0 = sym' v) :=
    List.filter_congr fun v hv ↦ by rw [h s hs v hv]
  simp only [hf]

/-- A pruning step keeps its survivors' columns below `n`. -/
theorem colsLt_pruneStep {n A : ℕ} {sym : ℕ → K} {L : List (Array K × Array K)}
    {st : List (List (Array K) × List ℕ)} (h : ∀ s ∈ st, ∀ v ∈ s.2, v < n) :
    ∀ s ∈ pruneStep A sym L st, ∀ v ∈ s.2, v < n := by
  intro x hx v hv
  obtain ⟨s, hs, ce, -, -, rfl⟩ := PruneProofs.mem_pruneStep.1 hx
  exact h s hs v (List.mem_filter.1 hv).1

theorem foldl_congr_inv {α β : Type*} (P : β → Prop) {f g : β → α → β} (l : List α) {b : β}
    (hb : P b) (hfg : ∀ b a, P b → f b a = g b a) (hP : ∀ b a, P b → P (g b a)) :
    l.foldl f b = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, List.foldl_cons, hfg b a hb, ih (hP b a hb)]

/-! ## The lanes, fast -/

/-- `gsLaneAt`, fast: without the final root check where it is redundant (and then without the
interpolation's distinctness check), with the fast substitution, the symbols read from `S`. The
interpolation here is Lee–O'Sullivan's (Mulders–Storjohann), the proof side's reference; the
compiled extractor's decoder (`decOf`, `Fast/Compiled.lean`) interpolates by the approximant basis
instead (`decodeStacksDistinctPM`, `Fast/LanePM.lean`: the certified solve on a PM-basis, the
products by the additive FFT). What the lane lists hold does not depend on the interpolation
(`mem_gsRunNoCheck`). -/
@[expose] def gsLaneAtFast (κ R A : ℕ) (S : ℕ → ℕ → K) (u : ℕ) : Array (CPolynomial K) :=
  let params := gsParamsFor (2 ^ κ + initialFold) (2 ^ (κ + R)) A
  let points := lanePointsS (2 ^ (κ + R)) S u
  if checkRedundant κ R params then gsRunDistinct points params.interp params.radius
  else GuruswamiSudan.decodeWithParams gsContextFast params ⟨points⟩

/-- `laneListAt`, fast. -/
@[expose] def laneListAtFast (κ R A : ℕ) (S : ℕ → ℕ → K) (u : ℕ) : List (Array K) :=
  (((gsLaneAtFast κ R A S u).toList.map (toNovelFast (κ + 1))).dedup).mergeSort coeffsLE

/-- `laneEncodedAt`, fast. -/
@[expose] def laneEncodedAtFast (κ R A : ℕ) (S : ℕ → ℕ → K) (u : ℕ) :
    List (Array K × Array K) :=
  (laneListAtFast κ R A S u).map fun c ↦ (c, novelFwd (κ + 1) (R - 1) c)

/-- `pruneUpTo`, fast: the symbols from the word's table. -/
@[expose] def pruneUpToFast (κ R A : ℕ) (W : ℕ → List K) (U : ℕ) :
    List (List (Array K) × List ℕ) :=
  let T := laneTable (2 ^ (κ + R)) W
  (List.range U).foldl
    (fun st u ↦
      if st.isEmpty then []
      else pruneStep A (tableSymbol T u) (laneEncodedAtFast κ R A (tableSymbol T) u) st)
    [([], List.range (2 ^ (κ + R)))]

/-- `decodeStacksAt`, fast. -/
@[expose] def decodeStacksAtFast (μ R A : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  (pruneUpToFast (μ - initialFold) R A W (2 ^ initialFold)).map fun s ↦ stackOf μ s.1

/-- `decodeStacks`, fast. -/
@[expose] def decodeStacksFast (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  decodeStacksAtFast μ R (johnsonThreshold μ R) W

/-- `fastStacks`, fast: the symbols from the word's table. -/
@[expose] def fastStacksFast (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  let κ := μ - initialFold
  let T := laneTable (2 ^ (κ + R)) W
  let st := (List.range (2 ^ initialFold)).foldl
    (fun st u ↦
      let c := novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ tableSymbol T u v.val)
      pruneStep (johnsonThreshold μ R) (tableSymbol T u) [(c, novelFwd κ R c)] st)
    [([], List.range (2 ^ (κ + R)))]
  st.map fun s ↦ stackOf μ s.1

/-- **The extractor, fast**: `extract` with `decodeStacksFast`. -/
@[expose] def extractFast (prog : LeanIsaProgram) (input : PublicInput) (bytecode : List K)
    (answers : Bytes → Option Digest) (keys : List Bytes) (π : Proof) :
    Option (Execution prog) := do
  let ((layout, logInverseRate), state) ← afterRoot bytecode π
  let (root, height, width) ← state.roots.head?
  let leaves := committedLeaves answers keys root height width
  let word := leafAt leaves height width
  let execution := candidateExecutionFast prog input layout
  (fastStacks layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacksFast layout.stackLog logInverseRate word).findSome? execution

/-- **The lane decoder lists the same polynomials, fast.** -/
theorem mem_gsLaneAtFast {κ R A u : ℕ} {S : ℕ → ℕ → K} {W : ℕ → List K}
    (hS : ∀ v < 2 ^ (κ + R), S u v = laneSymbol W u v) (p : CPolynomial K) :
    p ∈ (gsLaneAtFast κ R A S u).toList ↔ p ∈ (gsLaneAt κ R A W u).toList := by
  rw [gsLaneAtFast, gsLaneAt, lanePointsS_eq hS, ← gsContextFast_eq]
  split
  · rename_i h
    simp only [checkRedundant, Bool.and_eq_true, decide_eq_true_eq] at h
    have hd := distinct_lanePoints _ (Nat.pow_le_pow_right (by norm_num) h.1) W u
    have hW : (gsParamsFor (2 ^ κ + initialFold) (2 ^ (κ + R)) A).interp.weightedDegreeBound <
        (gsParamsFor (2 ^ κ + initialFold) (2 ^ (κ + R)) A).interp.multiplicity *
          ((lanePoints (2 ^ (κ + R)) W u).size - (gsParamsFor (2 ^ κ + initialFold) (2 ^ (κ + R)) A).radius) := by
      simpa [lanePoints] using h.2
    have hctx : gsContext = filteredCoreContextOfInterpRootContexts interpContext
        (rothRuckensteinRootContext K fieldRootCtx) := by
      rw [gsContext, interpContext_eq]
    rw [gsRunDistinct_eq hd, decodeWithParams, gsContextFast_eq, hctx,
      show (filteredCoreContextOfInterpRootContexts interpContext
          (rothRuckensteinRootContext K fieldRootCtx)).run _ _ _ =
        gsRunNoCheck interpContext _ _ _ from
        (gsRunNoCheck_eq _ _ _ _ hd hW).symm,
      mem_gsRunNoCheck _ _ _ _ hd hW]
  · rfl

theorem laneListAtFast_eq {κ R A u : ℕ} {S : ℕ → ℕ → K} {W : ℕ → List K}
    (hS : ∀ v < 2 ^ (κ + R), S u v = laneSymbol W u v) :
    laneListAtFast κ R A S u = laneListAt κ R A W u := by
  rw [laneListAtFast, laneListAt, toNovelFast_eq]
  refine mergeSort_dedup_eq fun x ↦ ?_
  simp only [List.mem_map, mem_gsLaneAtFast hS]

theorem pruneUpToFast_eq (κ R A : ℕ) (W : ℕ → List K) (U : ℕ) :
    pruneUpToFast κ R A W U = pruneUpTo κ R A W U := by
  rw [pruneUpToFast, pruneUpTo]
  have hT : ∀ u, ∀ v < 2 ^ (κ + R),
      tableSymbol (laneTable (2 ^ (κ + R)) W) u v = laneSymbol W u v :=
    fun u _ hv ↦ tableSymbol_laneTable hv W u
  refine foldl_congr_inv (fun st ↦ ∀ s ∈ st, ∀ v ∈ s.2, v < 2 ^ (κ + R)) _
    (by simp) (fun st u hst ↦ ?_) (fun st u hst ↦ ?_)
  · split
    · rfl
    · rw [laneEncodedAtFast, laneListAtFast_eq (hT u), ← laneEncodedAt]
      exact pruneStep_congr fun s hs v hv ↦ hT u v (hst s hs v hv)
  · split
    · simp
    · exact colsLt_pruneStep hst

theorem decodeStacksAtFast_eq : decodeStacksAtFast = decodeStacksAt := by
  funext μ R A W
  rw [decodeStacksAtFast, pruneUpToFast_eq, decodeStacksAt]

theorem decodeStacksFast_eq : decodeStacksFast = decodeStacks := by
  funext μ R W
  rw [decodeStacksFast, decodeStacksAtFast_eq, decodeStacks]

/-- `fastStacks`'s fold, the symbols from the table. -/
theorem fastFold_eq (κ R A U : ℕ) (W : ℕ → List K) :
    (List.range U).foldl
      (fun st u ↦
        pruneStep A (tableSymbol (laneTable (2 ^ (κ + R)) W) u)
          [(novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦
              tableSymbol (laneTable (2 ^ (κ + R)) W) u v.val),
            novelFwd κ R (novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦
              tableSymbol (laneTable (2 ^ (κ + R)) W) u v.val)))] st)
      [([], List.range (2 ^ (κ + R)))] =
    (List.range U).foldl
      (fun st u ↦
        pruneStep A (laneSymbol W u)
          [(novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ laneSymbol W u v.val),
            novelFwd κ R (novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ laneSymbol W u v.val)))]
          st)
      [([], List.range (2 ^ (κ + R)))] := by
  have hT : ∀ u, ∀ v < 2 ^ (κ + R),
      tableSymbol (laneTable (2 ^ (κ + R)) W) u v = laneSymbol W u v :=
    fun u _ hv ↦ tableSymbol_laneTable hv W u
  refine foldl_congr_inv (fun st ↦ ∀ s ∈ st, ∀ v ∈ s.2, v < 2 ^ (κ + R)) _
    (by simp) (fun st u hst ↦ ?_) (fun st u hst ↦ colsLt_pruneStep hst)
  have hc : (Array.ofFn fun v : Fin (2 ^ κ) ↦ tableSymbol (laneTable (2 ^ (κ + R)) W) u v.val) =
      Array.ofFn fun v : Fin (2 ^ κ) ↦ laneSymbol W u v.val := by
    congr 1
    funext v
    exact hT u v (lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [hc]
  exact pruneStep_congr fun s hs v hv ↦ hT u v (hst s hs v hv)

theorem fastStacksFast_eq : fastStacksFast = fastStacks := by
  funext μ R W
  simp only [fastStacksFast, fastStacks, fastFold_eq]

/-- **The fast extractor is the statement's.** -/
theorem extractFast_eq : extractFast = extract := by
  funext prog input bytecode answers keys π
  simp only [extractFast, decodeStacksFast_eq, candidateExecutionFast_eq, extract]

end

end LeanVM.Extraction.Fast
