module

public import LeanVM.Cost.Bounds.PMLane.Run
public import LeanVM.Cost.Bounds.PMLane.Shapes
public import LeanVM.Cost.Bounds.Decoder.Decode
public import LeanVM.Cost.Bounds.PMSolve.Final
import all LeanVM.Cost.InitLib

/-!
# Bound: the decoder on `pmSolver`, compiled

The price of `decodeStacksDistinctPM μ R W` (`Fast/LanePM.lean`, compiled in
`Cost/Extractor/PMLane.lean` as `decodeStacksPMC`), lane by lane, the proofs of
`Bounds/Decoder/{Decode,Lane,Prune}.lean` with each lane's run on `pmSolver`
(`gsRunPMC_cost`, `Bounds/PMLane/Run.lean`):

* a lane's run (`gsLaneWith pmSolver`: the parameter search, the lane's points, the run):
  **`gsLaneWithC_cost`** `≤ decoderLaneRunBoundPM p`;
* its candidates (`laneEncodedWith pmSolver`: the novel basis, deduplicated, sorted,
  re-encoded): **`laneEncodedWithC_cost`**, **`decoderLanePMC_cost`** `≤ decoderLaneBoundPM p`;
* the lanes pruned (`pruneUpToPMC`, `pruneUpToWith pmSolver`): **`pruneUpToPMC_cost`**
  `≤ pruneBound …`, where the final root check is redundant (`checkRedundant`, so that the lanes'
  lists, and the pruning's states, are the extractor's: `laneListWith_eq`, `pruneUpToWith_eq`);
* **`decodeStacksPMC_cost`** `≤ decoderBoundPM p μ R BW Lw` at an admissible shape whose lanes
  are word-sized, and **`decodeStacksPMC_cost_worst`**: at every admissible shape, at the model's
  prices with their margin, at most `(BW + 12·Lw)·2^26 + pmDecoderWorstPrice`
  (`decoderShapePM_ok`, `pmDecoderWorstPrice ≈ 2^80.49`).

Each lane's interpolation is priced by `interpolatePMC_cost_price` (`Bounds/PMSolve/Final.lean`),
at prices fitting the proved transforms (`FFTPricesOK p`) and where its per-shape conditions hold
(`LaneInterpOKPM p κ R A`, decided per shape at `marginPrices` in `Bounds/PMLane/Shapes.lean`):
`decodeStacksPMC_cost_worst` has no hypothesis on the interpolation.
The functions the compiler outlined on demand are named by their terms (`cost_const%`,
`Bounds/CostConst.lean`), not by their numbered names.
-/

namespace LeanVM.Cost.Bounds.PMLane

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction LeanVM.Extraction.Fast
open CompPoly.GuruswamiSudan LeanVM.Cost.Bounds.PMBasis

public section

variable (P : MachineProgram)

/-! ## Sizes -/

/-- The lane's run on `pmSolver` returns at most `max 1 ℓ` polynomials (`k > 1`). -/
theorem gsLaneWith_size_le {κ R A : ℕ} (h : κ + R ≤ 64)
    (hk : 1 < (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.messageDegree) (S : ℕ → ℕ → K)
    (u : ℕ) :
    (gsLaneWith pmSolver κ R A S u).size ≤
      max 1 (interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp) :=
  gsRunDistinctWith_size_le (lanePointsS_distinct h S u) _ _ hk

/-- Where the final root check is redundant, the new lane's candidates are the extractor's. -/
theorem laneEncodedWith_eq {κ R A : ℕ} (h : checkRedundant κ R (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A))
    (S : ℕ → ℕ → K) (u : ℕ) :
    laneEncodedWith pmSolver κ R A S u = laneEncodedDistinct κ R A S u := by
  rw [laneEncodedWith, laneEncodedDistinct, laneListWith_eq pmSolver h]

/-! ## A lane -/

/-- **A lane's run on `pmSolver`** (`gsLaneWith pmSolver κ R A S u`): at most
`decoderLaneRunBoundPM p κ R A BS`, `BS` the price of a symbol `S u v`. -/
theorem gsLaneWithC_cost (hP : Includes P (cost_const% (gsLaneWith pmSolver) costDeps))
    {p : PMPrices} (hp : PMFFT.FFTPricesOK p) (κ R A : ℕ) (hI : LaneInterpOKPM p κ R A)
    (S : ℕ → ℕ → K) (SVal : MachineValue)
    (hS : ∀ a b, RunsApp P SVal [encodeValue a, encodeValue b] (encodeValue (S a b)))
    {BS : ℕ} (hBS : ∀ a b : ℕ, appCost P SVal [encodeValue a, encodeValue b] ≤ BS) (u : ℕ)
    (h : DecoderLaneSizes κ R A) :
    machineCost P (cost_const% (gsLaneWith pmSolver) costIdx)
        [encodeValue κ, encodeValue R, encodeValue A, SVal, encodeValue u] ≤
      decoderLaneRunBoundPM p κ R A BS := by
  obtain ⟨hκR, hA, hb, hs, hk1, hX, hY⟩ := h
  rw [(cost_const% (gsLaneWith pmSolver) costEq) P hP κ R A S SVal hS]
  have hn : 2 ^ (κ + R) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hk : 2 ^ κ < 2 ^ 31 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [limbs_shift (show κ < 64 by omega), limbs_shift (show κ + R < 64 by omega),
    limbs_of_lt (show κ < 2 ^ 64 by omega), limbs_of_lt (show R < 2 ^ 64 by omega),
    limbs_of_lt (show κ + R < 2 ^ 64 by omega)]
  have h1 := decoderSearchC_cost P (by includes_sub) hk hn hA hb
  have h2 := decoderParamsAtC_cost P (by includes_sub) (k := 2 ^ κ) hn hA
    (m := gsMultiplicityAt (2 ^ κ) (2 ^ (κ + R)) A)
    ((decoderMultiplicity_le _ _ _).trans_lt hb)
  -- the points
  rw [(cost_const% lanePointsS costEq) P (by includes_sub) _ S SVal hS]
  have hf := fun v ↦ RunsApp.of_spec (us := [encodeValue (2 ^ (κ + R)), SVal, encodeValue u])
    (vs := [encodeValue v])
    ((cost_const% lanePointsS lam0.costSpec) P (by includes_sub) (2 ^ (κ + R)) S SVal hS u v)
  have h3 := ofFnFrom_cost P (by includes_sub) (n := 2 ^ (κ + R)) (by omega) _
    (.closure (cost_const% lanePointsS lam0.costIdx)
      [encodeValue (2 ^ (κ + R)), SVal, encodeValue u]) hf (BS + 13)
    (fun v ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [(cost_const% lanePointsS lam0.costEq) P (by includes_sub) _ S SVal hS,
        limbs_of_lt (show (v : ℕ) < 2 ^ 64 by have := v.isLt; omega)]
      have := hBS u v
      omega) 0 (Nat.zero_le _)
  -- the run
  have hd := lanePointsS_distinct (by omega : κ + R ≤ 64) S u
  have hi := PMSolve.interpolatePMC_cost_price P (by includes_sub) p hp
    (lanePointsS (2 ^ (κ + R)) S u) (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp
    (by rw [lanePointsS_size]; exact hI.1)
    (by rw [lanePointsS_size]; exact hI.2)
    (by rwa [lanePointsS_size]) hk1
  have h4 := gsRunPMC_cost P (by includes_sub) (lanePointsS (2 ^ (κ + R)) S u)
    (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).radius hi
    (by rwa [lanePointsS_size]) hk1 hd
    (by simp only [gsParamsFor, gsParamsAt]; omega) hX hY
    (by simp only [gsParamsFor, gsParamsAt]; omega)
  rw [lanePointsS_size] at h4
  simp only [length_ofFnFrom, Nat.sub_zero] at h3 ⊢
  unfold decoderLaneRunBoundPM
  simp only [Nat.max_self]
  have e : (BS + 30) * 2 ^ (κ + R) = (BS + 13 + 16) * 2 ^ (κ + R) + 2 ^ (κ + R) := by ring
  omega

/-- **One lane's candidates on `pmSolver`** (`laneEncodedWith pmSolver`: the run, its
candidates in the novel basis, deduplicated, sorted, each re-encoded): at most the run's price
plus `laneExtraBound κ R L k`. -/
theorem laneEncodedWithC_cost (hP : Includes P (cost_const% (laneEncodedWith pmSolver) costDeps))
    (κ R A : ℕ) (hκR : κ + R ≤ 62) (S : ℕ → ℕ → K) (SVal : MachineValue)
    (hS : ∀ a b, RunsApp P SVal [encodeValue a, encodeValue b] (encodeValue (S a b))) (u : ℕ)
    {L k : ℕ} (hL : (gsLaneWith pmSolver κ R A S u).size ≤ L) (hL60 : L < 2 ^ 30)
    (hk : ∀ p ∈ gsLaneWith pmSolver κ R A S u, p.val.size ≤ k) :
    machineCost P (cost_const% (laneEncodedWith pmSolver) costIdx)
        [encodeValue κ, encodeValue R, encodeValue A, SVal, encodeValue u] ≤
      machineCost P (cost_const% (gsLaneWith pmSolver) costIdx)
        [encodeValue κ, encodeValue R, encodeValue A, SVal, encodeValue u] +
        laneExtraBound κ R L k := by
  rw [(cost_const% (laneEncodedWith pmSolver) costEq) P hP κ R A S SVal hS,
    (cost_const% (laneListWith pmSolver) costEq) P (by includes_sub) κ R A S SVal hS]
  generalize hC : gsLaneWith pmSolver κ R A S u = cands at hL hk
  -- the novel basis
  have hf1 := fun p ↦ RunsApp.of_spec (us := [encodeValue κ]) (vs := [encodeValue p])
    ((cost_const% (laneListWith pmSolver) lam1.costSpec) P (by includes_sub) κ p)
  have hm1 := listMap_le P Auto.List.map.c30.costIdx
    (.closure (cost_const% (laneListWith pmSolver) lam1.costIdx) [encodeValue κ])
    (Auto.List.map.c30.costEq_nil P (by includes_sub) _ _ hf1)
    (Auto.List.map.c30.costEq_cons P (by includes_sub) _ _ hf1)
    ((46 * k + 34) * 2 ^ κ + κ * (174 * 2 ^ κ + 2921) + 35) cands.toList
    (fun p hp ↦ by
      rw [appCost_fn, List.singleton_append,
        (cost_const% (laneListWith pmSolver) lam1.costEq) P (by includes_sub)]
      simp only [List.length_cons, List.length_nil]
      have := toNovelFastC_cost P (by includes_sub) κ (by omega) p
      have := Nat.mul_le_mul_right (2 ^ κ) (show 46 * p.val.size + 34 ≤ 46 * k + 34 by
        have := hk p (by simpa using hp); omega)
      omega)
  -- the deduplication
  have hlen : (cands.toList.map (toNovelFast κ)).length ≤ L := by simpa using hL
  have hd := dedupC_cost P (by includes_sub) (2 ^ κ) (cands.toList.map (toNovelFast κ))
    (fun c hc ↦ by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hc
      exact toNovelFast_size κ p)
  have hd1 : ((21 * 2 ^ κ + 26) * (cands.toList.map (toNovelFast κ)).length + 25) *
      (cands.toList.map (toNovelFast κ)).length ≤ ((21 * 2 ^ κ + 26) * L + 25) * L :=
    Nat.mul_le_mul (by have := Nat.mul_le_mul_left (21 * 2 ^ κ + 26) hlen; omega) hlen
  -- the sort
  have hdl : (cands.toList.map (toNovelFast κ)).dedup.length ≤ L :=
    (List.dedup_sublist _).length_le.trans hlen
  have hl0 := fun a b ↦ RunsApp.of_spec (us := []) (vs := [encodeValue a, encodeValue b])
    ((cost_const% (laneListWith pmSolver) lam0.costSpec) P (by includes_sub) a b)
  have hs := mergeSortList_cost_sq P (by includes_sub) _
    (.closure (cost_const% (laneListWith pmSolver) lam0.costIdx) []) hl0
    (fun c : Array K ↦ c.size = 2 ^ κ) (53 * 2 ^ κ + 21)
    (fun a b ha hb ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]
      rw [(cost_const% (laneListWith pmSolver) lam0.costEq) P (by includes_sub)]
      have := coeffsLEC_cost P (by includes_sub) a b ha hb
      omega)
    _ (cands.toList.map (toNovelFast κ)).dedup rfl (by omega)
    (fun c hc ↦ mem_dedup_toNovel_size hc)
  have hs1 : (53 * 2 ^ κ + 21 + 74) *
      ((cands.toList.map (toNovelFast κ)).dedup.length *
        (cands.toList.map (toNovelFast κ)).dedup.length) ≤ (53 * 2 ^ κ + 95) * (L * L) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hdl hdl)
  -- the re-encoding
  have hlist : (laneListWith pmSolver κ R A S u).length ≤ L := by
    rw [laneListWith, List.length_mergeSort, hC]; exact hdl
  have hf2 := fun c ↦ RunsApp.of_spec (us := [encodeValue κ, encodeValue R]) (vs := [encodeValue c])
    ((cost_const% (laneEncodedWith pmSolver) lam0.costSpec) P (by includes_sub) κ R c)
  have hm2 := listMap_le P Auto.List.map.c30.costIdx
    (.closure (cost_const% (laneEncodedWith pmSolver) lam0.costIdx) [encodeValue κ, encodeValue R])
    (Auto.List.map.c30.costEq_nil P (by includes_sub) _ _ hf2)
    (Auto.List.map.c30.costEq_cons P (by includes_sub) _ _ hf2)
    (κ * (171 * 2 ^ (κ + R) + 2924) + 28 * 2 ^ (κ + R) + 47) (laneListWith pmSolver κ R A S u)
    (fun c _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        (cost_const% (laneEncodedWith pmSolver) lam0.costEq) P (by includes_sub)]
      simp only [List.length_cons, List.length_nil]
      have := novelFwd_cost P (by includes_sub) κ R hκR c
      omega)
  simp only [Array.length_toList, List.length_map] at hm1 hlen
  have h1 : ((46 * k + 34) * 2 ^ κ + κ * (174 * 2 ^ κ + 2921) + 35 + 13) * cands.size ≤
      ((46 * k + 34) * 2 ^ κ + κ * (174 * 2 ^ κ + 2921) + 35 + 13) * L :=
    Nat.mul_le_mul_left _ hL
  have e5 : ((46 * k + 34) * 2 ^ κ + κ * (174 * 2 ^ κ + 2921) + 51) * L =
      ((46 * k + 34) * 2 ^ κ + κ * (174 * 2 ^ κ + 2921) + 35 + 13) * L + 3 * L := by ring
  have h2 : (κ * (171 * 2 ^ (κ + R) + 2924) + 28 * 2 ^ (κ + R) + 47 + 13) *
      (laneListWith pmSolver κ R A S u).length ≤
      (κ * (171 * 2 ^ (κ + R) + 2924) + 28 * 2 ^ (κ + R) + 60) * L := Nat.mul_le_mul_left _ hlist
  have h3 : 3 * cands.size ≤ 3 * L := by omega
  unfold laneExtraBound
  omega

/-- **A lane's candidates on `pmSolver`** (`laneEncodedWith pmSolver κ R A S u`): at most
`decoderLaneBoundPM p κ R A BS`. -/
theorem decoderLanePMC_cost (hP : Includes P (cost_const% (laneEncodedWith pmSolver) costDeps))
    {p : PMPrices} (hp : PMFFT.FFTPricesOK p) (κ R A : ℕ) (hI : LaneInterpOKPM p κ R A)
    (S : ℕ → ℕ → K) (SVal : MachineValue)
    (hS : ∀ a b, RunsApp P SVal [encodeValue a, encodeValue b] (encodeValue (S a b)))
    {BS : ℕ} (hBS : ∀ a b : ℕ, appCost P SVal [encodeValue a, encodeValue b] ≤ BS) (u : ℕ)
    (h : DecoderLaneSizes κ R A) :
    machineCost P (cost_const% (laneEncodedWith pmSolver) costIdx)
        [encodeValue κ, encodeValue R, encodeValue A, SVal, encodeValue u] ≤
      decoderLaneBoundPM p κ R A BS := by
  have hrun := gsLaneWithC_cost P (by includes_sub) hp κ R A hI S SVal hS hBS u h
  obtain ⟨hκR, -, -, hs, hk1, -, hY⟩ := h
  have := laneEncodedWithC_cost P hP κ R A (by omega) S SVal hS u
    (L := max 1 (interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp))
    (k := 2 ^ κ) (gsLaneWith_size_le (by omega) hk1 S u) (by omega)
    (fun p hp ↦ by
      have := gsRunDistinctWith_mem_size_le hp
      simpa [gsParamsFor, gsParamsAt] using this)
  unfold decoderLaneBoundPM
  omega

/-! ## The lanes pruned -/

/-- **The lanes pruned on `pmSolver`** (`pruneUpToWith pmSolver κ R A W U`): at most
`pruneBound …`, the lanes' candidates of price at most `G` and at most `Lc` each, the survivors at
most `Smax` after every lane, where the final root check is redundant. -/
theorem pruneUpToPMC_cost (hP : Includes P pruneUpToPMC.costDeps) (κ R A U : ℕ)
    (hcr : checkRedundant κ R (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A))
    (hκR : κ + R ≤ 60) (hU : U < 2 ^ 62) (hA : A < 2 ^ 128) (W : ℕ → List K) (WVal : MachineValue)
    (hW : ∀ a, RunsApp P WVal [encodeValue a] (encodeValue (W a))) {BW Lw G Lc Smax : ℕ}
    (hBW : ∀ v : ℕ, v < 2 ^ 64 → appCost P WVal [encodeValue v] ≤ BW) (hLw : ∀ v, (W v).length ≤ Lw)
    (hG : ∀ u < U, machineCost P (cost_const% (laneEncodedWith pmSolver) costIdx)
      [encodeValue κ, encodeValue R, encodeValue A, .closure fastStacksFastC.lam1.lam2.costIdx
        [encodeValue (laneTable (2 ^ (κ + R)) W)], encodeValue u] ≤ G)
    (hLc : ∀ u, (laneEncodedDistinct κ R A (tableSymbol (laneTable (2 ^ (κ + R)) W)) u).length ≤ Lc)
    (hS : ∀ u < U, (pruneUpToDistinct κ R A W u).length ≤ Smax) :
    machineCost P pruneUpToPMC.costIdx
        [encodeValue κ, encodeValue R, encodeValue A, WVal, encodeValue U] ≤
      pruneBound κ R U BW Lw G Lc Smax := by
  rw [pruneUpToPMC.costEq P hP κ R A W WVal hW U]
  have hN : 2 ^ (κ + R) < 2 ^ 62 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hs : (1 <<< (κ + R) : ℕ) = 2 ^ (κ + R) := Nat.one_shiftLeft _
  rw [hs]
  -- the table
  have hf0 := fun v ↦ RunsApp.of_spec (us := [encodeValue κ, encodeValue R, WVal]) (vs := [encodeValue v])
    (pruneUpToPMC.lam0.costSpec P (by includes_sub) κ R W WVal hW v)
  have hof := ofFnFrom_cost P (by includes_sub) (n := 2 ^ (κ + R)) (by omega) _
    (.closure pruneUpToPMC.lam0.costIdx [encodeValue κ, encodeValue R, WVal]) hf0
    (BW + 12 * Lw + 12)
    (fun v ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [pruneUpToPMC.lam0.costEq P (by includes_sub) κ R W WVal hW]
      have := hBW v (by have := v.isLt; omega)
      have := reverseAux_cost P (by includes_sub) (W v) []
      have := hLw v
      simp only [List.length_reverse]
      omega) 0 (Nat.zero_le _)
  have := rangeLoop_cost P (by includes_sub) (2 ^ (κ + R)) [] (by omega)
  have := rangeLoop_cost P (by includes_sub) U [] (by omega)
  -- the lanes
  have hf1 := fun st u ↦ RunsApp.of_spec
    (us := [encodeValue κ, encodeValue R, encodeValue A, encodeValue (laneTable (2 ^ (κ + R)) W)])
    (vs := [encodeValue st, encodeValue u])
    (pruneUpToPMC.lam1.costSpec P (by includes_sub) κ R A (laneTable (2 ^ (κ + R)) W) st u)
  have hfold := listFoldl_range'_le P (by includes_sub) _
    (.closure pruneUpToPMC.lam1.costIdx
      [encodeValue κ, encodeValue R, encodeValue A, encodeValue (laneTable (2 ^ (κ + R)) W)])
    hf1 (G + Smax * (Lc * (48 * 2 ^ (κ + R) + 11 * U + 71) + 39) + 42) U 0
    [([], List.range (2 ^ (κ + R)))]
    (fun j _ hj ↦ by
      simp only [Nat.sub_zero, appCost_fn, List.cons_append, List.nil_append, List.length_cons,
        List.length_nil]
      have hst : (List.range' 0 j).foldl
          (fun st u ↦ if st.isEmpty = true then [] else pruneStep A
            (tableSymbol (laneTable (2 ^ (κ + R)) W) u)
            (laneEncodedWith pmSolver κ R A (tableSymbol (laneTable (2 ^ (κ + R)) W)) u) st)
          [([], List.range (2 ^ (κ + R)))] = pruneUpToDistinct κ R A W j := by
        rw [← pruneUpToWith_eq pmSolver hcr]
        simp only [pruneUpToWith, List.range_eq_range']
      rw [hst]
      have hsm := (pruneUpToDistinct_bounds W hLc j).2
      generalize hS' : pruneUpToDistinct κ R A W j = st at hsm
      have hSl : st.length ≤ Smax := hS' ▸ hS j (by omega)
      cases st with
      | nil =>
        rw [pruneUpToPMC.lam1.costEq_nil P (by includes_sub)]
        simp
      | cons s0 st =>
        rw [pruneUpToPMC.lam1.costEq_cons P (by includes_sub)]
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
        have := hG j (by omega)
        have hsym := fun v ↦ RunsApp.of_spec
          (us := [encodeValue (laneTable (2 ^ (κ + R)) W), encodeValue j]) (vs := [encodeValue v])
          (fastStacksFastC.lam1.lam2.costSpec P (by includes_sub) (laneTable (2 ^ (κ + R)) W) j v)
        rw [laneEncodedWith_eq hcr]
        have hp := pruneStep_cost P (by includes_sub) A hA _
          (.closure fastStacksFastC.lam1.lam2.costIdx
            [encodeValue (laneTable (2 ^ (κ + R)) W), encodeValue j]) hsym
          14 (fun v ↦ by
            simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
            rw [fastStacksFastC.lam1.lam2.costEq P (by includes_sub),
              (cost_const% tableSymbol costEq) P (by includes_sub)])
          (laneEncodedDistinct κ R A (tableSymbol (laneTable (2 ^ (κ + R)) W)) j) (s0 :: st)
          (2 ^ (κ + R)) U (by omega) (fun s hs ↦ by
            obtain ⟨h1, -, h3⟩ := hsm s hs
            exact ⟨by have := h3.length_le; simpa using this, by omega⟩)
        have hl := hLc j
        simp only [Nat.reduceAdd] at hp
        have h1 : (s0 :: st).length *
            ((laneEncodedDistinct κ R A (tableSymbol (laneTable (2 ^ (κ + R)) W)) j).length *
              (48 * 2 ^ (κ + R) + 11 * U + 71) + 39) ≤
            Smax * (Lc * (48 * 2 ^ (κ + R) + 11 * U + 71) + 39) :=
          Nat.mul_le_mul hSl
            (by have := Nat.mul_le_mul_right (48 * 2 ^ (κ + R) + 11 * U + 71) hl; omega)
        omega)
  simp only [List.range_eq_range'] at hfold ⊢
  simp only [length_ofFnFrom, Nat.sub_zero] at *
  unfold pruneBound
  have e : (BW + 12 * Lw + 28) * 2 ^ (κ + R) = (BW + 12 * Lw + 12 + 16) * 2 ^ (κ + R) := by
    ring
  have e2 : (G + Smax * (Lc * (48 * 2 ^ (κ + R) + 11 * U + 71) + 39) + 53) * U =
      (G + Smax * (Lc * (48 * 2 ^ (κ + R) + 11 * U + 71) + 39) + 42 + 11) * U := by ring
  cost_simp
  omega

/-! ## The decoder -/

/-- **The decoder on `pmSolver`** (`decodeStacksDistinctPM μ R W`): at most
`decoderBoundPM p μ R BW Lw` at an admissible shape whose lanes are word-sized
(`DecoderLaneSizes`), `BW` the price of a column `W v` and `Lw` its length, the interpolation
within `interpPMPrice p`. -/
theorem decodeStacksPMC_cost (hP : Includes P decodeStacksPMC.costDeps) {p : PMPrices}
    (hp : PMFFT.FFTPricesOK p) (μ R : ℕ) (hadm : Whir.Admissible μ R)
    (hsz : DecoderLaneSizes (μ - Whir.initialFold) R (johnsonThreshold μ R))
    (hI : LaneInterpOKPM p (μ - Whir.initialFold) R (johnsonThreshold μ R))
    (W : ℕ → List K) (WVal : MachineValue) (hW : ∀ a, RunsApp P WVal [encodeValue a] (encodeValue (W a)))
    {BW Lw : ℕ}
    (hBW : ∀ v : ℕ, v < 2 ^ 64 → appCost P WVal [encodeValue v] ≤ BW) (hLw : ∀ v, (W v).length ≤ Lw) :
    machineCost P decodeStacksPMC.costIdx [encodeValue μ, encodeValue R, WVal] ≤
      decoderBoundPM p μ R BW Lw := by
  have hadm' := hadm
  obtain ⟨h1, h2, h3, h4⟩ := hadm'
  unfold Whir.minLogStack at h1
  unfold Whir.maxLogStack at h2
  have hf : Whir.initialFold = 6 := rfl
  have hcr := checkRedundant_johnson hadm
  rw [decodeStacksPMC.costEq P hP μ R W WVal hW,
    (cost_const% (decodeStacksDistinctWith pmSolver) costEq) P (by includes_sub) μ R W WVal hW]
  set κ := μ - Whir.initialFold with hκ
  set A := johnsonThreshold μ R with hAdef
  set T := laneTable (2 ^ (κ + R)) W with hT
  have hsz' := hsz
  obtain ⟨hκR, hA, -, -, hk1, -, -⟩ := hsz'
  have hn : 2 ^ (κ + R) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- the threshold
  have hj := johnsonThreshold_cost P (by includes_sub) μ R (by omega) (by omega)
  rw [limbs_of_lt (show μ < 2 ^ 64 by omega)]
  simp only [show limbCount Whir.initialFold = 1 from rfl,
    show limbCount (1 <<< Whir.initialFold) = 1 from rfl, Nat.max_self]
  -- the lanes
  have hSV := fun a b ↦ RunsApp.of_spec (us := [encodeValue T]) (vs := [encodeValue a, encodeValue b])
    (fastStacksFastC.lam1.lam2.costSpec P (by includes_sub) T a b)
  have hLc : ∀ u, (laneEncodedDistinct κ R A (tableSymbol T) u).length ≤
      max 1 (interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp) := fun u ↦ by
    rw [laneEncodedDistinct_length]; exact laneListDistinct_length_le (by omega) hk1 _ u
  have hpr := pruneUpToPMC_cost P (by includes_sub) κ R A (2 ^ Whir.initialFold) hcr (by omega)
    (by rw [hf]; norm_num) (by omega) W WVal hW hBW hLw
    (G := decoderLaneBoundPM p κ R A 13)
    (fun u _ ↦ decoderLanePMC_cost P (by includes_sub) hp κ R A hI (tableSymbol T)
      (.closure fastStacksFastC.lam1.lam2.costIdx [encodeValue T]) hSV
      (fun a b ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [fastStacksFastC.lam1.lam2.costEq P (by includes_sub),
          (cost_const% tableSymbol costEq) P (by includes_sub)]) u hsz)
    hLc (Smax := 2 ^ 12) (fun u _ ↦ by
      rcases Nat.eq_zero_or_pos u with rfl | hu
      · simp [pruneUpToDistinct]
      · exact pruneUpToDistinct_length_le_johnson hadm W hu)
  -- the stacks
  rw [pruneUpToWith_eq pmSolver hcr]
  have hsurv := pruneUpToDistinct_length_le_johnson hadm W (U := 2 ^ Whir.initialFold)
    (by rw [hf]; norm_num)
  have hmem := (pruneUpToDistinct_bounds W hLc (2 ^ Whir.initialFold)).2
  have hfm := fun s ↦ RunsApp.of_spec (us := [encodeValue μ]) (vs := [encodeValue s])
    (fastStacksFastC.lam2.costSpec P (by includes_sub) μ s)
  have hm := listMap_le P Auto.List.map.c30.costIdx
    (.closure fastStacksFastC.lam2.costIdx [encodeValue μ])
    (Auto.List.map.c30.costEq_nil P (by includes_sub) _ _ hfm)
    (Auto.List.map.c30.costEq_cons P (by includes_sub) _ _ hfm)
    ((15 * 2 ^ Whir.initialFold + 48) * 2 ^ μ + 21)
    (pruneUpToDistinct κ R A W (2 ^ Whir.initialFold))
    (fun s hs ↦ by
      rw [appCost_fn, List.singleton_append, fastStacksFastC.lam2.costEq P (by includes_sub)]
      simp only [List.length_cons, List.length_nil]
      have := stackOf_cost P (by includes_sub) μ (by omega) s.1
      rw [(hmem s hs).1] at this
      omega)
  have hm2 : ((15 * 2 ^ Whir.initialFold + 48) * 2 ^ μ + 21 + 13) *
      (pruneUpToDistinct κ R A W (2 ^ Whir.initialFold)).length ≤
      ((15 * 2 ^ Whir.initialFold + 48) * 2 ^ μ + 34) * 2 ^ 12 := Nat.mul_le_mul_left _ hsurv
  unfold decoderBoundPM
  rw [← hκ, ← hAdef]
  omega

/-- The decoder's bound is affine in the word's prices. -/
theorem decoderBoundPM_eq (p : PMPrices) (μ R BW Lw : ℕ) :
    decoderBoundPM p μ R BW Lw = (BW + 12 * Lw) * 2 ^ (μ - Whir.initialFold + R) +
      decoderBoundPM p μ R 0 0 := by
  unfold decoderBoundPM pruneBound
  ring

/-! ## At every admissible shape -/

/-- **The decoder on `pmSolver` at every admissible shape**, at the model's prices with
their margin: at most `(BW + 12·Lw)·2^26 + pmDecoderWorstPrice` (`decoderShapePM_ok`,
`pmDecoderWorstPrice = 1696768204877294467202512 ≈ 2^80.49`): no hypothesis but the word's
prices, each lane's interpolation priced by `interpolatePMC_cost_price` at the shape's
decided conditions (`LaneInterpOKPM marginPrices`) and `FFTPricesOK marginPrices`
(`PMSolve.fftPricesOK_margin`). -/
theorem decodeStacksPMC_cost_worst (hP : Includes P decodeStacksPMC.costDeps)
    {μ R : ℕ} (hadm : Whir.Admissible μ R)
    (W : ℕ → List K) (WVal : MachineValue) (hW : ∀ a, RunsApp P WVal [encodeValue a] (encodeValue (W a)))
    {BW Lw : ℕ}
    (hBW : ∀ v : ℕ, v < 2 ^ 64 → appCost P WVal [encodeValue v] ≤ BW) (hLw : ∀ v, (W v).length ≤ Lw) :
    machineCost P decodeStacksPMC.costIdx [encodeValue μ, encodeValue R, WVal] ≤
      (BW + 12 * Lw) * 2 ^ 26 + pmDecoderWorstPrice := by
  obtain ⟨hsz, hI, hle⟩ := decoderShapePM_ok hadm
  have h := decodeStacksPMC_cost P hP PMSolve.fftPricesOK_margin μ R hadm hsz hI W WVal hW hBW
    hLw
  rw [decoderBoundPM_eq] at h
  have hadm' := hadm
  obtain ⟨-, h2, -, h4⟩ := hadm'
  simp only [Whir.maxLogStack] at h2
  have hp : 2 ^ (μ - Whir.initialFold + R) ≤ 2 ^ 26 :=
    Nat.pow_le_pow_right (by norm_num) (by simp only [Whir.initialFold]; omega)
  have := Nat.mul_le_mul_left (BW + 12 * Lw) hp
  omega

end

end LeanVM.Cost.Bounds.PMLane
