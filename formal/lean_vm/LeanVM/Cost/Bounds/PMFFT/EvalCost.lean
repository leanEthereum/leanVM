module

public import LeanVM.Cost.Bounds.PMFFT.PolyCost
public import LeanVM.Cost.Bounds.PMBasis.Recursion
public import LeanVM.Cost.Bounds.Decoder.Rows
public import LeanVM.Protocol.Extraction.Fast.FFT.Transform

/-!
# Bounds of the PM decoder's FFT: the evaluation-domain matrix products

`evalDot` (the pointwise dot products), `transformEntriesP` (every entry transformed by one plan),
the entries' largest degree, the size's search (`ceilLogLoop`), and the products `mulEvalP`,
`mulTruncEvalP` (on `novelTransform`, `fftMulContext`).
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast
open Auto.LeanVM.Extraction.Fast.EvalMat Auto.CompPoly.PolynomialMatrix

public section

variable (P : MachineProgram)

/-- **The pointwise dot products** (`evalDotC`), `N` points, `s` terms: at most
`80·N·s + 46·N + 20`. -/
theorem evalDotC_cost (hP : Includes P evalDotC.costDeps) (N s : ℕ) (hN : N ≤ 2 ^ 40)
    (hs : s < 2 ^ 40) (a : Array (Array K)) (B : Array (Array (Array K))) (c : ℕ) :
    machineCost P evalDotC.costIdx [encodeValue N, encodeValue s, encodeValue a, encodeValue B,
      encodeValue c] ≤ 80 * (N * s) + 46 * N + 20 := by
  rw [evalDotC.costEq P hP]
  have hof := ofFnFrom_cost P (by includes) (n := N) (by omega) _
    (.closure evalDotC.lam0.costIdx [encodeValue N, encodeValue s, encodeValue a, encodeValue B,
      encodeValue c])
    (fun v ↦ RunsApp.of_spec (evalDotC.lam0.costSpec P (by includes) N s a B c v)) (80 * s + 29)
    (fun v ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [evalDotC.lam0.costEq P (by includes)]
      have h1 := rangeLoop_cost P (by includes) s [] (by omega)
      have h2 := listFoldl_le P (by includes) _
        (.closure evalDotC.lam0.lam0.costIdx [encodeValue N, encodeValue a, encodeValue B,
          encodeValue c, encodeValue v])
        (fun acc k ↦ RunsApp.of_spec (evalDotC.lam0.lam0.costSpec P (by includes) N a B c v acc k))
        54 (fun _ ↦ True) (List.range s) (0 : K) trivial
        (fun acc _ k _ ↦ ⟨trivial, by
          simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [evalDotC.lam0.lam0.costEq P (by includes)]⟩)
      rw [List.length_range] at h2
      omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length]
  simp only [Nat.sub_zero] at hof
  have : (80 * s + 29 + 16) * N = 80 * (N * s) + 45 * N := by ring
  omega

/-- The proved price of a forward transform of size `2^j` (`planFwdPolyC_cost`). -/
@[expose] def fwdBound (j : ℕ) : ℕ :=
  29 * (2 ^ j * (j * j)) + 230 * (2 ^ j * j) + 46 * 2 ^ j + 231 * j + 85

/-- The proved price of an inverse transform of size `2^j` (`planInvPolyC_cost`). -/
@[expose] def invBound (j : ℕ) : ℕ :=
  37 * (2 ^ j * (j * j)) + 167 * (2 ^ j * j) + 44 * 2 ^ j + 156 * j + 84

/-- The proved price of the plan of size `2^j` (`mkPlanC_cost`). -/
@[expose] def planBound (j : ℕ) : ℕ :=
  28 * 2 ^ j + 76 * (j * j * j) + 276 * (j * j) + 468 * j + 2934

/-- **Every entry transformed by the plan** (`transformEntriesPC`), `rows × cols` entries, each
read at most `E`: at most `rows·cols·(E + fwdBound j + 28) + 41·rows + 18`. -/
theorem transformEntriesPC_cost (hP : Includes P transformEntriesPC.costDeps) {j : ℕ} (hj : j ≤ 40)
    (rows cols : ℕ) (hr : rows < 2 ^ 40) (hc : cols < 2 ^ 40)
    (entry : ℕ → ℕ → CompPoly.CPolynomial K) (eVal : MachineValue)
    (he : ∀ a b : ℕ, RunsApp P eVal [encodeValue a, encodeValue b] (encodeValue (entry a b)))
    (E : ℕ) (hE : ∀ a b : ℕ, appCost P eVal [encodeValue a, encodeValue b] ≤ E) :
    machineCost P transformEntriesPC.costIdx [encodeValue (FFT.mkPlan j), encodeValue rows,
      encodeValue cols, eVal] ≤ rows * cols * (E + fwdBound j + 28) + 41 * rows + 18 := by
  rw [transformEntriesPC.costEq P hP (FFT.mkPlan j) rows cols entry eVal he]
  have hof := ofFnFrom_cost P (by includes) (n := rows) (by omega) _
    (.closure transformEntriesPC.lam0.costIdx [encodeValue (FFT.mkPlan j), encodeValue rows,
      encodeValue cols, eVal])
    (fun i ↦ RunsApp.of_spec (transformEntriesPC.lam0.costSpec P (by includes) (FFT.mkPlan j) rows
      cols entry eVal he i)) ((E + fwdBound j + 27) * cols + cols + 24)
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [transformEntriesPC.lam0.costEq P (by includes) (FFT.mkPlan j) rows cols entry eVal he i]
      have h1 := ofFnFrom_cost P (by includes) (n := cols) (by omega) _
        (.closure transformEntriesPC.lam0.lam0.costIdx [encodeValue (FFT.mkPlan j), encodeValue rows,
          encodeValue cols, eVal, encodeValue i])
        (fun k ↦ RunsApp.of_spec (transformEntriesPC.lam0.lam0.costSpec P (by includes)
          (FFT.mkPlan j) rows cols entry eVal he i k)) (E + fwdBound j + 11)
        (fun k ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [transformEntriesPC.lam0.lam0.costEq P (by includes) (FFT.mkPlan j) rows cols entry
            eVal he i k]
          have := planFwdPolyC_cost P (by includes) hj (entry i k)
          have := hE i k
          rw [fwdBound]
          omega) 0 (Nat.zero_le _)
      rw [ofFnFrom_length]
      simp only [Nat.sub_zero] at h1
      rw [show E + fwdBound j + 11 + 16 = E + fwdBound j + 27 by ring] at h1
      omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length]
  simp only [Nat.sub_zero] at hof
  have : ((E + fwdBound j + 27) * cols + cols + 24 + 16) * rows =
      rows * cols * (E + fwdBound j + 28) + 40 * rows := by ring
  omega

theorem foldl_max_lt (g : ℕ → ℕ) (B : ℕ) (hg : ∀ k, g k < B) :
    ∀ (l : List ℕ) (a : ℕ), a < B → l.foldl (fun acc k ↦ max acc (g k)) a < B := by
  intro l
  induction l with
  | nil => intro a ha; exact ha
  | cons x l ih => intro a ha; exact ih _ (max_lt ha (hg x))

theorem cpoly_size_lt {f : CompPoly.CPolynomial K} {d : ℕ} (h : f.natDegree ≤ d) (hd : d < 2 ^ 40) :
    f.val.size < 2 ^ 41 := by
  have := FFT.size_le_natDegree_succ f
  omega

/-- **The entries' largest degree** (`maxEntryDegree.c432`), `rows × cols` entries of degree
below `2^40`: at most `81·rows·cols + 46·rows + 18`. -/
theorem maxEntryDegreeC_cost (hP : Includes P maxEntryDegree.c432.costDeps)
    (M : CompPoly.PolynomialMatrix K) (rows cols : ℕ) (hr : rows < 2 ^ 40) (hc : cols < 2 ^ 40)
    (d : ℕ) (hd : d < 2 ^ 40)
    (hM : ∀ i k, (CompPoly.PolynomialMatrix.rowGet (M.getD i #[]) k).natDegree ≤ d) :
    machineCost P maxEntryDegree.c432.costIdx [encodeValue M, encodeValue rows, encodeValue cols] ≤
      81 * (rows * cols) + 46 * rows + 18 := by
  rw [maxEntryDegree.c432.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) rows [] (by omega)
  have hinner : ∀ i acc : ℕ, acc < 2 ^ 40 → machineCost P maxEntryDegree.c432.lam0.costIdx
      [encodeValue M, encodeValue cols, encodeValue acc, encodeValue i] ≤ 81 * cols + 18 := by
    intro i acc hacc
    rw [maxEntryDegree.c432.lam0.costEq P (by includes)]
    have h2 := rangeLoop_cost P (by includes) cols [] (by omega)
    have h3 := listFoldl_le P (by includes) _
      (.closure maxEntryDegree.c432.lam0.lam0.costIdx [encodeValue M, encodeValue i])
      (fun a k ↦ RunsApp.of_spec (maxEntryDegree.c432.lam0.lam0.costSpec P (by includes) M i a k))
      55 (fun a ↦ a < 2 ^ 40) (List.range cols) acc hacc
      (fun a ha k _ ↦ ⟨by
        have := hM i k
        show max a _ < 2 ^ 40
        omega, by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [maxEntryDegree.c432.lam0.lam0.costEq P (by includes)]
        have e1 := hM i k
        have e2 := Decoder.natDegree_cost P (by includes)
          (CompPoly.PolynomialMatrix.rowGet (M.getD i #[]) k) (by
            have := cpoly_size_lt e1 hd; omega)
        have e3 := Decoder.rowGet_cost P (by includes) (M.getD i #[]) k
        cost_simp
        split_ifs <;> omega⟩)
    rw [List.length_range] at h3
    omega
  have h4 := listFoldl_le P (by includes) _
    (.closure maxEntryDegree.c432.lam0.costIdx [encodeValue M, encodeValue cols])
    (fun a i ↦ RunsApp.of_spec (maxEntryDegree.c432.lam0.costSpec P (by includes) M cols a i))
    (81 * cols + 20) (fun a ↦ a < 2 ^ 40) (List.range rows) 0 (by norm_num)
    (fun a ha i _ ↦ ⟨by
      exact foldl_max_lt _ _ (fun k ↦ (hM i k).trans_lt hd) _ _ ha, by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have := hinner i a ha
      omega⟩)
  rw [List.length_range] at h4
  have : (81 * cols + 20 + 11) * rows = 81 * (rows * cols) + 31 * rows := by ring
  omega

/-- **The size's search** (`ceilLogLoop.c437`) from `a`, `e ≤ 2^K`, `K ≤ 40`: at most
`22·(K − a) + 17`. -/
theorem ceilLogLoopC_cost (hP : Includes P ceilLogLoop.c437.costDeps) (e K : ℕ) (he : e ≤ 2 ^ K)
    (hK : K ≤ 40) : ∀ fuel a, fuel < 2 ^ 64 → a ≤ K →
      machineCost P ceilLogLoop.c437.costIdx [encodeValue e, encodeValue fuel, encodeValue a] ≤
        22 * (K - a) + 17 := by
  have hpK : 2 ^ K ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hK
  intro fuel
  induction fuel with
  | zero => intro a _ _; rw [ceilLogLoop.c437.costEq P hP]; cost_simp; omega
  | succ n ih =>
    intro a hn ha
    rw [ceilLogLoop.c437.costEq P hP]
    cost_simp
    rw [limbs_shift (by omega), limbs_two_pow (by omega)]
    split_ifs with h
    · omega
    · have hlt : a < K := by
        by_contra hc
        have : 2 ^ K ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have := ih (a + 1) (by omega) (by omega)
      cost_simp
      omega

/-- **A matrix of entries** (`PolynomialMatrix.ofFn.c439`), each at most `E`: at most
`rows·width·(E + 35) + 49·rows + 18`. -/
theorem matrixOfFnC_cost (hP : Includes P ofFn.c439.costDeps) (rows width : ℕ)
    (hr : rows < 2 ^ 40) (hw : width < 2 ^ 40) (entry : ℕ → ℕ → CompPoly.CPolynomial K)
    (eVal : MachineValue)
    (he : ∀ a b : ℕ, RunsApp P eVal [encodeValue a, encodeValue b] (encodeValue (entry a b)))
    (E : ℕ) (hE : ∀ a b : ℕ, appCost P eVal [encodeValue a, encodeValue b] ≤ E) :
    machineCost P ofFn.c439.costIdx [encodeValue rows, encodeValue width, eVal] ≤
      rows * width * (E + 35) + 49 * rows + 18 := by
  rw [ofFn.c439.costEq P hP rows width entry eVal he]
  have h1 := rangeLoop_cost P (by includes) rows [] (by omega)
  have h2 := map_cost P (by includes) _ (.closure ofFn.c439.lam0.costIdx [encodeValue width, eVal])
    (fun i ↦ RunsApp.of_spec (ofFn.c439.lam0.costSpec P (by includes) width entry eVal he i))
    ((E + 19) * width + width + 20 + 15 * width) (List.range rows)
    (fun i _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [ofFn.c439.lam0.costEq P (by includes) width entry eVal he i]
      have h3 := rangeLoop_cost P (by includes) width [] (by omega)
      have h4 := map_cost P (by includes) _ (.closure ofFn.c439.lam0.lam0.costIdx [eVal, encodeValue i])
        (fun k ↦ RunsApp.of_spec (ofFn.c439.lam0.lam0.costSpec P (by includes) entry eVal he i k))
        (E + 6) (List.range width)
        (fun k _ ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [ofFn.c439.lam0.lam0.costEq P (by includes) entry eVal he i k]
          have := hE i k
          omega)
      simp only [List.length_map, List.length_range] at h4 ⊢
      have : (E + 6 + 13) * width = (E + 19) * width := by ring
      omega)
  simp only [List.length_map, List.length_range] at h2 ⊢
  have : ((E + 19) * width + width + 20 + 15 * width + 13) * rows =
      rows * width * (E + 35) + 33 * rows := by ring
  omega

theorem maxEntryDegree_le (M : CompPoly.PolynomialMatrix K) (rows cols d : ℕ)
    (hM : ∀ i k, (CompPoly.PolynomialMatrix.rowGet (M.getD i #[]) k).natDegree ≤ d) :
    EvalMat.maxEntryDegree M rows cols ≤ d := by
  rw [EvalMat.maxEntryDegree]
  have step : ∀ (l : List ℕ) (a : ℕ), a ≤ d →
      l.foldl (fun acc i ↦ (List.range cols).foldl
        (fun acc k ↦ max acc (CompPoly.PolynomialMatrix.rowGet (M.getD i #[]) k).natDegree) acc) a ≤ d := by
    intro l
    induction l with
    | nil => intro a ha; exact ha
    | cons x l ih =>
      intro a ha
      refine ih _ ?_
      have := foldl_max_lt (fun k ↦ (CompPoly.PolynomialMatrix.rowGet (M.getD x #[]) k).natDegree)
        (d + 1) (fun k ↦ Nat.lt_succ_of_le (hM x k)) (List.range cols) a (by omega)
      simp only at this ⊢
      omega
  exact step _ 0 (Nat.zero_le _)

theorem novelTransform_plan (j : ℕ) : FFT.novelTransform.plan j = FFT.mkPlan j := rfl

/-- **The evaluation-domain product, explicitly** (`mulEvalPC`), `R × S` by `S × T` (`R, S ≥ 1`),
the transform's size `N = 2^J`, `J = ceilLog (deg A + deg B + 1) ≤ jm ≤ 36`. -/
theorem mulEvalPC_cost_explicit (hP : Includes P mulEvalPC.costDeps)
    (A B : CompPoly.PolynomialMatrix K) (dA dB jm : ℕ)
    (hdA : ∀ i k, (CompPoly.PolynomialMatrix.rowGet (A.getD i #[]) k).natDegree ≤ dA)
    (hdB : ∀ k c, (CompPoly.PolynomialMatrix.rowGet (B.getD k #[]) c).natDegree ≤ dB)
    (hjm : dA + dB + 1 ≤ 2 ^ jm) (hj : jm ≤ 36) (hR : A.size < 2 ^ 32) (hS : B.size < 2 ^ 32)
    (hT : B.MatrixWidth < 2 ^ 32) :
    ∃ J ≤ jm, machineCost P mulEvalPC.costIdx [encodeValue A, encodeValue B] ≤
      A.size * B.size * (fwdBound J + 122) + B.size * B.MatrixWidth * (fwdBound J + 122) +
        A.size * B.MatrixWidth * (80 * (2 ^ J * B.size) + 46 * 2 ^ J + invBound J + 75) +
        136 * A.size + 87 * B.size + planBound J + 989 := by
  rw [mulEvalPC.costEq P hP]
  have hW := Decoder.matrixWidthC_cost P (by includes) B (by omega)
  have hlog : limbCount FFT.novelTransform.maxLog = 1 := limbs_of_lt (show 64 < 2 ^ 64 by norm_num)
  set R := A.size with hRdef
  set S := B.size with hSdef
  set T := B.MatrixWidth with hTdef
  have hpj : 2 ^ jm ≤ 2 ^ 36 := Nat.pow_le_pow_right (by norm_num) hj
  have hmA := maxEntryDegree_le A R S dA hdA
  have hmB := maxEntryDegree_le B S T dB hdB
  set mA := EvalMat.maxEntryDegree A R S
  set mB := EvalMat.maxEntryDegree B S T
  set J := EvalMat.ceilLog (mA + mB + 1) with hJdef
  have hJ : J ≤ jm := EvalMat.ceilLog_le (by omega)
  refine ⟨J, hJ, ?_⟩
  have hJ64 : J ≤ FFT.novelTransform.maxLog := by show J ≤ 64; omega
  rw [ite_eq_left hJ64]
  simp only [novelTransform_plan]
  have h1 := maxEntryDegreeC_cost P (by includes) A R S (by omega) (by omega) dA (by omega) hdA
  have h2 := maxEntryDegreeC_cost P (by includes) B S T (by omega) (by omega) dB (by omega) hdB
  have h3 := ceilLogLoopC_cost P (by includes) (mA + mB + 1) jm (by omega) (by omega)
    (mA + mB + 1) 0 (by omega) (by omega)
  have hJ40 : J ≤ 40 := by omega
  have h4 := mkPlanC_cost P (by includes) hJ40
  have h5 := transformEntriesPC_cost P (by includes) hJ40 R S (by omega) (by omega)
    (fun i k ↦ CompPoly.PolynomialMatrix.rowGet (A.getD i #[]) k)
    (.closure mulEvalPC.lam0.costIdx [encodeValue A])
    (fun i k ↦ RunsApp.of_spec (mulEvalPC.lam0.costSpec P (by includes) A i k)) 13
    (fun i k ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mulEvalPC.lam0.costEq P (by includes), Decoder.rowGet_cost P (by includes)])
  have h6 := transformEntriesPC_cost P (by includes) hJ40 S T (by omega) (by omega)
    (fun k c ↦ CompPoly.PolynomialMatrix.rowGet (B.getD k #[]) c)
    (.closure mulEvalPC.lam0.costIdx [encodeValue B])
    (fun k c ↦ RunsApp.of_spec (mulEvalPC.lam0.costSpec P (by includes) B k c)) 13
    (fun k c ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mulEvalPC.lam0.costEq P (by includes), Decoder.rowGet_cost P (by includes)])
  have hN : 2 ^ J ≤ 2 ^ 36 := Nat.pow_le_pow_right (by norm_num) (by omega)
  set FA := FFT.transformEntriesP FFT.novelTransform (FFT.mkPlan J) R S fun i k ↦
    CompPoly.PolynomialMatrix.rowGet (A.getD i #[]) k with hFA
  set FB := FFT.transformEntriesP FFT.novelTransform (FFT.mkPlan J) S T fun k c ↦
    CompPoly.PolynomialMatrix.rowGet (B.getD k #[]) c with hFB
  have h7 := matrixOfFnC_cost P (by includes) R T (by omega) (by omega) _
    (.closure mulEvalPC.lam1.costIdx [encodeValue FA, encodeValue FB,
      encodeValue (FFT.mkPlan J), encodeValue (2 ^ J), encodeValue J, encodeValue R, encodeValue S,
      encodeValue T])
    (fun i c ↦ RunsApp.of_spec (mulEvalPC.lam1.costSpec P (by includes) _ _ _ _ _ _ _ _ i c))
    (80 * (2 ^ J * S) + 46 * 2 ^ J + 20 + invBound J + 20)
    (fun i c ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mulEvalPC.lam1.costEq P (by includes)]
      have e1 := evalDotC_cost P (by includes) (2 ^ J) S (by omega) (by omega) (FA.getD i #[]) FB c
      have e2 := planInvPolyC_cost P (by includes) hJ40
        (EvalMat.evalDot (2 ^ J) S (FA.getD i #[]) FB c)
      rw [invBound]
      omega)
  rw [limbs_shift (k := J) (by omega)]
  cost_simp
  have e3 : R * T * (80 * (2 ^ J * S) + 46 * 2 ^ J + 20 + invBound J + 20 + 35) =
      R * T * (80 * (2 ^ J * S) + 46 * 2 ^ J + invBound J + 75) := by ring
  have e4 : R * S * (13 + fwdBound J + 28) = R * S * (fwdBound J + 41) := by ring
  have e5 : S * T * (13 + fwdBound J + 28) = S * T * (fwdBound J + 41) := by ring
  have e6 : R * S * (fwdBound J + 122) = R * S * (fwdBound J + 41) + 81 * (R * S) := by ring
  have e7 : S * T * (fwdBound J + 122) = S * T * (fwdBound J + 41) + 81 * (S * T) := by ring
  rw [planBound]
  omega

/-! ## The model's prices -/

open LeanVM.Cost.Bounds.PMBasis

/-- The plan's price beyond its twiddle tables. -/
@[expose] def planPoly (j : ℕ) : ℕ := 76 * (j * j * j) + 276 * (j * j) + 468 * j + 2934

/-- **What one forward transform of size `2^j` needs of the model** (`fwdPrice`): the proved
transform, the plan's tables (and for `j ≥ 12` the rest of the plan; below, `2^20` holds it), an
entry's reads (its degree, its closure, the rows'). -/
@[expose] def fwdNeed (j : ℕ) : ℕ :=
  fwdBound j + 28 * 2 ^ j + (if j ≤ 11 then 0 else planPoly j) + 345

/-- **What one inverse transform of size `2^j` needs of the model** (`invPrice`): the proved
transform, the dot products' entry overheads, the output's closure. -/
@[expose] def invNeed (j : ℕ) : ℕ := invBound j + 46 * 2 ^ j + 75

/-- **The prices the proved bounds fit** (decidable: `decide` on numbers): a multiply-add at least
`80`, and for every `j ≤ 36` the transforms' needs within the model's `fwdPrice`, `invPrice`. -/
@[expose] def FFTPricesOK (p : PMPrices) : Prop :=
  80 ≤ p.mac ∧ ∀ j < 37, fwdNeed j ≤ fwdPrice p j ∧ invNeed j ≤ invPrice p j

instance (p : PMPrices) : Decidable (FFTPricesOK p) := by
  unfold FFTPricesOK; infer_instance

theorem fwdPrice_mono (p : PMPrices) {a b : ℕ} (h : a ≤ b) : fwdPrice p a ≤ fwdPrice p b := by
  unfold fwdPrice
  have h1 : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h
  have h2 : a * 2 ^ a ≤ b * 2 ^ b := Nat.mul_le_mul h h1
  have := Nat.mul_le_mul_left (p.toNovel + p.fwd) h2
  have := Nat.mul_le_mul_left p.ovh h1
  omega

theorem invPrice_mono (p : PMPrices) {a b : ℕ} (h : a ≤ b) : invPrice p a ≤ invPrice p b := by
  unfold invPrice
  have h1 : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h
  have h2 : a * 2 ^ a ≤ b * 2 ^ b := Nat.mul_le_mul h h1
  have := Nat.mul_le_mul_left (p.fromNovel + p.inv) h2
  have := Nat.mul_le_mul_left p.ovh h1
  omega

theorem dist3 (x a b c : ℕ) : x * (a + b + 0 + c) = x * (a + c) + x * b := by ring

theorem dist4 (x a b d c : ℕ) : x * (a + b + d + c) = x * (a + c) + x * b + x * d := by ring

theorem planPoly_le_11 {j : ℕ} (h : j ≤ 11) : planPoly j ≤ 142634 := by
  unfold planPoly
  have : j * j ≤ 121 := Nat.mul_le_mul h h
  have : j * j * j ≤ 1331 := Nat.mul_le_mul this h
  omega

/-- The plan within one transform (and `2^20` below `j = 12`). -/
theorem plan_fit (x J : ℕ) (hx0 : 1 ≤ x) :
    x * (fwdBound J + 345) + planBound J ≤ x * fwdNeed J + 142634 := by
  have hN27 : 28 * 2 ^ J ≤ x * (28 * 2 ^ J) := Nat.le_mul_of_pos_left _ hx0
  have hpb : planBound J = 28 * 2 ^ J + planPoly J := by unfold planBound planPoly; ring
  rw [hpb]
  unfold fwdNeed
  split_ifs with h12
  · have e := dist3 x (fwdBound J) (28 * 2 ^ J) 345
    have := planPoly_le_11 h12
    linarith
  · have hpp : planPoly J ≤ x * planPoly J := Nat.le_mul_of_pos_left _ hx0
    have e := dist4 x (fwdBound J) (28 * 2 ^ J) (planPoly J) 345
    linarith

/-- The explicit price within `evalMatPrice`'s form. -/
theorem evalMat_fit (R S T J jm mac F I : ℕ) (hR0 : 0 < R) (hS0 : 0 < S)
    (hN : 2 ^ J ≤ 2 ^ jm) (hmac : 80 ≤ mac) (hf : fwdNeed J ≤ F) (hi : invNeed J ≤ I) :
    R * S * (fwdBound J + 122) + S * T * (fwdBound J + 122) +
        R * T * (80 * (2 ^ J * S) + 46 * 2 ^ J + invBound J + 75) +
        136 * R + 87 * S + planBound J + 989 ≤
      (R * S + S * T) * F + R * T * I + R * S * T * 2 ^ jm * mac + 2 ^ 20 := by
  have hx1 : R ≤ R * S := Nat.le_mul_of_pos_right _ hS0
  have hx2 : S ≤ R * S := Nat.le_mul_of_pos_left _ hR0
  have hx0 : 1 ≤ R * S := Nat.mul_pos hR0 hS0
  have hplan := plan_fit (R * S) J hx0
  have h1 : R * S * fwdNeed J ≤ R * S * F := Nat.mul_le_mul_left _ hf
  have h2 : S * T * (fwdBound J + 122) ≤ S * T * F :=
    Nat.mul_le_mul_left _ (by unfold fwdNeed at hf; omega)
  have e1 : R * T * (80 * (2 ^ J * S) + 46 * 2 ^ J + invBound J + 75) =
      R * T * invNeed J + 80 * (R * S * T * 2 ^ J) := by unfold invNeed; ring
  have e2 : R * T * invNeed J ≤ R * T * I := Nat.mul_le_mul_left _ hi
  have e3 : 80 * (R * S * T * 2 ^ J) ≤ R * S * T * 2 ^ jm * mac := by
    rw [mul_comm (R * S * T * 2 ^ jm) mac]
    calc 80 * (R * S * T * 2 ^ J) ≤ mac * (R * S * T * 2 ^ J) := Nat.mul_le_mul_right _ hmac
      _ ≤ mac * (R * S * T * 2 ^ jm) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hN)
  have e4 : R * S * (fwdBound J + 122) + 136 * R + 87 * S ≤ R * S * (fwdBound J + 345) := by
    have : R * S * (fwdBound J + 345) = R * S * (fwdBound J + 122) + 223 * (R * S) := by ring
    omega
  have e5 : (R * S + S * T) * F = R * S * F + S * T * F := by ring
  omega

/-- **The evaluation-domain product within the model** (`mulEvalPC`): at most `evalMatPrice`, for
`R, S ≥ 1` rows, entries of degree at most `dA`, `dB`, `clog2 (dA + dB + 1) ≤ 36`. -/
theorem mulEvalPC_cost (hP : Includes P mulEvalPC.costDeps) (p : PMPrices) (hp : FFTPricesOK p)
    (A B : CompPoly.PolynomialMatrix K) (dA dB : ℕ)
    (hdA : ∀ i k, (CompPoly.PolynomialMatrix.rowGet (A.getD i #[]) k).natDegree ≤ dA)
    (hdB : ∀ k c, (CompPoly.PolynomialMatrix.rowGet (B.getD k #[]) c).natDegree ≤ dB)
    (hj : clog2 (dA + dB + 1) ≤ 36) (hR0 : 0 < A.size) (hR : A.size < 2 ^ 32)
    (hS0 : 0 < B.size) (hS : B.size < 2 ^ 32) (hT : B.MatrixWidth < 2 ^ 32) :
    machineCost P mulEvalPC.costIdx [encodeValue A, encodeValue B] ≤
      evalMatPrice p A.size B.size B.MatrixWidth dA dB := by
  set jm := clog2 (dA + dB + 1) with hjmdef
  have hjm : dA + dB + 1 ≤ 2 ^ jm := by
    rw [hjmdef, clog2_eq_ceilLog]; exact EvalMat.le_two_pow_ceilLog _
  obtain ⟨J, hJ, hcost⟩ := mulEvalPC_cost_explicit P hP A B dA dB jm hdA hdB hjm hj hR hS hT
  obtain ⟨hmac, hneed⟩ := hp
  obtain ⟨hf, hi⟩ := hneed J (by omega)
  have hf' := hf.trans (fwdPrice_mono p hJ)
  have hi' := hi.trans (invPrice_mono p hJ)
  have hN : 2 ^ J ≤ 2 ^ jm := Nat.pow_le_pow_right (by norm_num) hJ
  rw [evalMatPrice, ← hjmdef]
  set R := A.size
  set S := B.size
  set T := B.MatrixWidth
  set F := fwdPrice p jm
  set I := invPrice p jm
  have hx1 : R ≤ R * S := Nat.le_mul_of_pos_right _ hS0
  have hx2 : S ≤ R * S := Nat.le_mul_of_pos_left _ hR0
  have hx0 : 1 ≤ R * S := Nat.mul_pos hR0 hS0
  exact hcost.trans (evalMat_fit R S T J jm p.mac F I hR0 hS0 hN hmac hf' hi')

/-! ## The column-truncated product -/

/-- **An X-adic truncation** (`truncateX.c452`) at `order`: at most `55·order + 31`. -/
theorem truncateXC_cost (hP : Includes P truncateX.c452.costDeps) (order : ℕ) (ho : order < 2 ^ 40)
    (f : CompPoly.CPolynomial K) :
    machineCost P truncateX.c452.costIdx [encodeValue order, encodeValue f] ≤ 55 * order + 31 := by
  rw [truncateX.c452.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) order [] (by omega)
  have h2 := map_cost P (by includes) _ (.closure truncateX.c452.lam0.costIdx [encodeValue f])
    (fun i ↦ RunsApp.of_spec (truncateX.c452.lam0.costSpec P (by includes) f i)) 5 (List.range order)
    (fun i _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [truncateX.c452.lam0.costEq P (by includes)])
  have h3 := Decoder.ofArray_cost P (by includes)
    ((List.map (fun i ↦ f.coeff i) (List.range order)).toArray) (by simp; omega)
  simp only [List.size_toArray, List.length_map, List.length_range] at h2 h3 ⊢
  omega

/-- **The largest order** (`maxOrderOf.c449`), `cols` orders at most `O < 2^40`: at most
`40·cols + 16`. -/
theorem maxOrderOfC_cost (hP : Includes P maxOrderOf.c449.costDeps) (orders : Array ℕ) (cols O : ℕ)
    (hc : cols < 2 ^ 40) (hO : O < 2 ^ 40) (ho : ∀ c, orders.getD c 0 ≤ O) :
    machineCost P maxOrderOf.c449.costIdx [encodeValue orders, encodeValue cols] ≤ 40 * cols + 16 := by
  rw [maxOrderOf.c449.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) cols [] (by omega)
  have h2 := listFoldl_le P (by includes) _ (.closure maxOrderOf.c449.lam0.costIdx [encodeValue orders])
    (fun a c ↦ RunsApp.of_spec (maxOrderOf.c449.lam0.costSpec P (by includes) orders a c)) 14
    (fun a ↦ a < 2 ^ 40) (List.range cols) 0 (by norm_num)
    (fun a ha c _ ↦ ⟨by
      have := ho c
      show max a _ < 2 ^ 40
      omega, by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [maxOrderOf.c449.lam0.costEq P (by includes)]
      have := ho c
      cost_simp
      split_ifs <;> omega⟩)
  rw [List.length_range] at h2
  omega

theorem maxOrderOf_le (orders : Array ℕ) (cols O : ℕ) (ho : ∀ c, orders.getD c 0 ≤ O) :
    EvalMat.maxOrderOf orders cols ≤ O := by
  have := foldl_max_lt (fun c ↦ orders.getD c 0) (O + 1) (fun c ↦ Nat.lt_succ_of_le (ho c))
    (List.range cols) 0 (by omega)
  rw [EvalMat.maxOrderOf]
  omega

theorem min_sub_le {m d O O' : ℕ} (hm : m ≤ d) (hO : O' ≤ O) : min m (O' - 1) ≤ min d (O - 1) := by
  omega

/-- **The column-truncated product, explicitly** (`mulTruncEvalPC`). -/
theorem mulTruncEvalPC_cost_explicit (hP : Includes P mulTruncEvalPC.costDeps)
    (orders : Array ℕ) (A B : CompPoly.PolynomialMatrix K) (dA dB O jm : ℕ)
    (hdA : ∀ i k, (CompPoly.PolynomialMatrix.rowGet (A.getD i #[]) k).natDegree ≤ dA)
    (hdB : ∀ k c, (CompPoly.PolynomialMatrix.rowGet (B.getD k #[]) c).natDegree ≤ dB)
    (ho : ∀ c, orders.getD c 0 ≤ O) (hO : O < 2 ^ 40)
    (hjm : min dA (O - 1) + min dB (O - 1) + 1 ≤ 2 ^ jm) (hj : jm ≤ 36)
    (hdA' : dA < 2 ^ 40) (hdB' : dB < 2 ^ 40)
    (hR : A.size < 2 ^ 32) (hS : B.size < 2 ^ 32) (hT : B.MatrixWidth < 2 ^ 32) :
    ∃ J ≤ jm, machineCost P mulTruncEvalPC.costIdx [encodeValue orders, encodeValue A, encodeValue B] ≤
      A.size * B.size * (fwdBound J + 55 * O + 238) +
        B.size * B.MatrixWidth * (fwdBound J + 55 * O + 238) +
        A.size * B.MatrixWidth * (80 * (2 ^ J * B.size) + 46 * 2 ^ J + invBound J + 55 * O + 113) +
        182 * A.size + 133 * B.size + 40 * B.MatrixWidth + planBound J + 1079 := by
  rw [mulTruncEvalPC.costEq P hP]
  have hW := Decoder.matrixWidthC_cost P (by includes) B (by omega)
  have hlog : limbCount FFT.novelTransform.maxLog = 1 := limbs_of_lt (show 64 < 2 ^ 64 by norm_num)
  set R := A.size with hRdef
  set S := B.size with hSdef
  set T := B.MatrixWidth with hTdef
  have hpj : 2 ^ jm ≤ 2 ^ 36 := Nat.pow_le_pow_right (by norm_num) hj
  have hmA := maxEntryDegree_le A R S dA hdA
  have hmB := maxEntryDegree_le B S T dB hdB
  have hOO := maxOrderOf_le orders T O ho
  set mA := EvalMat.maxEntryDegree A R S
  set mB := EvalMat.maxEntryDegree B S T
  set O' := EvalMat.maxOrderOf orders T
  set J := EvalMat.ceilLog (min mA (O' - 1) + min mB (O' - 1) + 1) with hJdef
  have hJ : J ≤ jm := EvalMat.ceilLog_le (by have := min_sub_le hmA hOO; have := min_sub_le hmB hOO; omega)
  refine ⟨J, hJ, ?_⟩
  have hJ64 : J ≤ FFT.novelTransform.maxLog := by show J ≤ 64; omega
  rw [ite_eq_left hJ64]
  simp only [novelTransform_plan]
  have hmo := maxOrderOfC_cost P (by includes) orders T O (by omega) hO ho
  have h1 := maxEntryDegreeC_cost P (by includes) A R S (by omega) (by omega) dA hdA' hdA
  have h2 := maxEntryDegreeC_cost P (by includes) B S T (by omega) (by omega) dB hdB' hdB
  have hm1 := min_le_left mA (O' - 1)
  have hm2 := min_le_left mB (O' - 1)
  have h3 := ceilLogLoopC_cost P (by includes) (min mA (O' - 1) + min mB (O' - 1) + 1) jm
    (by have := min_sub_le hmA hOO; have := min_sub_le hmB hOO; omega) (by omega)
    (min mA (O' - 1) + min mB (O' - 1) + 1) 0 (by omega) (by omega)
  have hJ40 : J ≤ 40 := by omega
  have h4 := mkPlanC_cost P (by includes) hJ40
  have hE : ∀ (M : CompPoly.PolynomialMatrix K) (i k : ℕ), appCost P (.closure mulTruncEvalPC.lam0.costIdx
      [encodeValue M, encodeValue O', encodeValue T]) [encodeValue i, encodeValue k] ≤ 55 * O + 48 :=
    fun M i k ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mulTruncEvalPC.lam0.costEq P (by includes), Decoder.rowGet_cost P (by includes)]
      have := truncateXC_cost P (by includes) O' (by omega) (CompPoly.PolynomialMatrix.rowGet (M.getD i #[]) k)
      omega
  have h5 := transformEntriesPC_cost P (by includes) hJ40 R S (by omega) (by omega)
    (fun i k ↦ CompPoly.PolynomialMatrix.truncateX O' (CompPoly.PolynomialMatrix.rowGet (A.getD i #[]) k))
    (.closure mulTruncEvalPC.lam0.costIdx [encodeValue A, encodeValue O', encodeValue T])
    (fun i k ↦ RunsApp.of_spec (mulTruncEvalPC.lam0.costSpec P (by includes) A O' T i k)) _ (hE A)
  have h6 := transformEntriesPC_cost P (by includes) hJ40 S T (by omega) (by omega)
    (fun k c ↦ CompPoly.PolynomialMatrix.truncateX O' (CompPoly.PolynomialMatrix.rowGet (B.getD k #[]) c))
    (.closure mulTruncEvalPC.lam0.costIdx [encodeValue B, encodeValue O', encodeValue T])
    (fun k c ↦ RunsApp.of_spec (mulTruncEvalPC.lam0.costSpec P (by includes) B O' T k c)) _ (hE B)
  have hN : 2 ^ J ≤ 2 ^ 36 := Nat.pow_le_pow_right (by norm_num) (by omega)
  set FA := FFT.transformEntriesP FFT.novelTransform (FFT.mkPlan J) R S fun i k ↦
    CompPoly.PolynomialMatrix.truncateX O' (CompPoly.PolynomialMatrix.rowGet (A.getD i #[]) k) with hFA
  set FB := FFT.transformEntriesP FFT.novelTransform (FFT.mkPlan J) S T fun k c ↦
    CompPoly.PolynomialMatrix.truncateX O' (CompPoly.PolynomialMatrix.rowGet (B.getD k #[]) c) with hFB
  have h7 := matrixOfFnC_cost P (by includes) R T (by omega) (by omega) _
    (.closure mulTruncEvalPC.lam1.costIdx [encodeValue orders, encodeValue FA, encodeValue FB,
      encodeValue (2 ^ J), encodeValue (FFT.mkPlan J), encodeValue J, encodeValue R, encodeValue O',
      encodeValue S, encodeValue T])
    (fun i c ↦ RunsApp.of_spec (mulTruncEvalPC.lam1.costSpec P (by includes) _ _ _ _ _ _ _ _ _ _ i c))
    (80 * (2 ^ J * S) + 46 * 2 ^ J + 20 + invBound J + 55 * O + 31 + 27)
    (fun i c ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mulTruncEvalPC.lam1.costEq P (by includes)]
      have e1 := evalDotC_cost P (by includes) (2 ^ J) S (by omega) (by omega) (FA.getD i #[]) FB c
      have e2 := planInvPolyC_cost P (by includes) hJ40
        (EvalMat.evalDot (2 ^ J) S (FA.getD i #[]) FB c)
      have e3 := truncateXC_cost P (by includes) (orders.getD c 0) (by have := ho c; omega)
        (FFT.novelTransform.invP (FFT.mkPlan J) (EvalMat.evalDot (2 ^ J) S (FA.getD i #[]) FB c))
      have := ho c
      rw [invBound]
      omega)
  rw [limbs_shift (k := J) (by omega)]
  cost_simp
  have e3 : R * T * (80 * (2 ^ J * S) + 46 * 2 ^ J + 20 + invBound J + 55 * O + 31 + 27 + 35) =
      R * T * (80 * (2 ^ J * S) + 46 * 2 ^ J + invBound J + 55 * O + 113) := by ring
  have e4 : R * S * (55 * O + 48 + fwdBound J + 28) + 162 * (R * S) =
      R * S * (fwdBound J + 55 * O + 238) := by ring
  have e5 : S * T * (55 * O + 48 + fwdBound J + 28) + 162 * (S * T) =
      S * T * (fwdBound J + 55 * O + 238) := by ring
  rw [planBound]
  split_ifs <;> omega

theorem ovh_of_ok {p : PMPrices} (hp : FFTPricesOK p) : 504 ≤ p.ovh := by
  have := (hp.2 0 (by norm_num)).1
  simp [fwdNeed, fwdBound, fwdPrice] at this
  omega

/-- The explicit truncated price within `evalMatPrice` and the truncations' `ovh` per order. -/
theorem evalMatTrunc_fit (R S T J jm mac F I ovh O : ℕ) (hR0 : 0 < R) (hS0 : 0 < S)
    (hN : 2 ^ J ≤ 2 ^ jm) (hmac : 80 ≤ mac) (hf : fwdNeed J ≤ F) (hi : invNeed J ≤ I)
    (hovh : 504 ≤ ovh) :
    R * S * (fwdBound J + 55 * O + 238) + S * T * (fwdBound J + 55 * O + 238) +
        R * T * (80 * (2 ^ J * S) + 46 * 2 ^ J + invBound J + 55 * O + 113) +
        182 * R + 133 * S + 40 * T + planBound J + 1079 ≤
      (R * S + S * T) * F + R * T * I + R * S * T * 2 ^ jm * mac + 2 ^ 20 +
        ovh * ((R * S + S * T + R * T) * (O + 1)) := by
  have hx1 : R ≤ R * S := Nat.le_mul_of_pos_right _ hS0
  have hx2 : S ≤ R * S := Nat.le_mul_of_pos_left _ hR0
  have hx3 : T ≤ S * T := Nat.le_mul_of_pos_left _ hS0
  have hx0 : 1 ≤ R * S := Nat.mul_pos hR0 hS0
  have hplan := plan_fit (R * S) J hx0
  have h1 : R * S * fwdNeed J ≤ R * S * F := Nat.mul_le_mul_left _ hf
  have h2 : S * T * (fwdBound J + 345) ≤ S * T * F :=
    Nat.mul_le_mul_left _ (by unfold fwdNeed at hf; omega)
  have e1 : R * T * (80 * (2 ^ J * S) + 46 * 2 ^ J + invBound J + 55 * O + 113) =
      R * T * invNeed J + 80 * (R * S * T * 2 ^ J) + R * T * (55 * O + 38) := by unfold invNeed; ring
  have e2 : R * T * invNeed J ≤ R * T * I := Nat.mul_le_mul_left _ hi
  have e3 : 80 * (R * S * T * 2 ^ J) ≤ R * S * T * 2 ^ jm * mac := by
    rw [mul_comm (R * S * T * 2 ^ jm) mac]
    calc 80 * (R * S * T * 2 ^ J) ≤ mac * (R * S * T * 2 ^ J) := Nat.mul_le_mul_right _ hmac
      _ ≤ mac * (R * S * T * 2 ^ jm) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hN)
  have hO1 : 55 * O + 208 ≤ ovh * (O + 1) := by nlinarith
  have e4 : ovh * ((R * S + S * T + R * T) * (O + 1)) =
      R * S * (ovh * (O + 1)) + S * T * (ovh * (O + 1)) + R * T * (ovh * (O + 1)) := by ring
  have f1 : R * S * (55 * O + 208) ≤ R * S * (ovh * (O + 1)) := Nat.mul_le_mul_left _ hO1
  have f2 : S * T * (55 * O + 208) ≤ S * T * (ovh * (O + 1)) := Nat.mul_le_mul_left _ hO1
  have f3 : R * T * (55 * O + 38) ≤ R * T * (ovh * (O + 1)) := Nat.mul_le_mul_left _ (by omega)
  have g1 : R * S * (fwdBound J + 345) + R * S * (55 * O + 208) =
      R * S * (fwdBound J + 55 * O + 238) + 315 * (R * S) := by ring
  have g2 : S * T * (fwdBound J + 345) + S * T * (55 * O + 208) =
      S * T * (fwdBound J + 55 * O + 238) + 315 * (S * T) := by ring
  have e5 : (R * S + S * T) * F = R * S * F + S * T * F := by ring
  linarith

/-- **The column-truncated product within the model** (`mulTruncEvalPC`): at most `evalMatPrice`
at the truncated degrees and `ovh` per order of every entry (the truncations at the largest order
`O`), for `R, S ≥ 1` rows, `clog2 (min dA (O − 1) + min dB (O − 1) + 1) ≤ 36`. -/
theorem mulTruncEvalPC_cost (hP : Includes P mulTruncEvalPC.costDeps) (p : PMPrices)
    (hp : FFTPricesOK p) (orders : Array ℕ) (A B : CompPoly.PolynomialMatrix K) (dA dB O : ℕ)
    (hdA : ∀ i k, (CompPoly.PolynomialMatrix.rowGet (A.getD i #[]) k).natDegree ≤ dA)
    (hdB : ∀ k c, (CompPoly.PolynomialMatrix.rowGet (B.getD k #[]) c).natDegree ≤ dB)
    (ho : ∀ c, orders.getD c 0 ≤ O) (hO : O < 2 ^ 40) (hdA' : dA < 2 ^ 40) (hdB' : dB < 2 ^ 40)
    (hj : clog2 (min dA (O - 1) + min dB (O - 1) + 1) ≤ 36) (hR0 : 0 < A.size)
    (hR : A.size < 2 ^ 32) (hS0 : 0 < B.size) (hS : B.size < 2 ^ 32)
    (hT : B.MatrixWidth < 2 ^ 32) :
    machineCost P mulTruncEvalPC.costIdx [encodeValue orders, encodeValue A, encodeValue B] ≤
      evalMatPrice p A.size B.size B.MatrixWidth (min dA (O - 1)) (min dB (O - 1)) +
        p.ovh * ((A.size * B.size + B.size * B.MatrixWidth + A.size * B.MatrixWidth) * (O + 1)) := by
  set jm := clog2 (min dA (O - 1) + min dB (O - 1) + 1) with hjmdef
  have hjm : min dA (O - 1) + min dB (O - 1) + 1 ≤ 2 ^ jm := by
    rw [hjmdef, clog2_eq_ceilLog]; exact EvalMat.le_two_pow_ceilLog _
  obtain ⟨J, hJ, hcost⟩ := mulTruncEvalPC_cost_explicit P hP orders A B dA dB O jm hdA hdB ho hO hjm
    hj hdA' hdB' hR hS hT
  have hovh := ovh_of_ok hp
  obtain ⟨hmac, hneed⟩ := hp
  obtain ⟨hf, hi⟩ := hneed J (by omega)
  have hf' := hf.trans (fwdPrice_mono p hJ)
  have hi' := hi.trans (invPrice_mono p hJ)
  have hN : 2 ^ J ≤ 2 ^ jm := Nat.pow_le_pow_right (by norm_num) hJ
  rw [evalMatPrice, ← hjmdef]
  exact hcost.trans (evalMatTrunc_fit _ _ _ J jm p.mac _ _ p.ovh O hR0 hS0 hN hmac hf' hi' hovh)

end

end LeanVM.Cost.Bounds.PMFFT
