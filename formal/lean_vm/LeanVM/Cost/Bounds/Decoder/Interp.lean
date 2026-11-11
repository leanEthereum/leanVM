module

public import LeanVM.Cost.Bounds.Decoder.Poly
public import LeanVM.Cost.Bounds.Sizes.Interp
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic

/-!
# Bound: the decoder's interpolation, compiled

The prices of the pieces of a lane's interpolation that compute `G` and `R` (compiled in
`Cost/Extractor/PMLane.lean`), on `n` points:

* the vanishing polynomial (`vanishingC_cost`: `n` products by a linear factor,
  `362·n² + 501·n + 14`);
* Horner's evaluations (`evalHornerC_cost`, `evalBatchC_cost`), the derivative
  (`derivativeC_cost`), synthetic division by `X − x` (`divByLinearFactorC_cost`), one term
  (`interpTermC_cost`: an inverse, a division, a scaling), and the interpolating polynomial
  (`interpolateC_cost`: `309·|G|·n + 3529·n + 97·|G| + 74`).

The least row's normalization is bounded in `Bounds/Decoder/Interpolate.lean`, the interpolation
in `Bounds/PMSolve/Interp.lean`.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.CompPoly.CPolynomial LeanVM.Cost.Auto.LeanVM.Extraction.Fast

open LeanVM.Extraction.Fast.PMDegree (val_size_le_natDegree_add_one)

public section

variable (P : MachineProgram)

theorem size_linearFactor_le (x : K) : (CPolynomial.linearFactor x).val.size ≤ 2 :=
  (val_size_le_natDegree_add_one _).trans (by have := natDegree_linearFactor x; omega)

/-- `C r` over `K`: at most `51`. -/
theorem cK_cost (hP : Includes P C.c74.costDeps) (r : K) :
    machineCost P C.c74.costIdx [encodeValue r] ≤ 51 := by
  rw [C.c74.costEq P hP]
  have hs : (CPolynomial.Raw.C r).size = 1 := rfl
  have := trimLen_cost P (by includes) (CPolynomial.Raw.C r) (CPolynomial.Raw.C r).size
    (by rw [hs]; norm_num)
  have h1 : (Array.extract (CPolynomial.Raw.C r) 0 (CompPolyLib.trimLen (CPolynomial.Raw.C r)
      (CPolynomial.Raw.C r).size)).size ≤ 1 := by simp [CPolynomial.Raw.C]
  omega

/-- `X` over `K`: `13`. -/
theorem xK_cost (hP : Includes P X.c612.costDeps) : machineCost P X.c612.costIdx [] = 13 := by
  rw [X.c612.costEq P hP, Raw.X.c55.costEq P (by includes)]

/-- A linear factor `X − x`: at most `236`. -/
theorem linearFactorC_cost (hP : Includes P linearFactor.c611.costDeps) (x : K) :
    machineCost P linearFactor.c611.costIdx [encodeValue x] ≤ 236 := by
  rw [linearFactor.c611.costEq P hP]
  have := cK_cost P (by includes) (-x)
  have := xK_cost P (by includes)
  have hc : (CPolynomial.C (-x)).val.size ≤ 1 := by
    show (CPolynomial.Raw.C (-x)).trim.size ≤ 1
    exact (raw_trim_size_le _).trans (by simp [CPolynomial.Raw.C])
  have hx : (CPolynomial.X : CPolynomial K).val.size ≤ 2 := by
    show (CPolynomial.Raw.X : CPolynomial.Raw K).size ≤ 2
    simp [CPolynomial.Raw.X]
  have := addK_cost P (by includes) (CPolynomial.C (-x)).val (CPolynomial.X : CPolynomial K).val
    (by omega) (by omega)
  omega

/-- **The vanishing polynomial of `n` points** (`vanishingFast`, `n` products by a linear
factor): at most `362·n² + 501·n + 14`, written with `n·n` an atom. -/
theorem vanishingC_cost (hP : Includes P vanishingFast.c609.costDeps) (xs : Array K)
    (hn : xs.size < 2 ^ 58) :
    machineCost P vanishingFast.c609.costIdx [encodeValue xs] ≤
      362 * (xs.size * xs.size) + 501 * xs.size + 14 := by
  rw [vanishingFast.c609.costEq P hP]
  have hf := listFoldl_le_idx P (by includes) _ (.closure vanishingFast.c609.lam0.costIdx [])
    (fun acc x ↦ RunsApp.of_spec (vanishingFast.c609.lam0.costSpec P (by includes) acc x))
    (362 * xs.size + 487) (fun k acc ↦ acc.val.size + 2 * k ≤ 2 * xs.size + 1) xs.toList
    (fun k acc hacc x _ ↦ by
      refine ⟨?_, ?_⟩
      · have := cpoly_mul_size_le (CPolynomial.linearFactor x) acc
        have := size_linearFactor_le x
        omega
      · rw [appCost_fn, List.nil_append, List.length_nil,
          vanishingFast.c609.lam0.costEq P (by includes)]
        have := linearFactorC_cost P (by includes) x
        have hl := size_linearFactor_le x
        have := mulK_cost P (by includes) (CPolynomial.linearFactor x).val acc.val
          (by omega) (by omega)
        have : acc.val.size * (CPolynomial.linearFactor x).val.size ≤ 2 * acc.val.size :=
          by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hl
        have : (CPolynomial.linearFactor x).val.size * (CPolynomial.linearFactor x).val.size ≤ 4 :=
          Nat.mul_le_mul hl hl |>.trans (by norm_num)
        omega)
    xs.toList 1 (fun _ h ↦ h)
    (by show (CPolynomial.Raw.C (1 : K)).size + _ ≤ _
        simp [CPolynomial.Raw.C]; omega)
  have e : (362 * xs.size + 487 + 11) * xs.toList.length =
      362 * (xs.size * xs.size) + 498 * xs.size := by
    simp only [Array.length_toList]; ring
  omega

/-! ## The interpolating polynomial -/

/-- A natural number in `K`: at most `7`. -/
theorem natCastC_cost (hP : Includes P Auto.BF64.natCast.c577.costDeps) (n : ℕ) (hn : n < 2 ^ 64) :
    machineCost P Auto.BF64.natCast.c577.costIdx [encodeValue n] ≤ 7 := by
  rw [Auto.BF64.natCast.c577.costEq P hP]
  cost_simp
  split_ifs <;> omega

/-- **Horner's evaluation** (`evalHorner`): at most `46·|p| + 16`. -/
theorem evalHornerC_cost (hP : Includes P evalHorner.c20.costDeps) (x : K) (p : CPolynomial K) :
    machineCost P evalHorner.c20.costIdx [encodeValue x, encodeValue p] ≤ 46 * p.val.size + 16 := by
  rw [evalHorner.c20.costEq P hP, eval₂Horner.c21.costEq P (by includes),
    Raw.eval₂Horner.c22.costEq P (by includes)]
  have := foldr_cost P (by includes) _ (.closure Raw.eval₂Horner.c22.lam0.costIdx [encodeValue x])
    (fun a acc ↦ RunsApp.of_spec (us := [encodeValue x]) (vs := [encodeValue a, encodeValue acc])
      (Raw.eval₂Horner.c22.lam0.costSpec P (by includes) x a acc)) 32 (0 : K) p.val.toList
    (fun a _ acc ↦ by
      rw [appCost_fn, List.singleton_append, Raw.eval₂Horner.c22.lam0.costEq P (by includes)]; simp)
  simp only [Array.length_toList] at this
  omega

/-- **Horner at every point** (`evalBatchHorner`): at most `46·|p|·|xs| + 37·|xs| + 10`. -/
theorem evalBatchC_cost (hP : Includes P evalBatchHorner.c615.costDeps) (p : CPolynomial K)
    (xs : Array K) :
    machineCost P evalBatchHorner.c615.costIdx [encodeValue p, encodeValue xs] ≤
      46 * (p.val.size * xs.size) + 37 * xs.size + 10 := by
  rw [evalBatchHorner.c615.costEq P hP]
  have hf := fun x ↦ RunsApp.of_spec (us := [encodeValue p]) (vs := [encodeValue x])
    (evalBatchHorner.c615.lam0.costSpec P (by includes) p x)
  have := listMap_le P Auto.List.map.c30.costIdx (.closure evalBatchHorner.c615.lam0.costIdx [encodeValue p])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) (46 * p.val.size + 20) xs.toList
    (fun x _ ↦ by
      rw [appCost_fn, List.singleton_append, List.length_singleton,
        evalBatchHorner.c615.lam0.costEq P (by includes)]
      have := evalHornerC_cost P (by includes) x p
      omega)
  have e : (46 * p.val.size + 20 + 13) * xs.toList.length =
      46 * (p.val.size * xs.size) + 33 * xs.size := by simp only [Array.length_toList]; ring
  simp only [Array.length_toList, List.length_map] at this e ⊢
  omega

/-- **The derivative** (`derivative`): at most `97·|p| + 30`. -/
theorem derivativeC_cost (hP : Includes P derivative.c617.costDeps) (p : CPolynomial K)
    (hp : p.val.size < 2 ^ 58) :
    machineCost P derivative.c617.costIdx [encodeValue p] ≤ 97 * p.val.size + 30 := by
  rw [derivative.c617.costEq P hP]
  have hsz : (Array.extract p.val 1).size ≤ p.val.size := by simp
  have := zipIdx_cost P (by includes) (Array.extract p.val 1).toList 0 (by simp; omega)
  have hf := fun q ↦ RunsApp.of_spec (us := []) (vs := [encodeValue q])
    (derivative.c617.lam0.costSpec P (by includes) q)
  have hm := listMap_le P Auto.List.map.c30.costIdx (.closure derivative.c617.lam0.costIdx [])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) 41
    (Array.extract p.val 1).toList.zipIdx
    (fun q hq ↦ by
      have := List.mem_zipIdx hq
      simp only [Array.length_toList] at this
      rw [appCost_fn, List.nil_append, List.length_nil, derivative.c617.lam0.costEq P (by includes)]
      have := natCastC_cost P (by includes) (q.2 + 1) (by omega)
      cost_simp
      omega)
  have ht := trimLen_cost P (by includes)
    (CPolynomial.Raw.mk (Array.mapIdx (fun i c ↦ c * (↑(i + 1) : K)) (Array.extract p.val 1)))
    (CPolynomial.Raw.mk (Array.mapIdx (fun i c ↦ c * (↑(i + 1) : K)) (Array.extract p.val 1))).size
    (by simp; omega)
  simp only [List.length_zipIdx, Array.length_toList, List.length_map, Array.size_mapIdx,
    Array.size_extract] at *
  omega

theorem divFold_length (g : K × List K → ℕ → K) :
    ∀ (l : List ℕ) (st : K × List K),
      (l.foldl (fun state j ↦ (g state j, g state j :: state.2)) st).2.length =
        st.2.length + l.length := by
  intro l
  induction l with
  | nil => intro st; simp
  | cons j l ih => intro st; rw [List.foldl_cons, ih]; simp; omega

/-- **Division by `X − x`** (`divByLinearFactor`, synthetic division): at most `109·|p| + 51`. -/
theorem divByLinearFactorC_cost (hP : Includes P divByLinearFactor.c621.costDeps)
    (p : CPolynomial K) (x : K) (hp : p.val.size < 2 ^ 58) :
    machineCost P divByLinearFactor.c621.costIdx [encodeValue p, encodeValue x] ≤ 109 * p.val.size + 51 := by
  rw [divByLinearFactor.c621.costEq P hP]
  have := rangeLoop_cost P (by includes) (p.val.size - 1) [] (by omega)
  have := reverseAux_cost P (by includes) (List.range (p.val.size - 1)) []
  have hf := listFoldl_le P (by includes) _ (.closure divByLinearFactor.c621.lam0.costIdx [encodeValue p, encodeValue x])
    (fun st j ↦ RunsApp.of_spec (us := [encodeValue p, encodeValue x]) (vs := [encodeValue st, encodeValue j])
      (divByLinearFactor.c621.lam0.costSpec P (by includes) p x st j))
    50 (fun _ ↦ True) (List.range (p.val.size - 1)).reverse (0, []) trivial
    (fun st _ j hj ↦ ⟨trivial, by
      simp only [List.mem_reverse, List.mem_range] at hj
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        divByLinearFactor.c621.lam0.costEq P (by includes)]
      simp only [List.length_cons, List.length_nil]
      cost_simp
      omega⟩)
  generalize hL : List.foldl _ ((0 : K), ([] : List K)) (List.range (p.val.size - 1)).reverse = L
  have hlen : L.2.length = p.val.size - 1 := by
    rw [← hL]
    have := divFold_length (fun state j ↦ p.coeff (j + 1) + x * state.1)
      (List.range (p.val.size - 1)).reverse (0, [])
    simpa using this
  have := ofArray_cost P (by includes) L.2.toArray (by simp; omega)
  simp only [List.length_reverse, List.length_range, List.size_toArray] at *
  cost_simp
  omega

theorem size_divByLinearFactor_le (p : CPolynomial K) (x : K) :
    (CPolynomial.divByLinearFactor p x).val.size ≤ p.val.size + 1 := by
  have h1 := natDegree_divByLinearFactor_le_pred p x
  have h2 := val_size_le_natDegree_add_one (CPolynomial.divByLinearFactor p x)
  have h3 := natDegree_le_size p
  omega

/-- **One interpolation term** (`interpolationTermWithVanishing`: an inverse, a division by
`X − x`, a scaling): at most `210·|G| + 3260`. -/
theorem interpTermC_cost (hP : Includes P interpolationTermWithVanishing.c620.costDeps)
    (G : CPolynomial K) (pt : K × K) (dv : K) (hG : G.val.size < 2 ^ 58) :
    machineCost P interpolationTermWithVanishing.c620.costIdx [encodeValue G, encodeValue pt, encodeValue dv] ≤
      210 * G.val.size + 3260 := by
  rw [interpolationTermWithVanishing.c620.costEq P hP]
  have := invK_cost P (by includes) dv
  have := cK_cost P (by includes) (pt.2 / dv)
  have := divByLinearFactorC_cost P (by includes) G pt.1 hG
  have hd := size_divByLinearFactor_le G pt.1
  have hc : (CPolynomial.C (pt.2 / dv)).val.size ≤ 1 :=
    (raw_trim_size_le _).trans (by simp [CPolynomial.Raw.C])
  have := mulK_cost P (by includes) (CPolynomial.C (pt.2 / dv)).val
    (CPolynomial.divByLinearFactor G pt.1).val (by omega) (by omega)
  have : (CPolynomial.divByLinearFactor G pt.1).val.size * (CPolynomial.C (pt.2 / dv)).val.size ≤
      G.val.size + 1 := by
    calc _ ≤ (G.val.size + 1) * 1 := Nat.mul_le_mul hd hc
      _ = G.val.size + 1 := Nat.mul_one _
  have : (CPolynomial.C (pt.2 / dv)).val.size * (CPolynomial.C (pt.2 / dv)).val.size ≤ 1 :=
    Nat.mul_le_mul hc hc
  omega

theorem size_interpTerm_le (G : CPolynomial K) (pt : K × K) (dv : K) :
    (CPolynomial.interpolationTermWithVanishing G pt dv).val.size ≤ G.val.size + 2 := by
  unfold CPolynomial.interpolationTermWithVanishing
  have := cpoly_mul_size_le (CPolynomial.C (pt.2 / dv)) (CPolynomial.divByLinearFactor G pt.1)
  have := size_divByLinearFactor_le G pt.1
  have hc : (CPolynomial.C (pt.2 / dv)).val.size ≤ 1 :=
    (raw_trim_size_le _).trans (by simp [CPolynomial.Raw.C])
  omega

/-- **The interpolating polynomial** (`interpolateCoefficientFormWithVanishing`, `n` points,
the vanishing polynomial `G`): at most `309·|G|·n + 3529·n + 97·|G| + 74`. -/
theorem interpolateC_cost (hP : Includes P interpolateCoefficientFormWithVanishing.c614.costDeps)
    (G : CPolynomial K) (points : Array (K × K)) (hG : G.val.size < 2 ^ 58)
    (hn : points.size < 2 ^ 58) :
    machineCost P interpolateCoefficientFormWithVanishing.c614.costIdx [encodeValue G, encodeValue points] ≤
      309 * (G.val.size * points.size) + 3529 * points.size + 97 * G.val.size + 74 := by
  rw [interpolateCoefficientFormWithVanishing.c614.costEq P hP]
  have := derivativeC_cost P (by includes) G hG
  have hdG : G.derivative.val.size ≤ G.val.size := by
    show (CPolynomial.Raw.mk (Array.mapIdx _ (Array.extract G.val 1))).trim.size ≤ _
    exact (raw_trim_size_le _).trans (by simp)
  have hf := fun pt ↦ RunsApp.of_spec (us := []) (vs := [encodeValue pt])
    (LeanVM.Cost.Extractor.interpolatePMC.lam0.costSpec P (by includes) pt)
  have hm := listMap_le P Auto.List.map.c30.costIdx
    (.closure LeanVM.Cost.Extractor.interpolatePMC.lam0.costIdx [])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) 2 points.toList
    (fun pt _ ↦ by
      rw [appCost_fn, List.nil_append,
        LeanVM.Cost.Extractor.interpolatePMC.lam0.costEq P (by includes)]; simp)
  have he := evalBatchC_cost P (by includes) G.derivative
    (Array.map (fun point : K × K ↦ point.1) points)
  have := rangeLoop_cost P (by includes) points.size [] (by omega)
  have hfo := listFoldl_le P (by includes) _
    (.closure interpolateCoefficientFormWithVanishing.c614.lam0.costIdx
      [encodeValue G, encodeValue points, encodeValue ((CPolynomial.BatchEvalContext.horner K).evalBatchWith G.derivative
        (Array.map (fun point : K × K ↦ point.1) points))])
    (fun acc i ↦ RunsApp.of_spec
      (us := [encodeValue G, encodeValue points, encodeValue ((CPolynomial.BatchEvalContext.horner K).evalBatchWith
        G.derivative (Array.map (fun point : K × K ↦ point.1) points))]) (vs := [encodeValue acc, encodeValue i])
      (interpolateCoefficientFormWithVanishing.c614.lam0.costSpec P (by includes) G points _ acc i))
    (263 * G.val.size + 3447) (fun acc ↦ acc.val.size ≤ G.val.size + 2)
    (List.range points.size) 0 (by show (#[] : Array K).size ≤ _; simp)
    (fun acc hacc i _ ↦ by
      refine ⟨?_, ?_⟩
      · have := cpoly_add_size_le acc (CPolynomial.interpolationTermWithVanishing G
          (points.getD i (0, 0)) (((CPolynomial.BatchEvalContext.horner K).evalBatchWith
            G.derivative (Array.map (fun point : K × K ↦ point.1) points)).getD i 0))
        have := size_interpTerm_le G (points.getD i (0, 0)) (((CPolynomial.BatchEvalContext.horner
          K).evalBatchWith G.derivative (Array.map (fun point : K × K ↦ point.1) points)).getD i 0)
        omega
      · rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
          interpolateCoefficientFormWithVanishing.c614.lam0.costEq P (by includes)]
        simp only [List.length_cons, List.length_nil]
        have := interpTermC_cost P (by includes) G (points.getD i (0, 0))
          (((CPolynomial.BatchEvalContext.horner K).evalBatchWith G.derivative
            (Array.map (fun point : K × K ↦ point.1) points)).getD i 0) hG
        have := size_interpTerm_le G (points.getD i (0, 0)) (((CPolynomial.BatchEvalContext.horner
          K).evalBatchWith G.derivative (Array.map (fun point : K × K ↦ point.1) points)).getD i 0)
        have := addK_cost P (by includes) acc.val (CPolynomial.interpolationTermWithVanishing G
          (points.getD i (0, 0)) (((CPolynomial.BatchEvalContext.horner K).evalBatchWith
            G.derivative (Array.map (fun point : K × K ↦ point.1) points)).getD i 0)).val (by omega)
          (by omega)
        omega)
  have : G.derivative.val.size * (Array.map (fun point : K × K ↦ point.1) points).size ≤
      G.val.size * points.size := by simp only [Array.size_map]; exact Nat.mul_le_mul_right _ hdG
  have e : (263 * G.val.size + 3447 + 11) * (List.range points.size).length =
      263 * (G.val.size * points.size) + 3458 * points.size := by
    simp only [List.length_range]; ring
  simp only [Array.length_toList, List.length_map, Array.size_map] at *
  omega

end

end LeanVM.Cost.Bounds.Decoder
