/-
  LeanVM.Prover.WhirTables

  The executable opening's array computations are the specification's list computations.
-/

module

public import Statement.Prover.Whir
public import LeanVM.Prover.Ntt
public import LeanVM.Prover.Mle
public import LeanVM.Protocol.Whir.Complete.Opening

/-!
# The opening's tables

Each array computation of `Statement/Prover/Whir.lean` is the list computation of the
specification (`LeanVM.Protocol.Whir.Complete`): the round coefficients (`roundC0A_eq`,
`roundC2A_eq`), the incremental fold (`toList_foldPairsA_foldAll`; a fold, the multilinear
extension and the equality table are `LeanVM.Prover.Mle`'s), the out-of-domain claim's table
(`eqKernel_eq_tableOf`), gluing (`toList_glueTablesA`), the query table by tensor products
(`toList_queryTableA`) and the stack table (`toList_stackTableA`).
-/

namespace LeanVM.Prover.Enc

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete LeanVM.Protocol
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Verifier Finset

@[expose] public section

/-! ## Lists and arrays -/

theorem list_ext_getD {l l' : List E} (h : l.length = l'.length)
    (hg : ∀ i < l.length, l.getD i 0 = l'.getD i 0) : l = l' := by
  refine List.ext_getElem h fun i h₁ h₂ ↦ ?_
  have := hg i h₁
  rwa [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at this

theorem toList_getD_E (a : Array E) (i : ℕ) : a.toList.getD i 0 = a.getD i 0 :=
  array_getD_toList a i 0

/-! ## Sums and round coefficients -/

theorem roundC0_eq_sum : ∀ (l m : List E),
    roundC0 l m = ∑ x ∈ range (min l.length m.length / 2), l.getD (2 * x) 0 * m.getD (2 * x) 0
  | w0 :: w1 :: ws, g0 :: g1 :: gs => by
    rw [roundC0, roundC0_eq_sum ws gs]
    simp only [List.length_cons]
    rw [show min (ws.length + 1 + 1) (gs.length + 1 + 1) / 2 = min ws.length gs.length / 2 + 1 by
      omega, sum_range_succ', add_comm]
    congr 1
  | [], _ => by simp [roundC0]
  | [_], m => by simp [roundC0, show min 1 m.length / 2 = 0 by omega]
  | _ :: _ :: _, [] => by simp [roundC0]
  | _ :: _ :: _, [_] => by simp [roundC0]

theorem roundC2_eq_sum : ∀ (l m : List E),
    roundC2 l m = ∑ x ∈ range (min l.length m.length / 2),
      (l.getD (2 * x) 0 + l.getD (2 * x + 1) 0) * (m.getD (2 * x) 0 + m.getD (2 * x + 1) 0)
  | w0 :: w1 :: ws, g0 :: g1 :: gs => by
    rw [roundC2, roundC2_eq_sum ws gs]
    simp only [List.length_cons]
    rw [show min (ws.length + 1 + 1) (gs.length + 1 + 1) / 2 = min ws.length gs.length / 2 + 1 by
      omega, sum_range_succ', add_comm]
    congr 1
  | [], _ => by simp [roundC2]
  | [_], m => by simp [roundC2, show min 1 m.length / 2 = 0 by omega]
  | _ :: _ :: _, [] => by simp [roundC2]
  | _ :: _ :: _, [_] => by simp [roundC2]

theorem roundC0A_eq (W g : Array E) : roundC0A W g = roundC0 W.toList g.toList := by
  rw [roundC0A, sumRange_eq, roundC0_eq_sum, Array.length_toList, Array.length_toList]
  simp only [toList_getD_E]

theorem roundC2A_eq (W g : Array E) : roundC2A W g = roundC2 W.toList g.toList := by
  rw [roundC2A, sumRange_eq, roundC2_eq_sum, Array.length_toList, Array.length_toList]
  simp only [toList_getD_E]

/-! ## Folds -/

/-- The incremental fold is the specification's fold from the stack table. -/
theorem toList_foldPairsA_foldAll {f₀ : List E} {folds : List E} {g : Array E}
    (hg : g.toList = foldAll f₀ folds) (c : E) :
    (foldPairsA c g).toList = foldAll f₀ (folds ++ [c]) := by
  rw [toList_foldPairsA, hg, foldAll_concat]

/-! ## The equality kernel -/

theorem getD_eqTable_eqKernel (z : List E) (j : ℕ) :
    (eqTable z).getD j 0 = (eqKernel z).getD j 0 := by
  rw [← toList_getD_E, toList_eqTable]

/-- The out-of-domain claim's table is the equality kernel of the point. -/
theorem eqKernel_eq_tableOf {m : ℕ} (z : List E) (hz : z.length = m) :
    eqKernel z = tableOf m (eqEval z) := by
  subst hz
  refine list_ext_getD (by rw [length_eqKernel, length_tableOf]) fun j hj ↦ ?_
  rw [length_eqKernel] at hj
  rw [getD_eqKernel z j hj, getD_tableOf _ _ _ hj, eqEval_comm]

/-! ## Gluing -/

theorem toList_glueTablesA_aux (lam : E) : ∀ (Ts : List (Array E)) (W : Array E) (sc : E),
    (Ts.foldl (fun (acc : Array E × E) T ↦
      let s := acc.2 * lam
      (Array.zipWith (fun a b ↦ a + s * b) acc.1 T, s)) (W, sc)).1.toList =
      ((Ts.map Array.toList).foldl
        (fun (acc : List E × E) T ↦ (axpy (acc.2 * lam) acc.1 T, acc.2 * lam)) (W.toList, sc)).1
  | [], _, _ => rfl
  | T :: Ts, W, sc => by
    have h : (Array.zipWith (fun a b ↦ a + sc * lam * b) W T).toList =
        axpy (sc * lam) W.toList T.toList := by simp [axpy]
    rw [List.foldl_cons, List.map_cons, List.foldl_cons]
    exact (toList_glueTablesA_aux lam Ts _ _).trans (by rw [h])

theorem toList_glueTablesA (lam : E) (W : Array E) (Ts : List (Array E)) :
    (glueTablesA lam W Ts).toList = glueTables lam W.toList (Ts.map Array.toList) :=
  toList_glueTablesA_aux lam Ts W 1

/-! ## The query table -/

theorem novelAt_eq_prod {m i : ℕ} (hm : m ≤ 64) (hi : i < 2 ^ m) (a : K) :
    novelAt i a = ∏ c ∈ range m, if i.testBit c then normVanishingAt c a else 1 := by
  conv_lhs => rw [← bitsToNat_testBit hi]
  rw [novelAt_bitsToNat hm, ← Fin.prod_univ_eq_prod_range
    (fun c ↦ if i.testBit c then normVanishingAt c a else 1)]

theorem tensorA_aux : ∀ (ws pre : List K) (v : Array K), v.size = 2 ^ pre.length →
    (∀ i < 2 ^ pre.length, v.getD i 0 =
      ∏ c ∈ range pre.length, if i.testBit c then pre.getD c 0 else 1) →
    (ws.foldl (fun v w ↦ v ++ v.map (· * w)) v).size = 2 ^ (pre ++ ws).length ∧
      ∀ i < 2 ^ (pre ++ ws).length, (ws.foldl (fun v w ↦ v ++ v.map (· * w)) v).getD i 0 =
        ∏ c ∈ range (pre ++ ws).length, if i.testBit c then (pre ++ ws).getD c 0 else 1
  | [], pre, v, hs, hv => by simp only [List.foldl_nil, List.append_nil]; exact ⟨hs, hv⟩
  | w :: ws, pre, v, hs, hv => by
    rw [List.foldl_cons, show pre ++ w :: ws = (pre ++ [w]) ++ ws by simp]
    refine tensorA_aux ws (pre ++ [w]) _ (by simp [hs, pow_succ, mul_two]) fun i hi ↦ ?_
    simp only [List.length_append, List.length_singleton] at hi ⊢
    rw [prod_range_succ]
    have hgetD : ∀ c ∈ range pre.length, (pre ++ [w]).getD c 0 = pre.getD c 0 := fun c hc ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (mem_range.mp hc)]
    rw [prod_congr rfl fun c hc ↦ by rw [hgetD c hc]]
    have hlast : (pre ++ [w]).getD pre.length 0 = w := by simp [List.getD_eq_getElem?_getD]
    rw [hlast]
    by_cases hlo : i < 2 ^ pre.length
    · rw [Nat.testBit_lt_two_pow hlo, ← array_getD_toList, Array.toList_append,
        List.getD_append _ _ _ _ (by simpa [hs] using hlo), array_getD_toList, hv i hlo]
      simp
    · have hi' : i - 2 ^ pre.length < 2 ^ pre.length := by rw [pow_succ] at hi; omega
      have hbits : ∀ c < pre.length, i.testBit c = (i - 2 ^ pre.length).testBit c := by
        intro c hc
        have : i = 2 ^ pre.length * 1 + (i - 2 ^ pre.length) := by omega
        conv_lhs => rw [this]
        rw [Nat.testBit_two_pow_mul_add _ hi']
        simp [hc]
      have htop : i.testBit pre.length = true := by
        have : i = 2 ^ pre.length * 1 + (i - 2 ^ pre.length) := by omega
        rw [this, Nat.testBit_two_pow_mul_add _ hi']
        simp
      rw [htop, ← array_getD_toList, Array.toList_append,
        List.getD_append_right _ _ _ _ (by simpa [hs] using hlo), Array.toList_map,
        Array.length_toList, hs]
      rw [show (0 : K) = 0 * w from (zero_mul w).symm, List.getD_map, zero_mul, array_getD_toList,
        hv _ hi']
      simp only [ite_true]
      congr 1
      refine prod_congr rfl fun c hc ↦ by rw [hbits c (mem_range.mp hc)]

theorem tensorA_spec (ws : List K) :
    (tensorA ws).size = 2 ^ ws.length ∧ ∀ i < 2 ^ ws.length,
      (tensorA ws).getD i 0 = ∏ c ∈ range ws.length, if i.testBit c then ws.getD c 0 else 1 := by
  have := tensorA_aux ws [] #[1] (by simp) fun i hi ↦ by
    obtain rfl : i = 0 := by simpa using hi
    simp
  simp only [List.nil_append] at this
  exact this

theorem queryTableA_aux {m : ℕ} (hm : m ≤ 64) : ∀ (L : List (E × ℕ)) (acc : Array E),
    acc.size = 2 ^ m →
    (L.foldl (fun acc wq ↦
        Array.zipWith (fun a b ↦ a + wq.1 * ofK b) acc
          (tensorA ((List.range m).map fun c ↦ hatAt c wq.2))) acc).size = 2 ^ m ∧
    ∀ i < 2 ^ m, (L.foldl (fun acc wq ↦
        Array.zipWith (fun a b ↦ a + wq.1 * ofK b) acc
          (tensorA ((List.range m).map fun c ↦ hatAt c wq.2))) acc).getD i 0 =
      acc.getD i 0 + (L.map fun wq ↦ wq.1 * ofK (novelAt i (K.ofBits wq.2))).sum
  | [], acc, hs => by simpa using hs
  | wq :: L, acc, hs => by
    obtain ⟨ht, hte⟩ := tensorA_spec ((List.range m).map fun c ↦ hatAt c wq.2)
    simp only [List.length_map, List.length_range] at ht hte
    have hsz : (Array.zipWith (fun a b ↦ a + wq.1 * ofK b) acc
        (tensorA ((List.range m).map fun c ↦ hatAt c wq.2))).size = 2 ^ m := by
      simp [hs, ht]
    obtain ⟨h1, h2⟩ := queryTableA_aux hm L _ hsz
    refine ⟨h1, fun i hi ↦ ?_⟩
    rw [List.foldl_cons, h2 i hi, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    have hia : i < acc.size := by rw [hs]; exact hi
    have hit : i < (tensorA ((List.range m).map fun c ↦ hatAt c wq.2)).size := by rw [ht]; exact hi
    have hz : ∀ (a : Array E) (b : Array K) (f : E → K → E) (i : ℕ), i < a.size → i < b.size →
        (Array.zipWith f a b).getD i 0 = f (a.getD i 0) (b.getD i 0) := by
      intro a b f i ha hb
      simp [ha, hb]
    have hprod : (∏ c ∈ range m, if i.testBit c then
        ((List.range m).map fun c ↦ hatAt c wq.2).getD c 0 else 1) =
        ∏ c ∈ range m, if i.testBit c then normVanishingAt c (K.ofBits wq.2) else 1 := by
      refine prod_congr rfl fun c hc ↦ ?_
      have hc' := mem_range.mp hc
      rw [List.getD_eq_getElem _ _ (by simpa using hc'), List.getElem_map, List.getElem_range,
        hatAt_eq (by omega)]
    rw [hz _ _ _ _ hia hit, hte i hi, hprod, ← novelAt_eq_prod hm hi]

theorem toList_queryTableA {m : ℕ} (hm : m ≤ 64) (queries : List ℕ) (queryWeights : List E) :
    (queryTableA m queries queryWeights).toList = queryTable m queries queryWeights := by
  obtain ⟨hs, hg⟩ := queryTableA_aux hm (List.zip queryWeights queries)
    (Array.replicate (2 ^ m) 0) (by simp)
  refine list_ext_getD (by simp [queryTableA, hs, queryTable]) fun i hi ↦ ?_
  have hi' : i < 2 ^ m := by simpa [queryTableA, hs] using hi
  rw [toList_getD_E, queryTableA, hg i hi', queryTable,
    List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range]
  simp [hi']

/-! ## The stack table -/

theorem toList_stackTableA {μ : ℕ} (q : Column μ) :
    (stackTableA μ q.values.toArray).toList = stackTable μ q := by
  refine list_ext_getD (by simp [stackTableA]) fun i hi ↦ ?_
  have hi' : i < 2 ^ μ := by simpa [stackTableA] using hi
  rw [toList_getD_E, stackTableA, getD_ofFn _ _ _ hi', stackTable,
    List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range]
  rfl

end
end LeanVM.Prover.Enc
