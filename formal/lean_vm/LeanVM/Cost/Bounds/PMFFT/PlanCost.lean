module

public import LeanVM.Cost.Bounds.PMFFT.Lib
public import LeanVM.Cost.Bounds.FieldLib

/-!
# Bounds of the PM decoder's FFT: the plan

`mkPlan j` (`mkPlanC`): the conversion table (`tableUpTo`, `O(j²)` products), the batched
inverses (one inversion), the stages' twiddles by subset sums (`spanTable`, `< 2^j` entries in
all, `j − i − 1` linearized evaluations at stage `i`), the powers and the two level tables.
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast
open Auto.LeanVM.Extraction.Fast.FFT

public section

variable (P : MachineProgram)

/-- `Σ_{t<n} s_{o+t}·a^(2^t)` (`evalLinFrom.c394`): `76` per term, `5` at the end. -/
theorem evalLinFrom_cost (hP : Includes P evalLinFrom.c394.costDeps) (s : Array K) :
    ∀ (n o : ℕ) (a : K), o + n < 2 ^ 64 →
      machineCost P evalLinFrom.c394.costIdx [encodeValue s, encodeValue n, encodeValue o,
        encodeValue a] ≤ 76 * n + 5 := by
  intro n
  induction n with
  | zero => intro o a _; rw [evalLinFrom.c394.costEq P hP]; cost_simp; omega
  | succ n ih =>
    intro o a h
    rw [evalLinFrom.c394.costEq P hP]
    have := ih (o + 1) (a * a) (by omega)
    cost_simp
    omega

/-- `W_{i+1}`'s coefficients from `W_i`'s (`linStep.c395`), `n` coefficients: at most
`95·(n + 1) + 17`. -/
theorem linStep_cost (hP : Includes P linStep.c395.costDeps) (s : Array K) (β : K)
    (hs : s.size < 2 ^ 40) :
    machineCost P linStep.c395.costIdx [encodeValue s, encodeValue β] ≤ 95 * (s.size + 1) + 17 := by
  rw [linStep.c395.costEq P hP]
  have hof := ofFnFrom_cost P (by includes) (n := s.size + 1) (by omega) _
    (.closure linStep.c395.lam0.costIdx [encodeValue s, encodeValue β])
    (fun t ↦ RunsApp.of_spec (linStep.c395.lam0.costSpec P (by includes) s β t)) 78
    (fun t ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have ht : t.val < 2 ^ 41 := by have := t.isLt; omega
      rw [linStep.c395.lam0.costEq P (by includes)]
      cost_simp
      split_ifs <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length]
  cost_simp
  simp only [Nat.sub_zero] at hof
  omega

theorem tableUpTo_head {k : ℕ} (hk : 0 < k) :
    FFT.tableUpTo k = FFT.linData (k - 1) :: FFT.tableUpTo (k - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk
  simpa using FFT.tableUpTo_succ k

theorem tableUpTo_size_le {j : ℕ} : ∀ d ∈ FFT.tableUpTo j, d.1.size ≤ j := by
  intro d hd
  rw [FFT.tableUpTo_eq] at hd
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
  rw [(FFT.linData_spec i).1]
  simp at hi
  omega

/-- **The conversion table** (`tableUpTo.c392`): at most `86·k² + 150·k + 5`. -/
theorem tableUpTo_cost (hP : Includes P tableUpTo.c392.costDeps) :
    ∀ k, k ≤ 40 → machineCost P tableUpTo.c392.costIdx [encodeValue k] ≤ 86 * (k * k) + 150 * k + 5 := by
  intro k
  induction k with
  | zero => intro _; rw [tableUpTo.c392.costEq P hP]; simp
  | succ k ih =>
    intro hk
    rw [tableUpTo.c392.costEq P hP]
    have h1 := ih (by omega)
    cost_simp
    cases k with
    | zero =>
      simp only [show FFT.tableUpTo 0 = [] from rfl]
      rw [linData.c393.costEq P (by includes)]
      have := evalLinFrom_cost P (by includes) #[1] 1 0 (K.ofBits 1) (by norm_num)
      cost_simp
      simp only [Array.size_singleton] at this ⊢
      omega
    | succ k =>
      rw [tableUpTo_head (by omega)]
      simp only [Nat.add_sub_cancel]
      have hsz := (FFT.linData_spec k).1
      have h2 := linStep_cost P (by includes) (FFT.linData k).1 (FFT.linData k).2 (by omega)
      have hsz' : (FFT.linStep (FFT.linData k).1 (FFT.linData k).2).size = k + 2 := by
        simp [FFT.linStep, hsz]
      have h3 := evalLinFrom_cost P (by includes) (FFT.linStep (FFT.linData k).1 (FFT.linData k).2)
        (k + 2) 0 (K.ofBits (2 ^ (k + 1))) (by omega)
      rw [hsz']
      rw [hsz] at h2
      cost_simp
      rw [limbs_shift (by omega), limbs_two_pow (by omega)]
      nlinarith

/-- **Batched inversion** (`batchInvAux.c397`): `104` per element, one inversion. -/
theorem batchInvAux_cost (hP : Includes P batchInvAux.c397.costDeps) :
    ∀ (l : List K) (b : K), machineCost P batchInvAux.c397.costIdx [encodeValue l, encodeValue b] ≤
      104 * l.length + 2831 := by
  intro l
  induction l with
  | nil =>
    intro b
    rw [batchInvAux.c397.costEq P hP]
    have := invK_cost P (by includes) b
    dsimp only
    omega
  | cons x l ih =>
    intro b
    rw [batchInvAux.c397.costEq P hP]
    have := ih (b * x)
    simp only [List.length_cons]
    omega

/-- **Subset sums by doubling** (`spanTable.c402`), the closure at most `C`: at most
`28·2^n + (C + 36)·n + 11`. -/
theorem spanTable_cost (hP : Includes P spanTable.c402.costDeps) (c : ℕ → K) (cVal : MachineValue)
    (hc : ∀ a : ℕ, RunsApp P cVal [encodeValue a] (encodeValue (c a))) (C : ℕ)
    : ∀ n, n ≤ 40 → (∀ a : ℕ, a < n → appCost P cVal [encodeValue a] ≤ C) →
      machineCost P spanTable.c402.costIdx [cVal, encodeValue n] ≤ 28 * 2 ^ n + (C + 36) * n + 11 := by
  intro n
  induction n with
  | zero => intro _ _; rw [spanTable.c402.costEq P hP c cVal hc]; simp
  | succ k ih =>
    intro hk hC
    rw [spanTable.c402.costEq P hP c cVal hc]
    have h1 := ih (by omega) fun a ha ↦ hC a (by omega)
    have h2 := hC k (by omega)
    have hN : 2 ^ k ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hof := ofFnFrom_cost P (by includes) (n := 2 ^ k) (by omega) _
      (.closure spanTable.c402.lam0.costIdx [encodeValue k, encodeValue (FFT.spanTable c k), encodeValue (c k)])
      (fun w ↦ RunsApp.of_spec (spanTable.c402.lam0.costSpec P (by includes) k _ _ w)) 9
      (fun w ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [spanTable.c402.lam0.costEq P (by includes) k (FFT.spanTable c k) (c k) w]) 0
        (Nat.zero_le _)
    cost_simp
    rw [ofFnFrom_length, FFT.size_spanTable, Array.size_ofFn]
    simp only [Nat.sub_zero] at hof
    -- `cost_simp` reads the closure's index as its literal
    rw [show spanTable.c402.lam0.costIdx = (spanTable.c402.lam0.costIdx : ℕ) from rfl] at hof
    unfold spanTable.c402.lam0.costIdx at hof
    rw [pow_succ]
    nlinarith

/-- **Stage `i`'s twiddles of size `2^j`** (`stageTwiddles.c401`), `d.1` of at most `j`
coefficients: at most `28·2^(j−i−1) + (76·j + 91)·(j − i − 1) + 22`. -/
theorem stageTwiddles_cost (hP : Includes P stageTwiddles.c401.costDeps) {i j : ℕ} (hij : i < j)
    (hj : j ≤ 40) (d : Array K × K) (hd : d.1.size ≤ j) :
    machineCost P stageTwiddles.c401.costIdx [encodeValue j, encodeValue i, encodeValue d] ≤
      28 * 2 ^ (j - (i + 1)) + (76 * j + 91) * (j - (i + 1)) + 22 := by
  rw [stageTwiddles.c401.costEq P hP]
  have hs := spanTable_cost P (by includes) _
    (.closure stageTwiddles.c401.lam0.costIdx [encodeValue i, encodeValue d])
    (fun b ↦ RunsApp.of_spec (stageTwiddles.c401.lam0.costSpec P (by includes) i d b)) (76 * j + 55)
    (j - (i + 1)) (by omega) (fun b hb ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [stageTwiddles.c401.lam0.costEq P (by includes)]
      have := evalLinFrom_cost P (by includes) d.1 d.1.size 0
        (K.ofBits (2 ^ b * 2 ^ (i + 1))) (by omega)
      have hprod : limbCount (2 ^ b * 2 ^ (i + 1)) = 1 := by
        rw [← pow_add]; exact limbs_two_pow (by omega)
      rw [limbs_shift (by omega), limbs_shift (by omega), limbs_two_pow (by omega),
        limbs_two_pow (by omega), hprod]
      cost_simp
      nlinarith)
  have e : 76 * j + 55 + 36 = 76 * j + 91 := by ring
  rw [e] at hs
  cost_simp
  omega

theorem sum_two_pow_reflect (j : ℕ) : ∑ i ∈ Finset.range j, 2 ^ (j - (i + 1)) = 2 ^ j - 1 := by
  rw [Finset.sum_congr rfl fun i _ ↦ by rw [show j - (i + 1) = j - 1 - i by omega],
    Finset.sum_range_reflect (fun i ↦ 2 ^ i) j, Nat.geomSum_eq (le_refl 2)]
  simp

theorem tabInv_eq {j : ℕ} (hj : j ≤ 64) :
    List.zipWith (fun d b ↦ (d.1, b)) (FFT.tableUpTo j)
      (FFT.batchInv ((FFT.tableUpTo j).map fun d ↦ d.2)) = FFT.tableInvUpTo j := by
  rw [FFT.batchInv_eq _ (FFT.tableUpTo_ne_zero hj), FFT.zipWith_map_self, FFT.tableInvUpTo]

theorem tabInv_getD_size_le {j : ℕ} (k : ℕ) :
    ((FFT.tableInvUpTo j).getD k (#[], 0)).1.size ≤ j := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (FFT.tableInvUpTo j)[k]? with
  | none => simp
  | some x =>
    have hx := List.mem_of_getElem? h
    rw [FFT.tableInvUpTo] at hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    exact tableUpTo_size_le d hd

/-- **The plan of size `2^j`** (`mkPlanC`), `j ≤ 40`: at most
`28·2^j + 76·j³ + 276·j² + 468·j + 2934`. -/
theorem mkPlanC_cost (hP : Includes P mkPlanC.costDeps) {j : ℕ} (hj : j ≤ 40) :
    machineCost P mkPlanC.costIdx [encodeValue j] ≤
      28 * 2 ^ j + 76 * (j * j * j) + 276 * (j * j) + 468 * j + 2934 := by
  rw [mkPlanC.costEq P hP]
  have hlen : (FFT.tableUpTo j).length = j := FFT.length_tableUpTo j
  have hA := tableUpTo_cost P (by includes) j hj
  have hB := map_cost P (by includes) _ (.closure mkPlanC.lam0.costIdx [])
    (fun d ↦ RunsApp.of_spec (mkPlanC.lam0.costSpec P (by includes) d)) 2 (FFT.tableUpTo j)
    (fun d _ ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]
      rw [mkPlanC.lam0.costEq P (by includes)])
  have hC := batchInvAux_cost P (by includes) ((FFT.tableUpTo j).map fun d ↦ d.2) 1
  have hD := listZipWith_le P (by includes) _ (.closure mkPlanC.lam1.costIdx [])
    (fun d b ↦ RunsApp.of_spec (mkPlanC.lam1.costSpec P (by includes) d b)) 6 (FFT.tableUpTo j)
    (FFT.batchInv ((FFT.tableUpTo j).map fun d ↦ d.2))
    (fun d _ b _ ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]
      rw [mkPlanC.lam1.costEq P (by includes)])
  rw [tabInv_eq (by omega)]
  have hbl : (FFT.batchInv ((FFT.tableUpTo j).map fun d ↦ d.2)).length = j := by
    rw [FFT.batchInv_eq _ (FFT.tableUpTo_ne_zero (by omega))]; simp [hlen]
  have hNle : 2 ^ j ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hj
  have hE := ofFnFrom_cost_sum0 P (by includes) (n := j) (by omega) _
    (.closure mkPlanC.lam2.costIdx [encodeValue j, encodeValue (FFT.tableInvUpTo j),
      encodeValue (FFT.batchInv ((FFT.tableUpTo j).map fun d ↦ d.2)), encodeValue (FFT.tableUpTo j)])
    (fun i ↦ RunsApp.of_spec (by
      have := mkPlanC.lam2.costSpec P (by includes) j (FFT.tableInvUpTo j)
        (FFT.batchInv ((FFT.tableUpTo j).map fun d ↦ d.2)) (FFT.tableUpTo j) i
      exact this))
    (fun i ↦ 28 * 2 ^ (j - (i + 1)) + ((76 * j + 91) * j + 15 * j + 44))
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mkPlanC.lam2.costEq P (by includes)]
      have h1 := getD_cost_idx P (by includes) (FFT.tableInvUpTo j) (j - 1 - i.val) (#[], 0)
        (by omega)
      have h2 := stageTwiddles_cost P (by includes) i.isLt hj _ (tabInv_getD_size_le (j - 1 - i.val))
      have h3 : (76 * j + 91) * (j - (i.val + 1)) ≤ (76 * j + 91) * j :=
        Nat.mul_le_mul_left _ (by omega)
      cost_simp
      omega)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_two_pow_reflect,
    Finset.sum_const, Finset.card_range, smul_eq_mul] at hE
  have hG := ofFnFrom_cost P (by includes) (n := j) (by omega) _
    (.closure mkPlanC.lam3.costIdx [encodeValue j])
    (fun t ↦ RunsApp.of_spec (mkPlanC.lam3.costSpec P (by includes) j t)) 4
    (fun t ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mkPlanC.lam3.costEq P (by includes), limbs_shift (by omega)]
      cost_simp
      omega) 0 (Nat.zero_le _)
  have hH := ofFnFrom_cost P (by includes) (n := j) (by omega) _
    (.closure mkPlanC.lam4.costIdx [encodeValue j, encodeValue (FFT.tableUpTo j)])
    (fun i ↦ RunsApp.of_spec (mkPlanC.lam4.costSpec P (by includes) j _ i)) (15 * j + 17)
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mkPlanC.lam4.costEq P (by includes)]
      have h1 := getD_cost_idx P (by includes) (FFT.tableUpTo j) (j - 1 - i.val) (#[], 0) (by omega)
      cost_simp
      omega) 0 (Nat.zero_le _)
  have hI := ofFnFrom_cost P (by includes) (n := j) (by omega) _
    (.closure mkPlanC.lam5.costIdx [encodeValue j, encodeValue (FFT.tableInvUpTo j),
      encodeValue (FFT.batchInv ((FFT.tableUpTo j).map fun d ↦ d.2)), encodeValue (FFT.tableUpTo j)])
    (fun i ↦ RunsApp.of_spec (mkPlanC.lam5.costSpec P (by includes) j _ _ _ i)) (69 * j + 41)
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mkPlanC.lam5.costEq P (by includes)]
      have h1 := getD_cost_idx P (by includes) (FFT.tableInvUpTo j) (j - 1 - i.val) (#[], 0) (by omega)
      have h2 := ofFnFrom_cost P (by includes) (n := i.val) (by omega) _
        (.closure mkPlanC.lam5.lam0.costIdx [encodeValue j, encodeValue i,
          encodeValue ((FFT.tableInvUpTo j).getD (j - 1 - i.val) (#[], 0))])
        (fun t ↦ RunsApp.of_spec (mkPlanC.lam5.lam0.costSpec P (by includes) j i _ t)) 37
        (fun t ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [mkPlanC.lam5.lam0.costEq P (by includes)]) 0 (Nat.zero_le _)
      rw [ofFnFrom_length]
      have hi := i.isLt
      cost_simp
      simp only [Nat.sub_zero] at h2
      omega) 0 (Nat.zero_le _)
  simp only [ofFnFrom_length]
  simp only [List.length_map, hlen] at hB hC
  rw [hlen, hbl] at hD
  have hsum : ∑ x ∈ Finset.range j, 16 = 16 * j := by simp [mul_comm]
  rw [hsum] at hE
  simp only [Nat.sub_zero, min_self] at hD hG hH hI
  have e1 : (15 * j + 17 + 16) * j = 15 * (j * j) + 33 * j := by ring
  have e2 : (69 * j + 41 + 16) * j = 69 * (j * j) + 57 * j := by ring
  have e3 : j * ((76 * j + 91) * j + 15 * j + 44) =
      76 * (j * j * j) + 106 * (j * j) + 44 * j := by ring
  have e4 : 2 ^ j - 1 ≤ 2 ^ j := Nat.sub_le _ _
  omega

end

end LeanVM.Cost.Bounds.PMFFT
