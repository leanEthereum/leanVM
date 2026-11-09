module

public import LeanVM.Cost.Bounds.PMFFT.Lib

/-!
# Bounds of the PM decoder's FFT: the conversions monomial ↔ novel basis

`toNovelInPlace` and `fromNovelInPlace` by the plan of size `N = 2^j` (`j ≤ 36`), level by level:
level `i` is `toLevel` (the quotients `toQuot`, `N/2` entries, then the output, `N`) or
`fromLevel` (`N` entries); an entry's sparse sum runs at most `i` terms (`sumAsc`, `sumDesc`,
one product each). Half the entries of each pass run no sum (`sum_mod_block`), so level `i` costs
`O(N·i)`, the conversion `O(N·j²)`.
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast
open Auto.LeanVM.Extraction.Fast.FFT

public section

variable (P : MachineProgram)

/-! ## The sparse sums -/

theorem sumAsc_cost (hP : Includes P sumAsc.c375.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 64) (f : ℕ → K) (fVal : MachineValue)
    (hf : ∀ a : ℕ, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ)
    (hB : ∀ a : ℕ, appCost P fVal [encodeValue a] ≤ B) (x : ℕ) (hx : x < 2 ^ 64) :
    ∀ n a, a + n < 2 ^ 64 →
      machineCost P sumAsc.c375.costIdx [encodeValue pw, fVal, encodeValue x, encodeValue a,
        encodeValue n] ≤ (B + 29) * n + 5 := by
  intro n
  induction n with
  | zero => intro a _; rw [sumAsc.c375.costEq P hP pw f fVal hf]; simp
  | succ n ih =>
    intro a ha
    rw [sumAsc.c375.costEq P hP pw f fVal hf]
    have h1 := hpw a
    have h2 := hB a
    have h3 := ih (a + 1) (by omega)
    cost_simp
    split <;> nlinarith

theorem sumDesc_cost (hP : Includes P sumDesc.c372.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 64) (f : ℕ → K) (fVal : MachineValue)
    (hf : ∀ a : ℕ, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ)
    (hB : ∀ a : ℕ, appCost P fVal [encodeValue a] ≤ B) (x : ℕ) (hx : x < 2 ^ 64) :
    ∀ n, n < 2 ^ 64 →
      machineCost P sumDesc.c372.costIdx [encodeValue pw, fVal, encodeValue x, encodeValue n] ≤
        (B + 24) * n + 5 := by
  intro n
  induction n with
  | zero => intro _; rw [sumDesc.c372.costEq_zero P hP pw f fVal hf]; omega
  | succ n ih =>
    intro hn
    rw [sumDesc.c372.costEq_succ P hP pw f fVal hf]
    have h1 := hpw n
    have h2 := hB n
    have h3 := ih (by omega)
    cost_simp
    split <;> nlinarith

/-! ## Monomial → novel: one level -/

/-- The quotient pass's product (`toQuot.c370.lam0.lam0`): at most `44`. -/
theorem toQuotTerm_cost (hP : Includes P toQuot.c370.lam0.lam0.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) (s B : Array K) (c1 c0 c2 t : ℕ) (h1 : c1 < 2 ^ 42)
    (h0 : c0 < 2 ^ 42) (h2 : c2 < 2 ^ 42) :
    machineCost P toQuot.c370.lam0.lam0.costIdx [encodeValue pw, encodeValue s, encodeValue B,
      encodeValue c1, encodeValue c0, encodeValue c2, encodeValue t] ≤ 44 := by
  rw [toQuot.c370.lam0.lam0.costEq P hP]
  have := hpw t
  cost_simp
  omega

/-- The output pass's product (`toLevel.c369.lam0.lam0`, also `fromLevel`'s): at most `42`. -/
theorem levelTerm_cost (hP : Includes P toLevel.c369.lam0.lam0.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) (c1 c2 : Array K) (c0 c3 t : ℕ) (h0 : c0 < 2 ^ 42)
    (h3 : c3 < 2 ^ 42) :
    machineCost P toLevel.c369.lam0.lam0.costIdx [encodeValue pw, encodeValue c1, encodeValue c2,
      encodeValue c0, encodeValue c3, encodeValue t] ≤ 42 := by
  rw [toLevel.c369.lam0.lam0.costEq P hP]
  have := hpw t
  cost_simp
  omega

/-- A quotient entry (`toQuot.c370.lam0`): `74·i + 45` if it runs the sum (`m mod H < H/2`),
`22` otherwise. -/
theorem toQuotEntry_cost (hP : Includes P toQuot.c370.lam0.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) (N i : ℕ) (hN : N ≤ 2 ^ 40) (hi : i ≤ 40) (s B : Array K)
    (H : ℕ) (hH : H ≤ 2 ^ 40) (hH0 : 0 < H) (m : Fin (N / 2)) :
    machineCost P toQuot.c370.lam0.costIdx [encodeValue pw, encodeValue N, encodeValue i,
      encodeValue s, encodeValue B, encodeValue (H / 2), encodeValue (2 * H), encodeValue H,
      encodeValue m] ≤ if m.val % H < H / 2 then 74 * i + 45 else 22 := by
  rw [toQuot.c370.lam0.costEq P hP]
  have hm : m.val < 2 ^ 40 := by have := m.isLt; omega
  have hmod : m.val % H < H := Nat.mod_lt _ hH0
  have hmod' : m.val % H ≤ m.val := Nat.mod_le _ _
  have hsd := sumDesc_cost P (by includes) pw (fun t ↦ (hpw t).trans (by norm_num))
    (fun t ↦ s.getD t 0 * B.getD (2 * (m.val - m.val % H) + 2 * H + m.val % H - pw.getD t 0) 0)
    (.closure toQuot.c370.lam0.lam0.costIdx [encodeValue pw, encodeValue s, encodeValue B,
      encodeValue (2 * H), encodeValue (2 * (m.val - m.val % H)), encodeValue (m.val % H)])
    (fun a ↦ RunsApp.of_spec (toQuot.c370.lam0.lam0.costSpec P (by includes) pw s B _ _ _ a)) 50
    (fun a ↦ by
      rw [appCost_fn]
      have := toQuotTerm_cost P (by includes) pw hpw s B (2 * H) (2 * (m.val - m.val % H)) (m.val % H) a
        (by omega) (by omega) (by omega)
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      omega)
    (m.val % H) (by omega) i (by omega)
  cost_simp
  split_ifs <;> omega

/-- The sum of a two-class price over the blocks of a pass: `N/(2H)`... in general `M` blocks of
`H` entries, the first `H/2` of each at `a`, the rest at `b`. -/
theorem block_sum_le {H M a b : ℕ} :
    ∑ m ∈ Finset.range (H * M), ((if m % H < H / 2 then a else b) + 16) =
      M * ((H / 2) * a + (H - H / 2) * b + 16 * H) := by
  rw [sum_mod_block (fun x ↦ (if x < H / 2 then a else b) + 16), Finset.sum_add_distrib,
    sum_range_ite_lt _ _ _ _ (Nat.div_le_self _ _)]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

theorem two_pow_split {i j : ℕ} (h : i < j) : 2 ^ j = 2 * (2 ^ i * 2 ^ (j - i - 1)) := by
  rw [← pow_add, ← pow_succ']; congr 1; omega

/-- **The quotient pass** of level `i` over `N = 2^j` (`toQuot.c370`): at most
`19·N·i + 30·N + 41`. -/
theorem toQuot_cost (hP : Includes P toQuot.c370.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) {i j : ℕ} (hij : i < j) (hj : j ≤ 40)
    (hH : pw.getD i 0 = 2 ^ i) (s B : Array K) :
    machineCost P toQuot.c370.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue i,
      encodeValue s, encodeValue B] ≤ 19 * (2 ^ j * i) + 30 * 2 ^ j + 41 := by
  rw [toQuot.c370.costEq P hP, hH]
  have hsplit := two_pow_split hij
  set H := 2 ^ i with hHdef
  set M := 2 ^ (j - i - 1) with hMdef
  have hHpos : 0 < H := Nat.two_pow_pos i
  have hHle : H ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNle : 2 ^ j ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hj
  have hhalf : 2 ^ j / 2 = H * M := by omega
  have hof := ofFnFrom_cost_sum0 P (by includes) (n := 2 ^ j / 2) (by omega) _
    (.closure toQuot.c370.lam0.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue i,
      encodeValue s, encodeValue B, encodeValue (H / 2), encodeValue (2 * H), encodeValue H])
    (fun m ↦ RunsApp.of_spec (toQuot.c370.lam0.costSpec P (by includes) pw (2 ^ j) i s B _ _ _ m))
    (fun m ↦ if m % H < H / 2 then 74 * i + 53 else 30)
    (fun m ↦ by
      rw [appCost_fn]
      have := toQuotEntry_cost P (by includes) pw hpw (2 ^ j) i hNle (by omega) s B H hHle hHpos m
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      split_ifs at this ⊢ <;> omega)
  rw [show Finset.range (2 ^ j / 2) = Finset.range (H * M) by rw [hhalf], block_sum_le] at hof
  rw [ofFnFrom_length]
  cost_simp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have e1 : H = 1 := by simp [hHdef]
    have eR : M * ((H / 2) * (74 * 0 + 53) + (H - H / 2) * 30 + 16 * H) = 46 * M := by
      rw [e1]; ring
    rw [eR] at hof
    rw [e1] at hsplit hhalf
    simp only [Nat.mul_zero]
    omega
  · obtain ⟨h, hh⟩ : ∃ h, H = 2 * h := ⟨2 ^ (i - 1), by
      rw [hHdef, ← pow_succ']; congr 1; omega⟩
    have hdiv : H / 2 = h := by omega
    have eR : M * ((H / 2) * (74 * i + 53) + (H - H / 2) * 30 + 16 * H) =
        74 * (h * M * i) + 115 * (h * M) := by
      rw [hdiv, show H - h = h by omega, hh]; ring
    rw [eR] at hof
    have e2 : 2 ^ j * i = 4 * (h * M * i) := by rw [hsplit, hh]; ring
    have e3 : 2 ^ j = 4 * (h * M) := by rw [hsplit, hh]; ring
    omega

/-- An output entry of level `i` (`toLevel.c369.lam0`): `76·i + 40` in the block's low half (the
remainder's sum), `50` in its high half (`β·q`). -/
theorem toLevelEntry_cost (hP : Includes P toLevel.c369.lam0.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) (N i : ℕ) (hN : N ≤ 2 ^ 40) (hi : i ≤ 40) (B Q s : Array K)
    (β : K) (H : ℕ) (hH : H ≤ 2 ^ 40) (hH0 : 0 < H) (p : Fin N) :
    machineCost P toLevel.c369.lam0.costIdx [encodeValue pw, encodeValue N, encodeValue i,
      encodeValue B, encodeValue (2 * H), encodeValue Q, encodeValue s, encodeValue H,
      encodeValue β, encodeValue p] ≤ if p.val % (2 * H) < 2 * H / 2 then 76 * i + 40 else 50 := by
  rw [toLevel.c369.lam0.costEq P hP]
  have hp : p.val < 2 ^ 40 := by have := p.isLt; omega
  have hmod : p.val % (2 * H) < 2 * H := Nat.mod_lt _ (by omega)
  have hmod' : p.val % (2 * H) ≤ p.val := Nat.mod_le _ _
  have hsa := sumAsc_cost P (by includes) pw (fun t ↦ (hpw t).trans (by norm_num))
    (fun t ↦ s.getD t 0 * Q.getD ((p.val - p.val % (2 * H)) / 2 + p.val % (2 * H) - pw.getD t 0) 0)
    (.closure toLevel.c369.lam0.lam0.costIdx [encodeValue pw, encodeValue Q, encodeValue s,
      encodeValue ((p.val - p.val % (2 * H)) / 2), encodeValue (p.val % (2 * H))])
    (fun a ↦ RunsApp.of_spec (toLevel.c369.lam0.lam0.costSpec P (by includes) pw Q s _ _ a)) 47
    (fun a ↦ by
      rw [appCost_fn]
      have := levelTerm_cost P (by includes) pw hpw Q s ((p.val - p.val % (2 * H)) / 2) (p.val % (2 * H)) a
        (by omega) (by omega)
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      omega)
    (p.val % (2 * H)) (by omega) i 0 (by omega)
  rw [show 2 * H / 2 = H by omega]
  cost_simp
  split_ifs <;> omega

/-- **Level `i` of monomial → novel** over `N = 2^j` (`toLevel.c369`): at most
`57·N·i + 101·N + 91`. -/
theorem toLevel_cost (hP : Includes P toLevel.c369.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) {i j : ℕ} (hij : i < j) (hj : j ≤ 40)
    (hH : pw.getD i 0 = 2 ^ i) (d : Array K × K) (B : Array K) :
    machineCost P toLevel.c369.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue i,
      encodeValue d, encodeValue B] ≤ 57 * (2 ^ j * i) + 101 * 2 ^ j + 91 := by
  rw [toLevel.c369.costEq P hP]
  have hq := toQuot_cost P (by includes) pw hpw hij hj hH d.1 B
  rw [hH]
  have hsplit := two_pow_split hij
  set H := 2 ^ i with hHdef
  set M := 2 ^ (j - i - 1) with hMdef
  have hHpos : 0 < H := Nat.two_pow_pos i
  have hHle : H ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNle : 2 ^ j ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hj
  have hof := ofFnFrom_cost_sum0 P (by includes) (n := 2 ^ j) (by omega) _
    (.closure toLevel.c369.lam0.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue i,
      encodeValue B, encodeValue (2 * H), encodeValue (LeanVM.Extraction.Fast.FFT.toQuot pw (2 ^ j) i d.1 B),
      encodeValue d.1, encodeValue H, encodeValue d.2])
    (fun p ↦ RunsApp.of_spec (toLevel.c369.lam0.costSpec P (by includes) pw (2 ^ j) i B _ _ _ _ _ p))
    (fun p ↦ if p % (2 * H) < 2 * H / 2 then 76 * i + 49 else 59)
    (fun p ↦ by
      rw [appCost_fn]
      have := toLevelEntry_cost P (by includes) pw hpw (2 ^ j) i hNle (by omega) B
        (LeanVM.Extraction.Fast.FFT.toQuot pw (2 ^ j) i d.1 B) d.1 d.2 H hHle
        hHpos p
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      split_ifs at this ⊢ <;> omega)
  rw [show Finset.range (2 ^ j) = Finset.range (2 * H * M) by rw [hsplit]; ring_nf,
    block_sum_le] at hof
  have eR : M * ((2 * H / 2) * (76 * i + 49) + (2 * H - 2 * H / 2) * 59 + 16 * (2 * H)) =
      76 * (H * M * i) + 140 * (H * M) := by
    rw [show 2 * H / 2 = H by omega, show 2 * H - H = H by omega]; ring
  rw [eR] at hof
  have e2 : 2 ^ j * i = 2 * (H * M * i) := by rw [hsplit]; ring
  have e3 : 2 ^ j = 2 * (H * M) := by rw [hsplit]
  rw [ofFnFrom_length]
  cost_simp
  omega

/-! ## Monomial → novel: the levels -/

theorem sum_range_level (a b L : ℕ) :
    ∑ i ∈ Finset.range L, (a * i + b) ≤ a * (L * L) / 2 + b * L := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h := Finset.sum_range_id_mul_two L
  have : a * (∑ i ∈ Finset.range L, i) * 2 ≤ a * (L * L) := by
    rw [mul_assoc, h]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have : L * b = b * L := Nat.mul_comm _ _
  omega

/-- **Levels `L − 1, …, 0` of monomial → novel** over `N = 2^j` (`toLevels.c367`): at most
`29·N·L² + 101·N·L + 134·L + 20`. -/
theorem toLevels_cost (hP : Includes P toLevels.c367.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) {j L : ℕ} (hL : L ≤ j) (hj : j ≤ 40)
    (hH : ∀ i < L, pw.getD i 0 = 2 ^ i) (D : Array (Array K × K)) (B : Array K) :
    machineCost P toLevels.c367.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue D,
      encodeValue L, encodeValue B] ≤
      29 * (2 ^ j * (L * L)) + 101 * (2 ^ j * L) + 134 * L + 20 := by
  rw [toLevels.c367.costEq P hP]
  have hr := rangeLoop_cost P (by includes) L [] (by omega)
  have hf := foldr_cost_sum P (by includes) _
    (.closure toLevels.c367.lam0.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue D])
    (fun i b ↦ RunsApp.of_spec (toLevels.c367.lam0.costSpec P (by includes) pw (2 ^ j) D i b))
    (fun i ↦ 57 * 2 ^ j * i + (101 * 2 ^ j + 108)) B (List.range L)
    (fun i hi b ↦ by
      have hi := List.mem_range.mp hi
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [toLevels.c367.lam0.costEq P (by includes)]
      have := toLevel_cost P (by includes) pw hpw (by omega : i < j) hj (hH i hi) (D.getD i (#[], 0)) b
      rw [mul_assoc]
      omega)
  rw [sum_map_range] at hf
  have hs := sum_range_level (57 * 2 ^ j) (101 * 2 ^ j + 108 + 11) L
  rw [Finset.sum_congr rfl fun i _ ↦ show 57 * 2 ^ j * i + (101 * 2 ^ j + 108) + 11 =
    57 * 2 ^ j * i + (101 * 2 ^ j + 108 + 11) by ring] at hf
  have e1 : 57 * 2 ^ j * (L * L) / 2 ≤ 29 * (2 ^ j * (L * L)) := by
    have : 57 * 2 ^ j * (L * L) = 57 * (2 ^ j * (L * L)) := by ring
    exact Nat.div_le_of_le_mul (by omega)
  have e2 : (101 * 2 ^ j + 108 + 11) * L = 101 * (2 ^ j * L) + 119 * L := by ring
  omega

theorem mkPlan_pows_lt {j : ℕ} (hj : j ≤ 40) (t : ℕ) : (FFT.mkPlan j).pows.getD t 0 < 2 ^ 40 := by
  by_cases ht : t < j
  · rw [FFT.mkPlan_pows ht]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · simp [FFT.mkPlan, Array.getD_eq_getD_getElem?, ht]

/-- **Monomial → novel by the plan of size `N = 2^j`** (`toNovelInPlaceC`), `j ≤ 40`: at most
`29·N·j² + 101·N·j + 23·N + 134·j + 47`. -/
theorem toNovelInPlaceC_cost (hP : Includes P toNovelInPlaceC.costDeps) {j : ℕ} (hj : j ≤ 40)
    (a : Array K) :
    machineCost P toNovelInPlaceC.costIdx [encodeValue (FFT.mkPlan j), encodeValue a] ≤
      29 * (2 ^ j * (j * j)) + 101 * (2 ^ j * j) + 23 * 2 ^ j + 134 * j + 47 := by
  rw [toNovelInPlaceC.costEq P hP, FFT.mkPlan_log]
  have hNle : 2 ^ j ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hj
  have hof := ofFnFrom_cost P (by includes) (n := 2 ^ j) (by omega) _
    (.closure toNovelInPlaceC.lam0.costIdx [encodeValue (FFT.mkPlan j), encodeValue a])
    (fun p ↦ RunsApp.of_spec (by
      have := toNovelInPlaceC.lam0.costSpec P (by includes) (FFT.mkPlan j) a
      rw [FFT.mkPlan_log] at this
      exact this p)) 6
    (fun p ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have := toNovelInPlaceC.lam0.costEq P (by includes) (FFT.mkPlan j) a
      rw [FFT.mkPlan_log] at this
      rw [this p]) 0 (Nat.zero_le _)
  have hl := toLevels_cost P (by includes) _ (mkPlan_pows_lt hj) le_rfl hj
    (fun i hi ↦ FFT.mkPlan_pows hi) (FFT.mkPlan j).convFwd (Array.ofFn fun p : Fin (2 ^ j) ↦ a.getD p 0)
  rw [ofFnFrom_length, limbs_shift (by omega), limbs_of_lt (by omega : j < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  omega

/-! ## Novel → monomial -/

/-- An entry of level `i` of novel → monomial (`fromLevel.c381.lam0`): `76·i + 40` in the block's
low half, `71·i + 69` in its high half. -/
theorem fromLevelEntry_cost (hP : Includes P fromLevel.c381.lam0.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) (N i : ℕ) (hN : N ≤ 2 ^ 40) (hi : i ≤ 40) (B s : Array K)
    (β : K) (H : ℕ) (hH : H ≤ 2 ^ 40) (hH0 : 0 < H) (p : Fin N) :
    machineCost P fromLevel.c381.lam0.costIdx [encodeValue pw, encodeValue N, encodeValue i,
      encodeValue B, encodeValue (2 * H), encodeValue s, encodeValue H, encodeValue β,
      encodeValue p] ≤ if p.val % (2 * H) < 2 * H / 2 then 76 * i + 40 else 71 * i + 69 := by
  rw [fromLevel.c381.lam0.costEq P hP]
  have hp : p.val < 2 ^ 40 := by have := p.isLt; omega
  have hmod : p.val % (2 * H) < 2 * H := Nat.mod_lt _ (by omega)
  have hmod' : p.val % (2 * H) ≤ p.val := Nat.mod_le _ _
  have hterm : ∀ a : ℕ, appCost P (.closure toLevel.c369.lam0.lam0.costIdx [encodeValue pw,
      encodeValue B, encodeValue s, encodeValue (p.val - p.val % (2 * H) + H),
      encodeValue (p.val % (2 * H))]) [encodeValue a] ≤ 47 := fun a ↦ by
    rw [appCost_fn]
    have := levelTerm_cost P (by includes) pw hpw B s (p.val - p.val % (2 * H) + H) (p.val % (2 * H)) a
      (by omega) (by omega)
    simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    omega
  have hrun : ∀ a : ℕ, RunsApp P (.closure toLevel.c369.lam0.lam0.costIdx [encodeValue pw,
      encodeValue B, encodeValue s, encodeValue (p.val - p.val % (2 * H) + H),
      encodeValue (p.val % (2 * H))]) [encodeValue a] (encodeValue (s.getD a 0 *
        B.getD (p.val - p.val % (2 * H) + H + p.val % (2 * H) - pw.getD a 0) 0)) := fun a ↦
    RunsApp.of_spec (toLevel.c369.lam0.lam0.costSpec P (by includes) pw B s _ _ a)
  have hsa := sumAsc_cost P (by includes) pw (fun t ↦ (hpw t).trans (by norm_num)) _ _ hrun 47
    hterm (p.val % (2 * H)) (by omega) i 0 (by omega)
  have hsd := sumDesc_cost P (by includes) pw (fun t ↦ (hpw t).trans (by norm_num)) _ _ hrun 47
    hterm (p.val % (2 * H) - H) (by omega) i (by omega)
  rw [show 2 * H / 2 = H by omega]
  cost_simp
  split_ifs <;> omega

/-- **Level `i` of novel → monomial** over `N = 2^j` (`fromLevel.c381`): at most
`74·N·i + 80·N + 41`. -/
theorem fromLevel_cost (hP : Includes P fromLevel.c381.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) {i j : ℕ} (hij : i < j) (hj : j ≤ 40)
    (hH : pw.getD i 0 = 2 ^ i) (d : Array K × K) (B : Array K) :
    machineCost P fromLevel.c381.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue i,
      encodeValue d, encodeValue B] ≤ 74 * (2 ^ j * i) + 80 * 2 ^ j + 41 := by
  rw [fromLevel.c381.costEq P hP, hH]
  have hsplit := two_pow_split hij
  set H := 2 ^ i with hHdef
  set M := 2 ^ (j - i - 1) with hMdef
  have hHpos : 0 < H := Nat.two_pow_pos i
  have hHle : H ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNle : 2 ^ j ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hj
  have hof := ofFnFrom_cost_sum0 P (by includes) (n := 2 ^ j) (by omega) _
    (.closure fromLevel.c381.lam0.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue i,
      encodeValue B, encodeValue (2 * H), encodeValue d.1, encodeValue H, encodeValue d.2])
    (fun p ↦ RunsApp.of_spec (fromLevel.c381.lam0.costSpec P (by includes) pw (2 ^ j) i B _ _ _ _ p))
    (fun p ↦ if p % (2 * H) < 2 * H / 2 then 76 * i + 48 else 71 * i + 77)
    (fun p ↦ by
      rw [appCost_fn]
      have := fromLevelEntry_cost P (by includes) pw hpw (2 ^ j) i hNle (by omega) B d.1 d.2 H hHle
        hHpos p
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      split_ifs at this ⊢ <;> omega)
  rw [show Finset.range (2 ^ j) = Finset.range (2 * H * M) by rw [hsplit]; ring_nf,
    block_sum_le] at hof
  have eR : M * ((2 * H / 2) * (76 * i + 48) + (2 * H - 2 * H / 2) * (71 * i + 77) +
      16 * (2 * H)) = 147 * (H * M * i) + 157 * (H * M) := by
    rw [show 2 * H / 2 = H by omega, show 2 * H - H = H by omega]; ring
  rw [eR] at hof
  have e2 : 2 ^ j * i = 2 * (H * M * i) := by rw [hsplit]; ring
  have e3 : 2 ^ j = 2 * (H * M) := by rw [hsplit]
  rw [ofFnFrom_length]
  cost_simp
  omega

/-- **Levels `0, …, L − 1` of novel → monomial** over `N = 2^j` (`fromLevels.c379`): at most
`37·N·L² + 80·N·L + 84·L + 20`. -/
theorem fromLevels_cost (hP : Includes P fromLevels.c379.costDeps) (pw : Array ℕ)
    (hpw : ∀ t, pw.getD t 0 < 2 ^ 40) {j L : ℕ} (hL : L ≤ j) (hj : j ≤ 40)
    (hH : ∀ i < L, pw.getD i 0 = 2 ^ i) (D : Array (Array K × K)) (B : Array K) :
    machineCost P fromLevels.c379.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue D,
      encodeValue L, encodeValue B] ≤
      37 * (2 ^ j * (L * L)) + 80 * (2 ^ j * L) + 84 * L + 20 := by
  rw [fromLevels.c379.costEq P hP]
  have hr := rangeLoop_cost P (by includes) L [] (by omega)
  have hf := listFoldl_cost_sum P (by includes) _
    (.closure fromLevels.c379.lam0.costIdx [encodeValue pw, encodeValue (2 ^ j), encodeValue D])
    (fun b i ↦ RunsApp.of_spec (fromLevels.c379.lam0.costSpec P (by includes) pw (2 ^ j) D b i))
    (fun i ↦ 74 * 2 ^ j * i + (80 * 2 ^ j + 58)) (List.range L) B
    (fun b i hi ↦ by
      have hi := List.mem_range.mp hi
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [fromLevels.c379.lam0.costEq P (by includes)]
      have := fromLevel_cost P (by includes) pw hpw (by omega : i < j) hj (hH i hi) (D.getD i (#[], 0)) b
      rw [mul_assoc]
      omega)
  rw [sum_map_range] at hf
  have hs := sum_range_level (74 * 2 ^ j) (80 * 2 ^ j + 58 + 11) L
  rw [Finset.sum_congr rfl fun i _ ↦ show 74 * 2 ^ j * i + (80 * 2 ^ j + 58) + 11 =
    74 * 2 ^ j * i + (80 * 2 ^ j + 58 + 11) by ring] at hf
  have e1 : 74 * 2 ^ j * (L * L) / 2 ≤ 37 * (2 ^ j * (L * L)) := by
    have : 74 * 2 ^ j * (L * L) = 74 * (2 ^ j * (L * L)) := by ring
    exact Nat.div_le_of_le_mul (by omega)
  have e2 : (80 * 2 ^ j + 58 + 11) * L = 80 * (2 ^ j * L) + 69 * L := by ring
  omega

/-- **Novel → monomial by the plan of size `N = 2^j`** (`fromNovelInPlaceC`), `j ≤ 40`: at most
`37·N·j² + 80·N·j + 23·N + 84·j + 47`. -/
theorem fromNovelInPlaceC_cost (hP : Includes P fromNovelInPlaceC.costDeps) {j : ℕ} (hj : j ≤ 40)
    (c : Array K) :
    machineCost P fromNovelInPlaceC.costIdx [encodeValue (FFT.mkPlan j), encodeValue c] ≤
      37 * (2 ^ j * (j * j)) + 80 * (2 ^ j * j) + 23 * 2 ^ j + 84 * j + 47 := by
  rw [fromNovelInPlaceC.costEq P hP, FFT.mkPlan_log]
  have hNle : 2 ^ j ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hj
  have hof := ofFnFrom_cost P (by includes) (n := 2 ^ j) (by omega) _
    (.closure toNovelInPlaceC.lam0.costIdx [encodeValue (FFT.mkPlan j), encodeValue c])
    (fun p ↦ RunsApp.of_spec (by
      have := toNovelInPlaceC.lam0.costSpec P (by includes) (FFT.mkPlan j) c
      rw [FFT.mkPlan_log] at this
      exact this p)) 6
    (fun p ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have := toNovelInPlaceC.lam0.costEq P (by includes) (FFT.mkPlan j) c
      rw [FFT.mkPlan_log] at this
      rw [this p]) 0 (Nat.zero_le _)
  have hl := fromLevels_cost P (by includes) _ (mkPlan_pows_lt hj) le_rfl hj
    (fun i hi ↦ FFT.mkPlan_pows hi) (FFT.mkPlan j).convInv (Array.ofFn fun p : Fin (2 ^ j) ↦ c.getD p 0)
  rw [ofFnFrom_length, limbs_shift (by omega), limbs_of_lt (by omega : j < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  omega

end

end LeanVM.Cost.Bounds.PMFFT
