module

public import LeanVM.Cost.Bounds.FieldLib
public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.SortedMap
public import LeanVM.Cost.Extractor.PMLane

/-!
# Bounds: the novel-basis transforms, the pruning and the stacks

The functions the fast path (`fastStacksFast`) and the decoder's pruning (`pruneUpToWith`,
`decodeStacksDistinctPM`) share, compiled in the decoder's chain (`Cost/Extractor/PMLane.lean`)
(the list functions they call: `Bounds/ListLib.lean`; the field's: `Bounds/FieldLib.lean`). With
`N = 2^m` the buffer:

* `subspacePoly_cost` (`47·2^j + 12`), `novelTwiddles_cost` (`83·N + 2866`);
* **`novelInvStage_cost`** (`174·N + 2890`), **`novelFwdStage_cost`** (`171·N + 2890`) per
  butterfly stage, **`novelInv_cost`** (`κ` stages over `2^κ`), **`novelFwd_cost`** (`κ` stages over
  `2^(κ+R)`);
* **`pruneStep_cost`**: `|st|·(|L|·((B + 34)·n + 11·U + 71) + 39) + 16` for `|st|` survivors of at
  most `n` columns and `U` lanes, `|L|` candidates, `B` the symbol's price;
* **`stackOf_cost`**: `(15·|cs| + 48)·2^μ + 16`.

Word-size hypotheses: the buffers below `2^62` entries.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction

public section

variable (P : MachineProgram)

/-! ## List functions -/

/-! ## Field arithmetic: the subspace polynomial and the inverse -/

/-- A product over `range n` (`prodRange.c207`): `B + 41` per factor, `5` at the end. -/
theorem prodRange_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.prodRange.c207.costDeps)
    (f : ℕ → K) (fVal : MachineValue) (hf : ∀ a : ℕ, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ)
    (hB : ∀ a : ℕ, a < 2 ^ 64 → appCost P fVal [encodeValue a] ≤ B) :
    ∀ n, n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Cost.Rewrite.prodRange.c207.costIdx [fVal, encodeValue n] ≤
        (B + 41) * n + 5 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.LeanVM.Cost.Rewrite.prodRange.c207.costEq_zero P hP f fVal hf]; omega
  | succ n ih =>
    intro hn
    rw [Auto.LeanVM.Cost.Rewrite.prodRange.c207.costEq_succ P hP f fVal hf, limbs_of_lt hn]
    have := ih (by omega)
    have := hB n (by omega)
    nlinarith

/-- **The subspace polynomial** `W_j(x)` (`subspacePoly.c206`): `2^j` products, at most
`47·2^j + 12`. -/
theorem subspacePoly_cost (hP : Includes P Auto.LeanVM.Extraction.subspacePoly.c206.costDeps)
    (j : ℕ) (hj : j < 64) (x : K) :
    machineCost P Auto.LeanVM.Extraction.subspacePoly.c206.costIdx [encodeValue j, encodeValue x] ≤
      47 * 2 ^ j + 12 := by
  rw [Auto.LeanVM.Extraction.subspacePoly.c206.costEq P hP, limbs_shift hj,
    limbs_of_lt (by omega : j < 2 ^ 64)]
  have := prodRange_cost P (by includes) _
    (.closure Auto.LeanVM.Extraction.subspacePoly.c206.lam0.costIdx [encodeValue x])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.subspacePoly.c206.lam0.costSpec P
      (by includes) x a)) 6
    (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append,
        Auto.LeanVM.Extraction.subspacePoly.c206.lam0.costEq P (by includes), limbs_of_lt ha]
      rfl)
    (2 ^ j) (Nat.pow_lt_pow_right (by norm_num) hj)
  omega

/-- `Nat.testBit` (`testBit.c211`): `9` on words. -/
theorem testBit_cost (hP : Includes P Auto.Nat.testBit.c211.costDeps) (a b : ℕ) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) : machineCost P Auto.Nat.testBit.c211.costIdx [encodeValue a, encodeValue b] ≤ 9 := by
  rw [Auto.Nat.testBit.c211.costEq P hP, limbs_of_lt ha, limbs_of_lt hb,
    limbs_of_lt (lt_of_le_of_lt (Nat.shiftRight_le a b) ha),
    limbs_of_lt (lt_of_le_of_lt (Nat.and_le_left (n := 1) (m := a >>> b)) (by norm_num))]
  omega

/-! ## The novel-basis transforms -/

theorem pow_split {i m : ℕ} (h : i < m) : 2 ^ i * 2 ^ (m - (i + 1)) * 2 = 2 ^ m := by
  rw [← pow_add, ← pow_succ]; congr 1; omega

/-- **Stage `i`'s twiddles** over `2^m` (`novelTwiddles.c205`): `2^(m−i−1)` subspace polynomials
of `2^i` factors and one inverse: at most `83·2^m + 2866`. -/
theorem novelTwiddles_cost (hP : Includes P Auto.LeanVM.Extraction.novelTwiddles.c205.costDeps)
    (m i : ℕ) (hi : i < m) (hm : m ≤ 62) :
    machineCost P Auto.LeanVM.Extraction.novelTwiddles.c205.costIdx [encodeValue m, encodeValue i] ≤
      83 * 2 ^ m + 2866 := by
  rw [Auto.LeanVM.Extraction.novelTwiddles.c205.costEq P hP]
  have hsub := subspacePoly_cost P (by includes) i (by omega) (K.ofBits (2 ^ i))
  have hinv := invK_cost P (by includes) (subspacePoly i (K.ofBits (2 ^ i)))
  have hw : 2 ^ (m - (i + 1)) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hw _
    (.closure Auto.LeanVM.Extraction.novelTwiddles.c205.lam0.costIdx
      [encodeValue m, encodeValue i, encodeValue (subspacePoly i (K.ofBits (2 ^ i)))⁻¹])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelTwiddles.c205.lam0.costSpec P
      (by includes) m i _ a)) (47 * 2 ^ i + 54)
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have hw2 : (a : ℕ) * 2 ^ (i + 1) < 2 ^ 64 := by
        have h2 : 2 ^ (m - (i + 1)) * 2 ^ (i + 1) = 2 ^ m := by rw [← pow_add]; congr 1; omega
        have h3 : 2 ^ m ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hm
        have h4 : (a : ℕ) * 2 ^ (i + 1) < 2 ^ (m - (i + 1)) * 2 ^ (i + 1) :=
          Nat.mul_lt_mul_of_pos_right a.isLt (by positivity)
        omega
      rw [Auto.LeanVM.Extraction.novelTwiddles.c205.lam0.costEq P (by includes), limbs_of_lt hw2,
        limbs_of_lt (by omega : i < 2 ^ 64), limbs_shift (by omega : i + 1 < 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_two_pow (by omega : i + 1 < 64),
        limbs_of_lt (by have := a.isLt; omega : (a : ℕ) < 2 ^ 64)]
      have := subspacePoly_cost P (by includes) i (by omega) (K.ofBits (↑a * 2 ^ (i + 1)))
      omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : i < 64), limbs_of_lt (by omega : i < 2 ^ 64),
    limbs_of_lt (by omega : m < 2 ^ 64), limbs_of_lt (by omega : i + 1 < 2 ^ 64),
    limbs_shift (by omega : m - (i + 1) < 64), limbs_of_lt (by omega : m - (i + 1) < 2 ^ 64)]
  have e := pow_split hi
  have h1 : 2 ^ i * 2 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show i + 1 ≤ m by omega)
    rw [pow_succ] at this; omega
  have h2 : 2 ^ (m - (i + 1)) * 2 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show m - (i + 1) + 1 ≤ m by omega)
    rw [pow_succ] at this; omega
  rw [limbs_two_pow (by omega : i < 64)]
  simp only [max_self, Nat.sub_zero] at hof ⊢
  nlinarith

/-- **An inverse butterfly stage** over `2^m` (`novelInvStage.c204`): at most `174·2^m + 2890`. -/
theorem novelInvStage_cost (hP : Includes P Auto.LeanVM.Extraction.novelInvStage.c204.costDeps)
    (m i : ℕ) (hi : i < m) (hm : m ≤ 62) (b : Array K) :
    machineCost P Auto.LeanVM.Extraction.novelInvStage.c204.costIdx [encodeValue m, encodeValue i, encodeValue b] ≤
      174 * 2 ^ m + 2890 := by
  rw [Auto.LeanVM.Extraction.novelInvStage.c204.costEq P hP]
  have htw := novelTwiddles_cost P (by includes) m i hi hm
  have hN : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.closure Auto.LeanVM.Extraction.novelInvStage.c204.lam0.costIdx
      [encodeValue m, encodeValue i, encodeValue b, encodeValue (novelTwiddles m i)])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelInvStage.c204.lam0.costSpec P
      (by includes) m i b _ a)) 74
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have ha : (a : ℕ) < 2 ^ 64 := by have := a.isLt; omega
      have hpi : (a : ℕ) + 2 ^ i < 2 ^ 64 := by
        have := a.isLt
        have : 2 ^ m ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hm
        have : 2 ^ i ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [Auto.LeanVM.Extraction.novelInvStage.c204.lam0.costEq P (by includes), limbs_of_lt hpi,
        limbs_of_lt (by omega : i < 2 ^ 64), limbs_shift (by omega : i + 1 < 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_two_pow (by omega : i + 1 < 64),
        limbs_of_lt ha, limbs_shift (by omega : i < 64), limbs_two_pow (by omega : i < 64)]
      have := testBit_cost P (by includes) a i ha (by omega)
      split_ifs <;> simp only [max_self] <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : m < 64), limbs_of_lt (by omega : m < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  omega

/-- **A forward butterfly stage** over `2^m` (`novelFwdStage.c230`): at most `171·2^m + 2890`. -/
theorem novelFwdStage_cost (hP : Includes P Auto.LeanVM.Extraction.novelFwdStage.c230.costDeps)
    (m i : ℕ) (hi : i < m) (hm : m ≤ 62) (b : Array K) :
    machineCost P Auto.LeanVM.Extraction.novelFwdStage.c230.costIdx [encodeValue m, encodeValue i, encodeValue b] ≤
      171 * 2 ^ m + 2890 := by
  rw [Auto.LeanVM.Extraction.novelFwdStage.c230.costEq P hP]
  have htw := novelTwiddles_cost P (by includes) m i hi hm
  have hN : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.closure Auto.LeanVM.Extraction.novelFwdStage.c230.lam0.costIdx
      [encodeValue m, encodeValue i, encodeValue b, encodeValue (novelTwiddles m i)])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelFwdStage.c230.lam0.costSpec P
      (by includes) m i b _ a)) 71
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have ha : (a : ℕ) < 2 ^ 64 := by have := a.isLt; omega
      have hpi : (a : ℕ) + 2 ^ i < 2 ^ 64 := by
        have := a.isLt
        have : 2 ^ m ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hm
        have : 2 ^ i ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [Auto.LeanVM.Extraction.novelFwdStage.c230.lam0.costEq P (by includes), limbs_of_lt hpi,
        limbs_of_lt (by omega : i < 2 ^ 64), limbs_shift (by omega : i + 1 < 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_two_pow (by omega : i + 1 < 64),
        limbs_of_lt ha, limbs_shift (by omega : i < 64), limbs_two_pow (by omega : i < 64)]
      have := testBit_cost P (by includes) a i ha (by omega)
      split_ifs <;> simp only [max_self] <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : m < 64), limbs_of_lt (by omega : m < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  omega

/-- **The inverse transform** over `2^κ` (`novelInv κ y`, a fold of `novelInvStage` through
`fastStacksFastC.lam1.lam0` over `range κ`): at most `κ·(174·2^κ + 2906) + 3`. -/
theorem novelInv_cost (hP : Includes P LeanVM.Cost.Extractor.fastStacksFastC.lam1.lam0.costDeps)
    (hF : Includes P listFoldl.costDeps) (κ : ℕ) (hκ : κ ≤ 62) (y : Array K) :
    machineCost P listFoldl.costIdx
        [.closure LeanVM.Cost.Extractor.fastStacksFastC.lam1.lam0.costIdx [encodeValue κ], encodeValue y,
          encodeValue (List.range κ)] ≤ κ * (174 * 2 ^ κ + 2906) + 3 := by
  have := listFoldl_le P hF _ (.closure LeanVM.Cost.Extractor.fastStacksFastC.lam1.lam0.costIdx [encodeValue κ])
    (fun a b ↦ RunsApp.of_spec (LeanVM.Cost.Extractor.fastStacksFastC.lam1.lam0.costSpec P
      (by includes) κ a b)) (174 * 2 ^ κ + 2895) (fun _ ↦ True) (List.range κ) y trivial
    (fun acc _ i hi ↦ ⟨trivial, by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [LeanVM.Cost.Extractor.fastStacksFastC.lam1.lam0.costEq P (by includes)]
      have := novelInvStage_cost P (by includes) κ i (List.mem_range.1 hi) hκ acc
      omega⟩)
  rw [List.length_range] at this
  nlinarith

/-- **The forward transform** (`novelFwd.c228`): the `2^κ` coefficients tiled over
`N = 2^(κ+R)` and `κ` forward stages: at most `κ·(171·N + 2924) + 28·N + 37`. -/
theorem novelFwd_cost (hP : Includes P Auto.LeanVM.Extraction.novelFwd.c228.costDeps)
    (κ R : ℕ) (hκR : κ + R ≤ 62) (c : Array K) :
    machineCost P Auto.LeanVM.Extraction.novelFwd.c228.costIdx [encodeValue κ, encodeValue R, encodeValue c] ≤
      κ * (171 * 2 ^ (κ + R) + 2924) + 28 * 2 ^ (κ + R) + 37 := by
  rw [Auto.LeanVM.Extraction.novelFwd.c228.costEq P hP]
  have hN : 2 ^ (κ + R) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.closure Auto.LeanVM.Extraction.novelFwd.c228.lam1.costIdx [encodeValue κ, encodeValue R, encodeValue c])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelFwd.c228.lam1.costSpec P
      (by includes) κ R c a)) 11
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have ha : (a : ℕ) < 2 ^ 64 := by have := a.isLt; omega
      rw [Auto.LeanVM.Extraction.novelFwd.c228.lam1.costEq P (by includes),
        limbs_shift (by omega : κ < 64), limbs_of_lt (by omega : κ < 2 ^ 64), limbs_of_lt ha,
        limbs_two_pow (by omega : κ < 64)]
      omega) 0 (Nat.zero_le _)
  have hr := rangeLoop_cost P (by includes) κ [] (by omega)
  have hfr := foldr_cost P (by includes) _
    (.closure Auto.LeanVM.Extraction.novelFwd.c228.lam0.costIdx [encodeValue κ, encodeValue R])
    (fun a b ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelFwd.c228.lam0.costSpec P
      (by includes) κ R a b)) (171 * 2 ^ (κ + R) + 2898)
    (Array.ofFn fun p : Fin (2 ^ (κ + R)) ↦ c.getD (p % 2 ^ κ) 0) (List.range κ)
    (fun i hi b ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Extraction.novelFwd.c228.lam0.costEq P (by includes),
        limbs_of_lt (by omega : κ < 2 ^ 64), limbs_of_lt (by omega : R < 2 ^ 64),
        limbs_of_lt (by omega : κ + R < 2 ^ 64)]
      have := novelFwdStage_cost P (by includes) (κ + R) i (by have := List.mem_range.1 hi; omega)
        hκR b
      simp only [max_self]
      omega)
  rw [ofFnFrom_length, limbs_of_lt (by omega : κ < 2 ^ 64), limbs_of_lt (by omega : R < 2 ^ 64),
    limbs_shift (by omega : κ + R < 64), limbs_of_lt (by omega : κ + R < 2 ^ 64)]
  rw [List.length_range] at hfr
  simp only [Nat.sub_zero, max_self] at hof ⊢
  nlinarith

/-! ## The pruning and the stacks -/

/-- **One pruning step** (`pruneStep.c214`): for `|st|` survivors of at most `n` columns and `U`
lanes each, `|L|` candidates, and the symbol's price at most `B`: at most
`|st|·(|L|·((B + 34)·n + 11·U + 71) + 39) + 16`. -/
theorem pruneStep_cost (hP : Includes P Auto.LeanVM.Extraction.pruneStep.c214.costDeps) (A : ℕ)
    (hA : A < 2 ^ 128) (sym : ℕ → K) (symVal : MachineValue) (hsym : ∀ a : ℕ, RunsApp P symVal [encodeValue a] (encodeValue (sym a)))
    (B : ℕ) (hB : ∀ v : ℕ, appCost P symVal [encodeValue v] ≤ B) (L : List (Array K × Array K))
    (st : List (List (Array K) × List ℕ)) (n U : ℕ) (hn : n < 2 ^ 64)
    (hst : ∀ s ∈ st, s.2.length ≤ n ∧ s.1.length ≤ U) :
    machineCost P Auto.LeanVM.Extraction.pruneStep.c214.costIdx [encodeValue A, symVal, encodeValue L, encodeValue st] ≤
      st.length * (L.length * ((B + 34) * n + 11 * U + 71) + 39) + 16 := by
  rw [Auto.LeanVM.Extraction.pruneStep.c214.costEq P hP A sym symVal hsym]
  -- one survivor and one candidate
  have hce : ∀ s ∈ st, ∀ ce : Array K × Array K,
      appCost P (.closure Auto.LeanVM.Extraction.pruneStep.c214.lam0.lam0.costIdx [encodeValue A, symVal, encodeValue s])
        [encodeValue ce] ≤ (B + 34) * n + 11 * U + 44 := by
    intro s hs ce
    obtain ⟨h2, h1⟩ := hst s hs
    simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    rw [Auto.LeanVM.Extraction.pruneStep.c214.lam0.lam0.costEq P (by includes) A sym symVal hsym]
    have hf := filter_cost P (by includes) _
      (.closure Auto.LeanVM.Extraction.pruneStep.c214.lam0.lam0.lam0.costIdx [symVal, encodeValue ce])
      (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.pruneStep.c214.lam0.lam0.lam0.costSpec P
        (by includes) sym symVal hsym ce a)) (B + 11)
      s.2 (fun v _ ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [Auto.LeanVM.Extraction.pruneStep.c214.lam0.lam0.lam0.costEq P (by includes) sym symVal
          hsym]
        have := hB v
        omega)
    have hlf := List.length_filter_le (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2
    have hl := length_cost P (by includes)
      (List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2) (by omega)
    have ha := append_cost P (by includes) s.1 [ce.1]
    have hlA := limbs_le_two hA
    rw [limbs_of_lt (by omega :
      (List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2).length < 2 ^ 64)]
    have : (B + 11 + 15) * s.2.length ≤ (B + 26) * n := Nat.mul_le_mul_left _ h2
    have := max_le hlA (show 1 ≤ 2 by omega)
    split_ifs <;> nlinarith
  have hs : ∀ s ∈ st,
      appCost P (.closure Auto.LeanVM.Extraction.pruneStep.c214.lam0.costIdx [encodeValue A, symVal, encodeValue L])
        [encodeValue s] ≤ ((B + 34) * n + 11 * U + 60) * L.length + 15 := by
    intro s hs
    simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    rw [Auto.LeanVM.Extraction.pruneStep.c214.lam0.costEq P (by includes) A sym symVal hsym]
    have := filterMap_cost P (by includes) _
      (.closure Auto.LeanVM.Extraction.pruneStep.c214.lam0.lam0.costIdx [encodeValue A, symVal, encodeValue s])
      (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.pruneStep.c214.lam0.lam0.costSpec P
        (by includes) A sym symVal hsym s a)) _ L (fun ce _ ↦ hce s hs ce)
    nlinarith
  have hm := map_cost P (by includes) _
    (.closure Auto.LeanVM.Extraction.pruneStep.c214.lam0.costIdx [encodeValue A, symVal, encodeValue L])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.pruneStep.c214.lam0.costSpec P
      (by includes) A sym symVal hsym L a)) _ st hs
  refine (Nat.add_le_add_right (Nat.add_le_add hm
    (flatten_map_cost P (by includes) L.length _ st ?_)) 10).trans ?_
  · intro s _
    exact List.length_filterMap_le _ _
  · nlinarith

/-- **A stack from its lanes** (`stackOf.c234`): `2^μ` cells, each a lookup among the `|cs|`
lanes: at most `(15·|cs| + 48)·2^μ + 16`. -/
theorem stackOf_cost (hP : Includes P Auto.LeanVM.Extraction.stackOf.c234.costDeps) (μ : ℕ)
    (hμ : μ ≤ 62) (cs : List (Array K)) :
    machineCost P Auto.LeanVM.Extraction.stackOf.c234.costIdx [encodeValue μ, encodeValue cs] ≤
      (15 * cs.length + 48) * 2 ^ μ + 16 := by
  rw [Auto.LeanVM.Extraction.stackOf.c234.costEq P hP]
  have hN : 2 ^ μ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.closure Auto.LeanVM.Extraction.stackOf.c234.lam0.costIdx [encodeValue μ, encodeValue cs])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.stackOf.c234.lam0.costSpec P
      (by includes) μ cs a)) (15 * cs.length + 31)
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have ha : (a : ℕ) < 2 ^ 64 := by have := a.isLt; omega
      rw [Auto.LeanVM.Extraction.stackOf.c234.lam0.costEq P (by includes),
        limbs_of_lt (by omega : μ < 2 ^ 64),
        limbs_of_lt (by unfold Whir.initialFold; omega : Whir.initialFold < 2 ^ 64),
        limbs_shift (by omega : μ - Whir.initialFold < 64),
        limbs_of_lt (by omega : μ - Whir.initialFold < 2 ^ 64), limbs_of_lt ha,
        limbs_two_pow (by omega : μ - Whir.initialFold < 64)]
      have := getD_cost P (by includes) cs (a / 2 ^ (μ - Whir.initialFold)) #[]
        (lt_of_le_of_lt (Nat.div_le_self _ _) ha)
      simp only [max_self]
      omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : μ < 64), limbs_of_lt (by omega : μ < 2 ^ 64)]
  simp only [Nat.sub_zero, max_self] at hof ⊢
  nlinarith

/-! ## The Johnson threshold: square roots on two-limb numbers -/

/-- Newton's step from above, on naturals: never below `√n`. -/
theorem newton_ge (n g : ℕ) (hg : 0 < g) : Nat.sqrt n ≤ (g + n / g) / 2 := by
  have hs := Nat.sqrt_le n
  set s := Nat.sqrt n
  suffices 2 * s ≤ g + n / g by omega
  by_cases h : 2 * s ≤ g
  · exact le_trans h (Nat.le_add_right _ _)
  · obtain ⟨t, ht⟩ : ∃ t, t + g = 2 * s := ⟨2 * s - g, by omega⟩
    have key : t * g ≤ s * s := by
      have : (t : ℤ) * g ≤ (s : ℤ) * s := by
        have ht' : (t : ℤ) + g = 2 * s := by exact_mod_cast ht
        nlinarith [sq_nonneg ((t : ℤ) - g)]
      exact_mod_cast this
    have : t ≤ n / g := (Nat.le_div_iff_mul_le hg).2 (by omega)
    omega

/-- Newton's step from above halves the excess over `√n`. -/
theorem newton_half (n g : ℕ) (hg : Nat.sqrt n < g) :
    (g + n / g) / 2 - Nat.sqrt n ≤ (g - Nat.sqrt n) / 2 := by
  have hs := Nat.lt_succ_sqrt n
  have : n / g ≤ Nat.sqrt n := by
    have : n / g < Nat.sqrt n + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc n < (Nat.sqrt n).succ * (Nat.sqrt n).succ := hs
        _ ≤ (Nat.sqrt n + 1) * g := Nat.mul_le_mul_left _ (by omega)
    omega
  omega

/-- **Newton's iteration** (`Nat.sqrt.iter.c222`) from a guess `g ≥ √n`, `n < 2^127`, `g ≤ 2^126`: at most `19 + 21·(log₂(g − √n) + 1)` (`√n ≤ g`: each step halves the excess, `newton_half`). -/
theorem sqrtIter_cost (hP : Includes P Auto.Nat.sqrt.iter.c222.costDeps) (n : ℕ) (hn : n < 2 ^ 127) :
    ∀ g, Nat.sqrt n ≤ g → g ≤ 2 ^ 126 →
      machineCost P Auto.Nat.sqrt.iter.c222.costIdx [encodeValue n, encodeValue g] ≤
        19 + 21 * (Nat.log2 (g - Nat.sqrt n) + 1) := by
  intro g hg hg1
  have hl : ∀ x, x < 2 ^ 128 → limbCount x ≤ 2 := fun x h ↦ limbs_le_two h
  -- the common price of a step's arithmetic
  have hstep : ∀ g, g ≤ 2 ^ 126 →
      limbCount n * limbCount g +
        max (limbCount (g + n / g)) (max (limbCount g) (limbCount (n / g))) + limbCount (g + n / g) +
        max (limbCount ((g + n / g) / 2)) (limbCount g) ≤ 10 := by
    intro g hg1
    have h1 := hl n (by omega)
    have h2 := hl g (by omega)
    have h3 := hl (n / g) (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
    have h4 := hl (g + n / g) (by have := Nat.div_le_self n g; omega)
    have h5 := hl ((g + n / g) / 2) (by have := Nat.div_le_self n g; omega)
    have : limbCount n * limbCount g ≤ 4 := by nlinarith
    omega
  have := le_of_halving (α := ℕ) (fun x ↦ Nat.sqrt n ≤ x ∧ x ≤ 2 ^ 126)
    (fun x ↦ x - Nat.sqrt n)
    (fun x ↦ machineCost P Auto.Nat.sqrt.iter.c222.costIdx [encodeValue n, encodeValue x]) 21 19 ?hz ?h g
    ⟨hg, hg1⟩
  · simpa using this
  · rintro x ⟨hx1, hx3⟩ h0
    rw [Auto.Nat.sqrt.iter.c222.costEq P hP]
    have := hstep x hx3
    rcases Nat.eq_zero_or_pos x with rfl | hx2
    · simp only [Nat.div_zero, Nat.add_zero, Nat.zero_div, Nat.lt_irrefl, ↓reduceDIte] at this ⊢
      omega
    · have := newton_ge n x hx2
      simp only [show ¬(x + n / x) / 2 < x by omega, ↓reduceDIte]
      omega
  · rintro x ⟨hx1, hx3⟩ hpos
    rw [Auto.Nat.sqrt.iter.c222.costEq P hP]
    have hx2 : 0 < x := by omega
    have hge := newton_ge n x hx2
    have := hstep x hx3
    by_cases hlt : (x + n / x) / 2 < x
    · right
      refine ⟨(x + n / x) / 2, ⟨hge, by omega⟩, newton_half n x (by omega), ?_⟩
      simp only [hlt, ↓reduceDIte]
      omega
    · left
      simp only [hlt, ↓reduceDIte]
      omega

/-- **`Nat.sqrt`** (`Nat.sqrt.c221`) below `2^127`: at most `4489`. -/
theorem sqrt_cost (hP : Includes P Auto.Nat.sqrt.c221.costDeps) (n : ℕ) (hn : n < 2 ^ 127) :
    machineCost P Auto.Nat.sqrt.c221.costIdx [encodeValue n] ≤ 4489 := by
  rw [Auto.Nat.sqrt.c221.costEq P hP]
  have h1 := limbs_le_two (x := n) (by omega)
  by_cases h : n ≤ 1
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]
    have hlog : Nat.log2 n < 127 := (Nat.log2_lt (by omega)).2 hn
    have hlr := log2Rec_cost P (by includes) n (by omega)
    set k := Nat.log2 n / 2 + 1
    have hk : k ≤ 64 := by omega
    have hg : 1 <<< k ≤ 2 ^ 126 := by
      rw [Nat.one_shiftLeft]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsq : Nat.sqrt n ≤ 1 <<< k := by
      rw [Nat.one_shiftLeft]
      have hs := Nat.sqrt_le n
      have hl := Nat.lt_log2_self (n := n)
      have : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ k * 2 ^ k := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      by_contra hc
      have : 2 ^ k * 2 ^ k < Nat.sqrt n * Nat.sqrt n := Nat.mul_lt_mul'' (by omega) (by omega)
      omega
    have hit := sqrtIter_cost P (by includes) n hn (1 <<< k) hsq hg
    have : Nat.log2 (1 <<< k - Nat.sqrt n) ≤ 126 := by
      have := log2_mono (show 1 <<< k - Nat.sqrt n ≤ 2 ^ 126 by omega)
      rw [Nat.log2_two_pow] at this; exact this
    have := limbs_le_two (x := 1 <<< k) (by omega)
    rw [limbs_of_lt (by omega : Nat.log2 n < 2 ^ 64), limbs_of_lt (by omega : Nat.log2 n / 2 < 2 ^ 64),
      limbs_of_lt (by omega : k < 2 ^ 64)]
    omega

/-- `⌈√x⌉` (`ceilSqrt.c220`) below `2^127`: at most `13481`. -/
theorem ceilSqrt_cost (hP : Includes P Auto.LeanVM.Extraction.ceilSqrt.c220.costDeps) (x : ℕ)
    (hx : x < 2 ^ 127) : machineCost P Auto.LeanVM.Extraction.ceilSqrt.c220.costIdx [encodeValue x] ≤ 13481 := by
  rw [Auto.LeanVM.Extraction.ceilSqrt.c220.costEq P hP]
  have hs := sqrt_cost P (by includes) x hx
  have h1 := Nat.sqrt_le x
  have h2 := Nat.sqrt_le_self x
  have hs3 : Nat.sqrt x < 3 * 2 ^ 62 := Nat.sqrt_lt.2 (by norm_num; omega)
  have l2 := limbs_le_two (x := Nat.sqrt x * Nat.sqrt x) (by omega)
  have l3 := limbs_le_two (x := x) (by omega)
  rw [limbs_of_lt (by omega : Nat.sqrt x < 2 ^ 64), limbs_of_lt (by omega : Nat.sqrt x + 1 < 2 ^ 64)]
  split_ifs <;> omega

theorem johnsonSlack_row_length (i : ℕ) : (johnsonSlack.getD i []).length ≤ 18 := by
  rcases i with _ | _ | _ | _ | i <;> simp [johnsonSlack]

theorem johnsonSlackOf_le (μ R : ℕ) : johnsonSlackOf μ R ≤ 38959 := by
  unfold johnsonSlackOf
  have hrow : ∀ i, ∀ x ∈ johnsonSlack.getD i [], x ≤ 38959 := by
    intro i
    rcases i with _ | _ | _ | _ | i <;> simp [johnsonSlack]
  rw [List.getD_eq_getElem?_getD]
  generalize h : (johnsonSlack.getD (R - 1) [])[μ - Whir.minLogStack]? = o
  cases o with
  | none => simp
  | some x => exact hrow _ x (List.mem_of_getElem? h)

/-- The slack table lookup (`johnsonSlackOf.c224`): at most `664`. -/
theorem johnsonSlackOf_cost (hP : Includes P Auto.LeanVM.Extraction.johnsonSlackOf.c224.costDeps)
    (μ R : ℕ) (hμ : μ < 2 ^ 64) (hR : R < 2 ^ 64) :
    machineCost P Auto.LeanVM.Extraction.johnsonSlackOf.c224.costIdx [encodeValue μ, encodeValue R] ≤ 664 := by
  rw [Auto.LeanVM.Extraction.johnsonSlackOf.c224.costEq P hP,
    Auto.LeanVM.Extraction.johnsonSlack.c227.costEq P (by includes), limbs_of_lt hR,
    limbs_of_lt hμ, limbs_of_lt (by unfold Whir.minLogStack; omega : Whir.minLogStack < 2 ^ 64)]
  have h1 := getD_cost P (by includes) johnsonSlack (R - 1) [] (by omega)
  have h2 := getD_cost P (by includes) (johnsonSlack.getD (R - 1) []) (μ - Whir.minLogStack) 0
    (by omega)
  have h3 := johnsonSlack_row_length (R - 1)
  have h4 : johnsonSlack.length = 4 := rfl
  simp only [max_self]
  omega

/-- **The Johnson threshold** (`johnsonThreshold.c219`): two `⌈√·⌉`s' worth of `Nat.sqrt` on a
number below `2^126`, the slack table and a few two-limb operations: at most `14199`, for
`2κ + R ≤ 80` (`κ = μ − 6`). -/
theorem johnsonThreshold_cost (hP : Includes P Auto.LeanVM.Extraction.johnsonThreshold.c219.costDeps)
    (μ R : ℕ) (hμ : μ < 2 ^ 64) (hκR : 2 * (μ - Whir.initialFold) + R ≤ 80) :
    machineCost P Auto.LeanVM.Extraction.johnsonThreshold.c219.costIdx [encodeValue μ, encodeValue R] ≤ 14199 := by
  rw [Auto.LeanVM.Extraction.johnsonThreshold.c219.costEq P hP]
  have hf : Whir.initialFold = 6 := rfl
  set κ := μ - Whir.initialFold with hκ
  have hL : ∀ x, x < 2 ^ 128 → limbCount x ≤ 2 := fun x h ↦ limbs_le_two h
  have hN : 2 ^ (κ + R) ≤ 2 ^ 80 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK : 2 ^ κ ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX : 2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) < 2 ^ 126 := by
    have : 2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) ≤ 2 ^ 44 * 2 ^ κ * 2 ^ (κ + R) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have e : 2 ^ 44 * 2 ^ κ * 2 ^ (κ + R) = 2 ^ (44 + κ + (κ + R)) := by rw [← pow_add, ← pow_add]
    have : 2 ^ (44 + κ + (κ + R)) < 2 ^ 126 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  set X := 2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) with hXdef
  have hcs := ceilSqrt_cost P (by includes) X (by omega)
  have hsl := johnsonSlackOf_cost P (by includes) μ R hμ (by omega)
  have hsl' := johnsonSlackOf_le μ R
  have hcsv : ceilSqrt X ≤ X + 1 := by
    unfold ceilSqrt; have := Nat.sqrt_le_self X; split_ifs <;> omega
  have hslN : johnsonSlackOf μ R * 2 ^ (κ + R) ≤ 38959 * 2 ^ 80 :=
    Nat.mul_le_mul hsl' hN
  have l1 := hL μ (by omega)
  have l2 := hL κ (by omega)
  have l3 := hL R (by omega)
  have l4 := hL (1 <<< (κ + R)) (by rw [Nat.one_shiftLeft]; omega)
  have l5 := hL (κ + R) (by omega)
  have l6 := hL (1 <<< κ) (by rw [Nat.one_shiftLeft]; omega)
  have l7 := hL (2 ^ κ) (by omega)
  have l8 := hL (2 ^ κ - 1) (by omega)
  have l9 := hL (2 ^ 44 * (2 ^ κ - 1)) (by
    have : 2 ^ 44 * (2 ^ κ - 1) ≤ 2 ^ 44 * 2 ^ 40 := Nat.mul_le_mul_left _ (by omega)
    omega)
  have l10 := hL (2 ^ (κ + R)) (by omega)
  have l11 := hL (johnsonSlackOf μ R) (by omega)
  have l12 := hL (ceilSqrt X) (by omega)
  have l13 := hL (johnsonSlackOf μ R * 2 ^ (κ + R)) (by omega)
  have l14 := hL (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R)) (by omega)
  have l15 := hL (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R) + 2 ^ 22) (by omega)
  have l16 := hL (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R) + 2 ^ 22 - 1) (by omega)
  have l17 := hL (Whir.initialFold) (by omega)
  have l18 := hL X (by omega)
  have p1 : limbCount (2 ^ 44) * limbCount (2 ^ κ - 1) ≤ 4 := by
    rw [limbs_two_pow (by norm_num)]; omega
  have p2 : limbCount (2 ^ 44 * (2 ^ κ - 1)) * limbCount (2 ^ (κ + R)) ≤ 4 := by nlinarith
  have p3 : limbCount (johnsonSlackOf μ R) * limbCount (2 ^ (κ + R)) ≤ 4 := by nlinarith
  have p4 : limbCount (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R) + 2 ^ 22 - 1) * limbCount (2 ^ 22) ≤ 4 := by
    rw [limbs_two_pow (by norm_num)]; omega
  rw [limbs_shift (by norm_num : 44 < 64), limbs_shift (by norm_num : 22 < 64),
    limbs_two_pow (by norm_num : 22 < 64), limbs_two_pow (by norm_num : 44 < 64)]
  -- every `max` bounded, so that `linarith` reads them as atoms (`omega` would split on each)
  have M1 : max (limbCount μ) (limbCount Whir.initialFold) ≤ 2 := max_le l1 l17
  have M2 : max (limbCount (κ + R)) (max (limbCount κ) (limbCount R)) ≤ 2 := max_le l5 (max_le l2 l3)
  have M3 : max (limbCount (1 <<< (κ + R))) (limbCount (κ + R)) ≤ 2 := max_le l4 l5
  have M4 : max (limbCount (1 <<< κ)) (limbCount κ) ≤ 2 := max_le l6 l2
  have M5 : max (limbCount (2 ^ 44 * (2 ^ κ - 1))) (1 * limbCount (2 ^ κ - 1)) ≤ 2 :=
    max_le l9 (by omega)
  have M6 : max (limbCount X) (limbCount (2 ^ 44 * (2 ^ κ - 1)) * limbCount (2 ^ (κ + R))) ≤ 4 :=
    max_le (by omega) p2
  have M7 : max (limbCount (johnsonSlackOf μ R * 2 ^ (κ + R)))
      (limbCount (johnsonSlackOf μ R) * limbCount (2 ^ (κ + R))) ≤ 2 :=
    max_le l13 (by rw [limbs_of_lt (by omega : johnsonSlackOf μ R < 2 ^ 64)]; omega)
  have M8 : max (limbCount (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R)))
      (max (limbCount (ceilSqrt X)) (limbCount (johnsonSlackOf μ R * 2 ^ (κ + R)))) ≤ 2 :=
    max_le l14 (max_le l12 l13)
  have M9 : max (limbCount (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R) + 2 ^ 22))
      (max (limbCount (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R))) 1) ≤ 2 :=
    max_le l15 (max_le l14 (by norm_num))
  linarith

theorem le_one_mul (a X : ℕ) (h : a ≤ 1) : a * X ≤ X := by
  simpa using Nat.mul_le_mul_right X h

theorem johnsonThreshold_lt (μ R : ℕ) (hκR : 2 * (μ - Whir.initialFold) + R ≤ 80) :
    johnsonThreshold μ R < 2 ^ 128 := by
  unfold johnsonThreshold
  dsimp only
  set κ := μ - Whir.initialFold
  have hN : 2 ^ (κ + R) ≤ 2 ^ 80 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK : 2 ^ κ ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX : 2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) < 2 ^ 126 := by
    have : 2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) ≤ 2 ^ 44 * 2 ^ κ * 2 ^ (κ + R) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have e : 2 ^ 44 * 2 ^ κ * 2 ^ (κ + R) = 2 ^ (44 + κ + (κ + R)) := by rw [← pow_add, ← pow_add]
    have : 2 ^ (44 + κ + (κ + R)) < 2 ^ 126 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hcs : ceilSqrt (2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R)) ≤
      2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) + 1 := by
    unfold ceilSqrt; have := Nat.sqrt_le_self (2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R)); split_ifs <;> omega
  have hsl : johnsonSlackOf μ R * 2 ^ (κ + R) ≤ 38959 * 2 ^ 80 := Nat.mul_le_mul (johnsonSlackOf_le μ R) hN
  refine lt_of_le_of_lt (Nat.div_le_self _ _) ?_
  generalize ceilSqrt (2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R)) = cs at hcs ⊢
  generalize johnsonSlackOf μ R * 2 ^ (κ + R) = y at hsl ⊢
  generalize 2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) = X at hX hcs
  refine lt_of_le_of_lt (Nat.sub_le _ _) ?_
  norm_num at hX hsl ⊢
  omega

theorem pruneStep_single {A : ℕ} {sym : ℕ → K} {c : Array K × Array K}
    {st : List (List (Array K) × List ℕ)} :
    (pruneStep A sym [c] st).length ≤ st.length ∧
      ∀ x ∈ pruneStep A sym [c] st, ∃ s ∈ st, x.2.length ≤ s.2.length ∧ x.1.length = s.1.length + 1 := by
  refine ⟨?_, fun x hx ↦ ?_⟩
  · unfold pruneStep
    rw [List.length_flatMap]
    have : ∀ s ∈ st, (List.filterMap (fun ce ↦
        if A ≤ (List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2).length then
          some (s.1 ++ [ce.1], List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2) else none)
        [c]).length ≤ 1 := fun s _ ↦ by
      have := List.length_filterMap_le (fun ce : Array K × Array K ↦
        if A ≤ (List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2).length then
          some (s.1 ++ [ce.1], List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2) else none) [c]
      simpa using this
    have := List.sum_le_length_nsmul (st.map fun s ↦ (List.filterMap (fun ce ↦
        if A ≤ (List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2).length then
          some (s.1 ++ [ce.1], List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2) else none)
        [c]).length) 1 (by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      exact this s hs)
    simpa using this
  · obtain ⟨s, hs, ce, -, -, rfl⟩ := PruneProofs.mem_pruneStep.1 hx
    exact ⟨s, hs, List.length_filter_le _ _, by simp⟩

/-- The fast path's survivors after some lanes: at most one, of at most `N` columns, at most
`64 − r` lanes when `r` are left. -/
@[expose] def FastInv (N : ℕ) (st : List (List (Array K) × List ℕ)) (r : ℕ) : Prop :=
  st.length ≤ 1 ∧ ∀ s ∈ st, s.2.length ≤ N ∧ s.1.length + r ≤ 64

/-- **One lane of the fast path** (`fastStacksFastC.lam1`): read the lane's `2^κ` symbols, the
inverse transform, the threshold, the forward transform over `N = 2^(κ+R)`, one pruning step
against at most one survivor. -/
theorem fastLane_cost (hP : Includes P fastStacksFastC.lam1.costDeps) (μ R κ : ℕ)
    (T : Array (Array K)) (st : List (List (Array K) × List ℕ)) (u r : ℕ) (hμ : μ < 2 ^ 64)
    (hJ : 2 * (μ - Whir.initialFold) + R ≤ 80) (hκR : κ + R ≤ 62)
    (hst : FastInv (2 ^ (κ + R)) st (r + 1)) :
    machineCost P fastStacksFastC.lam1.costIdx [encodeValue μ, encodeValue R, encodeValue T, encodeValue κ, encodeValue st, encodeValue u] ≤
      κ * (345 * 2 ^ (κ + R) + 5845) + 108 * 2 ^ (κ + R) + 15122 := by
  rw [fastStacksFastC.lam1.costEq P hP]
  have hK : 2 ^ κ ≤ 2 ^ (κ + R) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN : 2 ^ (κ + R) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) (n := 2 ^ κ) (by omega) _
    (.closure fastStacksFastC.lam1.lam1.costIdx [encodeValue T, encodeValue κ, encodeValue u])
    (fun a ↦ RunsApp.of_spec (fastStacksFastC.lam1.lam1.costSpec P (by includes) T κ u a)) 15
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [fastStacksFastC.lam1.lam1.costEq P (by includes),
        Auto.LeanVM.Extraction.Fast.tableSymbol.c213.costEq P (by includes)]) 0 (Nat.zero_le _)
  have hr := rangeLoop_cost P (by includes) κ [] (by omega)
  have hinv := novelInv_cost P (by includes) (by includes) κ (by omega)
    (Array.ofFn fun v : Fin (2 ^ κ) ↦ Fast.tableSymbol T u v)
  have hj := johnsonThreshold_cost P (by includes) μ R hμ hJ
  have hfwd := novelFwd_cost P (by includes) κ R hκR
    (novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ Fast.tableSymbol T u v))
  have hpr := pruneStep_cost P (by includes) (johnsonThreshold μ R) (johnsonThreshold_lt μ R hJ) _
    (.closure fastStacksFastC.lam1.lam2.costIdx [encodeValue T, encodeValue u])
    (fun a ↦ RunsApp.of_spec (fastStacksFastC.lam1.lam2.costSpec P (by includes) T u a)) 14
    (fun v ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [fastStacksFastC.lam1.lam2.costEq P (by includes),
        Auto.LeanVM.Extraction.Fast.tableSymbol.c213.costEq P (by includes)])
    [(novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ Fast.tableSymbol T u v),
      novelFwd κ R (novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ Fast.tableSymbol T u v)))]
    st (2 ^ (κ + R)) 64 hN (fun s hs ↦ ⟨(hst.2 s hs).1, by have := (hst.2 s hs).2; omega⟩)
  have hst1 := hst.1
  have : st.length * (1 * ((14 + 34) * 2 ^ (κ + R) + 11 * 64 + 71) + 39) ≤
      48 * 2 ^ (κ + R) + 814 := by
    refine le_trans (le_one_mul _ _ hst1) ?_
    omega
  rw [ofFnFrom_length, limbs_shift (by omega : κ < 64), limbs_of_lt (by omega : κ < 2 ^ 64)]
  simp only [Nat.sub_zero, List.length_singleton, max_self] at hof hpr ⊢
  linarith [Nat.mul_le_mul_left κ hK]

/-- **The fast path** (`fastStacksFast μ R W`, compiled as `fastStacksFastC`): the word's
`N = 2^(κ+R)` columns reversed into a table (`B_W` per column read, `W_d` words each), then `64`
lanes (`fastLane_cost`), then at most one stack (`stackOf_cost`): at most
`64·(κ·(345·N + 5845) + 108·N + 15137) + (B_W + 12·W_d + 44)·N + 1008·2^μ + 1071`, for
`μ ≤ 40`, `R ≤ 8`. -/
theorem fastStacksFast_cost (hP : Includes P fastStacksFastC.costDeps) (μ R : ℕ) (hμ : μ ≤ 40)
    (hR : R ≤ 8) (W : ℕ → List K) (WVal : MachineValue) (hW : ∀ a : ℕ, RunsApp P WVal [encodeValue a] (encodeValue (W a)))
    (BW Wd : ℕ) (hBW : ∀ v : ℕ, v < 2 ^ 64 → appCost P WVal [encodeValue v] ≤ BW) (hWd : ∀ v, (W v).length ≤ Wd) :
    machineCost P fastStacksFastC.costIdx [encodeValue μ, encodeValue R, WVal] ≤
      64 * ((μ - Whir.initialFold) * (345 * 2 ^ (μ - Whir.initialFold + R) + 5845) +
          108 * 2 ^ (μ - Whir.initialFold + R) + 15137) +
        (BW + 12 * Wd + 44) * 2 ^ (μ - Whir.initialFold + R) + 1008 * 2 ^ μ + 1071 := by
  have hI : Includes P fastStacksFastC.lam1.costDeps := by includes
  rw [fastStacksFastC.costEq P hP μ R W WVal hW]
  have hf : Whir.initialFold = 6 := rfl
  set κ := μ - Whir.initialFold with hκ
  set N := 2 ^ (κ + R) with hNdef
  have hN : N < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) (n := N) hN _
    (.closure fastStacksFastC.lam0.costIdx [encodeValue μ, encodeValue R, WVal])
    (fun a ↦ RunsApp.of_spec (fastStacksFastC.lam0.costSpec P (by includes) μ R W WVal hW a))
    (BW + 12 * Wd + 12)
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [fastStacksFastC.lam0.costEq P (by includes) μ R W WVal hW]
      have := reverseAux_cost P (by includes) (W a) []
      have := hBW a (by have := a.isLt; omega)
      have := hWd a
      rw [List.length_reverse]
      omega) 0 (Nat.zero_le _)
  have hr1 := rangeLoop_cost P (by includes) N [] hN
  have hr2 := rangeLoop_cost P (by includes) (2 ^ Whir.initialFold) [] (by rw [hf]; norm_num)
  -- a lane keeps the survivors' invariant
  have hstep : ∀ st r, FastInv N st (r + 1) → ∀ u ∈ List.range (2 ^ Whir.initialFold),
      FastInv N (pruneStep (johnsonThreshold μ R) (Fast.tableSymbol (Fast.laneTable N W) u)
        [(novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ Fast.tableSymbol (Fast.laneTable N W) u v),
          novelFwd κ R (novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦
            Fast.tableSymbol (Fast.laneTable N W) u v)))] st) r := by
    intro st r hst u _hu
    obtain ⟨h1, h2⟩ := pruneStep_single (A := johnsonThreshold μ R)
      (sym := Fast.tableSymbol (Fast.laneTable N W) u)
      (c := (novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ Fast.tableSymbol (Fast.laneTable N W) u v),
        novelFwd κ R (novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦
          Fast.tableSymbol (Fast.laneTable N W) u v)))) (st := st)
    refine ⟨by have := hst.1; omega, fun x hx ↦ ?_⟩
    obtain ⟨s, hs, hx2, hx1⟩ := h2 x hx
    have := hst.2 s hs
    exact ⟨by omega, by omega⟩
  have hinit : FastInv N [([], List.range N)] (List.range (2 ^ Whir.initialFold)).length := by
    refine ⟨by simp, fun s hs ↦ ?_⟩
    simp only [List.mem_singleton] at hs
    subst hs
    simp [hf]
  have hfold := listFoldl_amortized P (by includes) _
    (.closure fastStacksFastC.lam1.costIdx [encodeValue μ, encodeValue R, encodeValue (Fast.laneTable N W), encodeValue κ])
    (fun a b ↦ RunsApp.of_spec (fastStacksFastC.lam1.costSpec P (by includes) μ R _ κ a b))
    (κ * (345 * N + 5845) + 108 * N + 15126) (fun _ ↦ 0) (FastInv N)
    (List.range (2 ^ Whir.initialFold)) [([], List.range N)] hinit
    (fun st r hst u hu ↦ ⟨hstep st r hst u hu, by
      simp only [appCost_fn, List.cons_append, List.nil_append, Nat.add_zero, Nat.zero_add]
      have h1 : μ < 2 ^ 64 := by omega
      have h2 : 2 * (μ - Whir.initialFold) + R ≤ 80 := by omega
      have h3 : κ + R ≤ 62 := by omega
      have hl := fastLane_cost P hI μ R κ (Fast.laneTable N W) st u r h1 h2 h3 hst
      rw [← hNdef] at hl
      simp only [List.length_cons, List.length_nil]
      omega⟩)
  -- the survivors at the end: at most one, of at most `64` lanes
  have hend : ∀ (l : List ℕ) (st : List (List (Array K) × List ℕ)), (∀ u ∈ l, u ∈
      List.range (2 ^ Whir.initialFold)) → FastInv N st l.length →
      FastInv N (l.foldl (fun st u ↦
        have c := novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ Fast.tableSymbol (Fast.laneTable N W) u v)
        pruneStep (johnsonThreshold μ R) (Fast.tableSymbol (Fast.laneTable N W) u)
          [(c, novelFwd κ R c)] st) st) 0 := by
    intro l
    induction l with
    | nil => intro st _ h; simpa using h
    | cons u l ih =>
      intro st hl h
      exact ih _ (fun x hx ↦ hl x (by simp [hx])) (hstep st l.length h u (hl u (by simp)))
  have hfin := hend _ _ (fun u hu ↦ hu) hinit
  have hmap := map_cost P (by includes) _ (.closure fastStacksFastC.lam2.costIdx [encodeValue μ])
    (fun a ↦ RunsApp.of_spec (fastStacksFastC.lam2.costSpec P (by includes) μ a))
    (1008 * 2 ^ μ + 21) _ (fun s hs ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [fastStacksFastC.lam2.costEq P (by includes)]
      have := stackOf_cost P (by includes) μ (by omega) s.1
      have := (hfin.2 s hs).2
      have : (15 * s.1.length + 48) * 2 ^ μ ≤ 1008 * 2 ^ μ := Nat.mul_le_mul_right _ (by omega)
      omega)
  have hlen := hfin.1
  have : (1008 * 2 ^ μ + 21 + 13) *
      (List.foldl (fun st u ↦
        have c := novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ Fast.tableSymbol (Fast.laneTable N W) u v)
        pruneStep (johnsonThreshold μ R) (Fast.tableSymbol (Fast.laneTable N W) u)
          [(c, novelFwd κ R c)] st)
        [([], List.range N)] (List.range (2 ^ Whir.initialFold))).length ≤ 1008 * 2 ^ μ + 34 := by
    rw [Nat.mul_comm]; exact le_one_mul _ _ hlen
  rw [List.length_range] at hfold
  rw [ofFnFrom_length, limbs_of_lt (by omega : μ < 2 ^ 64), limbs_of_lt (by rw [hf]; norm_num :
    Whir.initialFold < 2 ^ 64), limbs_of_lt (by omega : κ < 2 ^ 64),
    limbs_of_lt (by omega : R < 2 ^ 64), limbs_shift (by omega : κ + R < 64),
    limbs_of_lt (by omega : κ + R < 2 ^ 64), limbs_shift (by rw [hf]; norm_num : Whir.initialFold < 64)]
  simp only [Nat.sub_zero, max_self, hf] at hof hfold hmap this hr2 ⊢
  nlinarith

theorem leafAt_length_le (leaves : Array (List K)) (h w v : ℕ) (hl : ∀ l ∈ leaves, l.length ≤ w) :
    (leafAt leaves h w v).length ≤ w := by
  unfold leafAt
  rw [Array.getD_eq_getD_getElem?]
  generalize hx : leaves[v % 2 ^ h]? = o
  cases o with
  | none => simp
  | some l => exact hl l (Array.mem_of_getElem? hx)

end

end LeanVM.Cost.Bounds
