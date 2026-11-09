module

public import LeanVM.Cost.Bounds.Sizes.Roots
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Modular
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Basic

/-!
# Sizes along the decoder: inside the root finder

The root finder (`rootsInFieldFast`, `Fast/RootFinder.lean`) on a nonzero polynomial `p` of
degree `d`:

* **the gcds** (`gcdMonicFast`, the Euclidean chain with `rawModFast`): the result has degree at
  most the first argument's (`gcdMonicFast_natDegree_le`; CompPoly's
  `gcdMonic_toPoly_eq_normalize_gcd`); `monicNormalize` keeps the degree
  (`monicNormalize_natDegree`);
* **`X^q − X mod u`** (`xPowSubXModWith`): fewer than `|trim u|` coefficients
  (`xPowSubXModWith_size_lt`: the binary exponentiation's accumulator stays a remainder,
  `powModBinaryAuxWith_size_lt`); the root product `gcd(p, X^q − X)` has degree at most `d`
  (`rootProductFast_natDegree_le`);
* **Shoup's splitter** at a factor `u`: the trace polynomial `Σ β^(2^i)·(X^(2^i) mod u)` has degree
  below `deg u` (`traceCoordFast_natDegree_le`, `traceCoordFast_frobenius_natDegree_lt`); a factor
  has at most `p = 2` children, each of degree at most `deg u` (`refineFactorFast_children`), and
  the cache grows by at most one entry per factor (`refineFactorFast_cache_length`,
  `refineFactorsFast_bounds`: at most twice the factors, of degree at most the factors', the
  cache at most one entry more per factor); every final factor divides the root product, so has
  degree at most `d` (`splitCandidatesFast_natDegree_le`).
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.GuruswamiSudan LeanVM.Extraction.Fast LeanVM.Extraction LeanVM.Parameters
open CompPoly.CPolynomial.Roots.FiniteField

public section

/-! ## The gcds -/

theorem monicNormalize_natDegree (p : CPolynomial K) :
    (CPolynomial.monicNormalize p).natDegree = p.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.monicNormalize_toPoly_eq_normalize,
    Polynomial.natDegree_normalize, ← CPolynomial.natDegree_toPoly]

theorem toPoly_ne_zero {p : CPolynomial K} (hp : p ≠ 0) : p.toPoly ≠ 0 := by
  intro h; apply hp; rw [← CPolynomial.toPoly_inj, CPolynomial.toPoly_zero]; exact h

/-- **A gcd has degree at most its first argument's.** -/
theorem gcdMonicFast_natDegree_le {u : CPolynomial K} (hu : u ≠ 0) (v : CPolynomial K) :
    (gcdMonicFast u v).natDegree ≤ u.natDegree := by
  rw [gcdMonicFast_eq, CPolynomial.natDegree_toPoly, CPolynomial.gcdMonic_toPoly_eq_normalize_gcd,
    Polynomial.natDegree_normalize, CPolynomial.natDegree_toPoly u]
  exact Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left _ _) (toPoly_ne_zero hu)

/-! ## `X^q − X mod u` -/

section Raw

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

omit [LawfulBEq F] in
theorem raw_sub_size_le (p q : CPolynomial.Raw F) : (p - q).size ≤ max p.size q.size := by
  show (CPolynomial.Raw.sub p q).size ≤ _
  unfold CPolynomial.Raw.sub CPolynomial.Raw.add
  refine (CPolynomial.Raw.Trim.size_le_size _).trans ?_
  rw [CPolynomial.Raw.size_addRaw]
  simp [CPolynomial.Raw.neg]

theorem raw_one_trim : (1 : CPolynomial.Raw F).trim = 1 := by
  change CPolynomial.Raw.trim (#[] |>.push (1 : F)) = (#[] |>.push (1 : F))
  apply CPolynomial.Raw.Trim.push_trim
  simp

theorem raw_X_trim : (CPolynomial.Raw.X : CPolynomial.Raw F).trim = CPolynomial.Raw.X := by
  change CPolynomial.Raw.trim (#[(0 : F)] |>.push (1 : F)) = (#[(0 : F)] |>.push (1 : F))
  apply CPolynomial.Raw.Trim.push_trim
  simp

/-- A remainder modulo `monicNormalize u` of a trimmed input: fewer than `|trim u|`. -/
theorem remainderOnly_size_lt (u a : CPolynomial.Raw F) (ha : a.trim = a) (hu : u.trim ≠ 0) :
    (CPolynomial.Raw.ModContext.remainderOnly.modByMonic a
      (CPolynomial.Raw.monicNormalize u)).size < u.trim.size := by
  have hpos : 0 < u.trim.size := by
    rcases Nat.eq_zero_or_pos u.trim.size with h | h
    · exact absurd (Array.eq_empty_of_size_eq_zero h) hu
    · exact h
  rw [← monicNormalize_size u hu]
  exact modByMonicRemainderOnly_size_lt _ _ ha
    (by rw [monicNormalize_size u hu]; exact hpos) (monicNormalize_getLastD u hu)

/-- **The binary exponentiation's accumulator stays a remainder.** -/
theorem powModBinaryAuxWith_size_lt (u : CPolynomial.Raw F) (hu : u.trim ≠ 0) (n : ℕ) :
    ∀ acc c, acc.size < u.trim.size →
      (CPolynomial.Raw.powModBinaryAuxWith CPolynomial.Raw.MulContext.naive
        CPolynomial.Raw.ModContext.remainderOnly u n acc c).size < u.trim.size := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro acc c hacc
  rcases n with _ | n
  · rw [CPolynomial.Raw.powModBinaryAuxWith]; exact hacc
  · rw [CPolynomial.Raw.powModBinaryAuxWith]
    refine ih _ (Nat.div_lt_self (Nat.succ_pos n) (by decide)) _ _ ?_
    split
    · exact mulModWith_size_lt u acc c hu
    · exact hacc

/-- **`X^q − X mod u` has fewer than `|trim u|` coefficients.** -/
theorem xPowSubXModWith_size_lt (u : CPolynomial.Raw F) (hu : u.trim ≠ 0) (q : ℕ) :
    (CPolynomial.Raw.xPowSubXModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly q u).size < u.trim.size := by
  rw [CPolynomial.Raw.xPowSubXModWith]
  refine lt_of_le_of_lt (raw_sub_size_le _ _) (max_lt ?_ ?_)
  · rw [CPolynomial.Raw.powModWith]
    have : (u.trim == 0) = false := by simpa using hu
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact powModBinaryAuxWith_size_lt u hu _ _ _ (remainderOnly_size_lt u 1 raw_one_trim hu)
  · rw [CPolynomial.Raw.xModWith]
    have : (u.trim == 0) = false := by simpa using hu
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact remainderOnly_size_lt u _ raw_X_trim hu

end Raw

/-- **The root product `gcd(p, X^q − X)` has degree at most `deg p`.** -/
theorem rootProductFast_natDegree_le {p : CPolynomial K} (hp : p ≠ 0) :
    (rootProductFast p).natDegree ≤ p.natDegree := by
  classical
  rw [rootProductFast_eq, CPolynomial.natDegree_toPoly,
    finiteFieldRootProductWith_toPoly_eq_normalize_gcd _ _ _ hp]
  rw [Polynomial.natDegree_normalize]
  refine (Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left _ _) ?_).trans ?_
  · exact toPoly_ne_zero (monicNormalize_ne_zero_of_ne_zero hp)
  · rw [← CPolynomial.natDegree_toPoly, monicNormalize_natDegree]

/-! ## Shoup's splitter -/

/-- **The trace polynomial has degree at most the Frobenius powers'.** -/
theorem traceCoordFast_natDegree_le (beta : K) (powers : Array (CPolynomial K)) (d : ℕ)
    (h : ∀ p ∈ powers, p.natDegree ≤ d) : (traceCoordFast beta powers).natDegree ≤ d := by
  rw [traceCoordFast, traceCoordFast_fold]
  have hg : ∀ i, (powers.getD i 0).natDegree ≤ d := by
    intro i
    rw [Array.getD_eq_getD_getElem?]
    by_cases hi : i < powers.size
    · rw [Array.getElem?_eq_getElem hi, Option.getD_some]; exact h _ (Array.getElem_mem hi)
    · rw [Array.getElem?_eq_none (by omega), Option.getD_none, CPolynomial.natDegree_toPoly,
        CPolynomial.toPoly_zero]; simp
  have : ∀ (l : List ℕ) (acc : CPolynomial K), acc.natDegree ≤ d →
      (l.foldl (fun acc i ↦ acc + CPolynomial.C (beta ^ (2 ^ i)) * powers.getD i 0) acc).natDegree
        ≤ d := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons i l ih =>
      intro acc hacc
      refine ih _ ((CPolynomial.natDegree_add_le _ _).trans (max_le hacc ?_))
      refine (CPolynomial.natDegree_mul_le _ _).trans ?_
      rw [CPolynomial.natDegree_C, Nat.zero_add]
      exact hg i
  exact this _ 0 (by rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]; simp)

theorem natDegree_le_size_sub_one (p : CPolynomial K) : p.natDegree ≤ p.val.size - 1 := by
  unfold CPolynomial.natDegree
  split <;> omega

/-- **At a factor `u`, the trace polynomial has degree below `deg u`.** -/
theorem traceCoordFast_frobenius_natDegree_lt {u : CPolynomial K} (hu : u ≠ 0) (beta : K)
    (k : ℕ) : (traceCoordFast beta (frobeniusPowersFast u k)).natDegree ≤ u.natDegree - 1 := by
  refine traceCoordFast_natDegree_le _ _ _ fun p hp ↦ ?_
  have h1 := frobeniusPowersFast_size_lt hu k hp
  have h2 := natDegree_le_size_sub_one p
  have h3 : u.natDegree = u.val.size - 1 := by
    unfold CPolynomial.natDegree; split <;> omega
  omega

theorem pushNontrivialChild_bounds (children : Array (CPolynomial K)) (child : CPolynomial K) :
    (pushNontrivialChild children child).size ≤ children.size + 1 ∧
      ∀ c ∈ pushNontrivialChild children child, c ∈ children ∨ c = child := by
  unfold pushNontrivialChild
  split
  · exact ⟨by omega, fun c hc ↦ Or.inl hc⟩
  · refine ⟨by simp, fun c hc ↦ ?_⟩
    rw [Array.mem_push] at hc
    exact hc

theorem pushChildren_bounds (g : K → CPolynomial K) (D : ℕ) (hg : ∀ c, (g c).natDegree ≤ D) :
    ∀ (l : List K) (children : Array (CPolynomial K)), (∀ c ∈ children, c.natDegree ≤ D) →
      (l.foldl (fun children c ↦ pushNontrivialChild children (g c)) children).size ≤
          children.size + l.length ∧
        ∀ c ∈ l.foldl (fun children c ↦ pushNontrivialChild children (g c)) children,
          c.natDegree ≤ D := by
  intro l
  induction l with
  | nil => intro children h; exact ⟨by simp, h⟩
  | cons x l ih =>
    intro children h
    rw [List.foldl_cons]
    obtain ⟨hs, hm⟩ := pushNontrivialChild_bounds children (g x)
    obtain ⟨h1, h2⟩ := ih (pushNontrivialChild children (g x)) fun c hc ↦ by
      rcases hm c hc with hc | rfl
      · exact h c hc
      · exact hg x
    exact ⟨by simp only [List.length_cons]; omega, h2⟩

/-- **A factor has at most `p = 2` children, each of degree at most the factor's.** -/
theorem refineFactorFast_children (beta : K) (cache : ShoupTracePowerCache K) (u : CPolynomial K) :
    (refineFactorFast beta cache u).2.size ≤ 2 ∧
      ∀ c ∈ (refineFactorFast beta cache u).2, c.natDegree ≤ u.natDegree := by
  unfold refineFactorFast
  dsimp only
  split
  · simp
  · split
    · refine ⟨by simp, fun c hc ↦ ?_⟩
      rw [Array.mem_singleton] at hc
      rw [hc, monicNormalize_natDegree]
    · rename_i h0 _
      have hu : CPolynomial.monicNormalize u ≠ 0 := by
        intro h; apply h0; simp [h]
      have hg : ∀ c : K, (CPolynomial.monicNormalize (gcdMonicFast (CPolynomial.monicNormalize u)
          (traceCoordFast beta (tracePowersFast (CPolynomial.monicNormalize u) cache).1 -
            CPolynomial.C c))).natDegree ≤ u.natDegree := fun c ↦ by
        rw [monicNormalize_natDegree]
        exact (gcdMonicFast_natDegree_le hu _).trans (monicNormalize_natDegree u).le
      obtain ⟨h1, h2⟩ := pushChildren_bounds _ u.natDegree hg traceCtx.baseConstants.toList #[]
        (by simp)
      rw [← Array.foldl_toList]
      refine ⟨h1.trans ?_, h2⟩
      rw [Array.size_empty, Nat.zero_add, Array.length_toList, traceCtx.baseConstants_size,
        traceCtx_p]

/-- **The cache grows by at most one entry per factor.** -/
theorem refineFactorFast_cache_length (beta : K) (cache : ShoupTracePowerCache K)
    (u : CPolynomial K) : (refineFactorFast beta cache u).1.length ≤ cache.length + 1 := by
  unfold refineFactorFast
  dsimp only
  split
  · simp
  · split
    · simp
    · unfold tracePowersFast
      split <;> simp

/-- **One basis element over the factors**: at most twice the factors, of degree at most `d`, the
cache at most one entry more per factor. -/
theorem refineFactorsFast_bounds (beta : K) (cache : ShoupTracePowerCache K)
    (factors : Array (CPolynomial K)) (d : ℕ) (h : ∀ u ∈ factors, u.natDegree ≤ d) :
    (refineFactorsFast beta cache factors).2.size ≤ 2 * factors.size ∧
      (∀ c ∈ (refineFactorsFast beta cache factors).2, c.natDegree ≤ d) ∧
      (refineFactorsFast beta cache factors).1.length ≤ cache.length + factors.size := by
  have e : refineFactorsFast beta cache factors = factors.toList.foldl
      (fun st f ↦ ((refineFactorFast beta st.1 f).1, st.2 ++ (refineFactorFast beta st.1 f).2))
      (cache, #[]) := by
    rw [refineFactorsFast, ← Array.foldl_toList]
  rw [e]
  have hgen : ∀ (l : List (CPolynomial K)) (st : ShoupTracePowerCache K × Array (CPolynomial K)),
      (∀ u ∈ l, u.natDegree ≤ d) → (∀ c ∈ st.2, c.natDegree ≤ d) →
      (l.foldl (fun st f ↦ ((refineFactorFast beta st.1 f).1,
          st.2 ++ (refineFactorFast beta st.1 f).2)) st).2.size ≤ st.2.size + 2 * l.length ∧
      (∀ c ∈ (l.foldl (fun st f ↦ ((refineFactorFast beta st.1 f).1,
          st.2 ++ (refineFactorFast beta st.1 f).2)) st).2, c.natDegree ≤ d) ∧
      (l.foldl (fun st f ↦ ((refineFactorFast beta st.1 f).1,
          st.2 ++ (refineFactorFast beta st.1 f).2)) st).1.length ≤ st.1.length + l.length := by
    intro l
    induction l with
    | nil => intro st _ h2; exact ⟨by simp, h2, by simp⟩
    | cons x l ih =>
      intro st h1 h2
      rw [List.foldl_cons]
      obtain ⟨c1, c2⟩ := refineFactorFast_children beta st.1 x
      have c3 := refineFactorFast_cache_length beta st.1 x
      obtain ⟨r1, r2, r3⟩ := ih ((refineFactorFast beta st.1 x).1,
          st.2 ++ (refineFactorFast beta st.1 x).2) (fun u hu ↦ h1 u (by simp [hu])) (fun c hc ↦ by
        change c ∈ st.2 ++ _ at hc
        rw [Array.mem_append] at hc
        rcases hc with hc | hc
        · exact h2 c hc
        · exact (c2 c hc).trans (h1 x (by simp)))
      simp only [Array.size_append, List.length_cons] at r1 r3 ⊢
      exact ⟨by omega, r2, by omega⟩
  obtain ⟨r1, r2, r3⟩ := hgen factors.toList (cache, #[]) (fun u hu ↦ h u (by simpa using hu))
    (by simp)
  simp only [Array.size_empty, Nat.zero_add, Array.length_toList] at r1 r3
  exact ⟨r1, r2, r3⟩

/-- **Every factor the splitter returns divides its input, so has degree at most its.** -/
theorem splitCandidatesFast_natDegree_le {p : CPolynomial K} (hp : p ≠ 0) {f : CPolynomial K}
    (hf : f ∈ splitCandidatesFast p) : f.natDegree ≤ p.natDegree := by
  rw [splitCandidatesFast_eq] at hf
  have hd := shoupSplitCandidatesWith_dvd_input _ _ _ (Array.mem_toList_iff.2 hf)
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly p]
  exact Polynomial.natDegree_le_of_dvd hd (toPoly_ne_zero hp)

end

end LeanVM.Cost.Bounds
