module

public import LeanVMCircuits.Rec.PoolClaims

@[expose] public section

/-!
The union's soundness against a prover that tries many transcripts.

`Bind.union_sound` fixes what the union's transcript absorbs. A prover may absorb `Q` different words, each drawing
its own point, and answer with the one it likes. `union_sound_queries`: if each query's point is uniform on `S^5`
and in each query the selected and declared claims differ, the outcomes at which the prover's answer, for the query
it picks, passes the coverage test at that query's point are at most a `Q · 4N/|S|` fraction. The points need not be
independent: the bound is the union bound over the queries. `union_sound_sets_queries` is the same with the multisets
read as the sets the digests name (`Bind.union_sound_sets`).
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model PoolClaims UnionSound ProdCert

open Classical Finset in
/-- The union bound over `Q` queries. Query `q` absorbs what `val₀ q` gives the union's transcript and draws the
point `pt q`, uniform on `S^5`; in `val₀ q`, which holds every constraint but the tests and whose compressions and
output windows do not collide with themselves, the selected and declared claims differ. For each outcome the prover
picks a query `qOf ω` and answers with an assignment holding every constraint but the tests that absorbs what that
query's does and does not collide with it. Then the outcomes at which the answer's point is its query's and the
coverage test holds are at most a `Q · 4N/|S|` fraction. -/
theorem union_sound_queries (c : Cert) (s : State) (h : c.accepts s = true) {cv : Cover} (hcv : cv ∈ c.covers)
    (Q : ℕ) {st₀ : ℕ → ℕ → Fin 4 → K} {val₀ : ℕ → Val} (hv₀ : ∀ q < Q, Holds (st₀ q) s c.test (val₀ q))
    (hcr₀ : ∀ q < Q, HashCR s (val₀ q) (val₀ q)) (hwin₀ : ∀ q < Q, WindowCR s (val₀ q) (val₀ q))
    (hne : ∀ q < Q, onClaims (slots c.outs (c.poolOf cv.sel) (val₀ q)) ≠
      onClaims (slots c.outs (c.poolOf cv.decl) (val₀ q)))
    (S : Finset E) {Ω : Type} [Fintype Ω] (pt : ℕ → Ω → Fin 5 → E)
    (hS : ∀ q < Q, ∀ ω, pt q ω ∈ Fintype.piFinset fun _ : Fin 5 => S)
    (hpt : ∀ q < Q, ∀ f ∈ Fintype.piFinset (fun _ : Fin 5 => S), #S ^ 5 * #{ω | pt q ω = f} = Fintype.card Ω)
    (qOf : Ω → ℕ) (hq : ∀ ω, qOf ω < Q) (st : Ω → ℕ → Fin 4 → K) (val : Ω → Val)
    (hv : ∀ ω, Holds (st ω) s c.test (val ω)) (hcr : ∀ ω, HashCR s (val₀ (qOf ω)) (val ω))
    (hwin : ∀ ω, WindowCR s (val₀ (qOf ω)) (val ω))
    (hseed : ∀ ω, ∀ n ∈ seedsOf s (c.transcripts.getD cv.transcript default),
      nu (val₀ (qOf ω)) n = nu (val ω) n) :
    (#{ω | (c.points.getD cv.sel default).at (val ω) = pt (qOf ω) ω ∧
        ∀ a b, s.unions[cv.test]? = some (a, b) → val ω a = val ω b} : ℚ≥0) / Fintype.card Ω ≤
      Q * (4 * (2 * max (c.poolOf cv.sel).n (c.poolOf cv.decl).n : ℕ) / #S) := by
  classical
  -- Query `q`'s answers: the prover's where it picks `q`, `val₀ q` elsewhere.
  set ans : ℕ → Ω → Val := fun q ω => if qOf ω = q then val ω else val₀ q
  set sts : ℕ → Ω → ℕ → Fin 4 → K := fun q ω => if qOf ω = q then st ω else st₀ q
  set A : ℕ → Finset Ω := fun q => {ω | (c.points.getD cv.sel default).at (ans q ω) = pt q ω ∧
    ∀ a b, s.unions[cv.test]? = some (a, b) → ans q ω a = ans q ω b}
  have hsub : ({ω | (c.points.getD cv.sel default).at (val ω) = pt (qOf ω) ω ∧
      ∀ a b, s.unions[cv.test]? = some (a, b) → val ω a = val ω b} : Finset Ω) ⊆ (range Q).biUnion A := by
    intro ω hω
    rw [mem_biUnion]
    refine ⟨qOf ω, mem_range.mpr (hq ω), ?_⟩
    simpa [A, ans] using hω
  have hA : ∀ q ∈ range Q, (#(A q) : ℚ≥0) / Fintype.card Ω ≤
      4 * (2 * max (c.poolOf cv.sel).n (c.poolOf cv.decl).n : ℕ) / #S := by
    intro q hqQ
    have hqQ := mem_range.mp hqQ
    refine union_sound c s h hcv (hv₀ q hqQ) (hne q hqQ) S (pt q) (hS q hqQ) (hpt q hqQ) (sts q) (ans q)
      (fun ω => ?_) (fun ω => ?_) (fun ω => ?_) (fun ω n hn => ?_)
    · by_cases he : qOf ω = q <;> simp only [sts, ans, he, if_true, if_false]
      exacts [hv ω, hv₀ q hqQ]
    · by_cases he : qOf ω = q <;> simp only [ans, he, if_true, if_false]
      exacts [he ▸ hcr ω, hcr₀ q hqQ]
    · by_cases he : qOf ω = q <;> simp only [ans, he, if_true, if_false]
      exacts [he ▸ hwin ω, hwin₀ q hqQ]
    · by_cases he : qOf ω = q <;> simp only [ans, he, if_true, if_false]
      exact he ▸ hseed ω n hn
  calc (#{ω | (c.points.getD cv.sel default).at (val ω) = pt (qOf ω) ω ∧
          ∀ a b, s.unions[cv.test]? = some (a, b) → val ω a = val ω b} : ℚ≥0) / Fintype.card Ω
      ≤ (#((range Q).biUnion A) : ℚ≥0) / Fintype.card Ω := by
        gcongr
    _ ≤ (∑ q ∈ range Q, (#(A q) : ℚ≥0)) / Fintype.card Ω := by
        gcongr
        exact_mod_cast card_biUnion_le
    _ = ∑ q ∈ range Q, (#(A q) : ℚ≥0) / Fintype.card Ω := by rw [sum_div]
    _ ≤ ∑ _q ∈ range Q, (4 * (2 * max (c.poolOf cv.sel).n (c.poolOf cv.decl).n : ℕ) / #S : ℚ≥0) :=
        sum_le_sum hA
    _ = Q * (4 * (2 * max (c.poolOf cv.sel).n (c.poolOf cv.decl).n : ℕ) / #S) := by
        rw [sum_const, card_range, nsmul_eq_mul]

open Classical Finset in
/-- `union_sound_queries` with each query's multisets read as the sets the digests name: in query `q`'s assignment
the union's digests name sets (`SetsNamed`) of which the declared set's claims are not among the children's. -/
theorem union_sound_sets_queries (c : Cert) (s : State) (h : c.accepts s = true) {cv : Cover} (hcv : cv ∈ c.covers)
    (Q : ℕ) {st₀ : ℕ → ℕ → Fin 4 → K} {val₀ : ℕ → Val} (hv₀ : ∀ q < Q, Holds (st₀ q) s c.test (val₀ q))
    (hcr₀ : ∀ q < Q, HashCR s (val₀ q) (val₀ q)) (hwin₀ : ∀ q < Q, WindowCR s (val₀ q) (val₀ q))
    (F : (ℕ → K) → Bool → ℕ → K) (Cs : ℕ → ℕ → ClaimSet) (D : ℕ → ClaimSet)
    (hN : ∀ q < Q, SetsNamed c cv (val₀ q) F (Cs q) (D q))
    (hne : ∀ q < Q, ¬ (D q).tuples ≤ ∑ r ∈ range (c.poolOf cv.sel).runs, (Cs q r).tuples)
    (S : Finset E) {Ω : Type} [Fintype Ω] (pt : ℕ → Ω → Fin 5 → E)
    (hS : ∀ q < Q, ∀ ω, pt q ω ∈ Fintype.piFinset fun _ : Fin 5 => S)
    (hpt : ∀ q < Q, ∀ f ∈ Fintype.piFinset (fun _ : Fin 5 => S), #S ^ 5 * #{ω | pt q ω = f} = Fintype.card Ω)
    (qOf : Ω → ℕ) (hq : ∀ ω, qOf ω < Q) (st : Ω → ℕ → Fin 4 → K) (val : Ω → Val)
    (hv : ∀ ω, Holds (st ω) s c.test (val ω)) (hcr : ∀ ω, HashCR s (val₀ (qOf ω)) (val ω))
    (hwin : ∀ ω, WindowCR s (val₀ (qOf ω)) (val ω))
    (hseed : ∀ ω, ∀ n ∈ seedsOf s (c.transcripts.getD cv.transcript default),
      nu (val₀ (qOf ω)) n = nu (val ω) n) :
    (#{ω | (c.points.getD cv.sel default).at (val ω) = pt (qOf ω) ω ∧
        ∀ a b, s.unions[cv.test]? = some (a, b) → val ω a = val ω b} : ℚ≥0) / Fintype.card Ω ≤
      Q * (4 * (2 * max (c.poolOf cv.sel).n (c.poolOf cv.decl).n : ℕ) / #S) :=
  union_sound_queries c s h hcv Q hv₀ hcr₀ hwin₀
    (fun q hqQ => sets_differ c s h hcv (hv₀ q hqQ) (hN q hqQ) (hne q hqQ)) S pt hS hpt qOf hq st val hv hcr hwin
    hseed

end LeanVMCircuits.Rec.Bind
