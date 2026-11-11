/-
  LeanVM.Protocol.Whir.Complete.Levels

  The honest WHIR levels follow the verifier's: the fold rounds, a non-final level's commitment,
  out-of-domain values, queries and glue, and the final level's check and tail sumcheck.
-/

module

public import LeanVM.Protocol.Whir.Complete.Rounds
public import LeanVM.Protocol.Whir.Complete.Script
public import LeanVM.Protocol.Whir.Complete.Encoding

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Prover LeanVM.Prover.Enc Finset

@[expose] public section

/-- **One fold round follows the verifier's.** -/
theorem follows_foldRoundA (f w : Array E) (s : ℕ) (sv : WhirState) (cs : Commits) :
    Follows (fun cs' (a : Array E × Array E) (b : WhirState × FoldRound) ↦ cs' = cs ∧
        ∃ α β u₀ w₁ c₀ c₁,
          roundTableA f w s (halfA f s) (mulXA (halfA f s) (s / 2)) = [u₀, w₁, c₀, c₁] ∧
          b.2 = ⟨α, β⟩ ∧
          b.1 = { sv with claim := u₀ + α * (u₀ + sv.claim) + α * α * w₁ + β * c₀ +
              α * β * (c₀ + c₁), alphas := sv.alphas ++ [α] } ∧
          a = (foldLanesA f s (halfA f s) (mulXA (halfA f s) (s / 2)) α β,
            foldPairsA α w))
      (foldRoundA f w s) (foldRound sv) cs := by
  simp only [foldRoundA, foldRound, Script.grindBits, VerifierProgram.grindProofOfWork,
    Whir.foldGrindingBits, roundTableA, Script.bind_eq, VerifierProgram.bind_eq, Script.pure_eq,
    VerifierProgram.pure_eq, Script.grindS, Script.sampleE, Script.sendList,
    VerifierProgram.readScalar, VerifierProgram.sampleChallenge, Script.bind, VerifierProgram.bind]
  intro α β
  exact ⟨rfl, α, β, _, _, _, _, rfl, rfl, rfl, rfl⟩

/-! ## The invariant of a level's fold rounds -/

/-- The verifier's weight at the remaining point `x`, the terminal check's `weight` at
`point = alphas ++ x`. -/
def runW (B : List E → E) (lf : ℕ) (sv : WhirState) (x : List E) : E :=
  sv.glued.foldl (fun weight glued ↦ weight + glued.scalar * glued.weightAt
      ((sv.alphas ++ x).drop glued.foldStart))
    (B ((sv.alphas ++ x).drop lf ++ (sv.alphas ++ x).take lf))

/-- The verifier's fold of an opened row by the rounds so far. -/
def vfold (rounds : List FoldRound) (x : K) (v : List E) : List E :=
  rounds.foldl (fun v r ↦ foldLanes x r v) v

/-- **The invariant of a level's rounds**, `j` rounds done and `m` lane variables left: the
tables' shapes, the running claim `Σ w·f` over the weight's coefficients, the verifier's weight
the extension of `w`, and every opened row (`rowOf p`, `p < P`) folded by the rounds so far the
lanes of `f` at its point. -/
def FoldInv (μ lf : ℕ) (B : List E → E) (κ P : ℕ) (rowOf : ℕ → List E) (j m : ℕ) (sv : WhirState)
    (f w : Array E) (rounds : List FoldRound) : Prop :=
  w.size = 2 ^ κ * 2 ^ m ∧ f.size = (2 ^ κ + j) * 2 ^ m ∧ 2 ^ κ + j + m ≤ 2 ^ 61 ∧
  sv.claim = ∑ i ∈ range w.size, w.getD i 0 * f.getD i 0 ∧
  sv.alphas.length + κ + m = μ ∧
  (∀ x, x.length = κ + m → runW B lf sv x = multilinearEval w.toList x) ∧
  ∀ p < P, (vfold rounds (K.ofBits p) (rowOf p)).length = 2 ^ m ∧
    ∀ l < 2 ^ m, (vfold rounds (K.ofBits p) (rowOf p)).getD l 0 = laneVal f m l (K.ofBits p)

theorem runW_fold (B : List E → E) (lf : ℕ) (sv : WhirState) (c γ : E) (x : List E) :
    runW B lf { sv with claim := c, alphas := sv.alphas ++ [γ] } x = runW B lf sv (γ :: x) := by
  simp [runW]

/-- **A round keeps the invariant.** -/
theorem FoldInv.step {μ lf : ℕ} {B : List E → E} {κ P : ℕ} {rowOf : ℕ → List E} {j m : ℕ}
    {sv : WhirState} {f w : Array E} {rounds : List FoldRound}
    (hI : FoldInv μ lf B κ P rowOf j (m + 1) sv f w rounds) (α β u₀ w₁ c₀ c₁ : E)
    (ht : roundTableA f w (2 ^ (m + 1)) (halfA f (2 ^ (m + 1)))
      (mulXA (halfA f (2 ^ (m + 1))) (2 ^ m)) = [u₀, w₁, c₀, c₁]) :
    FoldInv μ lf B κ P rowOf (j + 1) m
      { sv with claim := u₀ + α * (u₀ + sv.claim) + α * α * w₁ + β * c₀ +
          α * β * (c₀ + c₁), alphas := sv.alphas ++ [α] }
      (foldLanesA f (2 ^ (m + 1)) (halfA f (2 ^ (m + 1)))
        (mulXA (halfA f (2 ^ (m + 1))) (2 ^ m)) α β) (foldPairsA α w)
      (rounds ++ [⟨α, β⟩]) := by
  obtain ⟨hw, hf, hcols, hclaim, hlen, hW, hrows⟩ := hI
  have hpos := Nat.two_pow_pos m
  have hH := size_halfA f hf
  have hXH : (mulXA (halfA f (2 ^ (m + 1))) (2 ^ m)).size = (2 ^ κ + j + 1) * 2 ^ m := by
    rw [size_mulXA, hH, Nat.mul_div_cancel _ hpos]
  refine ⟨?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · simp [foldPairsA, hw, pow_succ, ← mul_assoc]
  · simp [foldLanesA, hXH]; ring
  · exact claim_fold f w hf (k := κ) hw (by omega) α β _ hclaim u₀ w₁ c₀ c₁ ht
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x hx
    rw [runW_fold, hW (α :: x) (by simp [hx]; omega), toList_foldPairsA, multilinearEval_cons]
  · intro p hp
    obtain ⟨hl, hv⟩ := hrows p hp
    have hfold : vfold (rounds ++ [⟨α, β⟩]) (K.ofBits p) (rowOf p) =
        foldLanes (K.ofBits p) ⟨α, β⟩ (vfold rounds (K.ofBits p) (rowOf p)) := by
      simp [vfold, List.foldl_append]
    rw [hfold]
    refine ⟨by rw [length_foldLanes, hl, pow_succ, Nat.mul_div_cancel _ (by norm_num)], ?_⟩
    intro l hl'
    rw [getD_foldLanes _ _ _ l (by rw [hl, pow_succ]; omega), hv _ (by rw [pow_succ]; omega),
      hv _ (by rw [pow_succ]; omega),
      laneVal_fold f (cols := 2 ^ κ + j) hf (by omega) α β hl' (K.ofBits p)]

/-- **A level's fold rounds follow the verifier's**, keeping the invariant. -/
theorem follows_foldRoundsA {μ lf : ℕ} {B : List E → E} {κ P : ℕ} {rowOf : ℕ → List E}
    (cs : Commits) : ∀ (n j : ℕ) (sv : WhirState) (f w : Array E) (pre : List FoldRound),
    FoldInv μ lf B κ P rowOf j n sv f w pre →
    Follows (fun cs' (a : Array E × Array E) (b : WhirState × List FoldRound) ↦ cs' = cs ∧
        b.2.length = n ∧ FoldInv μ lf B κ P rowOf (j + n) 0 b.1 a.1 a.2 (pre ++ b.2))
      (foldRoundsA n (2 ^ n) f w) (foldRounds n sv) cs
  | 0, j, sv, f, w, pre, hI => by
    simpa [foldRoundsA, foldRounds, Follows] using hI
  | n + 1, j, sv, f, w, pre, hI => by
    simp only [foldRoundsA, foldRounds, Script.bind_eq, VerifierProgram.bind_eq]
    refine Follows.bind (fun cs₁ a b h ↦ ?_) _ _ _ (follows_foldRoundA f w (2 ^ (n + 1)) sv cs)
    obtain ⟨hcs, α, β, u₀, w₁, c₀, c₁, ht, hb2, hb1, rfl⟩ := h
    obtain ⟨sv', r⟩ := b
    simp only at hb2 hb1
    subst hb2 hb1
    rw [two_pow_succ_div_two] at ht ⊢
    have hI' := hI.step α β u₀ w₁ c₀ c₁ ht
    simp only
    rw [← Script.bind_ret (foldRoundsA n (2 ^ n) _ _)]
    refine Follows.bind (fun cs₂ a' b' h' ↦ ?_) _ _ _
      (follows_foldRoundsA cs₁ n (j + 1) _ _ _ _ hI')
    obtain ⟨hcs', hl, hI''⟩ := h'
    refine ⟨hcs'.trans hcs, by simp [hl], ?_⟩
    rw [show j + (n + 1) = j + 1 + n by ring]
    simpa using hI''

/-! ## The queries -/

/-- **The query positions**: the script receives the verifier's, each below `2^depth`. -/
theorem follows_sampleQueriesS (depth : ℕ) (cs : Commits) : ∀ (fuel rem : ℕ),
    Follows (fun cs' (a b : List ℕ) ↦ cs' = cs ∧ a = b ∧ ∀ q ∈ b, q < 2 ^ depth)
      (sampleQueriesS depth fuel rem) (sampleQueriesAux depth fuel rem) cs
  | 0, rem => by simp [sampleQueriesS, sampleQueriesAux, Follows]
  | fuel + 1, rem => by
    by_cases h0 : rem = 0
    · simp [sampleQueriesS, sampleQueriesAux, h0, Follows]
    · simp only [sampleQueriesS, sampleQueriesAux, h0, ite_false, Script.bind_eq,
        VerifierProgram.bind_eq, Script.pure_eq, VerifierProgram.pure_eq]
      refine Follows.bind (fun cs₁ c c' h ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs)
      obtain ⟨hcs, rfl⟩ := h
      refine Follows.bind (fun cs₂ a b h ↦ ?_) _ _ _ (follows_sampleQueriesS depth cs₁ fuel _)
      obtain ⟨hcs', rfl, hb⟩ := h
      refine ⟨hcs'.trans hcs, rfl, fun q hq ↦ ?_⟩
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hq
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact hb q hq

/-! ## The tail sumcheck -/

theorem grindingBits_two : grindingBits 2 = 0 := by decide

/-- **The tail sumcheck follows the verifier's**: from the claim `⟨w, g⟩` on tables of `2^n`
entries, it ends at the challenges' point on the claim `w̃(r) g̃(r)`. -/
theorem follows_tail (cs : Commits) : ∀ (n : ℕ) (w g : Array E), w.size = 2 ^ n → g.size = 2 ^ n →
    Follows (fun cs' _ (b : List E × E) ↦ cs' = cs ∧ b.1.length = n ∧
        b.2 = multilinearEval w.toList b.1 * multilinearEval g.toList b.1)
      (sumcheckBy (fun st : Array E × Array E ↦ [roundC0A st.1 st.2, 0, roundC2A st.1 st.2])
        (fun st r ↦ (foldPairsA r st.1, foldPairsA r st.2)) (List.replicate n none) (w, g))
      (sumcheck (dot w.toList g.toList) 3 (List.replicate n none)) cs
  | 0, w, g, hw, hg => by
    have h1 : w.toList.length = 1 := by simp [hw]
    have h2 : g.toList.length = 1 := by simp [hg]
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp h2
    show cs = cs ∧ ([] : List E).length = 0 ∧
      dot w.toList g.toList = multilinearEval w.toList [] * multilinearEval g.toList []
    rw [ha, hb]
    simp [dot, multilinearEval]
  | n + 1, w, g, hw, hg => by
    simp only [List.replicate_succ, sumcheckBy, sumcheck, wire, roundGrind, Option.isSome_none,
      Bool.false_eq_true, ite_false, add_zero, List.length_cons,
      Nat.add_one_sub_one, grindingBits_two, Script.grindBits, ite_true, List.headD_cons,
      List.drop_succ_cons, List.drop_zero, sumcheckRoundPoly, VerifierProgram.grindProofOfWork,
      VerifierProgram.bind_eq, VerifierProgram.pure_eq, Script.sendList, Script.sampleE,
      VerifierProgram.readScalar, VerifierProgram.readScalars, VerifierProgram.sampleChallenge,
      Script.bind, VerifierProgram.bind]
    intro c
    have hW : w.toList.length = g.toList.length := by simp [hw, hg]
    have hE : Even w.toList.length := by simp [hw, pow_succ]
    have hpoly := polyEval_roundQuad c w.toList g.toList hW hE
    simp only [roundQuad, ← roundC0A_eq, ← roundC2A_eq] at hpoly
    beta_reduce
    rw [hpoly, ← toList_foldPairsA, ← toList_foldPairsA]
    have hs : ∀ t : Array E, t.size = 2 ^ (n + 1) → (foldPairsA c t).size = 2 ^ n := fun t ht ↦ by
      simp [foldPairsA, ht, pow_succ]
    refine Follows.bind (fun cs₂ _ b h ↦ ?_) _ _ _
      (follows_tail cs n (foldPairsA c w) (foldPairsA c g) (hs w hw) (hs g hg))
    obtain ⟨rfl, hl, hb⟩ := h
    refine ⟨rfl, by simp [hl], ?_⟩
    simp only [multilinearEval_cons, ← toList_foldPairsA]
    exact hb

/-! ## Reading the honest words -/

/-- `X_(2^i)(x) = Ŵ_i(x)`. -/
theorem novelAt_two_pow {i : ℕ} (hi : i < 64) (x : K) : novelAt (2 ^ i) x = normVanishingAt i x := by
  have h := novelAt_two_pow_sub i (i + 1) (by omega) (by omega) x
  rw [show 2 ^ (i + 1) - 2 ^ i = 2 ^ i by rw [pow_succ]; omega, Nat.Ico_succ_singleton,
    prod_singleton] at h
  exact h

/-- `X_(2^i + c)(x) = X_c(x) Ŵ_i(x)` for `c < 2^i`. -/
theorem novelAt_two_pow_add {i c : ℕ} (hi : i < 64) (hc : c < 2 ^ i) (x : K) :
    novelAt (2 ^ i + c) x = novelAt c x * normVanishingAt i x := by
  have h := novelAt_two_pow_mul_add i 1 c hc x
  rw [mul_one, novelAt_two_pow hi] at h
  rw [h, mul_comm]

private theorem foldl_stop (count : ℕ) : ∀ (vals : List K) (b : List K), count ≤ b.length →
    vals.foldl (fun basis value ↦
      if count ≤ basis.length then basis else basis ++ basis.map (· * value)) b = b
  | [], _, _ => rfl
  | v :: vals, b, h => by
    rw [List.foldl_cons]
    simp only [h, ↓reduceIte]
    exact foldl_stop count vals b h

private theorem novelBasis_aux (x : K) (count : ℕ) : ∀ (n i : ℕ), i + n ≤ 64 →
    count ≤ 2 ^ (i + n) →
    (((List.range' i n).map fun t ↦ normVanishingAt t x).foldl (fun basis value ↦
      if count ≤ basis.length then basis else basis ++ basis.map (· * value))
        ((List.range (2 ^ i)).map fun c ↦ novelAt c x)).take count =
      (List.range count).map fun c ↦ novelAt c x
  | 0, i, _, hc => by
    rw [List.range'_zero, List.map_nil, List.foldl_nil, ← List.map_take, List.take_range,
      min_eq_left (by simpa using hc)]
  | n + 1, i, hin, hc => by
    rw [List.range'_succ, List.map_cons, List.foldl_cons]
    by_cases hstop : count ≤ ((List.range (2 ^ i)).map fun c ↦ novelAt c x).length
    · simp only [hstop, ↓reduceIte]
      rw [foldl_stop _ _ _ hstop, ← List.map_take, List.take_range,
        min_eq_left (by simpa using hstop)]
    · simp only [hstop, ↓reduceIte]
      have hb : ((List.range (2 ^ i)).map fun c ↦ novelAt c x) ++
          ((List.range (2 ^ i)).map fun c ↦ novelAt c x).map (· * normVanishingAt i x) =
          (List.range (2 ^ (i + 1))).map fun c ↦ novelAt c x := by
        rw [pow_succ, mul_two, List.range_add, List.map_append, List.map_map, List.map_map]
        refine congrArg (_ ++ ·) (List.map_congr_left fun c hc ↦ ?_)
        simp only [Function.comp_apply]
        rw [novelAt_two_pow_add (by omega) (List.mem_range.mp hc)]
      rw [hb]
      exact novelBasis_aux x count n (i + 1) (by omega) (by rwa [show i + 1 + n = i + (n + 1) by ring])

/-- **The verifier's novel basis**: `novelBasis (subspaceAt κ x) L` is `X_0(x), …, X_(L-1)(x)` for
`L ≤ 2^(κ+1)`. -/
theorem novelBasis_subspaceAt {κ L : ℕ} (hκ : κ < 64) (hL : L ≤ 2 ^ (κ + 1)) (x : K) :
    novelBasis (subspaceAt κ x) L = (List.range L).map fun c ↦ novelAt c x := by
  have h1 : ((List.range (2 ^ 0)).map fun c ↦ novelAt c x) = [1] := by simp [novelAt]
  have := novelBasis_aux x L (κ + 1) 0 (by omega) (by simpa using hL)
  rw [h1] at this
  rw [novelBasis, subspaceAt_eq, List.range_eq_range']
  exact this

/-- **`novelEval`** is `Σ_c p_c X_c(x)`. -/
theorem novelEval_subspaceAt {κ : ℕ} (hκ : κ < 64) (p : List E) (hp : p.length ≤ 2 ^ (κ + 1))
    (x : K) :
    novelEval p (subspaceAt κ x) = ∑ c ∈ range p.length, p.getD c 0 * ofK (novelAt c x) := by
  rw [novelEval, novelBasis_subspaceAt hκ hp, sumE_eq]
  have : ∀ (q : List E) (k : ℕ),
      (List.zipWith (fun p b ↦ p * ofK b) q ((List.range' k q.length).map fun c ↦ novelAt c x)).sum =
        ∑ c ∈ range q.length, q.getD c 0 * ofK (novelAt (k + c) x) := by
    intro q
    induction q with
    | nil => simp
    | cons a q ih =>
      intro k
      rw [List.length_cons, List.range'_succ, List.map_cons, List.zipWith_cons_cons, List.sum_cons,
        ih (k + 1), sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      rw [add_comm]
      exact congrArg₂ (· + ·) (sum_congr rfl fun c _ ↦ by rw [show k + 1 + c = k + (c + 1) by ring])
        rfl
  rw [List.range_eq_range', this p 0]
  simp

/-- `laneVal` of one lane. -/
theorem laneVal_zero (t : Array E) (x : K) :
    laneVal t 0 0 x = ∑ c ∈ range t.size, t.getD c 0 * ofK (novelAt c x) := by
  simp [laneVal]

/-- An encoded lane at a position. -/
theorem encAt_laneMsg (κ k : ℕ) (t : List E) (j p : ℕ) :
    encAt κ (laneMsg κ k t j) p =
      ∑ c ∈ range (2 ^ κ), t.getD (j + 2 ^ k * c) 0 * ofK (novelAt c (K.ofBits p)) := by
  rw [encAt, sum_cube]
  refine sum_congr rfl fun c hc ↦ ?_
  rw [laneMsg, bitsToNat_testBit (mem_range.mp hc)]

/-- **The lanes' codeword entries** are the table's lanes at the point. -/
theorem laneCodes_eq (κ k : ℕ) (t : List E) (ht : t.length = 2 ^ κ * 2 ^ k) (p : ℕ) :
    (laneCodes κ k t p).length = 2 ^ k ∧ ∀ l < 2 ^ k,
      (laneCodes κ k t p).getD l 0 = laneVal t.toArray k l (K.ofBits p) := by
  refine ⟨by simp [laneCodes], fun l hl ↦ ?_⟩
  rw [laneCodes, List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
    List.getElem_range, encAt_laneMsg, laneVal]
  simp only [List.size_toArray, ht, Nat.mul_div_cancel _ (Nat.two_pow_pos k)]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    add_comm, mul_comm c]

/-! ## Gluing a level's claims -/

theorem glueLevel_eq (sv : WhirState) (lam : E) (mu : ℕ) (z : List E) (y : E)
    (qs : List ℕ) (ws : List E) (b : E) :
    glueLevel sv lam mu z y qs ws b =
      { claim := sv.claim + lam * y + lam * lam * b,
        alphas := sv.alphas,
        glued := sv.glued ++ [⟨lam, sv.alphas.length, fun x ↦ eqEval z x⟩,
          ⟨lam * lam, sv.alphas.length, Verifier.inducedWeight mu qs ws⟩] } := rfl

theorem runW_glue (B : List E → E) (lf : ℕ) (sv : WhirState) (lam : E) (mu : ℕ) (z : List E)
    (y : E) (qs : List ℕ) (ws : List E) (b : E) (x : List E) :
    runW B lf (glueLevel sv lam mu z y qs ws b) x =
      runW B lf sv x + lam * eqEval z x + lam * lam * Verifier.inducedWeight mu qs ws x := by
  rw [glueLevel_eq]
  unfold runW
  rw [List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  dsimp only
  rw [List.drop_left]

theorem toList_glued (lam : E) (W T₁ T₂ : Array E) :
    (glueTablesA lam W [T₁, T₂]).toList =
      axpy (1 * lam * lam) (axpy (1 * lam) W.toList T₁.toList) T₂.toList := by
  rw [toList_glueTablesA]
  simp [glueTables]

theorem mle_glued (lam : E) (W T₁ T₂ : Array E) (h₁ : W.size = T₁.size)
    (h₂ : W.size = T₂.size) (x : List E) :
    multilinearEval (glueTablesA lam W [T₁, T₂]).toList x =
      multilinearEval W.toList x + lam * multilinearEval T₁.toList x +
        lam * lam * multilinearEval T₂.toList x := by
  rw [toList_glued, multilinearEval_axpy _ _ _ _ (by
      rw [length_axpy _ _ _ (by simpa using h₁)]; simpa using h₂),
    multilinearEval_axpy _ _ _ _ (by simpa using h₁)]
  simp only [one_mul]

theorem dot_glued (lam : E) (W T₁ T₂ : Array E) (h₁ : W.size = T₁.size)
    (h₂ : W.size = T₂.size) (g : List E) :
    dot (glueTablesA lam W [T₁, T₂]).toList g =
      dot W.toList g + lam * dot T₁.toList g + lam * lam * dot T₂.toList g := by
  rw [toList_glued, dot_axpy _ _ _ _ (by
      rw [length_axpy _ _ _ (by simpa using h₁)]; simpa using h₂),
    dot_axpy _ _ _ _ (by simpa using h₁)]
  simp only [one_mul]

theorem size_glued (lam : E) (W T₁ T₂ : Array E) (h₁ : W.size = T₁.size)
    (h₂ : W.size = T₂.size) :
    (glueTablesA lam W [T₁, T₂]).size = W.size := by
  rw [← Array.length_toList, toList_glued,
    length_axpy _ _ _ (by rw [length_axpy _ _ _ (by simpa using h₁)]; simpa using h₂),
    length_axpy _ _ _ (by simpa using h₁)]
  simp

/-- The extension of an equality table. -/
theorem mle_eqTable (z x : List E) (hx : x.length = z.length) :
    multilinearEval (eqTable z).toList x = eqEval z x := by
  rw [toList_eqTable, eqKernel_eq_tableOf z rfl,
    multilinearEval_tableOf (isMultilinearFn_eqEval z) x hx]

/-- The extension of a query table. -/
theorem mle_queryTableA {κ : ℕ} (hκ : κ ≤ 64) (qs : List ℕ) (ws : List E) (x : List E)
    (hx : x.length = κ) :
    multilinearEval (queryTableA κ qs ws).toList x = Verifier.inducedWeight κ qs ws x := by
  rw [toList_queryTableA hκ, queryTable_eq hκ,
    multilinearEval_tableOf (isMultilinearFn_inducedWeight κ qs ws) x hx]

/-! ## A level's query batch -/

private theorem list_sum_finset_sum {α : Type} (L : List α) (s : Finset ℕ) (f : α → ℕ → E) :
    (L.map fun a ↦ ∑ i ∈ s, f a i).sum = ∑ i ∈ s, (L.map fun a ↦ f a i).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, sum_add_distrib]

/-- The verifier's batch over the opened rows as a sum over the queries. -/
theorem sumE_zipWith_rows {β : Type} (word : ℕ → β) (G : ℕ → β → E) :
    ∀ (qs : List ℕ) (ws : List E),
    sumE (List.zipWith (fun (qr : ℕ × β) (a : E) ↦ a * G qr.1 qr.2) (List.zip qs (qs.map word)) ws) =
      ((List.zip ws qs).map fun wq ↦ wq.1 * G wq.2 (word wq.2)).sum
  | [], _ => by simp [sumE]
  | _ :: _, [] => by simp [sumE]
  | q :: qs, a :: ws => by
    have ih := sumE_zipWith_rows word G qs ws
    rw [sumE_eq] at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons, List.sum_cons, ih]

/-- **The low part at a queried point**: an opened row folded by the level's rounds, less the
high part's share, is the folded lane's low part there. -/
theorem fold_add_high (p : Array E) {κ ℓ : ℕ} (hp : p.size = 2 ^ κ + ℓ) (hℓ : ℓ ≤ 2 ^ κ)
    (hκ : κ + 1 < 64) (x : K) :
    laneVal p 0 0 x + novelEval (p.extract (2 ^ κ) p.size).toList (subspaceAt κ x) *
        ofK ((subspaceAt κ x).getD κ 0) =
      ∑ c ∈ range (2 ^ κ), p.getD c 0 * ofK (novelAt c x) := by
  set high := (p.extract (2 ^ κ) p.size).toList with hhigh
  have hlen : high.length = ℓ := by simp [hhigh, hp]
  have hget : ∀ j < ℓ, high.getD j 0 = p.getD (2 ^ κ + j) 0 := fun j hj ↦ by
    have hj2 : j < (p.extract (2 ^ κ) p.size).size := by simp [hp]; omega
    rw [hhigh, Enc.array_getD_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj2,
      Option.getD_some, Array.getElem_extract, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [laneVal_zero, novelEval_subspaceAt (by omega) _ (by rw [hlen, pow_succ]; omega), hlen, hp,
    sum_range_add, subspaceAt_eq, List.getD_eq_getElem _ _ (by simp), List.getElem_map,
    List.getElem_range, sum_mul]
  have hhi : ∀ j ∈ range ℓ, high.getD j 0 * ofK (novelAt j x) * ofK (normVanishingAt κ x) =
      p.getD (2 ^ κ + j) 0 * ofK (novelAt (2 ^ κ + j) x) := by
    intro j hj
    have hj' := mem_range.mp hj
    rw [novelAt_two_pow_add (by omega) (by omega), ofK_mul, hget j hj']
    ring
  rw [sum_congr rfl hhi, add_assoc, ← two_mul, show (2 : E) = 0 from CharTwo.two_eq_zero, zero_mul,
    add_zero]

/-- **The level's query batch** is the query table paired with the folded lane's low part. -/
theorem batched_eq (L : List K → List E) (word : Word) (rounds : List FoldRound) (p : Array E)
    {κ ℓ : ℕ} (hp : p.size = 2 ^ κ + ℓ) (hℓ : ℓ ≤ 2 ^ κ) (hκ : κ + 1 < 64) (qs : List ℕ)
    (ws : List E) (hrow : ∀ q ∈ qs, foldRow (L (word q)) (K.ofBits q) rounds = laneVal p 0 0 (K.ofBits q)) :
    sumE (List.zipWith (fun (qr : ℕ × List K) (a : E) ↦ a * (foldRow (L qr.2) (K.ofBits qr.1) rounds +
        novelEval (p.extract (2 ^ κ) p.size).toList (subspaceAt κ (K.ofBits qr.1)) *
          ofK ((subspaceAt κ (K.ofBits qr.1)).getD κ 0))) (List.zip qs (qs.map word)) ws) =
      dot (queryTableA κ qs ws).toList (p.extract 0 (2 ^ κ)).toList := by
  rw [sumE_zipWith_rows word (fun q row ↦ foldRow (L row) (K.ofBits q) rounds +
    novelEval (p.extract (2 ^ κ) p.size).toList (subspaceAt κ (K.ofBits q)) *
      ofK ((subspaceAt κ (K.ofBits q)).getD κ 0))]
  rw [toList_queryTableA (by omega), dot_eq_sum _ _ (by simp [queryTable, hp])]
  simp only [queryTable, List.length_map, List.length_range]
  rw [sum_congr rfl fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ (by simpa using mem_range.mp hi), List.getElem_map,
      List.getElem_range, ← List.sum_map_mul_right]]
  rw [← list_sum_finset_sum]
  refine congrArg List.sum (List.map_congr_left fun wq hwq ↦ ?_)
  have hq := (List.of_mem_zip hwq).2
  rw [hrow _ hq, fold_add_high p hp hℓ hκ, mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  have hi2 : i < (p.extract 0 (2 ^ κ)).size := by simp [hp]; omega
  have he : (p.extract 0 (2 ^ κ)).getD i 0 = p.getD i 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi2, Option.getD_some,
      Array.getElem_extract]
    simp [Array.getD_eq_getD_getElem?, show i < p.size by omega]
  rw [Enc.array_getD_toList, he]
  ring

/-! ## The levels -/

/-- The ladder's arithmetic the honest levels use: each level folds at most its variables and at
most `2^κ` rounds (its high part fits below `X_(2^(κ+1))`), on stacks of at most `28` variables. -/
def ladderOK : ℕ → List Whir.Level → Bool
  | _, [] => false
  | mu, [level] => decide (level.fold ≤ mu) && decide (level.fold ≤ 2 ^ (mu - level.fold)) &&
      decide (mu ≤ 28)
  | mu, level :: next :: rest => decide (level.fold ≤ mu) &&
      decide (level.fold ≤ 2 ^ (mu - level.fold)) && decide (mu ≤ 28) &&
      ladderOK (mu - level.fold) (next :: rest)

/-- Every admissible ladder satisfies `ladderOK`. -/
theorem ladderOK_of_ladder {μ R : ℕ} (h : Whir.Admissible μ R) {levels : List Whir.Level}
    (hl : Whir.ladder μ R = some levels) : ladderOK μ levels = true := by
  have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
      ∀ levels, Whir.ladder μ r = some levels → ladderOK μ levels = true := by decide +kernel
  exact key μ (Nat.lt_succ_of_le h.2.1) R (Nat.lt_succ_of_le h.2.2.2) h levels hl

theorem require_bind_of {α : Type} {c : Prop} [Decidable c] (hc : c) (G : Unit → VerifierProgram α) :
    (VerifierProgram.require c).bind G = G () := by
  simp [VerifierProgram.require, hc]

theorem zip_map_self {β : Type} (f : ℕ → β) : ∀ l : List ℕ, l.zip (l.map f) = l.map fun a ↦ (a, f a)
  | [] => rfl
  | a :: l => by simp [zip_map_self f l]

/-- The rows the verifier reads at level `index`. -/
def lanesOfV (index : ℕ) (row : List K) : List E :=
  if index = 0 then row.reverse.map ofK else extRow row

theorem ladderOK_cons {mu : ℕ} {l : Whir.Level} {r : List Whir.Level} (h : ladderOK mu (l :: r) = true) :
    l.fold ≤ mu ∧ l.fold ≤ 2 ^ (mu - l.fold) ∧ mu ≤ 28 := by
  cases r with
  | nil => simp only [ladderOK, Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨h.1.1, h.1.2, h.2⟩
  | cons n r =>
    simp only [ladderOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem size_queryTableA {κ : ℕ} (hκ : κ ≤ 64) (qs : List ℕ) (ws : List E) :
    (queryTableA κ qs ws).size = 2 ^ κ := by
  rw [← Array.length_toList, toList_queryTableA hκ]; simp [queryTable]

theorem getD_extract_low (p : Array E) {n i : ℕ} (hn : n ≤ p.size) (hi : i < n) :
    (p.extract 0 n).getD i 0 = p.getD i 0 := by
  have hi2 : i < (p.extract 0 n).size := by simp; omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi2, Option.getD_some,
    Array.getElem_extract]
  simp [Array.getD_eq_getD_getElem?, show i < p.size by omega]

/-- **The next level's invariant** after gluing the level's claims. -/
theorem foldInv_next {μ lf : ℕ} {B : List E → E} {κ ℓ ℓ' R' : ℕ} (hℓ' : ℓ' ≤ κ) (hκ : κ ≤ 28)
    {sv' : WhirState} {p w' : Array E} (hp' : p.size = 2 ^ κ + ℓ) (hw' : w'.size = 2 ^ κ)
    (hclaim : sv'.claim = ∑ i ∈ range w'.size, w'.getD i 0 * p.getD i 0)
    (hlen : sv'.alphas.length + κ = μ)
    (hW : ∀ x, x.length = κ → runW B lf sv' x = multilinearEval w'.toList x)
    (z : List E) (hz : z.length = κ) (lam : E) (qs : List ℕ) (b : E)
    (hb : b = dot (queryTableA κ qs (powers lam qs.length)).toList (p.extract 0 (2 ^ κ)).toList)
    (rowOf : ℕ → List E)
    (hrow : ∀ q < 2 ^ (κ - ℓ' + R'), rowOf q = laneCodes (κ - ℓ') ℓ' (p.extract 0 (2 ^ κ)).toList q) :
    FoldInv μ lf B (κ - ℓ') (2 ^ (κ - ℓ' + R')) rowOf 0 ℓ'
      (glueLevel sv' lam κ z (dotA (p.extract 0 (2 ^ κ)) (eqTable z)) qs (powers lam qs.length) b)
      (p.extract 0 (2 ^ κ))
      (glueTablesA lam w' [eqTable z, queryTableA κ qs (powers lam qs.length)]) [] := by
  set low := p.extract 0 (2 ^ κ) with hlow
  have hlowsz : low.size = 2 ^ κ := by simp [hlow, hp']
  have hsplit : 2 ^ κ = 2 ^ (κ - ℓ') * 2 ^ ℓ' := by rw [← pow_add, Nat.sub_add_cancel hℓ']
  have he₁ : (eqTable z).size = 2 ^ κ := by rw [size_eqTable, hz]
  have hT := size_queryTableA (by omega : κ ≤ 64) qs (powers lam qs.length)
  have hgsz := size_glued lam w' (eqTable z) (queryTableA κ qs (powers lam qs.length))
    (by rw [hw', he₁]) (by rw [hw', hT])
  have hdot : ∀ T : Array E, T.size = 2 ^ κ →
      ∑ i ∈ range T.size, T.getD i 0 * low.getD i 0 = dot T.toList low.toList := fun T hTs ↦ by
    rw [dot_eq_sum _ _ (by simp [hTs, hlowsz])]
    exact sum_congr rfl fun i _ ↦ by rw [Enc.array_getD_toList, Enc.array_getD_toList]
  refine ⟨by rw [hgsz, hw', hsplit], by rw [hlowsz, hsplit]; ring, ?_, ?_, ?_, ?_, ?_⟩
  · have : 2 ^ (κ - ℓ') ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 28 + 28 ≤ 2 ^ 61 := by norm_num
    omega
  · rw [glueLevel_eq, hdot _ (by rw [hgsz, hw']),
      dot_glued lam w' _ _ (by rw [hw', he₁]) (by rw [hw', hT]), hclaim, hb]
    have hc : ∑ i ∈ range w'.size, w'.getD i 0 * p.getD i 0 = dot w'.toList low.toList := by
      rw [← hdot w' hw']
      exact sum_congr rfl fun i hi ↦ by
        rw [hlow, getD_extract_low p (by rw [hp']; omega) (by rw [← hw']; exact mem_range.mp hi)]
    have hy : ∀ T : Array E, T.size = 2 ^ κ → dotA low T = dot T.toList low.toList := fun T hTs ↦ by
      rw [dotA, sumRange_eq, dot_eq_sum _ _ (by simp [hTs, hlowsz]), hlowsz, hTs, min_self]
      simp only [Array.length_toList, hTs]
      exact sum_congr rfl fun i _ ↦ by rw [Enc.array_getD_toList, Enc.array_getD_toList, mul_comm]
    rw [hc, hy _ he₁]
  · rw [glueLevel_eq]; simp only; omega
  · intro x hx
    rw [runW_glue, hW x (by omega),
      mle_glued lam w' _ _ (by rw [hw', he₁]) (by rw [hw', hT]),
      mle_eqTable z x (by omega), mle_queryTableA (by omega) qs _ x (by omega)]
  · intro q hq
    rw [hrow q hq]
    have h := laneCodes_eq (κ - ℓ') ℓ' low.toList (by simp [hlowsz, hsplit]) q
    refine ⟨h.1, fun l hl ↦ ?_⟩
    rw [vfold, List.foldl_nil, h.2 l hl, Array.toArray_toList]

/-- **The honest levels follow the verifier's.** -/
theorem follows_levelsA (μ lf : ℕ) (B : List E → E) :
    ∀ (levels : List Whir.Level) (index mu : ℕ) (f w : Array E) (sv : WhirState) (cs : Commits)
      (word : Word) (width : ℕ), ladderOK mu levels = true → cs.length = index + 1 →
      (∀ level ∈ levels.head?, cs[index]? = some (mu - level.fold + level.logInvRate, width, word) ∧
        FoldInv μ lf B (mu - level.fold) (2 ^ (mu - level.fold + level.logInvRate))
          (fun p ↦ lanesOfV index (word p)) 0 level.fold sv f w []) →
      Follows (fun _ _ _ ↦ True) (levelsA mu levels f w) (whirLevels μ lf B index levels sv) cs
  | [], _, _, _, _, _, _, _, _, hok, _, _ => by simp [ladderOK] at hok
  | level :: rest, index, mu, f, w, sv, cs, word, width, hok, hcs, hpre => by
    obtain ⟨hcsi, hI⟩ := hpre level rfl
    unfold levelsA whirLevels
    simp only [Script.bind_eq, VerifierProgram.bind_eq]
    refine Follows.bind (fun cs₁ a b h ↦ ?_) _ _ _
      (follows_foldRoundsA (μ := μ) cs level.fold 0 sv f w [] hI)
    obtain ⟨hcs₁, hrl, hI'⟩ := h
    subst hcs₁
    obtain ⟨p, w'⟩ := a
    obtain ⟨sv', rounds⟩ := b
    simp only [Nat.zero_add, List.nil_append] at hrl hI' ⊢
    set κ := mu - level.fold with hκ
    obtain ⟨hw', hp', hcols, hclaim, hlen, hW, hrows⟩ := hI'
    have hmu : μ - sv'.alphas.length = κ := by omega
    rw [hmu]
    have hrow0 : ∀ q < 2 ^ (κ + level.logInvRate),
        foldRow (lanesOfV index (word q)) (K.ofBits q) rounds = laneVal p 0 0 (K.ofBits q) := by
      intro q hq
      obtain ⟨hl1, hv⟩ := hrows q hq
      rw [foldRow, ← hv 0 (by simp)]
      obtain ⟨v, hv'⟩ := List.length_eq_one_iff.mp (by simpa using hl1)
      simp only [vfold] at hv'
      rw [vfold, hv']
      rfl
    have hans : ∀ qs : List ℕ, (∀ q ∈ qs, q < 2 ^ (κ + level.logInvRate)) →
        answerOf cs₁ index qs = some (qs.map word) := by
      intro qs hqs
      rw [answerOf, hcsi, Option.map_some]
      exact congrArg some (List.map_congr_left fun q hq ↦ by
        simp only; rw [Nat.mod_eq_of_lt (hqs q hq)])
    cases rest with
    | nil =>
      dsimp only
      have hplen : p.toList.length = 2 ^ κ + level.fold := by simp [hp']
      rw [← hplen]
      refine Follows.bind (fun cs₂ _ folded h ↦ ?_) _ _ _ (Follows.sendList_readN cs₁ p.toList)
      obtain ⟨rfl, rfl⟩ := h
      refine Follows.bind (fun cs₃ _ _ h ↦ ?_) _ _ _ (Follows.grindBits_grindP _ cs₂)
      subst h
      rw [sampleQueries]
      refine Follows.bind (fun cs₄ _ queries h ↦ ?_) _ _ _ (follows_sampleQueriesS _ cs₃ _ _)
      obtain ⟨rfl, rfl, hq⟩ := h
      refine Follows.bind (fun cs₅ _ words h ↦ ?_) _ _ _ (Follows.queryS_queryP (hans _ hq))
      obtain ⟨rfl, -, rfl⟩ := h
      rw [require_bind_of]
      · unfold tailA
        have hg : (p.extract 0 (2 ^ κ)).size = 2 ^ κ := by simp [hp']
        have hgD : ∀ i < 2 ^ κ, (p.extract 0 (2 ^ κ)).getD i 0 = p.getD i 0 := fun i hi ↦ by
          have hi2 : i < (p.extract 0 (2 ^ κ)).size := by rw [hg]; exact hi
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi2, Option.getD_some,
            Array.getElem_extract]
          simp [Array.getD_eq_getD_getElem?, show i < p.size by rw [hp']; omega]
        have hcl : sv'.claim = dot w'.toList (p.extract 0 (2 ^ κ)).toList := by
          rw [hclaim, dot_eq_sum _ _ (by rw [Array.length_toList, Array.length_toList, hw', hg]; simp)]
          simp only [Array.length_toList, hw', pow_zero, mul_one]
          exact sum_congr rfl fun i hi ↦ by
            rw [Enc.array_getD_toList, Enc.array_getD_toList, hgD i (mem_range.mp hi)]
        rw [hcl]
        refine Follows.bind (fun cs₆ _ b h ↦ ?_) _ _ _
          (follows_tail cs₅ κ w' (p.extract 0 (2 ^ κ)) (by simp [hw']) hg)
        obtain ⟨-, hbl, hb⟩ := h
        refine Follows.ret_require ?_ trivial
        have ht : List.take (2 ^ κ) p.toList = (p.extract 0 (2 ^ κ)).toList := by
          simp [Array.toList_extract]
        change runW B lf sv' b.1 * _ = _
        rw [hW b.1 (by simp [hbl]), ht, hb]
      · simp only [lanesOfV] at hrow0
        have hl := hok
        simp only [ladderOK, Bool.and_eq_true, decide_eq_true_eq] at hl
        rw [zip_map_self, List.all_eq_true]
        intro x hx
        obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hx
        refine decide_eq_true ?_
        have h2 : level.fold ≤ 2 ^ κ := hl.1.2
        have h3 : mu ≤ 28 := hl.2
        rw [hrow0 q (hq q hq'), novelEval_subspaceAt (by omega) _ (by
            rw [hplen, pow_succ]; omega), laneVal_zero]
        simp only [hplen, Enc.array_getD_toList]
        rw [hp']; simp
    | cons next rest' =>
      dsimp only
      simp only [levelShape]
      obtain ⟨h1, h2, h28⟩ := ladderOK_cons hok
      have hok' : ladderOK κ (next :: rest') = true := by
        rw [ladderOK] at hok
        simp only [Bool.and_eq_true] at hok
        exact hok.2
      obtain ⟨hn1, -, -⟩ := ladderOK_cons hok'
      have hp'' : p.size = 2 ^ κ + level.fold := by rw [hp']; ring
      have hw'' : w'.size = 2 ^ κ := by rw [hw']; ring
      have hlowsz : (p.extract 0 (2 ^ κ)).size = 2 ^ κ := by simp [hp'']
      have hwf := levelWordFast_eq (κ := κ - next.fold) (by omega) next.fold next.logInvRate
        (p.extract 0 (2 ^ κ))
      refine Follows.bind (fun cs₂ _ _ h ↦ ?_) _ _ _
        (Follows.commitS_commitP (hwf ▸ wellShaped_levelWord _ _ _ _) cs₁)
      subst h
      have hhl : (p.extract (2 ^ κ) p.size).toList.length = level.fold := by simp [hp'']
      have hsend := Follows.sendList_readN (cs₁ ++ [(κ - next.fold + next.logInvRate,
        2 * 2 ^ next.fold, levelWordFast (κ - next.fold) next.fold next.logInvRate
          (p.extract 0 (2 ^ κ)))]) (p.extract (2 ^ κ) p.size).toList
      rw [hhl] at hsend
      refine Follows.bind (fun cs₃ _ high h ↦ ?_) _ _ _ hsend
      obtain ⟨rfl, rfl⟩ := h
      refine Follows.bind (fun cs₃' _ _ h ↦ ?_) _ _ _ (Follows.grindBits_grindP _ _)
      subst h
      refine Follows.bind (fun cs₄ z z' h ↦ ?_) _ _ _ (Follows.sampleN_sampleN _ κ)
      obtain ⟨rfl, rfl, hz⟩ := h
      have hood := Follows.sendE_readE (dotA (p.extract 0 (2 ^ κ)) (eqTable z))
        (cs₁ ++ [(κ - next.fold + next.logInvRate, 2 * 2 ^ next.fold,
          levelWordFast (κ - next.fold) next.fold next.logInvRate (p.extract 0 (2 ^ κ)))])
      refine Follows.bind (fun cs₆ _ y h ↦ ?_) _ _ _ hood
      obtain ⟨rfl, rfl⟩ := h
      refine Follows.bind (fun cs₇ _ _ h ↦ ?_) _ _ _ (Follows.grindBits_grindP _ _)
      subst h
      rw [sampleQueries]
      refine Follows.bind (fun cs₈ queries queries' h ↦ ?_) _ _ _ (follows_sampleQueriesS _ _ _ _)
      obtain ⟨rfl, rfl, hq⟩ := h
      refine Follows.bind (fun cs₁₀ lam lam' h ↦ ?_) _ _ _ (Follows.sampleE_sampleE _)
      obtain ⟨rfl, rfl⟩ := h
      have hans' : answerOf (cs₁ ++ [(κ - next.fold + next.logInvRate,
          2 * 2 ^ next.fold, levelWordFast (κ - next.fold) next.fold next.logInvRate
            (p.extract 0 (2 ^ κ)))]) index queries = some (queries.map word) := by
        rw [answerOf, List.getElem?_append_left (by omega), hcsi, Option.map_some]
        exact congrArg some (List.map_congr_left fun q hq' ↦ by
          simp only; rw [Nat.mod_eq_of_lt (hq q hq')])
      refine Follows.bind (fun cs₁₁ _ words h ↦ ?_) _ _ _ (Follows.queryS_queryP hans')
      obtain ⟨rfl, -, rfl⟩ := h
      refine follows_levelsA μ lf B (next :: rest') (index + 1) κ (p.extract 0 (2 ^ κ)) _ _ _
        (levelWordFast (κ - next.fold) next.fold next.logInvRate (p.extract 0 (2 ^ κ)))
        (2 * 2 ^ next.fold) hok' (by simp [hcs]) ?_
      intro level' hl'
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hl'
      subst hl'
      refine ⟨by rw [List.getElem?_append_right (by omega)]; simp [hcs], ?_⟩
      refine foldInv_next hn1 (by omega) hp'' hw'' hclaim (by omega)
        (fun x hx ↦ hW x (by simpa using hx)) z hz lam queries _ ?_ _ ?_
      · exact (batched_eq (lanesOfV index) word rounds p hp'' h2 (by omega) queries _
          fun q hq' ↦ hrow0 q (hq q hq'))
      · intro q hq'
        simp only [lanesOfV, Nat.add_one_ne_zero, ite_false]
        rw [hwf, extRow_levelWord _ _ _ _ hq']

end
end LeanVM.Protocol.Whir.Complete
