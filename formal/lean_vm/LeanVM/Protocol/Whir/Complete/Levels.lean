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
        ∃ θ γ α β u₀ v₀ c₀ v₁ c₁,
          roundTableA f w s (premixA f s θ) (mulXA (premixA f s θ) (s / 2)) = [u₀, v₀, c₀, v₁, c₁] ∧
          b.2 = ⟨θ, α, β⟩ ∧
          b.1 = { sv with claim := (1 + γ) * (u₀ + α * v₀ + β * c₀) +
              γ * ((sv.claim + v₀ + θ * u₀) + α * v₁ + β * c₁), gammas := sv.gammas ++ [γ] } ∧
          a = (foldLanesA f s (premixA f s θ) (mulXA (premixA f s θ) (s / 2)) α β,
            foldPairsA γ w))
      (foldRoundA f w s) (foldRound sv) cs := by
  simp only [foldRoundA, foldRound, Script.grindBits, VerifierProgram.grindProofOfWork,
    Whir.foldGrindingBits, roundTableA, Script.bind_eq, VerifierProgram.bind_eq, Script.pure_eq,
    VerifierProgram.pure_eq, Script.grindS, Script.sampleE, Script.sendList,
    VerifierProgram.readScalar, VerifierProgram.sampleChallenge, Script.bind, VerifierProgram.bind]
  intro θ γ α β
  exact ⟨rfl, θ, γ, α, β, _, _, _, _, _, rfl, rfl, rfl, rfl⟩

/-! ## The invariant of a level's fold rounds -/

/-- The verifier's weight at the remaining point `x`, the terminal check's `weight` at
`point = gammas ++ x`. -/
def runW (B : List E → E) (lf : ℕ) (sv : WhirState) (x : List E) : E :=
  sv.glued.foldl (fun weight glued ↦ weight + glued.scalar * glued.weightAt
      ((sv.gammas ++ x).drop glued.foldStart))
    (B ((sv.gammas ++ x).drop lf ++ (sv.gammas ++ x).take lf))

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
  sv.gammas.length + κ + m = μ ∧
  (∀ x, x.length = κ + m → runW B lf sv x = multilinearEval w.toList x) ∧
  ∀ p < P, (vfold rounds (K.ofBits p) (rowOf p)).length = 2 ^ m ∧
    ∀ l < 2 ^ m, (vfold rounds (K.ofBits p) (rowOf p)).getD l 0 = laneVal f m l (K.ofBits p)

theorem runW_fold (B : List E → E) (lf : ℕ) (sv : WhirState) (c γ : E) (x : List E) :
    runW B lf { sv with claim := c, gammas := sv.gammas ++ [γ] } x = runW B lf sv (γ :: x) := by
  simp [runW]

/-- **A round keeps the invariant.** -/
theorem FoldInv.step {μ lf : ℕ} {B : List E → E} {κ P : ℕ} {rowOf : ℕ → List E} {j m : ℕ}
    {sv : WhirState} {f w : Array E} {rounds : List FoldRound}
    (hI : FoldInv μ lf B κ P rowOf j (m + 1) sv f w rounds) (θ γ α β u₀ v₀ c₀ v₁ c₁ : E)
    (ht : roundTableA f w (2 ^ (m + 1)) (premixA f (2 ^ (m + 1)) θ)
      (mulXA (premixA f (2 ^ (m + 1)) θ) (2 ^ m)) = [u₀, v₀, c₀, v₁, c₁]) :
    FoldInv μ lf B κ P rowOf (j + 1) m
      { sv with claim := (1 + γ) * (u₀ + α * v₀ + β * c₀) +
          γ * ((sv.claim + v₀ + θ * u₀) + α * v₁ + β * c₁), gammas := sv.gammas ++ [γ] }
      (foldLanesA f (2 ^ (m + 1)) (premixA f (2 ^ (m + 1)) θ)
        (mulXA (premixA f (2 ^ (m + 1)) θ) (2 ^ m)) α β) (foldPairsA γ w)
      (rounds ++ [⟨θ, α, β⟩]) := by
  obtain ⟨hw, hf, hcols, hclaim, hlen, hW, hrows⟩ := hI
  have hpos := Nat.two_pow_pos m
  have hH := size_premixA f hf θ
  have hXH : (mulXA (premixA f (2 ^ (m + 1)) θ) (2 ^ m)).size = (2 ^ κ + j + 1) * 2 ^ m := by
    rw [size_mulXA, hH, Nat.mul_div_cancel _ hpos]
  refine ⟨?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · simp [foldPairsA, hw, pow_succ, ← mul_assoc]
  · simp [foldLanesA, hXH]; ring
  · exact claim_fold f w hf (k := κ) hw (by omega) θ γ α β _ hclaim u₀ v₀ c₀ v₁ c₁ ht
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x hx
    rw [runW_fold, hW (γ :: x) (by simp [hx]; omega), toList_foldPairsA, multilinearEval_cons]
  · intro p hp
    obtain ⟨hl, hv⟩ := hrows p hp
    have hfold : vfold (rounds ++ [⟨θ, α, β⟩]) (K.ofBits p) (rowOf p) =
        foldLanes (K.ofBits p) ⟨θ, α, β⟩ (vfold rounds (K.ofBits p) (rowOf p)) := by
      simp [vfold, List.foldl_append]
    rw [hfold]
    refine ⟨by rw [length_foldLanes, hl, pow_succ, Nat.mul_div_cancel _ (by norm_num)], ?_⟩
    intro l hl'
    rw [getD_foldLanes _ _ _ l (by rw [hl, pow_succ]; omega), hv _ (by rw [pow_succ]; omega),
      hv _ (by rw [pow_succ]; omega),
      laneVal_fold f (cols := 2 ^ κ + j) hf (by omega) θ α β hl' (K.ofBits p)]

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
    obtain ⟨hcs, θ, γ, α, β, u₀, v₀, c₀, v₁, c₁, ht, hb2, hb1, rfl⟩ := h
    obtain ⟨sv', r⟩ := b
    simp only at hb2 hb1
    subst hb2 hb1
    rw [two_pow_succ_div_two] at ht ⊢
    have hI' := hI.step θ γ α β u₀ v₀ c₀ v₁ c₁ ht
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

end
end LeanVM.Protocol.Whir.Complete
