/-
  LeanVM.Protocol.Whir.Complete.Levels

  The honest WHIR levels follow the verifier's: the fold rounds, a non-final level's commitment,
  out-of-domain values, queries and glue, and the final level's check and tail sumcheck.
-/

module

public import LeanVM.Protocol.Whir.Complete.Rounds
public import LeanVM.Protocol.Whir.Complete.Script

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

end
end LeanVM.Protocol.Whir.Complete
