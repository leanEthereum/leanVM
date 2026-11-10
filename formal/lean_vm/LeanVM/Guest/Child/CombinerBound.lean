/-
  LeanVM.Guest.Child.CombinerBound

  The ideal failure probability of the statement's refusing verifier: a vanishing fold combiner
  at a queried point with probability `|E|⁻¹` per round and query, a zero challenge `|E|⁻¹` per
  sample.
-/

module

public import LeanVM.Protocol.Compile.Rom.IdealCalc
public import LeanVM.Guest.Child.Combiner
public import LeanVM.Protocol.Verifier.Deferred

/-!
# The refusing verifier's ideal failure probability

Against challenges uniform and independent, a round's combiner `α + β·x` vanishes at a point `x`
the level queries with probability `|E|⁻¹`: the point is drawn after `α` and `β`, and for every
`x` and `β` exactly one `α` makes it vanish. The rounds' challenges are drawn by `foldRound`
(`exp0_foldRound_le`), the points by `sampleQueries` (`avg2_queryHits_le`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Guest.Completeness Strategy
open scoped ENNReal

@[expose] public section

variable {S : Strategy}

/-- The uniform average of a function of two challenges, the first outer. -/
noncomputable def avg2 (φ : E → E → ℝ≥0∞) : ℝ≥0∞ :=
  avgE fun a ↦ avgE fun b ↦ φ a b

/-! ## The rounds' challenges -/

/-- **A fold round draws `α` and `β` uniform and independent.** -/
theorem exp0_foldRound_le (φ : E → E → ℝ≥0∞) (s : WhirState) (h : List Ev) (g : Option E) :
    S.exp0 (foldRound s) h g (fun p _ _ ↦ φ p.2.alpha p.2.beta) ≤ avg2 φ := by
  unfold foldRound
  iterate 8 refine exp0_bind_le (fun _ _ _ ↦ ?_) _ _ _
  rename_i h' g'
  rcases g' with _ | c
  · simp only [VerifierProgram.sampleChallenge, VerifierProgram.bind_eq, VerifierProgram.bind,
      VerifierProgram.pure_eq, exp0]
    rw [avgE_const]
    exact le_rfl
  · simp only [VerifierProgram.sampleChallenge, VerifierProgram.bind_eq, VerifierProgram.bind,
      VerifierProgram.pure_eq, exp0]
    rfl

/-- **A level's fold rounds**: `n` rounds, each `α, β` uniform and independent. -/
theorem exp0_foldRounds_le (φ : E → E → ℝ≥0∞) :
    ∀ (n : ℕ) (s : WhirState) (h : List Ev) (g : Option E),
      S.exp0 (foldRounds n s) h g (fun p _ _ ↦ (p.2.map fun r ↦ φ r.alpha r.beta).sum) ≤
        n * avg2 φ
  | 0, s, h, g => by simp [foldRounds, exp0]
  | n + 1, s, h, g => by
    rw [foldRounds, VerifierProgram.bind_eq, exp0_bind]
    calc S.exp0 (foldRound s) h g (fun p h' g' ↦ S.exp0 (match p with
          | (s, round) => do
            let (s, rounds) ← foldRounds n s
            return (s, round :: rounds)) h' g'
            (fun p _ _ ↦ (p.2.map fun r ↦ φ r.alpha r.beta).sum))
        ≤ S.exp0 (foldRound s) h g (fun p _ _ ↦ φ p.2.alpha p.2.beta + n * avg2 φ) := by
          refine exp0_mono (fun p h' g' ↦ ?_) _ _ _
          obtain ⟨s', r⟩ := p
          dsimp only
          rw [VerifierProgram.bind_eq, exp0_bind]
          calc S.exp0 (foldRounds n s') h' g' (fun q h'' g'' ↦ S.exp0 (match q with
                | (s, rounds) => (return (s, r :: rounds) : VerifierProgram _)) h'' g''
                (fun p _ _ ↦ (p.2.map fun r ↦ φ r.alpha r.beta).sum))
              = S.exp0 (foldRounds n s') h' g' (fun q _ _ ↦ φ r.alpha r.beta +
                  (q.2.map fun r ↦ φ r.alpha r.beta).sum) := by
                congr 1
            _ ≤ φ r.alpha r.beta + n * avg2 φ := by
                rw [exp0_add]
                exact add_le_add (exp0_const_le _ _ _ _) (exp0_foldRounds_le φ n s' h' g')
      _ ≤ avg2 φ + n * avg2 φ := by
          rw [exp0_add]
          exact add_le_add (exp0_foldRound_le φ s h g) (exp0_const_le _ _ _ _)
      _ = _ := by push_cast; ring

/-- A fold round adds one `γ`. -/
theorem returns_foldRound {s : WhirState} {p : WhirState × FoldRound}
    (h : VerifierProgram.Returns (foldRound s) p) : p.1.gammas.length = s.gammas.length + 1 := by
  unfold foldRound at h
  repeat (obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h)
  rw [VerifierProgram.returns_ret h]
  simp

/-- A level's fold rounds add one `γ` each. -/
theorem returns_foldRounds : ∀ {n : ℕ} {s : WhirState} {p : WhirState × List FoldRound},
    VerifierProgram.Returns (foldRounds n s) p → p.1.gammas.length = s.gammas.length + n
  | 0, s, p, h => by
    rw [foldRounds] at h
    rw [VerifierProgram.returns_ret h]
    rfl
  | n + 1, s, p, h => by
    rw [foldRounds] at h
    obtain ⟨⟨s', r⟩, h1, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨⟨s'', rs⟩, h2, h⟩ := VerifierProgram.returns_bind h
    rw [VerifierProgram.returns_ret h]
    rw [returns_foldRounds h2, returns_foldRound h1]
    omega

/-! ## The queried points -/

/-- **A run of `sampleQueriesAux` does not read the history.** -/
theorem exp0_sQA_hist (d : ℕ) : ∀ (fuel rem : ℕ) (C : List ℕ → Option E → ℝ≥0∞)
    (h h' : List Ev) (g : Option E),
    S.exp0 (sampleQueriesAux d fuel rem) h g (fun qs _ g ↦ C qs g) =
      S.exp0 (sampleQueriesAux d fuel rem) h' g (fun qs _ g ↦ C qs g)
  | 0, rem, C, h, h', g => rfl
  | fuel + 1, rem, C, h, h', g => by
    rw [sampleQueriesAux]
    split
    · rfl
    · simp only [VerifierProgram.sampleChallenge, VerifierProgram.bind_eq, VerifierProgram.bind]
      rcases g with _ | c
      · simp only [exp0]
        refine congrArg avgE (funext fun e ↦ ?_)
        simp only [exp0_bind]
        exact exp0_sQA_hist d fuel _ _ _ _ none
      · simp only [exp0, exp0_bind]
        exact exp0_sQA_hist d fuel _ _ _ _ none

/-- A run of `sampleQueriesAux` returns at most `rem` positions. -/
theorem exp0_sQA_length (d : ℕ) (x : ℝ≥0∞) : ∀ (fuel rem : ℕ) (h : List Ev) (g : Option E),
    S.exp0 (sampleQueriesAux d fuel rem) h g (fun qs _ _ ↦ qs.length * x) ≤ rem * x
  | 0, rem, h, g => by simp [sampleQueriesAux, exp0]
  | fuel + 1, rem, h, g => by
    rw [sampleQueriesAux]
    split
    · simp [exp0]
    · rename_i hrem
      simp only [VerifierProgram.sampleChallenge, VerifierProgram.bind_eq, VerifierProgram.bind]
      have key : ∀ (L : List ℕ) (h' : List Ev), L.length = min (128 / d) rem →
          S.exp0 ((sampleQueriesAux d fuel (rem - min (128 / d) rem)).bind fun rest ↦
            VerifierProgram.ret (L ++ rest)) h' none (fun qs _ _ ↦ qs.length * x) ≤ rem * x := by
        intro L h' hL
        rw [exp0_bind]
        calc S.exp0 (sampleQueriesAux d fuel (rem - min (128 / d) rem)) h' none
              (fun rest h'' g'' ↦ S.exp0 (VerifierProgram.ret (L ++ rest)) h'' g''
                (fun qs _ _ ↦ qs.length * x))
            = S.exp0 (sampleQueriesAux d fuel (rem - min (128 / d) rem)) h' none
                (fun rest _ _ ↦ L.length * x + rest.length * x) := by
              congr 1
              funext rest h'' g''
              simp [exp0, add_mul]
          _ ≤ L.length * x + (rem - min (128 / d) rem : ℕ) * x := by
              rw [exp0_add]
              exact add_le_add (exp0_const_le _ _ _ _) (exp0_sQA_length d x fuel _ h' none)
          _ = rem * x := by
              rw [hL, ← add_mul]
              congr 1
              norm_cast
              omega
      rcases g with _ | c
      · simp only [exp0]
        exact avgE_le_const fun e ↦ key _ _ (by simp)
      · exact key _ _ (by simp)

/-- After a grind, the waiting challenge is the first sample's: averaging it is drawing it. -/
theorem avg_exp0_sQA_ground (d fuel rem : ℕ) (hrem : rem ≠ 0)
    (C : List ℕ → List Ev → Option E → ℝ≥0∞) (h : List Ev) :
    avgE (fun c ↦ S.exp0 (sampleQueriesAux d (fuel + 1) rem) h (some c) C) =
      S.exp0 (sampleQueriesAux d (fuel + 1) rem) h none C := by
  rw [sampleQueriesAux]
  simp only [hrem, ↓reduceIte]
  rfl

/-- The queried points at which the combiner `a + b·X` vanishes, counted. -/
noncomputable def hits (a b : E) (qs : List ℕ) : ℝ≥0∞ :=
  (qs.map fun q ↦ if a + b * ofK (K.ofBits q) = 0 then 1 else 0).sum

/-- A vanishing combiner at some queried point is a hit of some round. -/
theorem ind_not_combinersNonzero_le (qs : List ℕ) (rounds : List FoldRound) :
    (if CombinersNonzero qs rounds then 0 else 1 : ℝ≥0∞) ≤
      (rounds.map fun r ↦ hits r.alpha r.beta qs).sum := by
  split
  · exact bot_le
  · rename_i hn
    simp only [CombinersNonzero, not_forall, not_not, exists_prop] at hn
    obtain ⟨q, hq, r, hr, h0⟩ := hn
    have h1 : (1 : ℝ≥0∞) ≤ hits r.alpha r.beta qs := by
      have := List.single_le_sum (fun _ _ ↦ bot_le)
        (if r.alpha + r.beta * ofK (K.ofBits q) = 0 then (1 : ℝ≥0∞) else 0)
        (List.mem_map_of_mem (f := fun q ↦ if r.alpha + r.beta * ofK (K.ofBits q) = 0
          then (1 : ℝ≥0∞) else 0) hq)
      simp only [h0, ↓reduceIte] at this
      exact this
    exact h1.trans (List.single_le_sum (fun _ _ ↦ bot_le) _ (List.mem_map_of_mem hr))

/-- The expected hits of one round's combiner at a level's queried points. -/
noncomputable def queryHits (S : Strategy) (d q : ℕ) (a b : E) : ℝ≥0∞ :=
  S.exp0 (sampleQueries d q) [] none (fun qs _ _ ↦ hits a b qs)

/-- **A level's queried points miss every round's combiner** but with the rounds' expected
hits. -/
theorem exp0_notCombinersNonzero_le (d q : ℕ) (rounds : List FoldRound) (h : List Ev) :
    S.exp0 (sampleQueries d q) h none
        (fun qs _ _ ↦ if CombinersNonzero qs rounds then 0 else 1) ≤
      (rounds.map fun r ↦ queryHits S d q r.alpha r.beta).sum := by
  have hmono : ∀ (qs : List ℕ) (_ : List Ev) (_ : Option E),
      (if CombinersNonzero qs rounds then 0 else 1 : ℝ≥0∞) ≤
        (rounds.map fun r ↦ hits r.alpha r.beta qs).sum :=
    fun qs _ _ ↦ ind_not_combinersNonzero_le qs rounds
  have h1 := exp0_mono (S := S) hmono (sampleQueries d q) h none
  refine h1.trans (le_of_eq ?_)
  refine (exp0_list_sum rounds (fun r qs _ _ ↦ hits r.alpha r.beta qs) (sampleQueries d q) h
    none).trans ?_
  refine congrArg List.sum (List.map_congr_left fun r _ ↦ ?_)
  exact exp0_sQA_hist d q q (fun qs _ ↦ hits r.alpha r.beta qs) h [] none

/-- **A round's combiner vanishes at a queried point with probability `|E|⁻¹`**, per query. -/
theorem avg2_queryHits_le (d q : ℕ) : avg2 (queryHits S d q) ≤ q * epsE := by
  unfold avg2 queryHits
  have e1 : (fun a ↦ avgE fun b ↦ S.exp0 (sampleQueries d q) [] none (fun qs _ _ ↦ hits a b qs)) =
      fun a ↦ S.exp0 (sampleQueries d q) [] none (fun qs _ _ ↦ avgE fun b ↦ hits a b qs) :=
    funext fun a ↦ avg_exp0 (fun b qs _ _ ↦ hits a b qs) _ _ _
  rw [e1, avg_exp0 (fun a qs _ _ ↦ avgE fun b ↦ hits a b qs)]
  refine (exp0_mono (C' := fun qs _ _ ↦ qs.length * epsE) (fun qs _ _ ↦ ?_) _ _ _).trans
    (exp0_sQA_length d _ q q [] none)
  exact avgE_avgE_list_le (fun q a b ↦ if a + b * ofK (K.ofBits q) = 0 then 1 else 0) epsE qs
    fun x _ ↦ avgE_avgE_combiner _

end
end LeanVM.Guest.Child
