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
public import LeanVM.Protocol.Compile.Cost

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

/-! ## A level's check -/

/-- The query grind is a proof of work. -/
theorem grindPoW_query : VerifierProgram.grindProofOfWork Whir.queryGrindingBits =
    VerifierProgram.grind Whir.queryGrindingBits (VerifierProgram.ret ()) := rfl

/-- **The query grind, the queried points and the check that no combiner vanishes there**: the
check fails, against a uniform waiting challenge, with at most the rounds' expected hits. -/
theorem sqStep {β : Type} {depth q : ℕ} {rounds : List FoldRound} {d : ℝ≥0∞}
    {T' T : List ℕ → VerifierProgram β} (hT : ∀ qs, DivLE S d (T' qs) (T qs)) :
    DivLE S ((rounds.map fun r ↦ queryHits S depth q r.alpha r.beta).sum + d)
      (VerifierProgram.grindProofOfWork Whir.queryGrindingBits >>= fun _ ↦
        sampleQueries depth q >>= fun qs ↦
          VerifierProgram.require (CombinersNonzero qs rounds) >>= fun _ ↦ T' qs)
      (VerifierProgram.grindProofOfWork Whir.queryGrindingBits >>= fun _ ↦
        sampleQueries depth q >>= fun qs ↦ T qs) := by
  intro K h g
  simp only [LawfulMonad.bind_assoc]
  refine (failFrom_bind_le_returns
    (f := fun _ ↦ sampleQueries depth q >>= fun qs ↦ T qs >>= K)
    (D := fun _ h' g' ↦ S.exp0 (sampleQueries depth q) h' g'
      (fun qs _ _ ↦ (if CombinersNonzero qs rounds then 0 else 1) + d)) _
    (fun _ _ h' g' ↦ ?_) h g).trans ?_
  · refine failFrom_bind_le_returns (f := fun qs ↦ T qs >>= K) _ (fun qs _ h'' g'' ↦ ?_) h' g'
    rw [VerifierProgram.bind_eq]
    refine (failFrom_require_bind_le _ _ h'' g'').trans ?_
    calc (if CombinersNonzero qs rounds then 0 else 1) + S.failFrom (T' qs >>= K) h'' g''
        ≤ (if CombinersNonzero qs rounds then 0 else 1) + (S.failFrom (T qs >>= K) h'' g'' + d) :=
          add_le_add le_rfl (hT qs K h'' g'')
      _ = _ := by ring
  · refine add_le_add le_rfl ?_
    rw [grindPoW_query]
    simp only [exp0]
    split
    · exact bot_le
    · rename_i hg
      rcases q with _ | q
      · refine avgE_le_const fun c ↦ ?_
        show (if CombinersNonzero [] rounds then 0 else 1) + d ≤ _
        have hc : CombinersNonzero [] rounds := fun q hq ↦ absurd hq List.not_mem_nil
        simp only [hc, ↓reduceIte, zero_add]
        exact le_add_self
      · have e := avg_exp0_sQA_ground (S := S) depth q (q + 1) (Nat.succ_ne_zero q)
          (fun qs _ _ ↦ (if CombinersNonzero qs rounds then 0 else 1) + d)
          (h ++ [Ev.grind Whir.queryGrindingBits])
        refine le_of_eq_of_le e ?_
        rw [exp0_add (C := fun qs _ _ ↦ if CombinersNonzero qs rounds then 0 else 1)
          (C' := fun _ _ _ ↦ d)]
        exact add_le_add (exp0_notCombinersNonzero_le depth (q + 1) rounds _)
          (exp0_const_le _ _ _ _)

/-! ## The levels -/

/-- `failFrom_bind_le_returns` with the expected difference bounded. -/
theorem failFrom_bind_le_of {α : Type} {f' f : α → VerifierProgram Bool}
    {D : α → List Ev → Option E → ℝ≥0∞} {A : VerifierProgram α} {h : List Ev} {g : Option E}
    {c : ℝ≥0∞}
    (hf : ∀ a, VerifierProgram.Returns A a → ∀ h g,
      S.failFrom (f' a) h g ≤ S.failFrom (f a) h g + D a h g)
    (hD : S.exp0 A h g D ≤ c) : S.failFrom (A >>= f') h g ≤ S.failFrom (A >>= f) h g + c :=
  (failFrom_bind_le_returns A hf h g).trans (add_le_add le_rfl hD)

/-- The rounds times the queries of a list of levels. -/
def roundQueries (L : List Whir.Level) : ℕ := (L.map fun l ↦ l.fold * l.queries).sum

/-- One step of a difference proof between two programs written alike. -/
local macro "div_step" : tactic => `(tactic| first
  | exact DivLE.refl _ _
  | (refine sqStep (fun _ ↦ ?_))
  | (refine DivLE.bind_refl (fun _ ↦ ?_) _)
  | split
  | dsimp only)

/-- **The levels refusing a vanishing combiner** fail at most `|E|⁻¹` more often per round and
query of each level. -/
theorem whirLevels_div (logN lf : ℕ) (eb : List E → E) :
    ∀ (L : List Whir.Level) (index : ℕ) (s : WhirState),
      DivLE S (roundQueries L * epsE) (whirLevelsRefusingZeroCombiner logN lf eb index L s)
        (whirLevels logN lf eb index L s)
  | [], _, _ => DivLE.refl _ _
  | level :: rest, index, s => by
    intro K h g
    rw [whirLevelsRefusingZeroCombiner, whirLevels, LawfulMonad.bind_assoc,
      LawfulMonad.bind_assoc]
    refine failFrom_bind_le_of (D := fun p _ _ ↦
      (p.2.map fun r ↦ queryHits S (logN - p.1.gammas.length + level.logInvRate) level.queries
        r.alpha r.beta).sum + roundQueries rest * epsE) (fun p _ h' g' ↦ ?_) ?_
    · obtain ⟨s', rounds⟩ := p
      dsimp only
      refine (?_ : DivLE S _ _ _) K h' g'
      cases rest with
      | nil =>
        dsimp only
        repeat div_step
      | cons next rest' =>
        dsimp only
        repeat (first | exact whirLevels_div logN lf eb _ _ _ | div_step)
    · rw [exp0_add (fun (p : WhirState × List FoldRound) (_ : List Ev) (_ : Option E) ↦
        (p.2.map fun r ↦ queryHits S (logN - p.1.gammas.length + level.logInvRate) level.queries
          r.alpha r.beta).sum) (fun _ _ _ ↦ (roundQueries rest : ℝ≥0∞) * epsE)]
      calc S.exp0 (foldRounds level.fold s) h g (fun p _ _ ↦ (p.2.map fun r ↦ queryHits S
              (logN - p.1.gammas.length + level.logInvRate) level.queries r.alpha r.beta).sum) +
            S.exp0 (foldRounds level.fold s) h g (fun _ _ _ ↦ roundQueries rest * epsE)
          ≤ level.fold * avg2 (queryHits S
              (logN - (s.gammas.length + level.fold) + level.logInvRate) level.queries) +
            roundQueries rest * epsE := by
            refine add_le_add ?_ (exp0_const_le _ _ _ _)
            refine le_trans (exp0_mono_returns (C' := fun p _ _ ↦ (p.2.map fun r ↦ queryHits S
              (logN - (s.gammas.length + level.fold) + level.logInvRate) level.queries
                r.alpha r.beta).sum) _ (fun p hp _ _ ↦ le_of_eq ?_) h g) ?_
            · rw [returns_foldRounds hp]
            · exact exp0_foldRounds_le _ _ _ _ _
        _ ≤ level.fold * (level.queries * epsE) + roundQueries rest * epsE := by
            gcongr
            exact avg2_queryHits_le _ _
        _ = roundQueries (level :: rest) * epsE := by
            simp only [roundQueries, List.map_cons, List.sum_cons]
            push_cast
            ring

/-! ## The verifier -/

/-- A refining program costs at most what the refined one costs. -/
theorem costs_of_refines {α : Type} {height : ℕ} {P' P : VerifierProgram α}
    (h : Limits.Refines P' P) :
    ∀ {n : ℕ} {Q : α → Prop}, VerifierProgram.Costs height P n Q →
      VerifierProgram.Costs height P' n Q := by
  induction h with
  | fail P => intro n Q _; trivial
  | ret a => intro n Q hc; exact hc
  | read _ ih => intro n Q hc; exact ⟨hc.1, fun x ↦ ih x (hc.2 x)⟩
  | sample _ ih => intro n Q hc; exact ⟨hc.1, fun x ↦ ih x (hc.2 x)⟩
  | grind _ ih => intro n Q hc; exact ⟨hc.1, ih hc.2⟩
  | commit _ ih => intro n Q hc; exact ⟨hc.1, hc.2.1, ih hc.2.2⟩
  | query _ ih => intro n Q hc; exact ⟨hc.1, fun r ↦ ih r (hc.2 r)⟩

/-- A common first part keeps a difference, the continuations compared at its returned
values. -/
theorem DivLE.bind_refl_returns {α β : Type} {c : ℝ≥0∞} {f' f : α → VerifierProgram β}
    (A : VerifierProgram α) (hf : ∀ a, VerifierProgram.Returns A a → DivLE S c (f' a) (f a)) :
    DivLE S c (A >>= f') (A >>= f) := by
  intro K h g
  rw [LawfulMonad.bind_assoc, LawfulMonad.bind_assoc]
  exact failFrom_bind_le_of (D := fun _ _ _ ↦ c) (fun a ha h g ↦ hf a ha K h g)
    (exp0_const_le _ _ _ _)

/-- Every ladder has at most `2048` rounds times queries. -/
theorem roundQueries_ladder_le {μ r : ℕ} {L : List Whir.Level} (h : Whir.ladder μ r = some L) :
    roundQueries L ≤ 2048 := by
  have hA : μ < 29 ∧ r < 5 := by
    unfold Whir.ladder at h
    split_ifs at h with hA
    obtain ⟨-, h2, -, h4⟩ := hA
    exact ⟨Nat.lt_succ_of_le h2, Nat.lt_succ_of_le h4⟩
  have key : ∀ μ < 29, ∀ r < 5, (Whir.ladder μ r).all (fun L ↦ roundQueries L ≤ 2048) = true := by
    decide +kernel
  have := key μ hA.1 r hA.2
  rw [h] at this
  simpa using this

/-- One step of a difference proof between two programs written alike, no check inserted. -/
local macro "div_step0" : tactic => `(tactic| first
  | with_reducible exact DivLE.refl _ _
  | (refine DivLE.bind_refl (fun _ ↦ ?_) _)
  | split
  | dsimp only)

theorem verifyWhir_div (logN rate : ℕ) (target : E) (eb : List E → E) :
    DivLE S (2048 * epsE) (verifyWhirRefusingZeroCombiner logN rate target eb)
      (verifyWhir logN rate target eb) := by
  unfold verifyWhirRefusingZeroCombiner verifyWhir
  refine DivLE.bind_refl_returns _ fun L hL ↦ ?_
  have hl : Whir.ladder logN rate = some L := by
    revert hL
    cases Whir.ladder logN rate with
    | none => intro h; cases h
    | some L' => intro h; cases h; rfl
  refine (whirLevels_div _ _ _ L 0 _).mono ?_
  gcongr
  exact_mod_cast roundQueries_ladder_le hl

theorem verifyStackedOpening_div (stackLog rate : ℕ) (claims : List StackClaim) :
    DivLE S (2048 * epsE) (verifyStackedOpeningRefusingZeroCombiner stackLog rate claims)
      (verifyStackedOpening stackLog rate claims) := by
  unfold verifyStackedOpeningRefusingZeroCombiner verifyStackedOpening
  repeat (first | with_reducible exact verifyWhir_div _ _ _ _ | div_step0)

theorem verifyExecution_div (bv : List K → List E → E → VerifierProgram Unit) (bytecode : List K)
    (publicInput : Digest) :
    DivLE S (2048 * epsE) (verifyExecutionRefusingZeroCombiner bv bytecode publicInput)
      (verifyExecution bv bytecode publicInput) := by
  unfold verifyExecutionRefusingZeroCombiner verifyExecution
  repeat (first | with_reducible exact verifyStackedOpening_div _ _ _ | div_step0)

/-- **The statement's refusing verifier, against a winning strategy**, fails with probability at
most `|E|⁻¹` per round and query of the opening (at most `2048`) and per sample (a quarter of the
cost). -/
theorem failFrom_refusingZeroProgram_le {bytecode : List K} {publicInput : Digest} {height n : ℕ}
    (hacc : S.AcceptsFrom (leanVmVerifierProgram bytecode publicInput) [])
    (hgs : GrindThenSample (leanVmVerifierProgram bytecode publicInput))
    (hP : (leanVmVerifierProgram bytecode publicInput).CostLE height n) :
    S.failFrom (Limits.refusingZeroProgram bytecode publicInput) [] none ≤
      (2048 + (n / 4 : ℕ)) * epsE := by
  have hR : Limits.Refines (verifyExecutionRefusingZeroCombiner computedBytecodeValue bytecode
      publicInput >>= fun _ ↦ VerifierProgram.ret true) (leanVmVerifierProgram bytecode
        publicInput) :=
    Limits.Refines.bind (Limits.verifyExecutionRefusingZeroCombiner_refines _ _ _)
      fun _ ↦ Limits.Refines.refl _
  have h1 := failFrom_refusingZero_le (S := S) _ n (costs_of_refines hR hP) [] none
  have h2 := verifyExecution_div (S := S) computedBytecodeValue bytecode publicInput
    (fun _ ↦ VerifierProgram.ret true) [] none
  have h3 : S.failFrom (leanVmVerifierProgram bytecode publicInput) [] none = 0 :=
    failFrom_eq_zero _ _ _ hacc hgs (Or.inl rfl)
  have e : leanVmVerifierProgram bytecode publicInput =
      verifyExecution computedBytecodeValue bytecode publicInput >>= fun _ ↦
        VerifierProgram.ret true := rfl
  rw [e] at h3
  rw [h3, zero_add] at h2
  unfold Limits.refusingZeroProgram
  refine h1.trans ?_
  simp only [reduceCtorEq, ↓reduceIte, add_zero]
  calc S.failFrom (verifyExecutionRefusingZeroCombiner computedBytecodeValue bytecode publicInput >>=
        fun _ ↦ VerifierProgram.ret true) [] none + ((n / 4 : ℕ) : ℝ≥0∞) * epsE
      ≤ 2048 * epsE + ((n / 4 : ℕ) : ℝ≥0∞) * epsE := add_le_add h2 le_rfl
    _ = _ := by ring

end
end LeanVM.Guest.Child
