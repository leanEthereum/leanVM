/-
  LeanVM.Protocol.EndToEnd.Sound.CutXrun

  The cut verifier's extracted run: wherever the ghost verifier's run returns, the cut's run from
  the same state returns the same value.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.CutRun
public import LeanVM.Protocol.EndToEnd.Sound.Extractor
public import LeanVM.Protocol.Compile.Rom.Replay
public import LeanVM.Protocol.Verifier.Deferred
public import LeanVM.Protocol.Verifier.Cost

/-!
# The cut verifier's run

`XCut H F p q`: wherever the extracted run of `p` (`xrun`, with the hash and permutation answers
`H`, `F`) returns a value, the extracted run of `q` from the same state and history returns it
too, with a history the first one extends by no commitment. It passes through a
common prefix program (`XCut.bind`) and a final return (`XCut.mapRet`), so the cut levels
(`xcut_whirLevelsGF`; the final level's rest opens rows but commits nothing, `NoCommitQ`) give
the cut verifier (`xcut_leanVmProgramG`).

`replayU_cut`: so the replay of the cut (`Rom.replayU`) on permutation answers agreeing with the
run's on its inputs returns the ghost verifier's value, at the extracted run's state, whose roots
hold the commitments of the ghost's whole history.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.KeccakHash

@[expose] public section

variable (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)

/-! ## Programs without commitments -/

/-- No commitment on any path (openings allowed). -/
def NoCommitQ {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoCommitQ (k x)
  | .sample k => ∀ c, NoCommitQ (k c)
  | .grind _ k => NoCommitQ k
  | .commit _ _ _ => False
  | .query _ _ k => ∀ rows, NoCommitQ (k rows)

theorem NoCommitQ.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : NoCommitQ p) (hf : ∀ a, NoCommitQ (f a)) : NoCommitQ (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit _ _ _ _ => exact hp.elim
  | query _ _ k ih => exact fun rows ↦ ih rows (hp rows)

/-- **A history along a program without commitments commits nothing.** -/
theorem NoCommitQ.commits_nil {α : Type} :
    ∀ {p : VerifierProgram α} {h : List Ev} {q : VerifierProgram α},
      NoCommitQ p → p.after h = some q → commits h = []
  | _, [], _, _, _ => rfl
  | .ret _, _ :: _, _, _, ha => by simp [VerifierProgram.after] at ha
  | .fail, _ :: _, _, _, ha => by simp [VerifierProgram.after] at ha
  | .read k, e :: es, _, hp, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    exact NoCommitQ.commits_nil (h := es) (hp _) ha
  | .sample k, e :: es, _, hp, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    exact NoCommitQ.commits_nil (h := es) (hp _) ha
  | .grind b k, e :: es, _, hp, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    split at ha
    · exact NoCommitQ.commits_nil (p := k) (h := es) hp ha
    · simp at ha
  | .commit _ _ _, _, _, hp, _ => hp.elim
  | .query _ _ k, e :: es, _, hp, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    exact NoCommitQ.commits_nil (h := es) (hp _) ha

theorem noCommitQ_readScalars : ∀ n, NoCommitQ (VerifierProgram.readScalars n)
  | 0 => trivial
  | n + 1 => by
    unfold VerifierProgram.readScalars
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦
      NoCommitQ.bind (noCommitQ_readScalars n) fun _ ↦ trivial

theorem noCommitQ_grindProofOfWork (b : ℕ) : NoCommitQ (VerifierProgram.grindProofOfWork b) := by
  unfold VerifierProgram.grindProofOfWork
  split <;> trivial

theorem noCommitQ_require (c : Prop) [Decidable c] : NoCommitQ (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split <;> trivial

theorem noCommitQ_sumcheck (claim : E) (count : ℕ) :
    ∀ eqs : List (Option E), NoCommitQ (sumcheck claim count eqs) := by
  intro eqs
  induction eqs generalizing claim with
  | nil => trivial
  | cons e eqs ih =>
    unfold sumcheck
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommitQ.bind ?_ fun _ ↦ NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦
      NoCommitQ.bind (ih _) fun _ ↦ trivial
    cases e <;> unfold sumcheckRoundPoly <;> simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    · exact NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦ NoCommitQ.bind (noCommitQ_readScalars _)
        fun _ ↦ NoCommitQ.bind (noCommitQ_grindProofOfWork _) fun _ ↦ trivial
    · exact NoCommitQ.bind (noCommitQ_readScalars _) fun _ ↦
        NoCommitQ.bind (noCommitQ_grindProofOfWork _) fun _ ↦ trivial

theorem noCommitQ_sampleQueriesAux (depth : ℕ) :
    ∀ (fuel remaining : ℕ), NoCommitQ (sampleQueriesAux depth fuel remaining)
  | 0, _ => trivial
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    split
    · trivial
    · exact NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦
        NoCommitQ.bind (noCommitQ_sampleQueriesAux depth fuel _) fun _ ↦ trivial

/-- **The rest of the final level commits nothing.** -/
theorem noCommitQ_finRest (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) (tr : WhirTrace) :
    NoCommitQ ((finRest logN laneFolds eb index level s rounds tr).bind fun _ ↦
      VerifierProgram.ret tr) := by
  refine NoCommitQ.bind ?_ fun _ ↦ trivial
  cases tr with
  | mid => trivial
  | final _ folded =>
    simp only [finRest, finalTailRest, VerifierProgram.bind_eq]
    exact NoCommitQ.bind (noCommitQ_grindProofOfWork _) fun _ ↦ NoCommitQ.bind
      (NoCommitQ.bind (noCommitQ_sampleQueriesAux _ _ _) fun _ ↦
        NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦ noCommitQ_require _) fun _ ↦
      NoCommitQ.bind (noCommitQ_sumcheck _ _ _) fun _ ↦ noCommitQ_require _

/-! ## Returned values -/

/-- A program returns along a history only a value it may return. -/
theorem returns_of_after {α : Type} {a : α} : ∀ {p : VerifierProgram α} {l : List Ev},
    p.after l = some (.ret a) → VerifierProgram.Returns p a
  | _, [], h => by
    simp only [VerifierProgram.after, Option.some.injEq] at h
    subst h
    exact .ret a
  | .ret _, _ :: _, h => by simp [VerifierProgram.after] at h
  | .fail, _ :: _, h => by simp [VerifierProgram.after] at h
  | .read k, e :: es, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    exact .read _ (returns_of_after h)
  | .sample k, e :: es, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    exact .sample _ (returns_of_after h)
  | .grind b k, e :: es, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split at h
    · exact .grind _ (returns_of_after h)
    · simp at h
  | .commit ht w k, e :: es, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split at h
    · exact .commit _ _ (returns_of_after h)
    · simp at h
  | .query i ps k, e :: es, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    exact .query _ _ _ (returns_of_after h)

/-- A cost's postcondition holds of every value the program may return. -/
theorem post_of_returns {α : Type} {height n : ℕ} {Q : α → Prop} {p : VerifierProgram α} {a : α}
    (hc : VerifierProgram.Costs height p n Q) (hr : VerifierProgram.Returns p a) : Q a := by
  induction hr generalizing n with
  | ret a => exact hc
  | read x _ ih => exact ih (hc.2 x)
  | sample x _ ih => exact ih (hc.2 x)
  | grind _ _ ih => exact ih hc.2
  | commit _ _ _ ih => exact ih hc.2.2
  | query _ _ rows _ ih => exact ih (hc.2 rows)

theorem returns_foldRounds {n : ℕ} {s : WhirState} {r : WhirState × List FoldRound}
    (h : VerifierProgram.Returns (foldRounds n s) r) : r.1.alphas.length = s.alphas.length + n :=
  post_of_returns (Q := fun r : WhirState × List FoldRound ↦ r.1.alphas.length = s.alphas.length + n)
    (costs_foldRounds (height := 0) n s) h

/-- A level's rest hands its continuation a state with the same `α`s. -/
theorem returns_midTailPre {logN index : ℕ} {level next : Whir.Level} {s : WhirState}
    {rounds : List FoldRound} {p : List E × WhirState}
    (h : VerifierProgram.Returns (midTailPre logN index level next s rounds) p) :
    p.2.alphas = s.alphas := by
  unfold midTailPre midTailC at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  rfl

/-! ## The final proof of work -/

/-- The positions a challenge names first: `n` of `depth` bits (`sample_queries`'s first chunk). -/
def firstPositions (depth n : ℕ) (c : E) : List ℕ :=
  (List.range n).map fun i ↦ (eToNat c >>> (i * depth)) % 2 ^ depth

/-- **A hit of a proof of work of `bits` bits**: the answer `u` passes it, and its challenge names
the phase's first `n` positions at `depth` bits. -/
def GrindHit (bits depth n : ℕ) (phase : List Opening) (u : KeccakState) : Prop :=
  powOk bits (Keccak.lane u 2) = true ∧
    firstPositions depth n (challengeOf u) = (phase.map Opening.leafIndex).take n

/-- **The final query's proof of work hits from the state `s`** on the answers `F`: the next
scalar is its nonce, and the permutation that absorbs it answers a hit for the next phase, at the
final level's query depth and count. -/
def FinalOK (F : KeccakState → Option KeccakState) (depth count : ℕ) (s : VerifierProgramState) :
    Prop :=
  ∃ n xs sp1 sp2 phase rest, s.stream = n :: xs ∧ s.sponge.ground = none ∧
    absorb (m := Option) F s.sponge n dsPowNonce = some sp1 ∧
    duplex (m := Option) F sp1 = some sp2 ∧ s.openings = phase :: rest ∧
    GrindHit Whir.queryGrindingBits depth (min (128 / depth) count) phase sp2.state

/-- The final level's query depth of a ladder whose levels start after `a` folds. -/
def finalDepth (logN a : ℕ) (levels : List Whir.Level) : ℕ :=
  logN - (a + (levels.map (·.fold)).sum) + (levels.getLast?.map (·.logInvRate)).getD 0

/-- The final level's query count of a ladder. -/
def finalCount (levels : List Whir.Level) : ℕ := (levels.getLast?.map (·.queries)).getD 0

/-- **The final shape's hit**: the stack's size and rate have a ladder, at whose final level the
final query's proof of work hits. -/
def FinalShapeOK (F : KeccakState → Option KeccakState) (logN ρ : ℕ) (s : VerifierProgramState) :
    Prop :=
  ∃ config, Whir.ladder logN ρ = some config ∧
    FinalOK F (finalDepth logN 0 config) (finalCount config) s

/-! ## The cut on runs -/

/-- **`q` cuts `p` on runs, ending in `Q`**: wherever `p`'s extracted run returns a value, `q`'s
does, with a history that `p`'s extends by no commitment, at a state where `Q` holds. -/
def XCut {α : Type} (Q : α → VerifierProgramState → Prop) (p q : VerifierProgram α) : Prop :=
  ∀ s h a s' hist, xrun H F p s h = some (a, s', hist) → ∃ s₁ h₁,
    xrun H F q s h = some (a, s₁, h₁) ∧ (∃ l, hist = h₁ ++ l ∧ commits l = []) ∧ Q a s₁

variable {H F}

theorem XCut.mono {α : Type} {Q Q' : α → VerifierProgramState → Prop} {p q : VerifierProgram α}
    (hpq : XCut H F Q p q) (hQ : ∀ a s, Q a s → Q' a s) : XCut H F Q' p q := by
  intro s h a s' hist hx
  obtain ⟨s₁, h₁, hq, hl, hQa⟩ := hpq s h a s' hist hx
  exact ⟨s₁, h₁, hq, hl, hQ _ _ hQa⟩

/-- Binding the same program before cut continuations cuts, the continuations at the values it
may return. -/
theorem XCut.bind {α β : Type} (p : VerifierProgram α) {f g : α → VerifierProgram β}
    {Q : β → VerifierProgramState → Prop}
    (hfg : ∀ a, VerifierProgram.Returns p a → XCut H F Q (f a) (g a)) :
    XCut H F Q (p.bind f) (p.bind g) := by
  intro s h b s' hist hx
  rw [xrun_bind] at hx ⊢
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨l, -, ha, -⟩ := xrun_after H F _ _ _ hr
  obtain ⟨s₁, h₁, hg, hl⟩ := hfg r.1 (returns_of_after ha) _ _ _ _ _ hf
  exact ⟨s₁, h₁, by rw [hr, Option.bind_some, hg], hl⟩

theorem XCut.mapRet {α β : Type} {p q : VerifierProgram α} {Q : α → VerifierProgramState → Prop}
    {Q' : β → VerifierProgramState → Prop} (hpq : XCut H F Q p q) (w : α → β)
    (hQ : ∀ a s, Q a s → Q' (w a) s) :
    XCut H F Q' (p.bind fun a ↦ VerifierProgram.ret (w a)) (q.bind fun a ↦ VerifierProgram.ret (w a)) := by
  intro s h b s' hist hx
  rw [xrun_bind] at hx ⊢
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, -, rfl⟩ := hf
  obtain ⟨s₁, h₁, hq, hl, hQa⟩ := hpq _ _ _ _ _ hr
  exact ⟨s₁, h₁, by rw [hq, Option.bind_some]; rfl, hl, hQ _ _ hQa⟩

/-- The query positions' run: the openings and roots kept, and from a challenge a grind drew,
the first positions it names. -/
theorem xrun_sampleQueriesAux {depth : ℕ} : ∀ (fuel remaining : ℕ) {st : VerifierProgramState}
    {h : List Ev} {qs : List ℕ} {st' : VerifierProgramState} {h' : List Ev},
    xrun H F (sampleQueriesAux depth fuel remaining) st h = some (qs, st', h') →
    st'.openings = st.openings ∧ st'.roots = st.roots ∧
      ∀ c, st.sponge.ground = some c → remaining ≤ fuel →
        ∃ rest, qs = firstPositions depth (min (128 / depth) remaining) c ++ rest
  | 0, remaining, st, h, qs, st', h', hx => by
    simp only [sampleQueriesAux, VerifierProgram.pure_eq, xrun, Option.some.injEq,
      Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl, -⟩ := hx
    refine ⟨rfl, rfl, fun c _ hr ↦ ⟨[], ?_⟩⟩
    rw [show remaining = 0 by omega]
    simp [firstPositions]
  | fuel + 1, remaining, st, h, qs, st', h', hx => by
    unfold sampleQueriesAux at hx
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq] at hx
    split at hx
    · rename_i hr0
      simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl, -⟩ := hx
      refine ⟨rfl, rfl, fun c _ _ ↦ ⟨[], ?_⟩⟩
      simp [firstPositions, hr0]
    · rw [xrun_bind] at hx
      obtain ⟨r, hr, hx⟩ := Option.bind_eq_some_iff.mp hx
      rw [xrun_bind] at hx
      obtain ⟨r', hr', hx⟩ := Option.bind_eq_some_iff.mp hx
      simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl, -⟩ := hx
      simp only [VerifierProgram.sampleChallenge, xrun] at hr
      obtain ⟨c', hc', hr⟩ := Option.bind_eq_some_iff.mp hr
      simp only [Option.some.injEq] at hr
      subst hr
      obtain ⟨ho, hroots, -⟩ := xrun_sampleQueriesAux fuel _ hr'
      refine ⟨ho, hroots, fun c hg _ ↦ ⟨r'.1, ?_⟩⟩
      simp only [squeeze, hg, pure, Option.some.injEq] at hc'
      subst hc'
      rfl

/-- **The final level's rest hits**: where it returns from a state, the final query's proof of
work hits there, at the level's depth and count. -/
theorem finalOK_of_xrun {logN laneFolds : ℕ} {eb : List E → E} {index : ℕ} {level : Whir.Level}
    {s : WhirState} {rounds : List FoldRound} {folded : List E} {st : VerifierProgramState}
    {h : List Ev} {a : Unit} {st' : VerifierProgramState} {hist : List Ev}
    (hx : xrun H F (finalTailRest logN laneFolds eb index level s rounds folded) st h =
      some (a, st', hist)) :
    FinalOK F (logN - s.alphas.length + level.logInvRate) level.queries st := by
  unfold finalTailRest at hx
  simp only [VerifierProgram.bind_eq] at hx
  rw [xrun_bind] at hx
  obtain ⟨r1, h1, hx⟩ := Option.bind_eq_some_iff.mp hx
  rw [xrun_bind] at hx
  obtain ⟨r2, h2, -⟩ := Option.bind_eq_some_iff.mp hx
  rw [xrun_bind] at h2
  obtain ⟨r3, h3, h2⟩ := Option.bind_eq_some_iff.mp h2
  rw [xrun_bind] at h2
  obtain ⟨r4, h4, -⟩ := Option.bind_eq_some_iff.mp h2
  have hbits : Whir.queryGrindingBits ≠ 0 := by decide
  simp only [VerifierProgram.grindProofOfWork, hbits, ↓reduceIte, xrun] at h1
  split at h1
  · rename_i n xs hst hg
    obtain ⟨r, hr, h1⟩ := Option.bind_eq_some_iff.mp h1
    split_ifs at h1 with hp
    simp only [Option.some.injEq] at h1
    subst h1
    have hr' := hr
    simp only [absorbNonce, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr'
    obtain ⟨sp1, hsp1, sp2, hsp2, rfl⟩ := hr'
    obtain ⟨ho, -, hpos⟩ := xrun_sampleQueriesAux _ _ h3
    obtain ⟨rest, hqs⟩ := hpos _ rfl le_rfl
    simp only [VerifierProgram.queryOpenings, xrun] at h4
    split at h4
    · rename_i root height width phase rest' hroot hop
      split at h4
      · rename_i rows hrows
        simp only [openPhaseWithHash] at hrows
        split_ifs at hrows with hcond
        · refine ⟨n, xs, sp1, sp2, phase, rest', hst, hg, hsp1, hsp2, by rw [← hop, ho], hp, ?_⟩
          rw [hcond.2, hqs, List.take_left' (by simp [firstPositions])]
        · simp [pure] at hrows
      · simp at h4
    · simp at h4
  · simp at h1

/-- The full final step's run returns where the cut's does, with the same trace, and the final
query's proof of work hits after it. -/
theorem xcut_fin (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) :
    XCut H F (fun _ st ↦ FinalOK F (logN - s.alphas.length + level.logInvRate) level.queries st)
      (finFull logN laneFolds eb index level s rounds) (finCut logN index level s rounds) := by
  intro st h a s' hist hx
  rw [finFull_eq, xrun_bind] at hx
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨l, hl, hafter, -⟩ := xrun_after H F _ _ _ hf
  have hr1 : r.1 = a := by
    have := hafter
    obtain ⟨u, m₁, m₂, -, -, hret⟩ := after_bind_ret this
    exact (after_ret_eq hret).2
  subst hr1
  refine ⟨r.2.1, r.2.2, hr, ⟨l, hl, (noCommitQ_finRest logN laneFolds eb index level s rounds
    r.1).commits_nil hafter⟩, ?_⟩
  obtain ⟨tr, st1, h1⟩ := r
  rw [xrun_bind] at hf
  obtain ⟨r', hr', -⟩ := Option.bind_eq_some_iff.mp hf
  cases tr with
  | mid => simp [finRest, xrun] at hr'
  | final _ folded => exact finalOK_of_xrun hr'

theorem finalDepth_single (logN a : ℕ) (level : Whir.Level) :
    finalDepth logN a [level] = logN - (a + level.fold) + level.logInvRate := by
  simp [finalDepth]

theorem finalDepth_cons (logN a : ℕ) (level next : Whir.Level) (rest : List Whir.Level) :
    finalDepth logN a (level :: next :: rest) = finalDepth logN (a + level.fold) (next :: rest) := by
  simp only [finalDepth, List.map_cons, List.sum_cons, List.getLast?_cons_cons]
  rw [Nat.add_assoc]

theorem finalCount_cons (level next : Whir.Level) (rest : List Whir.Level) :
    finalCount (level :: next :: rest) = finalCount (next :: rest) := by
  simp only [finalCount, List.getLast?_cons_cons]

/-- **The cut levels' run** returns where the full levels' does, the final query's proof of work
hitting after it. -/
theorem xcut_whirLevelsGF (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      XCut H F (fun _ st ↦ FinalOK F (finalDepth logN s.alphas.length levels) (finalCount levels) st)
        (whirLevelsGF logN (finFull logN laneFolds eb) index levels s)
        (whirLevelsGF logN (finCut logN) index levels s)
  | _, [], _ => fun _ _ _ _ _ hx ↦ by simp [whirLevelsGF, xrun] at hx
  | index, [level], s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    refine XCut.bind _ fun r hr ↦ (xcut_fin logN laneFolds eb index level r.1 r.2).mono ?_
    intro _ st hst
    rwa [finalDepth_single, finalCount, ← returns_foldRounds hr]
  | index, level :: next :: rest, s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    refine XCut.bind _ fun r hr ↦ ?_
    rw [midTailC_eq_pre, midTailC_eq_pre]
    refine XCut.bind _ fun p hp ↦
      ((xcut_whirLevelsGF logN laneFolds eb (index + 1) (next :: rest) p.2).mapRet
        (fun tr ↦ WhirTrace.mid r.2 p.1 tr)
        (Q' := fun _ st ↦ FinalOK F (finalDepth logN p.2.alphas.length (next :: rest))
          (finalCount (next :: rest)) st) fun _ _ h ↦ h).mono ?_
    intro _ st hst
    rw [returns_midTailPre hp, returns_foldRounds hr] at hst
    rwa [finalDepth_cons, finalCount_cons]

theorem xcut_verifyStackedOpeningG (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    XCut H F (fun _ st ↦ FinalShapeOK F stackLog logInvRate st)
      (verifyStackedOpeningG stackLog logInvRate claims)
      (verifyStackedOpeningCut stackLog logInvRate claims) := by
  refine XCut.bind _ fun _ _ ↦ XCut.bind _ fun c _ ↦ ?_
  unfold verifyWhirG verifyWhirCut
  simp only [VerifierProgram.bind_eq]
  refine XCut.bind _ fun config hc ↦ ?_
  rw [whirLevelsG_eq]
  exact (xcut_whirLevelsGF _ _ _ _ _ _).mono fun _ st hst ↦ ⟨config, returns_liftOption hc, hst⟩

theorem xcut_veBodyG (ev : List K → List E → E → VerifierProgram Unit) (publicInput : Digest)
    (layout : Verifier.Layout) (ρ : ℕ) :
    XCut H F (fun _ st ↦ FinalShapeOK F layout.stackLog ρ st) (veBodyG ev publicInput layout ρ)
      (veBodyCut ev publicInput layout ρ) := by
  unfold veBodyG veBodyCut
  simp only [VerifierProgram.bind_eq]
  refine XCut.bind _ fun _ _ ↦ XCut.bind _ fun ood _ ↦ XCut.bind _ fun r _ ↦ ?_
  obtain ⟨cl, kp, ks⟩ := r
  refine XCut.bind _ fun y _ ↦ ?_
  obtain ⟨t, w⟩ := y
  exact xcut_verifyStackedOpeningG _ _ _

/-- What the cut verifier's run ends with: the final query's proof of work hits at the announced
shape. -/
def CutEnd (F : KeccakState → Option KeccakState) (r : Bool × ((Verifier.Layout × ℕ) × WhirTrace))
    (s : VerifierProgramState) : Prop :=
  FinalShapeOK F r.2.1.1.stackLog r.2.1.2 s

/-- **The cut verifier's run** returns where the ghost verifier's does, the final query's proof
of work hitting after it. -/
theorem xcut_leanVmProgramG (bytecode : List K) (pd : Digest) :
    XCut H F (CutEnd F) (leanVmProgramG bytecode pd) (leanVmProgramCut bytecode pd) :=
  (XCut.bind _ fun (a : Verifier.Layout × ℕ) _ ↦ (xcut_veBodyG _ pd a.1 a.2).mapRet
    (fun tr ↦ (a, tr)) (Q' := fun r st ↦ FinalShapeOK F r.1.1.stackLog r.1.2 st)
    fun _ _ h ↦ h).mapRet (fun d ↦ (true, d)) fun _ _ h ↦ h

/-! ## The replay of the cut -/

/-- An accepting extracted run of the verifier is one of the ghost verifier, with its data. -/
theorem xrun_leanVmProgramG {bytecode : List K} {pd : Digest} {s : VerifierProgramState}
    {h : List Ev} {s' : VerifierProgramState} {hist : List Ev}
    (hx : xrun H F (leanVmVerifierProgram bytecode pd) s h = some (true, s', hist)) :
    ∃ d, xrun H F (leanVmProgramG bytecode pd) s h = some ((true, d), s', hist) := by
  rw [← leanVmProgramG_eq, xrun_bind] at hx
  obtain ⟨⟨⟨b, d⟩, s₁, h₁⟩, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl⟩ := hf
  exact ⟨d, hr⟩

/-- **The replay of the cut returns the ghost verifier's value**: where the ghost verifier's
extracted run returns, the cut's returns the same value, and so does the replay of the cut on
permutation answers agreeing with `F` on its inputs, at the cut run's state; that state's roots
hold the commitments of the ghost's whole history. -/
theorem replayU_cut {F' : KeccakState → Option KeccakState} {bytecode : List K} {pd : Digest}
    {s : VerifierProgramState} {h : List Ev} {a : Bool × ((Verifier.Layout × ℕ) × WhirTrace)}
    {s' : VerifierProgramState} {hist : List Ev}
    (hx : xrun H F (leanVmProgramG bytecode pd) s h = some (a, s', hist))
    (hR : RootsInv H s h)
    (hF : ∀ x ∈ replayIn F (leanVmProgramCut bytecode pd) s, F' x = F x) :
    ∃ s₁ h₁, xrun H F (leanVmProgramCut bytecode pd) s h = some (a, s₁, h₁) ∧
      replayU F' (leanVmProgramCut bytecode pd) s = some (a, s₁) ∧
      commits hist = s₁.roots.map (fun r ↦ (r.2.1, r.2.2, extract H r.1 r.2.1 r.2.2)) ∧
      CutEnd F a s₁ := by
  obtain ⟨s₁, h₁, hc, ⟨l, rfl, hl⟩, hend⟩ := xcut_leanVmProgramG bytecode pd s h a s' hist hx
  refine ⟨s₁, h₁, hc, ?_, ?_, hend⟩
  · rw [replayU_congr _ _ hF]
    exact replayU_of_xrun H F _ _ _ hc
  · rw [commits_append, hl, List.append_nil]
    exact xrun_rootsInv H F _ _ _ hR hc

end
end LeanVM.Protocol.EndToEnd.Sound
