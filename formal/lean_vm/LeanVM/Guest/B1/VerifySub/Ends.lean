/-
  LeanVM.Guest.B1.VerifySub.Ends

  Which deployed runs end with no ground challenge waiting: the phases of the deferring verifier
  and the stacked opening, for the carried sponges of the completeness direction.
-/

module

public import LeanVM.Guest.B1.VerifySub.NZBridge
public import LeanVM.Protocol.Verifier.WhirTarget

/-!
# Runs ending with no ground challenge

A grind leaves its challenge waiting for the next squeeze (the sponge's `ground`); the guest
carries a sponge only with nothing waiting (`Fs.Carries`). `EndsClear p`: a run of `p` from a
sponge with nothing waiting ends with nothing waiting. `EndsAny p`: every run of `p` does (it ends
with a read or a squeeze). Both compose along `bind` (`EndsClear.bind`, `EndsAny.bind`,
`endsAny_bind_right`).

The phases: the announced sizes, the stack's commitment and the bus's GKR are `EndsClear`; the
out-of-domain sample, the bus's challenges, the tables, the Keccak reduction and the ring switch are
`EndsAny`. The stacked opening (`Whir.whirOpen`, `Limits.whirOpenNZ`, and refusing zero challenges)
is `EndsAny`: its final level squeezes its queries after its grind (every deployed ladder's final
level queries, `ladder_lastQ`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {α β : Type}

/-- A run from a sponge with nothing waiting ends with nothing waiting. -/
def EndsClear (p : VerifierProgram α) : Prop :=
  ∀ st a st', st.sponge.ground = none → runId p st = some (a, st') → st'.sponge.ground = none

/-- Every run ends with nothing waiting. -/
def EndsAny (p : VerifierProgram α) : Prop :=
  ∀ st a st', runId p st = some (a, st') → st'.sponge.ground = none

theorem EndsAny.clear {p : VerifierProgram α} (h : EndsAny p) : EndsClear p :=
  fun st a st' _ hr ↦ h st a st' hr

theorem EndsClear.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : EndsClear p)
    (hf : ∀ a, EndsClear (f a)) : EndsClear (p.bind f) := by
  intro st b st'' hg h
  obtain ⟨a, st', h1, h2⟩ := runId_bind_some h
  exact hf a st' b st'' (hp st a st' hg h1) h2

theorem EndsAny.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : EndsAny p)
    (hf : ∀ a, EndsClear (f a)) : EndsAny (p.bind f) := by
  intro st b st'' h
  obtain ⟨a, st', h1, h2⟩ := runId_bind_some h
  exact hf a st' b st'' (hp st a st' h1) h2

theorem endsAny_bind_right {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hf : ∀ a, EndsAny (f a)) : EndsAny (p.bind f) := by
  intro st b st'' h
  obtain ⟨a, st', -, h2⟩ := runId_bind_some h
  exact hf a st' b st'' h2

theorem endsAny_rz {p : VerifierProgram α} (h : EndsAny p) : EndsAny p.refusingZeroChallenge :=
  fun st a st' hr ↦ h st a st' (runId_of_rz _ _ _ hr)

/-! ## The primitives -/

theorem absorb_ground (π : KeccakState → Id KeccakState) (sp : Sponge) (x : E) (t : ℕ) :
    (Id.run (Compile.absorb π sp x t)).ground = sp.ground := by
  unfold Compile.absorb
  split <;> rfl

theorem squeeze_ground (π : KeccakState → Id KeccakState) (sp : Sponge) :
    (Id.run (squeeze π sp)).2.ground = none := by
  obtain ⟨S, P, g⟩ := sp
  cases g <;> rfl

theorem endsClear_ret (a : α) : EndsClear (VerifierProgram.ret a) := by
  intro st b st' hg h
  have e : runId (VerifierProgram.ret a) st = some (a, st) := rfl
  rw [e, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact hg

theorem endsAny_fail : EndsAny (VerifierProgram.fail : VerifierProgram α) :=
  fun _ _ _ h ↦ absurd h (by rintro ⟨⟩)

theorem endsClear_require (c : Prop) [Decidable c] : EndsClear (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split
  · exact endsClear_ret _
  · exact endsAny_fail.clear

theorem endsClear_liftOption (o : Option α) : EndsClear (liftOption o) := by
  cases o
  · exact endsAny_fail.clear
  · exact endsClear_ret _

theorem endsAny_read_bind (k : E → VerifierProgram α) (hk : ∀ x, EndsClear (k x)) :
    EndsAny (VerifierProgram.read k) := by
  rintro ⟨⟨S, P, g⟩, stream, os, R⟩ a st' h
  match stream, g, h with
  | [], _, h => exact absurd h (by rintro ⟨⟩)
  | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
  | x :: xs, none, h =>
    refine hk x _ a st' ?_ h
    show (Id.run (Compile.absorb keccakF1600 ⟨S, P, none⟩ x dsObserve)).ground = none
    rw [absorb_ground]

theorem endsAny_readE : EndsAny VerifierProgram.readScalar :=
  endsAny_read_bind _ fun _ ↦ endsClear_ret _

theorem endsAny_sample_bind (k : E → VerifierProgram α) (hk : ∀ c, EndsClear (k c)) :
    EndsAny (VerifierProgram.sample k) := by
  intro st a st' h
  exact hk _ _ a st' (squeeze_ground _ st.sponge) h

theorem endsAny_sampleE : EndsAny VerifierProgram.sampleChallenge :=
  endsAny_sample_bind _ fun _ ↦ endsClear_ret _

theorem endsClear_readN : ∀ n, EndsClear (VerifierProgram.readScalars n)
  | 0 => endsClear_ret _
  | n + 1 => by
    simp only [VerifierProgram.readScalars, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact (endsAny_readE.bind fun _ ↦ (endsClear_readN n).bind fun _ ↦ endsClear_ret _).clear

theorem endsAny_readN {n : ℕ} (hn : 0 < n) : EndsAny (VerifierProgram.readScalars n) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [VerifierProgram.readScalars, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact endsAny_readE.bind fun _ ↦ (endsClear_readN n).bind fun _ ↦ endsClear_ret _

theorem endsClear_sampleN : ∀ n, EndsClear (VerifierProgram.sampleChallenges n)
  | 0 => endsClear_ret _
  | n + 1 => by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact (endsAny_sampleE.bind fun _ ↦ (endsClear_sampleN n).bind fun _ ↦ endsClear_ret _).clear

theorem endsAny_sampleN {n : ℕ} (hn : 0 < n) : EndsAny (VerifierProgram.sampleChallenges n) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact endsAny_sampleE.bind fun _ ↦ (endsClear_sampleN n).bind fun _ ↦ endsClear_ret _

theorem endsClear_queryOpenings (i : ℕ) (ps : List ℕ) :
    EndsClear (VerifierProgram.queryOpenings i ps) := by
  rintro ⟨sp, stream, os, R⟩ a st' hg h
  cases hR : R[i]? with
  | none =>
    rw [VerifierProgram.queryOpenings, runId_query_none _ _ _ _ (Or.inl hR)] at h
    exact absurd h (by rintro ⟨⟩)
  | some v =>
    obtain ⟨root, height, width⟩ := v
    cases os with
    | nil =>
      rw [VerifierProgram.queryOpenings, runId_query_none _ _ _ _ (Or.inr rfl)] at h
      exact absurd h (by rintro ⟨⟩)
    | cons phase rest =>
      rw [VerifierProgram.queryOpenings, runId_query _ _ _ _ _ _ _ _ hR] at h
      split at h
      · exact endsClear_ret _ ⟨sp, stream, rest, R⟩ a st' hg h
      · exact absurd h (by rintro ⟨⟩)

/-! ## The grinds -/

theorem endsAny_grind_bind (bits : ℕ) {f : Unit → VerifierProgram α} (hf : EndsAny (f ())) :
    EndsAny ((VerifierProgram.grindProofOfWork bits).bind f) :=
  endsAny_bind_right fun _ ↦ hf

/-! ## The sumchecks -/

theorem endsClear_sumcheck (claim : E) (count : ℕ) : ∀ eqs : List (Option E),
    EndsClear (sumcheck claim count eqs) := by
  intro eqs
  induction eqs generalizing claim with
  | nil => exact endsClear_ret _
  | cons e eqs ih =>
    unfold sumcheck
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine (endsAny_bind_right fun _ ↦ ?_).clear
    exact endsAny_sampleE.bind fun _ ↦ (ih _).bind fun _ ↦ endsClear_ret _

theorem endsAny_sumcheck (claim : E) (count : ℕ) (e : Option E) (eqs : List (Option E)) :
    EndsAny (sumcheck claim count (e :: eqs)) := by
  unfold sumcheck
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine endsAny_bind_right fun _ ↦ ?_
  exact endsAny_sampleE.bind fun _ ↦ (endsClear_sumcheck _ _ _).bind fun _ ↦ endsClear_ret _

/-- A search for `EndsClear` and `EndsAny` through binds and the primitives. -/
macro "ends" : tactic => `(tactic| repeat' (first
  | with_reducible exact endsClear_ret _
  | with_reducible exact endsClear_require _
  | with_reducible exact endsClear_liftOption _
  | with_reducible exact endsClear_readN _
  | with_reducible exact endsClear_sampleN _
  | with_reducible exact endsAny_readE
  | with_reducible exact endsAny_sampleE
  | with_reducible exact endsAny_readE.clear
  | with_reducible exact endsAny_sampleE.clear
  | with_reducible exact endsClear_queryOpenings _ _
  | with_reducible (refine EndsClear.bind (endsClear_readN _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_require _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_queryOpenings _ _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_ret _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_sampleN _) fun _ ↦ ?_)
  | with_reducible (refine (EndsAny.bind endsAny_readE fun _ ↦ ?_).clear)
  | with_reducible (refine (EndsAny.bind endsAny_sampleE fun _ ↦ ?_).clear)
  | with_reducible (refine EndsClear.bind (endsClear_liftOption _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_sumcheck _ _ _) fun _ ↦ ?_)
  | with_reducible exact endsClear_sumcheck _ _ _
  | split))

/-! ## The prefix's phases -/

theorem endsClear_readSizes (bytecode : List K) : EndsClear (readAnnouncedSizes bytecode) := by
  unfold readAnnouncedSizes
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  ends

theorem endsClear_commit (hh ww : ℕ) : EndsClear (VerifierProgram.readCommitment hh ww) := by
  rintro ⟨⟨S, P, g⟩, stream, os, R⟩ a st' hg h
  simp only at hg
  subst hg
  match stream, h with
  | [], h => exact absurd h (by rintro ⟨⟩)
  | [_], h => exact absurd h (by rintro ⟨⟩)
  | x0 :: x1 :: xs, h =>
    have e : runId (VerifierProgram.readCommitment hh ww) ⟨⟨S, P, none⟩, x0 :: x1 :: xs, os, R⟩ =
        some ((), ⟨Id.run (Compile.absorb keccakF1600 (Id.run (Compile.absorb keccakF1600
          ⟨S, P, none⟩ x0 dsObserve)) x1 dsObserve), xs, os,
          R ++ [(digestFromHalves (x0, x1), hh, ww)]⟩) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    show (Id.run (Compile.absorb keccakF1600 _ x1 dsObserve)).ground = none
    rw [absorb_ground, absorb_ground]

theorem endsClear_commitStack (μ r : ℕ) : EndsClear (commitStack μ r) := by
  unfold commitStack
  simp only [VerifierProgram.bind_eq]
  refine EndsClear.bind (endsClear_liftOption _) fun config ↦ ?_
  split
  · exact endsAny_fail.clear
  · exact endsClear_commit _ _

theorem endsAny_readOod (μ : ℕ) : EndsAny (readOod μ) := by
  unfold readOod
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine endsAny_bind_right fun _ ↦ endsAny_bind_right fun _ ↦ ?_
  exact endsAny_readE.bind fun _ ↦ endsClear_ret _

theorem endsAny_busChallenges (d : ℕ) : EndsAny (busChallenges d) := by
  unfold busChallenges
  refine endsAny_bind_right fun _ ↦ endsAny_bind_right fun _ ↦ ?_
  exact endsAny_sampleE.bind fun _ ↦ endsClear_ret _

theorem endsAny_gkrStep (n : ℕ) (last : Bool) (s : GkrState) : EndsAny (gkrStep (n + 1) last s) := by
  unfold gkrStep
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  repeat (first
    | exact (endsAny_sampleN (Nat.succ_pos _)).bind fun _ ↦ endsClear_ret _
    | refine endsAny_bind_right fun _ ↦ ?_)

theorem endsClear_gkrLayers : ∀ (n : ℕ) (s : GkrState), EndsClear (gkrLayers n s)
  | 0, _ => endsClear_ret _
  | 1, s => by
    unfold gkrLayers
    simp only [VerifierProgram.bind_eq]
    exact ((endsAny_gkrStep 0 _ _).bind fun _ ↦ endsClear_gkrLayers 0 _).clear
  | n + 2, s => by
    unfold gkrLayers
    split
    · simp only [VerifierProgram.bind_eq]
      exact ((endsAny_gkrStep 0 _ _).bind fun _ ↦ endsClear_gkrLayers (n + 1) _).clear
    · simp only [VerifierProgram.bind_eq]
      exact ((endsAny_gkrStep 1 _ _).bind fun _ ↦ endsClear_gkrLayers n _).clear

theorem endsClear_gkrPhase (depth : ℕ) : EndsClear (Tables.gkrPhase depth) := by
  unfold Tables.gkrPhase verifyGkrGrandProducts
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc]
  refine (endsAny_readE.bind fun _ ↦ ?_).clear
  refine (endsAny_readE.bind fun _ ↦ ?_).clear
  refine EndsClear.bind (endsClear_gkrLayers _ _) fun _ ↦ ?_
  ends

theorem endsAny_tablesSeg (ev : List K → List E → E → VerifierProgram Unit) (L : Layout)
    (pi : Digest) (weights : List E) (beta : E) (point tv : List E) :
    EndsAny (Tables.tablesSeg ev L pi weights beta point tv) := by
  unfold Tables.tablesSeg
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine endsAny_bind_right fun _ ↦ endsAny_bind_right fun _ ↦ ?_
  unfold publicInputPhase
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind]
  exact endsAny_sampleE.bind fun _ ↦ endsClear_ret _

theorem endsAny_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    EndsAny (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  generalize List.range keccakDepth = steps
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  repeat' (first
    | with_reducible (refine (endsAny_readN (show 0 < kBits by decide)).bind fun _ ↦ ?_)
    | with_reducible (refine endsAny_bind_right fun _ ↦ ?_)
    | split)
  all_goals ends

theorem endsAny_keccakPhaseClaims (layout : Layout) (claims : List ColumnClaim) :
    EndsAny (keccakPhaseClaims layout claims) := by
  unfold keccakPhaseClaims
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine endsAny_bind_right fun _ ↦ ?_
  exact (endsAny_verifyKeccak _ _ _).bind fun _ ↦ by ends

theorem endsAny_ringSwitch (point s : List E) : EndsAny (ringSwitch point s) := by
  unfold ringSwitch
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine endsAny_bind_right fun _ ↦ ?_
  exact (endsAny_sampleN (by decide)).bind fun _ ↦ endsClear_ret _

/-! ## The stacked opening -/

theorem endsAny_liftOption_bind {o : Option α} {f : α → VerifierProgram β}
    (hf : ∀ a, o = some a → EndsAny (f a)) : EndsAny ((liftOption o).bind f) := by
  cases o with
  | none => exact endsAny_fail
  | some a => exact hf a rfl

/-- **Every deployed ladder's final level queries.** -/
theorem ladder_lastQ {μ r : ℕ} {levels : List Whir.Level} (h : Whir.ladder μ r = some levels) :
    ∀ l ∈ levels.getLast?, 1 ≤ l.queries := by
  have hadm : Whir.Admissible μ r := by
    unfold Whir.ladder at h
    split at h
    · assumption
    · cases h
  have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
      ∀ levels, Whir.ladder μ r = some levels → ∀ l ∈ levels.getLast?, 1 ≤ l.queries := by
    decide +kernel
  have hb : μ < Whir.maxLogStack + 1 ∧ r < 5 := by
    unfold Whir.Admissible at hadm
    omega
  exact key μ hb.1 r hb.2 hadm levels h

theorem endsAny_sampleQueriesAux (depth : ℕ) : ∀ fuel rem, 0 < fuel → 0 < rem →
    EndsAny (sampleQueriesAux depth fuel rem)
  | 0, _, h, _ => absurd h (by omega)
  | fuel + 1, rem, _, hr => by
    unfold sampleQueriesAux
    simp only [hr.ne', ↓reduceIte]
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact endsAny_sampleE.bind fun _ ↦ (endsClear_sampleQueriesAux depth _ _).bind fun _ ↦
      endsClear_ret _
where
  endsClear_sampleQueriesAux (depth : ℕ) : ∀ fuel rem, EndsClear (sampleQueriesAux depth fuel rem)
    | 0, _ => endsClear_ret _
    | fuel + 1, rem => by
      unfold sampleQueriesAux
      split
      · exact endsClear_ret _
      · simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
        exact (endsAny_sampleE.bind fun _ ↦ (endsClear_sampleQueriesAux depth _ _).bind fun _ ↦
          endsClear_ret _).clear

theorem endsAny_sampleQueries {depth n : ℕ} (hn : 0 < n) : EndsAny (sampleQueries depth n) :=
  endsAny_sampleQueriesAux depth n n hn hn

theorem endsAny_whirLevelsOpen (logN laneFolds : ℕ) : ∀ (index : ℕ) (levels : List Whir.Level)
    (s : WhirState), (∀ l ∈ levels.getLast?, 1 ≤ l.queries) →
      EndsAny (Whir.whirLevelsOpen logN laneFolds index levels s)
  | _, [], _, _ => endsAny_fail
  | index, [level], s, hq => by
    have hq1 : 1 ≤ level.queries := hq level rfl
    rw [Whir.whirLevelsOpen]
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine endsAny_bind_right fun p ↦ ?_
    obtain ⟨s', rounds⟩ := p
    dsimp only
    refine endsAny_bind_right fun _ ↦ endsAny_bind_right fun _ ↦ ?_
    refine (endsAny_sampleQueries (by omega)).bind fun _ ↦ ?_
    ends
  | index, level :: next :: rest, s, hq => by
    have ih := fun s ↦ endsAny_whirLevelsOpen logN laneFolds (index + 1) (next :: rest) s
      fun l hl ↦ hq l hl
    rw [Whir.whirLevelsOpen]
    generalize Whir.whirLevelsOpen logN laneFolds (index + 1) (next :: rest) = W at ih ⊢
    simp only [VerifierProgram.bind_eq]
    refine endsAny_bind_right fun p ↦ ?_
    obtain ⟨s', rounds⟩ := p
    dsimp only
    repeat (first | exact ih _ | refine endsAny_bind_right fun _ ↦ ?_)

theorem endsAny_whirOpen (μ r : ℕ) (target : E) : EndsAny (Whir.whirOpen μ r target) := by
  unfold Whir.whirOpen
  simp only [VerifierProgram.bind_eq]
  exact endsAny_liftOption_bind fun levels h ↦
    endsAny_whirLevelsOpen μ _ 0 levels _ (ladder_lastQ h)

theorem endsClear_sumcheckNZ (claim : E) (count : ℕ) : ∀ eqs : List (Option E),
    EndsClear (Limits.sumcheckNZ claim count eqs) := by
  intro eqs
  induction eqs generalizing claim with
  | nil => exact endsClear_ret _
  | cons e eqs ih =>
    unfold Limits.sumcheckNZ
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine (endsAny_bind_right fun _ ↦ ?_).clear
    exact endsAny_sampleE.bind fun _ ↦ (endsClear_require _).bind fun _ ↦
      (ih _).bind fun _ ↦ endsClear_ret _

theorem endsAny_whirLevelsOpenNZ_last (logN laneFolds index : ℕ) (level : Whir.Level)
    (s : WhirState) (hq1 : 1 ≤ level.queries) :
    EndsAny (Limits.whirLevelsOpenNZ logN laneFolds index [level] s) := by
  rw [Limits.whirLevelsOpenNZ]
  simp only [VerifierProgram.bind_eq]
  refine endsAny_bind_right fun p ↦ ?_
  obtain ⟨s', rounds⟩ := p
  dsimp only
  refine endsAny_bind_right fun _ ↦ endsAny_bind_right fun _ ↦ ?_
  refine (endsAny_sampleQueries (by omega)).bind fun _ ↦ ?_
  refine EndsClear.bind (endsClear_require _) fun _ ↦ ?_
  refine EndsClear.bind (endsClear_queryOpenings _ _) fun _ ↦ ?_
  refine EndsClear.bind (endsClear_require _) fun _ ↦ ?_
  refine EndsClear.bind (endsClear_sumcheckNZ _ _ _) fun _ ↦ ?_
  exact endsClear_ret _

theorem endsAny_whirLevelsOpenNZ (logN laneFolds : ℕ) : ∀ (index : ℕ) (levels : List Whir.Level)
    (s : WhirState), (∀ l ∈ levels.getLast?, 1 ≤ l.queries) →
      EndsAny (Limits.whirLevelsOpenNZ logN laneFolds index levels s)
  | _, [], _, _ => endsAny_fail
  | index, [level], s, hq => endsAny_whirLevelsOpenNZ_last logN laneFolds index level s (hq level rfl)
  | index, level :: next :: rest, s, hq => by
    have ih := fun s ↦ endsAny_whirLevelsOpenNZ logN laneFolds (index + 1) (next :: rest) s
      fun l hl ↦ hq l hl
    rw [Limits.whirLevelsOpenNZ]
    generalize Limits.whirLevelsOpenNZ logN laneFolds (index + 1) (next :: rest) = W at ih ⊢
    simp only [VerifierProgram.bind_eq]
    refine endsAny_bind_right fun p ↦ ?_
    obtain ⟨s', rounds⟩ := p
    dsimp only
    repeat (first | exact ih _ | refine endsAny_bind_right fun _ ↦ ?_)

theorem endsAny_whirOpenNZ (μ r : ℕ) (target : E) : EndsAny (Limits.whirOpenNZ μ r target) := by
  unfold Limits.whirOpenNZ
  simp only [VerifierProgram.bind_eq]
  exact endsAny_liftOption_bind fun levels h ↦
    endsAny_whirLevelsOpenNZ μ _ 0 levels _ (ladder_lastQ h)

end
end LeanVM.Guest.B1.VerifySub
