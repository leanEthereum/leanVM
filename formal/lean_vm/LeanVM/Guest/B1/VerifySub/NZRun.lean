/-
  LeanVM.Guest.B1.VerifySub.NZRun

  Deployed runs of the Spec's programs, for the completeness direction: a sequence's run splits,
  a run refusing zero challenges is a run, a run's query steps split, and a deployed run that
  reads all it is given is a `RunsWith`.
-/

module

public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Tables.RunF
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Protocol.WithHashBridge

/-!
# Deployed runs, for completeness

* `runId_bind_some`: a run of `p.bind f` is a run of `p`, then of `f`.
* `runId_of_rz`: a run of `p.refusingZeroChallenge` is a run of `p`.
* `queryStepsOf_bind`: the query steps of `p.bind f` are `p`'s, then `f a`'s, past a run of `p`
  to `a`.
* `runsWith_of_runId`: a run that reads all the words and openings it is given, from a carried
  sponge to one with no ground challenge, is a `RunsWith`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {α β : Type}

/-- **A sequence's run splits.** -/
theorem runId_bind_some {p : VerifierProgram α} {f : α → VerifierProgram β}
    {st : VerifierProgramState} {r : β × VerifierProgramState}
    (h : runId (p.bind f) st = some r) :
    ∃ a st', runId p st = some (a, st') ∧ runId (f a) st' = some r := by
  rw [run_bind] at h
  obtain ⟨⟨a, st'⟩, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨a, st', h1, h2⟩

/-- A query's run, past its root and phase. -/
theorem runId_query (i : ℕ) (ps : List ℕ) (k : List (List K) → VerifierProgram α) (sp : Sponge)
    (stream : List E) (phase : List Opening) (rest : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) {root : Digest} {height width : ℕ}
    (hR : R[i]? = some (root, height, width)) :
    runId (VerifierProgram.query i ps k) ⟨sp, stream, phase :: rest, R⟩ =
      match Id.run (openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
      | some rows => runId (k rows) ⟨sp, stream, rest, R⟩
      | none => none := by
  simp only [runId, Compile.runWithHash, hR]
  rfl

/-- A query's run fails without its root or a phase. -/
theorem runId_query_none (i : ℕ) (ps : List ℕ) (k : List (List K) → VerifierProgram α)
    (st : VerifierProgramState)
    (h : st.roots[i]? = none ∨ st.openings = []) :
    runId (VerifierProgram.query i ps k) st = none := by
  obtain ⟨sp, stream, os, R⟩ := st
  simp only at h
  rcases h with h | rfl
  · simp only [runId, Compile.runWithHash, h]
    rfl
  · simp only [runId, Compile.runWithHash]
    rcases R[i]? with _ | ⟨root, height, width⟩ <;> rfl

/-- **A run refusing zero challenges is a run.** -/
theorem runId_of_rz : ∀ (p : VerifierProgram α) (st : VerifierProgramState)
    (r : α × VerifierProgramState), runId p.refusingZeroChallenge st = some r → runId p st = some r
  | .ret _, _, _, h => h
  | .fail, _, _, h => h
  | .read k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, r, h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x :: xs, none, h => exact runId_of_rz (k x) _ r h
  | .sample k, st, r, h => by
    have e1 : runId (VerifierProgram.sample k).refusingZeroChallenge st =
        runId (if (Id.run (squeeze keccakF1600 st.sponge)).1 = 0 then VerifierProgram.fail
          else (k (Id.run (squeeze keccakF1600 st.sponge)).1).refusingZeroChallenge)
          { st with sponge := (Id.run (squeeze keccakF1600 st.sponge)).2 } := rfl
    have e2 : runId (VerifierProgram.sample k) st =
        runId (k (Id.run (squeeze keccakF1600 st.sponge)).1)
          { st with sponge := (Id.run (squeeze keccakF1600 st.sponge)).2 } := rfl
    rw [e1] at h
    rw [e2]
    split at h
    · exact absurd h (by rintro ⟨⟩)
    · exact runId_of_rz _ _ r h
  | .grind bits k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, r, h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | n :: xs, none, h =>
      simp only [VerifierProgram.refusingZeroChallenge, runId, Compile.runWithHash] at h ⊢
      generalize absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n = N at h ⊢
      obtain ⟨pw, sp'⟩ := N
      change (if powOk bits pw = true then _ else _) = _ at h
      change (if powOk bits pw = true then _ else _) = _
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact runId_of_rz k _ r h
      · exact absurd h (by rintro ⟨⟩)
  | .commit hh ww k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, r, h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | [_], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x0 :: x1 :: xs, none, h => exact runId_of_rz k _ r h
  | .query i ps k, ⟨sp, stream, os, R⟩, r, h => by
    cases hR : R[i]? with
    | none =>
      rw [show (VerifierProgram.query i ps k).refusingZeroChallenge =
        VerifierProgram.query i ps fun rows ↦ (k rows).refusingZeroChallenge from rfl,
        runId_query_none _ _ _ _ (Or.inl hR)] at h
      exact absurd h (by rintro ⟨⟩)
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil =>
        rw [show (VerifierProgram.query i ps k).refusingZeroChallenge =
          VerifierProgram.query i ps fun rows ↦ (k rows).refusingZeroChallenge from rfl,
          runId_query_none _ _ _ _ (Or.inr rfl)] at h
        exact absurd h (by rintro ⟨⟩)
      | cons phase rest =>
        rw [show (VerifierProgram.query i ps k).refusingZeroChallenge =
          VerifierProgram.query i ps fun rows ↦ (k rows).refusingZeroChallenge from rfl,
          runId_query _ _ _ _ _ _ _ _ hR] at h
        rw [runId_query _ _ _ _ _ _ _ _ hR]
        split at h
        · rename_i rows hrows
          exact runId_of_rz (k rows) _ r h
        · exact absurd h (by rintro ⟨⟩)

/-- The query steps' openings are the deployed run's. -/
theorem openPhase_keccak (root : Digest) (height width : ℕ) (ps : List ℕ) (phase : List Opening) :
    Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) =
      Id.run (openPhaseWithHash (m := Id) keccak256 root height width ps phase) := by
  rw [openPhase_eq_withHash, keccak256With_keccakF1600]

/-- A query's steps, past its root and phase. -/
theorem queryStepsOf_query (i : ℕ) (ps : List ℕ) (k : List (List K) → VerifierProgram α)
    (sp : Sponge) (stream : List E) (phase : List Opening) (rest : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) {root : Digest} {height width : ℕ}
    (hR : R[i]? = some (root, height, width)) :
    Limits.queryStepsOf (VerifierProgram.query i ps k) ⟨sp, stream, phase :: rest, R⟩ =
      match Id.run (openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
      | some rows => (height, ps.zip phase) :: Limits.queryStepsOf (k rows) ⟨sp, stream, rest, R⟩
      | none => [] := by
  simp only [Limits.queryStepsOf, hR, openPhase_keccak]
  rfl

/-- **A sequence's query steps split** past a run of its first part. -/
theorem queryStepsOf_bind (f : α → VerifierProgram β) : ∀ (p : VerifierProgram α)
    (st : VerifierProgramState) (a : α) (st' : VerifierProgramState), runId p st = some (a, st') →
      Limits.queryStepsOf (p.bind f) st = Limits.queryStepsOf p st ++ Limits.queryStepsOf (f a) st'
  | .ret b, st, a, st', h => by
    have e : runId (VerifierProgram.ret b) st = some (b, st) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .fail, _, _, _, h => absurd h (by rintro ⟨⟩)
  | .read k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x :: xs, none, h => exact queryStepsOf_bind f (k x) _ a st' h
  | .sample k, st, a, st', h => queryStepsOf_bind f (k _) _ a st' h
  | .grind bits k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | n :: xs, none, h =>
      simp only [runId, Compile.runWithHash] at h
      simp only [VerifierProgram.bind, Limits.queryStepsOf]
      generalize absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n = N at h ⊢
      obtain ⟨pw, sp'⟩ := N
      change (if powOk bits pw = true then _ else _) = _ at h
      split at h
      · rename_i hp
        change (if powOk bits pw = true then _ else _) =
          (if powOk bits pw = true then _ else _) ++ _
        simp only [hp, ↓reduceIte]
        exact queryStepsOf_bind f k _ a st' h
      · exact absurd h (by rintro ⟨⟩)
  | .commit hh ww k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | [_], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x0 :: x1 :: xs, none, h => exact queryStepsOf_bind f k _ a st' h
  | .query i ps k, ⟨sp, stream, os, R⟩, a, st', h => by
    cases hR : R[i]? with
    | none =>
      rw [runId_query_none _ _ _ _ (Or.inl hR)] at h
      exact absurd h (by rintro ⟨⟩)
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil =>
        rw [runId_query_none _ _ _ _ (Or.inr rfl)] at h
        exact absurd h (by rintro ⟨⟩)
      | cons phase rest =>
        rw [runId_query _ _ _ _ _ _ _ _ hR] at h
        rw [show (VerifierProgram.query i ps k).bind f =
          VerifierProgram.query i ps fun rows ↦ (k rows).bind f from rfl,
          queryStepsOf_query _ _ _ _ _ _ _ _ hR, queryStepsOf_query _ _ _ _ _ _ _ _ hR]
        split at h
        · rename_i rows hrows
          simp only [List.cons_append]
          exact congrArg _ (queryStepsOf_bind f (k rows) _ a st' h)
        · exact absurd h (by rintro ⟨⟩)

/-- **A run reading all it is given is a `RunsWith`**: from a sponge the guest carries to one with
no ground challenge. -/
theorem runsWith_of_runId {p : VerifierProgram α} {s : Fs} {sp : Sponge} (hs : s.Carries sp)
    {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {a : α}
    {t : VerifierProgramState} (h : runId p ⟨sp, xs, os, R⟩ = some (a, t))
    (hst : t.stream = []) (hos : t.openings = []) (hg : t.sponge.ground = none) :
    Whir.RunsWith p s xs os R a (Tables.fsOfT t.sponge) t.roots := by
  have hT := Tables.runT_of_runId p ⟨s, none, xs, os, R⟩ sp hs a t h
  obtain ⟨pre, opre, hs1, ho1, hf⟩ := Tables.runT_frame p _ a _ hT
  simp only [hst, hos, List.append_nil] at hs1 ho1
  subst hs1 ho1
  intro sp2 hs2 rest orest
  have e := hf rest orest
  obtain ⟨sp', hc, hr⟩ := Tables.runId_of_runT p ⟨s, none, xs ++ rest, os ++ orest, R⟩ sp2 hs2 a _ e
  refine ⟨sp', ?_, hr⟩
  obtain ⟨h1, h2, h3⟩ := hc
  exact ⟨h1, h2, h3.trans hg⟩

end
end LeanVM.Guest.B1.VerifySub
