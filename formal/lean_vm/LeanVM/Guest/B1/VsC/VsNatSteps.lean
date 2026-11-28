/-
  LeanVM.Guest.B1.VsC.VsNatSteps

  A deployed run's recorded queries and query steps, packed steps included; the steps of a
  plain carried run on a longer stream; the stacked opening ending with no ground challenge.
-/

module

public import LeanVM.Guest.B1.VsC.Os.CCapsRun
public import LeanVM.Guest.B1.VsC.Os.CInvOpen
public import LeanVM.Guest.B1.VsC.Os.CInvLevel

/-!
# Recorded queries and query steps of a deployed run

* **`runSteps`**: a deployed run of `p` keeps its roots as a prefix, consumes one phase of openings
  per query step, and `recordQueries p` runs alongside it, its queries (each read at the end's
  roots' height, `hgtAt`) being `p`'s query steps without their openings (`stepPos`). Packed steps
  included, unlike `Whir.runId_recordQueries`'s converse.
* **`queryStepsOf_bind'`**, `runId_bind_q`: the steps of `p.bind f` are `p`'s, then `f a`'s, past a
  run of `p` to `a`, packed steps included.
* `noPacked_recordQueries`; **`qstT_frame`**: a carried run's steps on a longer stream and more
  phases are the same.
* `EndsClear`, `EndsAny`, **`endsAny_whirOpen`** (restored from the bus era's
  `VerifySub/Ends.lean`, the deployed ladder's final level querying from `LadderOk`): a run of the
  stacked opening ends with no ground challenge waiting.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT NoPacked)
open LeanVM.Guest.B1.VerifySub (runId_bind_some)

@[expose] public section

variable {α β : Type}

/-! ## Recorded queries -/

/-- A recorded query at the roots `R`: its tree's height, and its positions. -/
def hgtAt (R : List (Digest × ℕ × ℕ)) (q : ℕ × List ℕ) : ℕ × List ℕ := ((R[q.1]?.map (·.2.1)).getD 0, q.2)

/-- A query step without its openings. -/
def stepPos (b : ℕ × List (ℕ × Opening)) : ℕ × List ℕ := (b.1, b.2.map Prod.fst)

/-- A grind's deployed run, past its nonce. -/
theorem grind_run (bits : ℕ) (k : VerifierProgram α) (S0 : KeccakState) (P0 : List (E × ℕ)) (n : E) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    runId (.grind bits k) ⟨⟨S0, P0, none⟩, n :: xs, os, R⟩ =
      if powOk bits (Id.run (absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n)).1 = true then
        runId k ⟨(Id.run (absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n)).2, xs, os, R⟩
      else none := by
  simp only [runId, Compile.runWithHash]
  generalize absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n = N
  obtain ⟨pw, sp'⟩ := N
  rfl

/-- A grind's query steps, past its nonce. -/
theorem grind_steps (bits : ℕ) (k : VerifierProgram α) (S0 : KeccakState) (P0 : List (E × ℕ)) (n : E)
    (xs : List E) (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    Limits.queryStepsOf (.grind bits k) ⟨⟨S0, P0, none⟩, n :: xs, os, R⟩ =
      if powOk bits (Id.run (absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n)).1 = true then
        Limits.queryStepsOf k ⟨(Id.run (absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n)).2, xs, os, R⟩
      else [] := by
  simp only [Limits.queryStepsOf]

/-- **A deployed run, its steps and its recorded queries.** -/
theorem runSteps : ∀ (p : VerifierProgram α) (st : VerifierProgramState) (a : α) (st' : VerifierProgramState),
    runId p st = some (a, st') →
    st.roots <+: st'.roots ∧ (Limits.queryStepsOf p st).length + st'.openings.length = st.openings.length ∧
      ∃ qr, runId (Prover.recordQueries p) st = some ((a, qr), st') ∧
        qr.map (hgtAt st'.roots) = (Limits.queryStepsOf p st).map stepPos
  | .ret b, st, a, st', h => by
    have e : runId (VerifierProgram.ret b) st = some (b, st) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.prefix_refl _, by simp [Limits.queryStepsOf], [], rfl, rfl⟩
  | .fail, _, _, _, h => absurd h (by rintro ⟨⟩)
  | .read k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x :: xs, none, h =>
      simp only [runId, Compile.runWithHash] at h
      simp only [runId, Compile.runWithHash, Prover.recordQueries, Limits.queryStepsOf]
      generalize absorb (m := Id) keccakF1600 ⟨S0, P0, none⟩ x dsObserve = N at h ⊢
      exact runSteps (k x) _ a st' h
  | .sample k, ⟨sp, stream, os, R⟩, a, st', h => by
    simp only [runId, Compile.runWithHash] at h
    simp only [runId, Compile.runWithHash, Prover.recordQueries, Limits.queryStepsOf]
    generalize Compile.squeeze (m := Id) keccakF1600 sp = N at h ⊢
    obtain ⟨c, sp1⟩ := N
    exact runSteps (k c) _ a st' h
  | .readPacked n k, ⟨sp, stream, os, R⟩, a, st', h => by
    simp only [runId, Compile.runWithHash] at h
    simp only [runId, Compile.runWithHash, Prover.recordQueries, Limits.queryStepsOf]
    generalize observePacked (m := Id) keccakF1600 sp (stream.take n) = N at h ⊢
    split at h
    · rename_i hc
      simp only [ite_eq_left hc]
      exact runSteps (k _) _ a st' h
    · exact absurd h (by rintro ⟨⟩)
  | .samplePacked n k, ⟨sp, stream, os, R⟩, a, st', h => by
    simp only [runId, Compile.runWithHash] at h
    simp only [runId, Compile.runWithHash, Prover.recordQueries, Limits.queryStepsOf]
    generalize samplesPacked (m := Id) keccakF1600 sp n = N at h ⊢
    obtain ⟨cs, sp1⟩ := N
    exact runSteps (k cs) _ a st' h
  | .grind bits k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | n :: xs, none, h =>
      rw [grind_run] at h
      rw [show Prover.recordQueries (VerifierProgram.grind bits k) = .grind bits (Prover.recordQueries k) from rfl,
        grind_run bits (Prover.recordQueries k), grind_steps]
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact runSteps k _ a st' h
      · exact absurd h (by rintro ⟨⟩)
  | .commit hh ww k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | [_], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x0 :: x1 :: xs, none, h =>
      simp only [runId, Compile.runWithHash] at h
      simp only [runId, Compile.runWithHash, Prover.recordQueries, Limits.queryStepsOf]
      generalize absorb (m := Id) keccakF1600 ⟨S0, P0, none⟩ x0 dsObserve = N at h ⊢
      generalize absorb (m := Id) keccakF1600 N x1 dsObserve = N' at h ⊢
      obtain ⟨h1, h2, h3⟩ := runSteps k _ a st' h
      exact ⟨(List.prefix_append R _).trans h1, h2, h3⟩
  | .query i ps k, ⟨sp, stream, os, R⟩, a, st', h => by
    cases hR : R[i]? with
    | none =>
      rw [VerifySub.runId_query_none _ _ _ _ (Or.inl hR)] at h
      exact absurd h (by rintro ⟨⟩)
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil =>
        rw [VerifySub.runId_query_none _ _ _ _ (Or.inr rfl)] at h
        exact absurd h (by rintro ⟨⟩)
      | cons phase rest =>
        rw [VerifySub.runId_query _ _ _ _ _ _ _ _ hR] at h
        simp only [Prover.recordQueries]
        rw [VerifySub.runId_query _ _ _ _ _ _ _ _ hR, VerifySub.queryStepsOf_query _ _ _ _ _ _ _ _ hR]
        cases hop : Id.run (openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
        | none =>
          rw [hop] at h
          exact absurd h (by rintro ⟨⟩)
        | some rows =>
          rw [hop] at h
          simp only
          obtain ⟨i1, i2, qr, i3, i4⟩ := runSteps (k rows) _ a st' h
          change (Limits.queryStepsOf (k rows) ⟨sp, stream, rest, R⟩).length + st'.openings.length = rest.length
            at i2
          have hlt : i < R.length := (List.getElem?_eq_some_iff.mp hR).1
          obtain ⟨t, ht⟩ := i1
          have hR' : st'.roots[i]? = some (root, height, width) := by
            rw [← ht]
            exact (List.getElem?_append_left hlt).trans hR
          obtain ⟨hlen, -, -, -⟩ := phase_of_some hop
          refine ⟨⟨t, ht⟩, ?_, (i, ps) :: qr, ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · rw [run_bind, i3]
            rfl
          · have hz : (ps.zip phase).map Prod.fst = ps := List.map_fst_zip (by omega)
            rw [List.map_cons, List.map_cons, i4]
            simp only [hgtAt, stepPos, hR', Option.map_some, Option.getD_some, hz]

/-- **A sequence's query steps split**, packed steps included. -/
theorem queryStepsOf_bind' (f : α → VerifierProgram β) : ∀ (p : VerifierProgram α) (st : VerifierProgramState)
    (a : α) (st' : VerifierProgramState), runId p st = some (a, st') →
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
    | x :: xs, none, h => exact queryStepsOf_bind' f (k x) _ a st' h
  | .sample k, st, a, st', h => queryStepsOf_bind' f (k _) _ a st' h
  | .readPacked n k, ⟨sp, stream, os, R⟩, a, st', h => by
    simp only [runId, Compile.runWithHash] at h
    simp only [VerifierProgram.bind, Limits.queryStepsOf]
    generalize observePacked (m := Id) keccakF1600 sp (stream.take n) = N at h ⊢
    split at h
    · rename_i hc
      simp only [ite_eq_left hc]
      exact queryStepsOf_bind' f (k _) _ a st' h
    · exact absurd h (by rintro ⟨⟩)
  | .samplePacked n k, ⟨sp, stream, os, R⟩, a, st', h => by
    simp only [runId, Compile.runWithHash] at h
    simp only [VerifierProgram.bind, Limits.queryStepsOf]
    generalize samplesPacked (m := Id) keccakF1600 sp n = N at h ⊢
    obtain ⟨cs, sp1⟩ := N
    exact queryStepsOf_bind' f (k cs) _ a st' h
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
        exact queryStepsOf_bind' f k _ a st' h
      · exact absurd h (by rintro ⟨⟩)
  | .commit hh ww k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | [_], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x0 :: x1 :: xs, none, h => exact queryStepsOf_bind' f k _ a st' h
  | .query i ps k, ⟨sp, stream, os, R⟩, a, st', h => by
    cases hR : R[i]? with
    | none =>
      rw [VerifySub.runId_query_none _ _ _ _ (Or.inl hR)] at h
      exact absurd h (by rintro ⟨⟩)
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil =>
        rw [VerifySub.runId_query_none _ _ _ _ (Or.inr rfl)] at h
        exact absurd h (by rintro ⟨⟩)
      | cons phase rest =>
        rw [VerifySub.runId_query _ _ _ _ _ _ _ _ hR] at h
        rw [show (VerifierProgram.query i ps k).bind f =
          VerifierProgram.query i ps fun rows ↦ (k rows).bind f from rfl,
          VerifySub.queryStepsOf_query _ _ _ _ _ _ _ _ hR, VerifySub.queryStepsOf_query _ _ _ _ _ _ _ _ hR]
        split at h
        · rename_i rows hrows
          simp only [List.cons_append]
          exact congrArg _ (queryStepsOf_bind' f (k rows) _ a st' h)
        · exact absurd h (by rintro ⟨⟩)

/-- **A sequence's run splits, with its steps.** -/
theorem runId_bind_q {p : VerifierProgram α} {f : α → VerifierProgram β} {st : VerifierProgramState}
    {r : β × VerifierProgramState} (h : runId (p.bind f) st = some r) :
    ∃ a st', runId p st = some (a, st') ∧ runId (f a) st' = some r ∧
      Limits.queryStepsOf (p.bind f) st = Limits.queryStepsOf p st ++ Limits.queryStepsOf (f a) st' := by
  obtain ⟨a, st', h1, h2⟩ := runId_bind_some h
  exact ⟨a, st', h1, h2, queryStepsOf_bind' f p st a st' h1⟩

/-- A run consuming no openings has no step. -/
theorem steps_nil {p : VerifierProgram α} {st : VerifierProgramState} {a : α} {st' : VerifierProgramState}
    (h : runId p st = some (a, st')) (ho : st'.openings.length = st.openings.length) :
    Limits.queryStepsOf p st = [] := by
  have := (runSteps p st a st' h).2.1
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem noPacked_recordQueries : ∀ (p : VerifierProgram α), NoPacked p → NoPacked (Prover.recordQueries p)
  | .ret _, _ => trivial
  | .fail, _ => trivial
  | .read k, h => fun x => noPacked_recordQueries (k x) (h x)
  | .sample k, h => fun x => noPacked_recordQueries (k x) (h x)
  | .readPacked _ _, h => (h : False).elim
  | .samplePacked _ _, h => (h : False).elim
  | .grind _ k, h => noPacked_recordQueries k h
  | .commit _ _ k, h => noPacked_recordQueries k h
  | .query _ _ k, h => fun r => NoPacked.bind (noPacked_recordQueries (k r) (h r)) fun _ => trivial

/-! ## A carried run's steps on a longer stream -/

/-- **A carried run's steps on a longer stream and more phases are the same.** -/
theorem qstT_frame : ∀ (p : VerifierProgram α) (st : TSt) (a : α) (st' : TSt), runT p st = some (a, st') →
    ∀ zs orest, qstT p ⟨st.sponge, st.ground, st.stream ++ zs, st.openings ++ orest, st.roots⟩ = qstT p st
  | .ret b, _, _, _, _, _, _ => rfl
  | .fail, _, _, _, h, _, _ => by simp [runT] at h
  | .readPacked _ _, _, _, _, h, _, _ => by simp [runT] at h
  | .samplePacked _ _, _, _, _, h, _, _ => by simp [runT] at h
  | .read k, ⟨s, g, stream, os, R⟩, a, st', h, zs, orest => by
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | x :: xs, none, h => exact qstT_frame (k x) _ a st' h zs orest
  | .sample k, ⟨s, g, stream, os, R⟩, a, st', h, zs, orest => by
    cases g with
    | none => exact qstT_frame (k _) _ a st' h zs orest
    | some c => exact qstT_frame (k c) _ a st' h zs orest
  | .grind b k, ⟨s, g, stream, os, R⟩, a, st', h, zs, orest => by
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | n :: xs, none, h =>
      simp only [runT] at h
      split at h
      · rename_i hp
        show (if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else _) =
          (if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else _)
        simp only [hp, ↓reduceIte]
        exact qstT_frame k _ a st' h zs orest
      · simp at h
  | .commit hh ww k, ⟨s, g, stream, os, R⟩, a, st', h, zs, orest => by
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | [_], _, h => simp [runT] at h
    | _ :: _ :: _, some _, h => simp [runT] at h
    | x0 :: x1 :: xs, none, h => exact qstT_frame k _ a st' h zs orest
  | .query i ps k, ⟨s, g, stream, os, R⟩, a, st', h, zs, orest => by
    cases hR : R[i]? with
    | none => simp [runT, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runT, hR] at h
      | cons phase rest =>
        simp only [runT, hR] at h
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h
          simp only [List.cons_append, qstT, hR, hop]
          exact congrArg _ (qstT_frame (k rows) _ a st' h zs orest)

/-! ## The stacked opening ends with no ground challenge -/

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

theorem absorb_ground (π : KeccakState → Id KeccakState) (sp : Sponge) (x : E) (t : ℕ) :
    (Id.run (Compile.absorb π sp x t)).ground = sp.ground := by
  unfold Compile.absorb
  split <;> rfl

theorem squeeze_ground (π : KeccakState → Id KeccakState) (sp : Sponge) :
    (Id.run (Compile.squeeze π sp)).2.ground = none := by
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

theorem endsClear_sampleN : ∀ n, EndsClear (VerifierProgram.sampleChallenges n)
  | 0 => endsClear_ret _
  | n + 1 => by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact (endsAny_sampleE.bind fun _ ↦ (endsClear_sampleN n).bind fun _ ↦ endsClear_ret _).clear

theorem endsClear_queryOpenings (i : ℕ) (ps : List ℕ) :
    EndsClear (VerifierProgram.queryOpenings i ps) := by
  rintro ⟨sp, stream, os, R⟩ a st' hg h
  cases hR : R[i]? with
  | none =>
    rw [VerifierProgram.queryOpenings, VerifySub.runId_query_none _ _ _ _ (Or.inl hR)] at h
    exact absurd h (by rintro ⟨⟩)
  | some v =>
    obtain ⟨root, height, width⟩ := v
    cases os with
    | nil =>
      rw [VerifierProgram.queryOpenings, VerifySub.runId_query_none _ _ _ _ (Or.inr rfl)] at h
      exact absurd h (by rintro ⟨⟩)
    | cons phase rest =>
      rw [VerifierProgram.queryOpenings, VerifySub.runId_query _ _ _ _ _ _ _ _ hR] at h
      split at h
      · exact endsClear_ret _ ⟨sp, stream, rest, R⟩ a st' hg h
      · exact absurd h (by rintro ⟨⟩)

theorem endsClear_sumcheck (claim : E) (count : ℕ) : ∀ eqs : List (Option E),
    EndsClear (sumcheck claim count eqs) := by
  intro eqs
  induction eqs generalizing claim with
  | nil => exact endsClear_ret _
  | cons e eqs ih =>
    unfold sumcheck
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine (endsAny_bind_right fun _ ↦ ?_).clear
    refine endsAny_sampleE.bind fun _ ↦ (ih _).bind fun r ↦ ?_
    obtain ⟨_, _⟩ := r
    exact endsClear_ret _

/-- A search for `EndsClear` through binds and the primitives. -/
macro "nends" : tactic => `(tactic| repeat' (first
  | with_reducible exact endsClear_ret _
  | with_reducible exact endsClear_require _
  | with_reducible exact endsClear_liftOption _
  | with_reducible exact endsClear_readN _
  | with_reducible exact endsClear_sampleN _
  | with_reducible exact endsAny_readE.clear
  | with_reducible exact endsAny_sampleE.clear
  | with_reducible exact endsClear_queryOpenings _ _
  | with_reducible exact endsClear_sumcheck _ _ _
  | with_reducible (refine EndsClear.bind (endsClear_readN _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_require _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_queryOpenings _ _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_ret _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_sampleN _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_liftOption _) fun _ ↦ ?_)
  | with_reducible (refine EndsClear.bind (endsClear_sumcheck _ _ _) fun _ ↦ ?_)
  | split))

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
    (s : WhirState), (∀ l ∈ levels, 1 ≤ l.queries) →
      EndsAny (whirLevelsOpen logN laneFolds index levels s)
  | _, [], _, _ => endsAny_fail
  | index, [level], s, hq => by
    have hq1 : 1 ≤ level.queries := hq level (List.mem_singleton_self _)
    rw [whirLevelsOpen]
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine endsAny_bind_right fun p ↦ ?_
    obtain ⟨s', rounds⟩ := p
    dsimp only
    refine endsAny_bind_right fun _ ↦ endsAny_bind_right fun _ ↦ ?_
    refine (endsAny_sampleQueries (by omega)).bind fun _ ↦ ?_
    nends
  | index, level :: next :: rest, s, hq => by
    have ih := fun s ↦ endsAny_whirLevelsOpen logN laneFolds (index + 1) (next :: rest) s
      fun l hl ↦ hq l (List.mem_cons_of_mem _ hl)
    rw [whirLevelsOpen]
    generalize whirLevelsOpen logN laneFolds (index + 1) (next :: rest) = W at ih ⊢
    simp only [VerifierProgram.bind_eq]
    refine endsAny_bind_right fun p ↦ ?_
    obtain ⟨s', rounds⟩ := p
    dsimp only
    repeat (first | exact ih _ | refine endsAny_bind_right fun _ ↦ ?_)

theorem endsAny_liftOption_bind {o : Option α} {f : α → VerifierProgram β}
    (hf : ∀ a, o = some a → EndsAny (f a)) : EndsAny ((liftOption o).bind f) := by
  cases o with
  | none => exact endsAny_fail
  | some a => exact hf a rfl

/-- **The stacked opening ends with no ground challenge**, at the deployed stack logs and rates. -/
theorem endsAny_whirOpen {μ r : ℕ} (h1 : 16 ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4) (target : E) :
    EndsAny (whirOpen μ r target) := by
  unfold whirOpen
  simp only [VerifierProgram.bind_eq]
  exact endsAny_liftOption_bind fun levels hl ↦ endsAny_whirLevelsOpen μ _ 0 levels _ fun l hl' ↦
    (ladderOk_of h1 h2 h3 h4 levels hl l hl').2.2

end
end LeanVM.Guest.B1.VsC
