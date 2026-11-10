/-
  LeanVM.Guest.B1.Whir.CInvNZ

  The run refusing a vanishing combiner (`Limits.whirOpenNZ`), read at the honest run's levels:
  no round's combiner vanishes at a queried point.
-/

module

public import LeanVM.Guest.B1.Whir.CTrace
public import LeanVM.Guest.NZProgram

/-!
# No vanishing combiner, level by level

`Limits.whirOpenNZ` is `whirOpen` with `require`s added (a nonzero `γ`, `λ`, closing challenge,
and `CombinersNZ queries rounds` at each level). On the words and openings of an honest run
(`LvsRunD`, Whir/CTrace) it runs the same levels, so each level's check holds at that run's
positions and rounds: `LvsNZ`, `lvsNZ_of_run`, and `combinersNZ_folds` (`FoldsNonzero` at each
queried point, as `OqStatic` asks).

* `rT_*`: the carried run (`Tables.runT`) read backwards, primitive by primitive.
* `foldRounds_run`: the fold rounds forward from `RoundsOk`; `foldRoundsNZ_runT`: an accepting run
  of `foldRoundsNZ` is one of `foldRounds`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none
  runT_bind)

@[expose] public section

variable {α : Type}

/-! ## The carried run, backwards -/

theorem rT_bind_some {β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {st : TSt}
    {r : β × TSt} (h : runT (p.bind f) st = some r) :
    ∃ a st1, runT p st = some (a, st1) ∧ runT (f a) st1 = some r := by
  rw [runT_bind] at h
  obtain ⟨⟨a, st1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨a, st1, h1, h2⟩

theorem rT_readE {f : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runT (VerifierProgram.readScalar.bind f) st = some r) :
    ∃ x xs, st.stream = x :: xs ∧ st.ground = none ∧
      runT (f x) ⟨st.sponge.absorb x dsObserve, none, xs, st.openings, st.roots⟩ = some r := by
  replace h : runT (.read f) st = some r := h
  obtain ⟨s, g, stream, os, R⟩ := st
  match stream, g, h with
  | [], _, h => simp [runT] at h
  | _ :: _, some _, h => simp [runT] at h
  | x :: xs, none, h => exact ⟨x, xs, rfl, rfl, h⟩

theorem rT_sampleE_none {f : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runT (VerifierProgram.sampleChallenge.bind f) st = some r) (hg : st.ground = none) :
    runT (f st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, none, st.stream, st.openings, st.roots⟩ =
      some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  exact h

theorem rT_sampleE_some {f : E → VerifierProgram α} {st : TSt} {r : α × TSt} {c : E}
    (h : runT (VerifierProgram.sampleChallenge.bind f) st = some r) (hg : st.ground = some c) :
    runT (f c) ⟨st.sponge, none, st.stream, st.openings, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  exact h

theorem rT_grindPoW {b : ℕ} (hb : b ≠ 0) {f : Unit → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runT ((VerifierProgram.grindProofOfWork b).bind f) st = some r) :
    ∃ n xs, st.stream = n :: xs ∧ st.ground = none ∧
      runT (f ()) ⟨⟨capOf (st.sponge.nonceState n), []⟩, some (challengeOf (st.sponge.nonceState n)),
        xs, st.openings, st.roots⟩ = some r := by
  unfold VerifierProgram.grindProofOfWork at h
  simp only [hb, ↓reduceIte] at h
  replace h : runT (.grind b (f ())) st = some r := h
  obtain ⟨s, g, stream, os, R⟩ := st
  match stream, g, h with
  | [], _, h => simp [runT] at h
  | _ :: _, some _, h => simp [runT] at h
  | n :: xs, none, h =>
    simp only [runT] at h
    by_cases hp : powOk b (Keccak.lane (s.nonceState n) 2) = true
    · simp only [hp, ↓reduceIte] at h
      exact ⟨n, xs, rfl, rfl, h⟩
    · simp [hp] at h

theorem rT_commitB {hh ww : ℕ} {f : Unit → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runT ((VerifierProgram.readCommitment hh ww).bind f) st = some r) :
    ∃ x0 x1 xs, st.stream = x0 :: x1 :: xs ∧ st.ground = none ∧
      runT (f ()) ⟨(st.sponge.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, st.openings,
        st.roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ = some r := by
  replace h : runT (.commit hh ww (f ())) st = some r := h
  obtain ⟨s, g, stream, os, R⟩ := st
  match stream, g, h with
  | [], _, h => simp [runT] at h
  | [_], _, h => simp [runT] at h
  | _ :: _ :: _, some _, h => simp [runT] at h
  | x0 :: x1 :: xs, none, h => exact ⟨x0, x1, xs, rfl, rfl, h⟩

theorem rT_queryB {i : ℕ} {ps : List ℕ} {f : List (List K) → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runT ((VerifierProgram.queryOpenings i ps).bind f) st = some r) :
    ∃ root height width phase rest rows, st.roots[i]? = some (root, height, width) ∧
      st.openings = phase :: rest ∧
      Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) = some rows ∧
      runT (f rows) ⟨st.sponge, st.ground, st.stream, rest, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  cases hR : R[i]? with
  | none => simp [VerifierProgram.queryOpenings, VerifierProgram.bind, runT, hR] at h
  | some v =>
    obtain ⟨root, height, width⟩ := v
    cases os with
    | nil => simp [VerifierProgram.queryOpenings, VerifierProgram.bind, runT, hR] at h
    | cons phase rest =>
      simp only [VerifierProgram.queryOpenings, VerifierProgram.bind, runT, hR] at h
      cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
          phase) with
      | none => simp [hop] at h
      | some rows =>
        simp only [hop] at h
        exact ⟨root, height, width, phase, rest, rows, rfl, rfl, hop, h⟩

theorem rT_require {c : Prop} [Decidable c] {f : Unit → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runT ((VerifierProgram.require c).bind f) st = some r) :
    c ∧ runT (f ()) st = some r := by
  unfold VerifierProgram.require at h
  split_ifs at h with hc
  · exact ⟨hc, h⟩
  · simp [VerifierProgram.bind, runT] at h

theorem rT_readScalars {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runT ((VerifierProgram.readScalars n).bind f) st = some r →
      ∃ ys xs, ys.length = n ∧ st.stream = ys ++ xs ∧
        runT (f ys) ⟨st.sponge.absorbAll ys dsObserve, none, xs, st.openings, st.roots⟩ = some r
  | 0, st, r, hg, h => by
    refine ⟨[], st.stream, rfl, rfl, ?_⟩
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only at hg
    subst hg
    exact h
  | n + 1, st, r, hg, h => by
    have e : (VerifierProgram.readScalars (n + 1)).bind f =
        VerifierProgram.readScalar.bind fun x ↦ (VerifierProgram.readScalars n).bind fun xs ↦
          f (x :: xs) := by
      show ((VerifierProgram.read VerifierProgram.ret).bind fun x ↦
        ((VerifierProgram.readScalars n).bind fun xs ↦ VerifierProgram.ret (x :: xs))).bind f = _
      simp only [VerifierProgram.bind_assoc]
      rfl
    rw [e] at h
    obtain ⟨x, xs, hs, -, h1⟩ := rT_readE h
    obtain ⟨ys, zs, hl, hz, h2⟩ := rT_readScalars n _ r rfl h1
    simp only at hz
    exact ⟨x :: ys, zs, by simp [hl], by rw [hs, hz]; rfl, h2⟩

theorem rT_sampleChallenges {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runT ((VerifierProgram.sampleChallenges n).bind f) st = some r →
      runT (f (st.sponge.squeezeN n).1)
        ⟨(st.sponge.squeezeN n).2, none, st.stream, st.openings, st.roots⟩ = some r
  | 0, st, r, hg, h => by
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only at hg
    subst hg
    exact h
  | n + 1, st, r, hg, h => by
    have e : (VerifierProgram.sampleChallenges (n + 1)).bind f =
        VerifierProgram.sampleChallenge.bind fun x ↦ (VerifierProgram.sampleChallenges n).bind
          fun xs ↦ f (x :: xs) := by
      show ((VerifierProgram.sample VerifierProgram.ret).bind fun x ↦
        ((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x :: xs))).bind f = _
      simp only [VerifierProgram.bind_assoc]
      rfl
    rw [e] at h
    exact rT_sampleChallenges n _ r rfl (rT_sampleE_none h hg)

theorem rT_sampleOod2 {mu : ℕ} {f : List (List E) → VerifierProgram α} {st : TSt}
    {r : α × TSt} (hg : st.ground = none)
    (h : runT ((sampleOodPoints mu 2).bind f) st = some r) :
    runT (f [(st.sponge.squeezeN mu).1, ((st.sponge.squeezeN mu).2.squeezeN mu).1])
      ⟨((st.sponge.squeezeN mu).2.squeezeN mu).2, none, st.stream, st.openings, st.roots⟩ = some r := by
  have e : (sampleOodPoints mu 2).bind f = (VerifierProgram.sampleChallenges mu).bind fun p1 ↦
      (VerifierProgram.sampleChallenges mu).bind fun p2 ↦ f [p1, p2] := by
    simp only [sampleOodPoints, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rw [e] at h
  exact rT_sampleChallenges mu _ r rfl (rT_sampleChallenges mu st r hg h)

theorem rT_liftOption {β : Type} {o : Option α} {f : α → VerifierProgram β} {st : TSt}
    {r : β × TSt} (h : runT ((liftOption o).bind f) st = some r) :
    ∃ a, o = some a ∧ runT (f a) st = some r := by
  cases o with
  | none =>
    change runT VerifierProgram.fail st = some r at h
    simp [runT] at h
  | some a => exact ⟨a, rfl, h⟩

/-! ## The fold rounds -/

/-- **The fold rounds forward**, every round passing. -/
theorem foldRounds_run : ∀ (n : ℕ) (s : WhirState) (fs ws : List E), ws.length = 7 * n →
    RoundsOk n fs ws →
    RunsTo (foldRounds n s) ⟨fs, []⟩ ws (roundsSpec n s fs ws) ⟨roundsCap n fs ws, []⟩
  | 0, s, fs, ws, hl, _ => by
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    exact runsTo_ret _ _
  | n + 1, s, fs, ws, hl, hok => by
    obtain ⟨hg, -, hok'⟩ := hok
    obtain ⟨n1, u0, v0, c0, v1, c1, n2, he⟩ : ∃ n1 u0 v0 c0 v1 c1 n2,
        ws.take 7 = [n1, u0, v0, c0, v1, c1, n2] := by
      have : (ws.take 7).length = 7 := by simp; omega
      match ws.take 7, this with
      | [a, b, c, d, e, f, g], _ => exact ⟨a, b, c, d, e, f, g, rfl⟩
    rw [he] at hg
    have h1 := opening_round_run s fs n1 u0 v0 c0 v1 c1 n2 hg.1 hg.2
    have ih := foldRounds_run n (roundSpec s fs (ws.take 7)).1 (roundSponge fs (ws.take 7)).cap
      (ws.drop 7) (by simp; omega) hok'
    rw [he] at ih
    have h := h1.bind (f := fun x ↦ match x with
        | (s, round) => do
          let (s, rounds) ← foldRounds n s
          return (s, round :: rounds))
      (ih.bind (f := fun x ↦ match x with
        | (s', rounds) => (pure (s', (roundSpec s fs [n1, u0, v0, c0, v1, c1, n2]).2 :: rounds) :
          VerifierProgram (WhirState × List FoldRound))) (runsTo_ret _ _))
    refine RunsTo.of_eq h rfl ?_ ?_ ?_
    · rw [← he, List.append_nil, List.take_append_drop]
    · simp only [roundsSpec, he]
    · simp only [roundsCap, he]

/-- Requires added to a program. -/
inductive Adds : {α : Type} → VerifierProgram α → VerifierProgram α → Prop
  | ret {α : Type} (a : α) : Adds (.ret a) (.ret a)
  | fail {α : Type} : Adds (α := α) .fail .fail
  | read {α : Type} {k k' : E → VerifierProgram α} : (∀ x, Adds (k' x) (k x)) → Adds (.read k') (.read k)
  | sample {α : Type} {k k' : E → VerifierProgram α} : (∀ x, Adds (k' x) (k x)) →
      Adds (.sample k') (.sample k)
  | grind {α : Type} {b : ℕ} {k k' : VerifierProgram α} : Adds k' k → Adds (.grind b k') (.grind b k)
  | commit {α : Type} {h w : ℕ} {k k' : VerifierProgram α} : Adds k' k →
      Adds (.commit h w k') (.commit h w k)
  | query {α : Type} {i : ℕ} {ps : List ℕ} {k k' : List (List K) → VerifierProgram α} :
      (∀ r, Adds (k' r) (k r)) → Adds (.query i ps k') (.query i ps k)
  | req {α : Type} (c : Prop) [Decidable c] {k' k : VerifierProgram α} : Adds k' k →
      Adds ((VerifierProgram.require c).bind fun _ ↦ k') k

theorem Adds.refl : ∀ (p : VerifierProgram α), Adds p p
  | .ret a => .ret a
  | .fail => .fail
  | .read k => .read fun x ↦ Adds.refl (k x)
  | .sample k => .sample fun x ↦ Adds.refl (k x)
  | .grind _ k => .grind (Adds.refl k)
  | .commit _ _ k => .commit (Adds.refl k)
  | .query _ _ k => .query fun r ↦ Adds.refl (k r)

theorem Adds.bind {β : Type} {p' p : VerifierProgram α} (h : Adds p' p) {f' f : α → VerifierProgram β}
    (hf : ∀ a, Adds (f' a) (f a)) : Adds (p'.bind f') (p.bind f) := by
  induction h with
  | ret a => exact hf a
  | fail => exact .fail
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih
  | req c _ ih =>
    rw [VerifierProgram.bind_assoc]
    exact .req c ih

/-- **A run of a program with requires added is one of the program.** -/
theorem Adds.run {p' p : VerifierProgram α} (h : Adds p' p) :
    ∀ st r, runT p' st = some r → runT p st = some r := by
  induction h with
  | ret a => intro st r h; exact h
  | fail => intro st r h; simp [runT] at h
  | read _ ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | x :: xs, none, h => exact ih x _ r h
  | sample _ ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases g with
    | none => exact ih _ _ r h
    | some c => exact ih c _ r h
  | grind _ ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | n :: xs, none, h =>
      simp only [runT] at h ⊢
      split_ifs at h with hp
      simp only [hp, ↓reduceIte]
      exact ih _ r h
  | commit _ ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | [_], _, h => simp [runT] at h
    | _ :: _ :: _, some _, h => simp [runT] at h
    | x0 :: x1 :: xs, none, h => exact ih _ r h
  | @query i ps k k' _ ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [runT, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runT, hR] at h
      | cons phase rest =>
        simp only [runT, hR] at h ⊢
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h ⊢
          exact ih rows _ r h
  | req c _ ih =>
    intro st r h
    exact ih st r (rT_require h).2

theorem adds_foldRoundsNZ : ∀ (n : ℕ) (s : WhirState),
    Adds (Limits.foldRoundsNZ n s) (foldRounds n s)
  | 0, s => Adds.refl _
  | n + 1, s => by
    unfold Limits.foldRoundsNZ foldRounds
    refine Adds.bind ?_ fun p ↦ ?_
    · unfold Limits.foldRoundNZ foldRound
      refine Adds.bind (Adds.refl _) fun _ ↦ ?_
      refine Adds.bind (Adds.refl _) fun _ ↦ ?_
      refine Adds.bind (Adds.refl _) fun _ ↦ ?_
      refine Adds.bind (Adds.refl _) fun _ ↦ ?_
      refine Adds.bind (Adds.refl _) fun _ ↦ ?_
      refine Adds.bind (Adds.refl _) fun _ ↦ ?_
      refine Adds.bind (Adds.refl _) fun _ ↦ ?_
      refine Adds.bind (Adds.refl _) fun _ ↦ ?_
      refine Adds.bind (Adds.refl _) fun gamma ↦ ?_
      exact Adds.req _ (Adds.refl _)
    · obtain ⟨s', round⟩ := p
      exact Adds.bind (adds_foldRoundsNZ n s') fun _ ↦ Adds.refl _


/-! ## The levels -/

/-- **No round's combiner vanishes at a queried point**, level by level of the honest run. -/
def LvsNZ (logN : ℕ) : ℕ → List Whir.Level → WhirState → List E → List LvD → Prop
  | _, [level], s, cap, [LvD.fin rw W] =>
    Limits.CombinersNZ (W.qs (rsF level cap rw)
      (logN - (rsSt level s cap rw).gammas.length + level.logInvRate) level.queries)
      (rsRounds level s cap rw)
  | index, level :: next :: rest, s, cap, LvD.next rw W :: ds =>
    Limits.CombinersNZ (W.qs (rsF level cap rw) (logN - (rsSt level s cap rw).gammas.length)
      (logN - (rsSt level s cap rw).gammas.length + level.logInvRate) level.queries)
      (rsRounds level s cap rw) ∧
    LvsNZ logN (index + 1) (next :: rest)
      (W.glued logN index level (rsSt level s cap rw) (rsF level cap rw) (rsRounds level s cap rw))
      (capOf ((W.F3 (rsF level cap rw) (logN - (rsSt level s cap rw).gammas.length)
        (logN - (rsSt level s cap rw).gammas.length + level.logInvRate) level.queries).nonceState W.n2))
      ds
  | _, _, _, _, _ => True

/-- The fold rounds of a level of the honest run, carried. -/
theorem rounds_nz {n : ℕ} {s : WhirState} {cap rw rest : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {p : WhirState × List FoldRound} {st1 : TSt}
    (hc : ∃ sp, (⟨cap, []⟩ : Fs).Carries sp) (hrl : rw.length = 7 * n) (hok : RoundsOk n cap rw)
    (h : runT (Limits.foldRoundsNZ n s) ⟨⟨cap, []⟩, none, rw ++ rest, os, R⟩ = some (p, st1)) :
    p = roundsSpec n s cap rw ∧ st1 = ⟨⟨roundsCap n cap rw, []⟩, none, rest, os, R⟩ := by
  have h1 := (adds_foldRoundsNZ n s).run _ _ h
  rw [runT_of_runsTo (foldRounds_run n s cap rw hrl hok) hc rest os R] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

/-- **The run refusing a vanishing combiner, on the honest run's words and openings, checks every
level's combiners.** -/
theorem lvsNZ_of_run (logN lane : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (cap : List E)
      (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (w : WhirEnd)
      (ds : List LvD) (r : WhirEnd × TSt), (∃ sp, (⟨cap, []⟩ : Fs).Carries sp) →
      (∀ l ∈ levels, LvOk logN l) → LvsRunD logN lane index levels s cap R xs os w ds →
      runT (Limits.whirLevelsOpenNZ logN lane index levels s) ⟨⟨cap, []⟩, none, xs, os, R⟩ = some r →
      LvsNZ logN index levels s cap ds
  | [level], index, s, cap, R, xs, os, w, [LvD.fin rw W], r, hc, hlv, hD, h => by
    have hl := hlv level (by simp)
    obtain ⟨hrl, hrok, hxs, hos, hfin, -⟩ := hD
    rw [Limits.whirLevelsOpenNZ] at h
    obtain ⟨p, st1, h1, h2⟩ := rT_bind_some h
    rw [hxs] at h1
    obtain ⟨rfl, rfl⟩ := rounds_nz hc hrl hrok h1
    set mu := logN - (rsSt level s cap rw).gammas.length with hmu
    set d := mu + level.logInvRate with hd
    obtain ⟨fold, xs1, hfl, hs1, h⟩ := rT_readScalars (2 ^ mu + level.fold) _ _ rfl h2
    obtain ⟨nn, xs2, hs2, -, h⟩ := rT_grindPoW (by decide) h
    obtain ⟨qs', st2, hq1, h⟩ := rT_bind_some h
    simp only at hs1 hs2
    have hw : W.fold ++ ([W.nn] ++ tailWords W.pairs) = fold ++ nn :: xs2 := by
      rw [← List.append_assoc]; exact hs1.trans (by rw [hs2])
    obtain ⟨e1, e2⟩ := List.append_inj hw (by rw [hfl, hfin.flen])
    simp only [List.singleton_append, List.cons.injEq] at e2
    obtain ⟨e2, -⟩ := e2
    subst e1 e2
    have hcq : ∃ sp, Fs.CarriesGround (capOf (W.qS (rsF level cap rw)))
        (challengeOf (W.qS (rsF level cap rw))) sp :=
      ⟨⟨W.qS (rsF level cap rw), [], some (challengeOf (W.qS (rsF level cap rw)))⟩, rfl, rfl, rfl⟩
    have hfq := runT_of_runsFromG (sampleQueries_runG d level.queries hl.hP hl.2.2
      (capOf (W.qS (rsF level cap rw))) (challengeOf (W.qS (rsF level cap rw)))) hcq xs2 os R
    have e := hq1.symm.trans hfq
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact (rT_require h).1
  | level :: next :: rest, index, s, cap, R, xs, os, w, LvD.next rw W :: ds, r, hc, hlv, hD, h => by
    have hl := hlv level (by simp)
    obtain ⟨xs', os', hrl, hrok, hxs, hos, hnext, hD'⟩ := hD
    rw [Limits.whirLevelsOpenNZ] at h
    obtain ⟨p, st1, h1, h2⟩ := rT_bind_some h
    rw [hxs, List.append_assoc] at h1
    obtain ⟨rfl, rfl⟩ := rounds_nz hc hrl hrok h1
    set mu := logN - (rsSt level s cap rw).gammas.length with hmu
    set d := mu + level.logInvRate with hd
    obtain ⟨x0, x1, xs1, hs1, -, h⟩ := rT_commitB h2
    obtain ⟨high, xs2, hhl, hs2, h⟩ := rT_readScalars level.fold _ _ rfl h
    have h := rT_sampleOod2 rfl h
    obtain ⟨ys, xs3, hyl, hs3, h⟩ := rT_readScalars Whir.oodSamples _ _ rfl h
    obtain ⟨y0, y1, rfl⟩ : ∃ y0 y1, ys = [y0, y1] := by
      match ys, hyl with
      | [y0, y1], _ => exact ⟨y0, y1, rfl⟩
    obtain ⟨nn, xs4, hs4, -, h⟩ := rT_grindPoW (by decide) h
    obtain ⟨qs', st2, hq1, h⟩ := rT_bind_some h
    simp only at hs1 hs2 hs3 hs4
    have hw := hs1
    rw [hs2, hs3, hs4] at hw
    simp only [NextW.words, List.cons_append, List.append_assoc, List.cons.injEq,
      List.nil_append] at hw
    obtain ⟨rfl, rfl, hw⟩ := hw
    obtain ⟨e1, e2⟩ := List.append_inj hw (by rw [hhl, hnext.hlen])
    subst e1
    simp only [List.cons.injEq] at e2
    obtain ⟨rfl, rfl, rfl, e3⟩ := e2
    subst e3
    have hcq : ∃ sp, Fs.CarriesGround (capOf (W.qS (rsF level cap rw) mu))
        (challengeOf (W.qS (rsF level cap rw) mu)) sp :=
      ⟨⟨W.qS (rsF level cap rw) mu, [], some (challengeOf (W.qS (rsF level cap rw) mu))⟩, rfl, rfl, rfl⟩
    have hfq := runT_of_runsFromG (sampleQueries_runG d level.queries hl.hP hl.2.2
      (capOf (W.qS (rsF level cap rw) mu)) (challengeOf (W.qS (rsF level cap rw) mu))) hcq
      (W.n2 :: xs') os (R ++ [(digestFromHalves (W.x0, W.x1), levelShape mu next (2 * 2 ^ next.fold))])
    have e := hq1.symm.trans hfq
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨hcomb, h⟩ := rT_require h
    obtain ⟨n2, xs5, hs5, -, h⟩ := rT_grindPoW (by decide) h
    simp only [List.cons.injEq] at hs5
    obtain ⟨rfl, rfl⟩ := hs5
    have h := rT_sampleE_some h rfl
    obtain ⟨-, h⟩ := rT_require h
    obtain ⟨root, height, width, phase, orest, rows, -, hos', hop, h⟩ := rT_queryB h
    simp only at hos'
    rw [hos] at hos'
    simp only [List.cons.injEq] at hos'
    obtain ⟨rfl, rfl⟩ := hos'
    obtain ⟨-, -, -, rfl⟩ := phase_of_some hop
    exact ⟨hcomb, lvsNZ_of_run logN lane (next :: rest) (index + 1) _ _ _ xs' os' w ds r
      (carries_capOf _) (fun l hl' ↦ hlv l (by simp_all)) hD' h⟩
  | [], _, _, _, _, _, _, _, _, _, _, _, hD, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, [], _, _, _, hD, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.next _ _ :: _, _, _, _, hD, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.fin _ _ :: _ :: _, _, _, _, hD, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, [], _, _, _, hD, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, LvD.fin _ _ :: _, _, _, _, hD, _ => by simp [LvsRunD] at hD

/-- **On an honest run, the run refusing a vanishing combiner checks every level's combiners.** -/
theorem whirOpenNZ_lvs {μ r : ℕ} {target : E} {S : KeccakState} {xs : List E}
    {os : List (List Opening)} {root : Digest} {w w' : WhirEnd} {s' : Fs}
    {roots' : List (Digest × ℕ × ℕ)} {cfg : List Whir.Level} {ds : List LvD} (hlad : LadderOk μ r)
    (hcfg : Whir.ladder μ r = some cfg)
    (hD : LvsRunD μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [], []⟩ (capOf S)
      [(root, stackShape μ r)] xs os w ds)
    (h : RunsWith (Limits.whirOpenNZ μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w' s'
      roots') :
    LvsNZ μ 0 cfg ⟨target, [], []⟩ (capOf S) ds := by
  have e := runT_of_runsWith h (carries_capOf S) [] []
  simp only [List.append_nil] at e
  unfold Limits.whirOpenNZ at e
  obtain ⟨cfg', hc', e⟩ := rT_liftOption e
  rw [hcfg, Option.some.injEq] at hc'
  subst hc'
  exact lvsNZ_of_run μ _ cfg 0 _ _ _ xs os w ds _ (carries_capOf S) (hlad cfg hcfg) hD e

/-- **A level's combiners at its positions**, as `OqStatic` asks. -/
theorem combinersNZ_folds {qs : List ℕ} {rounds : List FoldRound}
    (h : Limits.CombinersNZ qs rounds) : ∀ q ∈ qs, FoldsNonzero rounds (K.ofBits q) :=
  fun q hq r hr ↦ h q hq r hr

end
end LeanVM.Guest.B1.Whir
