/-
  LeanVM.Guest.B1.VsC.Os.LeftQs

  The queries `OpenRunQueries` records: one per level, at the level's depth, at its openings' leaf
  indices; so `merkleHints true qs os` is the levels' `levelHints`.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftLq
public import LeanVM.Guest.B1.VsC.OpenStackedA

/-!
# The recorded queries, level by level

* `runId_recordQueries`: a run of `recordQueries p` is a run of `p`, its roots only appended to,
  and its recorded queries, each read at the end's roots' height, are `p`'s query steps without
  their openings.
* `NoQ`: a program with no `query`; its steps are none (`qstT_noQ`), so a run's steps skip it
  (`qstT_bind_noQ`). The `qe_*` lemmas read one primitive's steps, as the `rq_*` lemmas read its run.
* `lvsSteps`: the steps of the honest run's levels, level `j`'s at the height of its roots' entry
  `index + j`. `qstT_levels`: an accepting run's steps, level by level (as `lvsAgree_of_run`);
  `whirOpen_steps`, `honRun_steps`.
* `HonRun.steps_os`: level `l`'s step is at the level's depth, on `os`'s `l`-th phase, each opening
  at its leaf index.
* `merkleHints_range`, `openRunQueries_levels`, `merkleHints_open`: `qs` is
  `(depth_l, (os.getD l []).map leafIndex)` per level, so `merkleHints true qs os` is the levels'
  `levelHints (l == 0) depth_l …` concatenated, the form `HonRun.lqPops_os` gives.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT NoPacked noPacked_whirOpen noPacked_sampleQueries)

@[expose] public section

variable {α : Type}

/-! ## A run of `recordQueries` -/

/-- **A run of `recordQueries p` is a run of `p`**, its roots only appended to, and its queries,
each at the end's roots' height, are `p`'s query steps without their openings. -/
theorem runId_recordQueries : ∀ (p : VerifierProgram α), NoPacked p → ∀ (st : VerifierProgramState) (a : α)
    (qr : List (ℕ × List ℕ)) (st' : VerifierProgramState),
    runId (Prover.recordQueries p) st = some ((a, qr), st') →
    runId p st = some (a, st') ∧ st.roots <+: st'.roots ∧
      qr.map (fun q => ((st'.roots[q.1]?.map (·.2.1)).getD 0, q.2)) =
        (Limits.queryStepsOf p st).map fun b => (b.1, b.2.map Prod.fst)
  | .ret b, _, st, a, qr, st', h => by
    have e : runId (Prover.recordQueries (VerifierProgram.ret b)) st = some ((b, []), st) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, List.prefix_refl _, rfl⟩
  | .fail, _, _, _, _, _, h => absurd h (by rintro ⟨⟩)
  | .readPacked _ _, hnp, _, _, _, _, _ => (hnp : False).elim
  | .samplePacked _ _, hnp, _, _, _, _, _ => (hnp : False).elim
  | .read k, hnp, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, qr, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x :: xs, none, h =>
      simp only [runId, Compile.runWithHash, Prover.recordQueries] at h
      simp only [runId, Compile.runWithHash, Limits.queryStepsOf]
      generalize absorb (m := Id) keccakF1600 ⟨S0, P0, none⟩ x dsObserve = N at h ⊢
      exact runId_recordQueries (k x) (hnp x) _ a qr st' h
  | .sample k, hnp, ⟨sp, stream, os, R⟩, a, qr, st', h => by
    simp only [runId, Compile.runWithHash, Prover.recordQueries] at h
    simp only [runId, Compile.runWithHash, Limits.queryStepsOf]
    generalize Compile.squeeze (m := Id) keccakF1600 sp = N at h ⊢
    obtain ⟨c, sp1⟩ := N
    exact runId_recordQueries (k c) (hnp c) _ a qr st' h
  | .grind bits k, hnp, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, qr, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | n :: xs, none, h =>
      simp only [runId, Compile.runWithHash, Prover.recordQueries] at h
      simp only [runId, Compile.runWithHash, Limits.queryStepsOf]
      generalize absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n = N at h ⊢
      obtain ⟨pw, sp'⟩ := N
      change (if powOk bits pw = true then _ else _) = _ at h
      change (if powOk bits pw = true then _ else _) = _ ∧ _ ∧ _ = List.map _ (if powOk bits pw = true then _ else _)
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact runId_recordQueries k hnp _ a qr st' h
      · exact absurd h (by rintro ⟨⟩)
  | .commit hh ww k, hnp, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, qr, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | [_], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x0 :: x1 :: xs, none, h =>
      simp only [runId, Compile.runWithHash, Prover.recordQueries] at h
      simp only [runId, Compile.runWithHash, Limits.queryStepsOf]
      generalize absorb (m := Id) keccakF1600 ⟨S0, P0, none⟩ x0 dsObserve = N at h ⊢
      generalize absorb (m := Id) keccakF1600 N x1 dsObserve = N' at h ⊢
      obtain ⟨h1, h2, h3⟩ := runId_recordQueries k hnp _ a qr st' h
      exact ⟨h1, (List.prefix_append R _).trans h2, h3⟩
  | .query i ps k, hnp, ⟨sp, stream, os, R⟩, a, qr, st', h => by
    simp only [Prover.recordQueries] at h
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
        rw [VerifySub.runId_query _ _ _ _ _ _ _ _ hR, VerifySub.queryStepsOf_query _ _ _ _ _ _ _ _ hR]
        cases hop : Id.run (openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
        | none =>
          rw [hop] at h
          exact absurd h (by rintro ⟨⟩)
        | some rows =>
          rw [hop] at h
          simp only
          obtain ⟨⟨a0, qr0⟩, st'', h1, h2⟩ := VerifySub.runId_bind_some h
          have e2 : runId (VerifierProgram.ret (a0, (i, ps) :: qr0)) st'' =
            some ((a0, (i, ps) :: qr0), st'') := rfl
          rw [e2, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h2
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
          obtain ⟨i1, i2, i3⟩ := runId_recordQueries (k rows) (hnp rows) _ _ _ _ h1
          refine ⟨i1, i2, ?_⟩
          have hlt : i < R.length := (List.getElem?_eq_some_iff.mp hR).1
          obtain ⟨t, ht⟩ := i2
          have hR' : st''.roots[i]? = some (root, height, width) := by
            rw [← ht]
            exact (List.getElem?_append_left hlt).trans hR
          obtain ⟨hlen, -, -, -⟩ := phase_of_some hop
          rw [List.map_cons, List.map_cons, hR', i3, Option.map_some, Option.getD_some,
            List.map_fst_zip (by omega)]

/-! ## Programs with no query -/

/-- **A program with no `query`.** -/
def NoQ : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoQ (k x)
  | .sample k => ∀ x, NoQ (k x)
  | .readPacked _ k => ∀ x, NoQ (k x)
  | .samplePacked _ k => ∀ x, NoQ (k x)
  | .grind _ k => NoQ k
  | .commit _ _ k => NoQ k
  | .query _ _ _ => False

theorem NoQ.bind {β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : NoQ p) (hf : ∀ a, NoQ (f a)) : NoQ (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x => ih x (hp x)
  | sample k ih => exact fun x => ih x (hp x)
  | readPacked n k ih => exact fun x => ih x (hp x)
  | samplePacked n k ih => exact fun x => ih x (hp x)
  | grind b k ih => exact ih hp
  | commit h w k ih => exact ih hp
  | query i ps k ih => exact (hp : False).elim

theorem NoQ.bind' {β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoQ p)
    (hf : ∀ a, NoQ (f a)) : NoQ (p >>= f) :=
  NoQ.bind hp hf

/-- **A program with no query has no step.** -/
theorem qstT_noQ : ∀ (p : VerifierProgram α), NoQ p → ∀ st : TSt, qstT p st = []
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .readPacked _ _, _, _ => rfl
  | .samplePacked _ _, _, _ => rfl
  | .query _ _ _, hp, _ => (hp : False).elim
  | .read k, hp, ⟨s, g, stream, os, R⟩ => by
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | x :: xs, none => exact qstT_noQ (k x) (hp x) _
  | .sample k, hp, ⟨s, g, stream, os, R⟩ => by
    cases g with
    | some c => exact qstT_noQ (k c) (hp c) _
    | none => exact qstT_noQ (k _) (hp _) _
  | .grind b k, hp, ⟨s, g, stream, os, R⟩ => by
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | n :: xs, none =>
      show (if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else _) = _
      split
      · exact qstT_noQ k hp _
      · rfl
  | .commit hh ww k, hp, ⟨s, g, stream, os, R⟩ => by
    match stream, g with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, some _ => rfl
    | x0 :: x1 :: xs, none => exact qstT_noQ k hp _

/-- **A run's steps skip a part with no query.** -/
theorem qstT_bind_noQ {β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoQ p)
    {st : TSt} {a : α} {st' : TSt} (h : runT p st = some (a, st')) :
    qstT (p.bind f) st = qstT (f a) st' := by
  rw [qstT_bind f p st a st' h, qstT_noQ p hp st, List.nil_append]

theorem noQ_readScalar : NoQ VerifierProgram.readScalar := fun _ => trivial

theorem noQ_sampleChallenge : NoQ VerifierProgram.sampleChallenge := fun _ => trivial

theorem noQ_readScalars : ∀ n, NoQ (VerifierProgram.readScalars n)
  | 0 => trivial
  | n + 1 => NoQ.bind' noQ_readScalar fun _ => NoQ.bind' (noQ_readScalars n) fun _ => trivial

theorem noQ_grindProofOfWork (bits : ℕ) : NoQ (VerifierProgram.grindProofOfWork bits) := by
  unfold VerifierProgram.grindProofOfWork
  split
  · exact trivial
  · exact (trivial : True)

theorem noQ_require (c : Prop) [Decidable c] : NoQ (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split <;> exact trivial

theorem noQ_sumcheckRoundPoly (count : ℕ) (claim : E) (eq : Option E) :
    NoQ (sumcheckRoundPoly count claim eq) := by
  cases eq with
  | none =>
    exact NoQ.bind' noQ_readScalar fun _ => NoQ.bind' (noQ_readScalars _) fun _ =>
      NoQ.bind' (noQ_grindProofOfWork _) fun _ => trivial
  | some _ =>
    exact NoQ.bind' (noQ_readScalars _) fun _ =>
      NoQ.bind' (noQ_grindProofOfWork _) fun _ => trivial

theorem noQ_sumcheck (claim : E) (count : ℕ) : ∀ eqs : List (Option E), NoQ (sumcheck claim count eqs)
  | [] => trivial
  | _ :: eqs => NoQ.bind' (noQ_sumcheckRoundPoly _ _ _) fun _ =>
      NoQ.bind' noQ_sampleChallenge fun _ => NoQ.bind' (noQ_sumcheck _ count eqs) fun _ => trivial

theorem noQ_sampleQueriesAux (depth : ℕ) : ∀ fuel remaining, NoQ (sampleQueriesAux depth fuel remaining)
  | 0, _ => trivial
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    split
    · exact trivial
    · exact NoQ.bind' noQ_sampleChallenge fun _ =>
        NoQ.bind' (noQ_sampleQueriesAux depth fuel _) fun _ => trivial

theorem noQ_sampleQueries (depth count : ℕ) : NoQ (sampleQueries depth count) :=
  noQ_sampleQueriesAux depth count count

theorem noQ_foldRound (s : WhirState) : NoQ (foldRound s) :=
  NoQ.bind' noQ_readScalar fun _ => NoQ.bind' noQ_readScalar fun _ =>
    NoQ.bind' noQ_readScalar fun _ => NoQ.bind' noQ_readScalar fun _ =>
      NoQ.bind' (noQ_grindProofOfWork _) fun _ => NoQ.bind' noQ_sampleChallenge fun _ =>
        NoQ.bind' noQ_sampleChallenge fun _ => trivial

theorem noQ_foldRounds : ∀ (n : ℕ) (s : WhirState), NoQ (foldRounds n s)
  | 0, _ => trivial
  | n + 1, s => NoQ.bind' (noQ_foldRound s) fun _ => NoQ.bind' (noQ_foldRounds n _) fun _ => trivial

/-! ## One primitive's steps -/

theorem qe_readE {f : E → VerifierProgram α} {st : TSt} {x : E} {xs : List E}
    (hs : st.stream = x :: xs) (hg : st.ground = none) :
    qstT (VerifierProgram.readScalar.bind f) st =
      qstT (f x) ⟨st.sponge.absorb x dsObserve, none, xs, st.openings, st.roots⟩ := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hs hg
  subst hs hg
  rfl

theorem qe_sampleE_none {f : E → VerifierProgram α} {st : TSt} (hg : st.ground = none) :
    qstT (VerifierProgram.sampleChallenge.bind f) st =
      qstT (f st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, none, st.stream, st.openings, st.roots⟩ := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  rfl

theorem qe_sampleE_some {f : E → VerifierProgram α} {st : TSt} {c : E} (hg : st.ground = some c) :
    qstT (VerifierProgram.sampleChallenge.bind f) st =
      qstT (f c) ⟨st.sponge, none, st.stream, st.openings, st.roots⟩ := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  rfl

theorem qe_grindPoW {b : ℕ} (hb : b ≠ 0) {f : Unit → VerifierProgram α} {st : TSt}
    {r : α × TSt} {n : E} {xs : List E} (h : runT ((VerifierProgram.grindProofOfWork b).bind f) st = some r)
    (hs : st.stream = n :: xs) (hg : st.ground = none) :
    qstT ((VerifierProgram.grindProofOfWork b).bind f) st =
      qstT (f ()) ⟨⟨capOf (st.sponge.nonceState n), []⟩, some (challengeOf (st.sponge.nonceState n)),
        xs, st.openings, st.roots⟩ := by
  unfold VerifierProgram.grindProofOfWork at h ⊢
  simp only [hb, ↓reduceIte] at h ⊢
  replace h : runT (.grind b (f ())) st = some r := h
  show qstT (.grind b (f ())) st = _
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hs hg
  subst hs hg
  simp only [runT] at h
  by_cases hp : powOk b (Keccak.lane (s.nonceState n) 2) = true
  · show (if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else _) = _
    split
    · rfl
    · rename_i hn
      exact absurd hp hn
  · simp [hp] at h

theorem qe_commitB {hh ww : ℕ} {f : Unit → VerifierProgram α} {st : TSt} {x0 x1 : E} {xs : List E}
    (hs : st.stream = x0 :: x1 :: xs) (hg : st.ground = none) :
    qstT ((VerifierProgram.readCommitment hh ww).bind f) st =
      qstT (f ()) ⟨(st.sponge.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, st.openings,
        st.roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hs hg
  subst hs hg
  rfl

theorem qe_queryB {i : ℕ} {ps : List ℕ} {f : List (List K) → VerifierProgram α} {st : TSt}
    {root : Digest} {height width : ℕ} {phase : List Opening} {rest : List (List Opening)}
    {rows : List (List K)} (hR : st.roots[i]? = some (root, height, width))
    (hos : st.openings = phase :: rest)
    (hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) = some rows) :
    qstT ((VerifierProgram.queryOpenings i ps).bind f) st =
      (height, ps.zip phase) :: qstT (f rows) ⟨st.sponge, st.ground, st.stream, rest, st.roots⟩ := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hR hos
  subst hos
  simp only [VerifierProgram.queryOpenings, VerifierProgram.bind, qstT, hR, hop]

theorem qe_readScalars {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (ys xs : List E) (st : TSt), ys.length = n → st.stream = ys ++ xs → st.ground = none →
      qstT ((VerifierProgram.readScalars n).bind f) st =
        qstT (f ys) ⟨st.sponge.absorbAll ys dsObserve, none, xs, st.openings, st.roots⟩
  | 0, ys, xs, st, hl, hs, hg => by
    obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hl
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only [List.nil_append] at hs hg
    subst hs hg
    rfl
  | n + 1, ys, xs, st, hl, hs, hg => by
    obtain ⟨y, ys', rfl⟩ : ∃ y ys', ys = y :: ys' := by
      cases ys with
      | nil => simp at hl
      | cons y ys' => exact ⟨y, ys', rfl⟩
    have e : (VerifierProgram.readScalars (n + 1)).bind f =
        VerifierProgram.readScalar.bind fun x ↦ (VerifierProgram.readScalars n).bind fun xs ↦
          f (x :: xs) := by
      show ((VerifierProgram.read VerifierProgram.ret).bind fun x ↦
        ((VerifierProgram.readScalars n).bind fun xs ↦ VerifierProgram.ret (x :: xs))).bind f = _
      simp only [VerifierProgram.bind_assoc]
      rfl
    rw [e, qe_readE (x := y) (xs := ys' ++ xs) hs hg]
    exact qe_readScalars n ys' xs _ (by simpa using hl) rfl rfl

theorem qe_sampleChallenges {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt), st.ground = none →
      qstT ((VerifierProgram.sampleChallenges n).bind f) st =
        qstT (f (st.sponge.squeezeN n).1)
          ⟨(st.sponge.squeezeN n).2, none, st.stream, st.openings, st.roots⟩
  | 0, st, hg => by
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only at hg
    subst hg
    rfl
  | n + 1, st, hg => by
    have e : (VerifierProgram.sampleChallenges (n + 1)).bind f =
        VerifierProgram.sampleChallenge.bind fun x ↦ (VerifierProgram.sampleChallenges n).bind
          fun xs ↦ f (x :: xs) := by
      show ((VerifierProgram.sample VerifierProgram.ret).bind fun x ↦
        ((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x :: xs))).bind f = _
      simp only [VerifierProgram.bind_assoc]
      rfl
    rw [e, qe_sampleE_none hg]
    exact qe_sampleChallenges n _ rfl

theorem qe_sampleChallengesG {f : List E → VerifierProgram α} (m : ℕ) {st : TSt} {c : E}
    (hg : st.ground = some c) :
    qstT ((VerifierProgram.sampleChallenges (m + 1)).bind f) st =
      qstT (f (c :: (st.sponge.squeezeN m).1))
        ⟨(st.sponge.squeezeN m).2, none, st.stream, st.openings, st.roots⟩ := by
  have e : (VerifierProgram.sampleChallenges (m + 1)).bind f =
      VerifierProgram.sampleChallenge.bind fun x ↦
        (VerifierProgram.sampleChallenges m).bind fun xs ↦ f (x :: xs) := by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rw [e, qe_sampleE_some hg]
  exact qe_sampleChallenges m _ rfl

/-! ## The levels' steps -/

/-- **The steps of the honest run's levels**: level `j`'s at the height of its roots' entry
`index + j`, its positions with its openings. -/
def lvsSteps (logN : ℕ) : ℕ → List LvAt → List (ℕ × List (ℕ × Opening))
  | _, [] => []
  | index, L :: Ls => (((L.R[index]?).map (·.2.1)).getD 0, (L.qs logN).zip L.phase) ::
      lvsSteps logN (index + 1) Ls

theorem lvsSteps_fin (logN index : ℕ) (level : Whir.Level) (s : WhirState) (cap : List E)
    (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (rw : List E) (W : FinW) :
    lvsSteps logN index (lvsAt logN index [level] s cap R xs os [LvD.fin rw W]) =
      [(((R[index]?).map (·.2.1)).getD 0, (W.qs (rsF level cap rw)
        (logN - (rsSt level s cap rw).alphas.length + level.logInvRate) level.queries).zip W.phase)] :=
  rfl

theorem lvsSteps_next (logN index : ℕ) (level next : Whir.Level) (rest : List Whir.Level) (s : WhirState)
    (cap : List E) (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (rw : List E)
    (W : NextW) (ds : List LvD) :
    lvsSteps logN index (lvsAt logN index (level :: next :: rest) s cap R xs os (LvD.next rw W :: ds)) =
      (((R[index]?).map (·.2.1)).getD 0, (W.qs (rsF level cap rw)
        (logN - (rsSt level s cap rw).alphas.length)
        (logN - (rsSt level s cap rw).alphas.length + level.logInvRate) level.queries).zip W.phase) ::
      lvsSteps logN (index + 1) (lvsAt logN (index + 1) (next :: rest)
        (W.glued logN index level (rsSt level s cap rw) (rsF level cap rw) (rsRounds level s cap rw))
        (W.F3 (rsF level cap rw) (logN - (rsSt level s cap rw).alphas.length)
          (logN - (rsSt level s cap rw).alphas.length + level.logInvRate) level.queries).squeeze.2.cap
        (W.roots (logN - (rsSt level s cap rw).alphas.length) next R)
        (xs.drop (rw.length + W.words.length)) os.tail ds) :=
  rfl

/-- **An accepting run's steps, level by level**: each level's query opens its roots' entry
`index + j` at its positions, on its phase. -/
theorem qstT_levels (logN lane : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (cap : List E)
      (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (w : WhirEnd)
      (ds : List LvD) (r : WhirEnd × TSt), (∃ sp, (⟨cap, []⟩ : Fs).Carries sp) →
      (∀ l ∈ levels, LvOk logN l) → LvsRunD logN lane index levels s cap R xs os w ds →
      index < R.length →
      runT (whirLevelsOpen logN lane index levels s) ⟨⟨cap, []⟩, none, xs, os, R⟩ = some r →
      AllQ (whirLevelsOpen logN lane index levels s) ⟨⟨cap, []⟩, none, xs, os, R⟩ →
      qstT (whirLevelsOpen logN lane index levels s) ⟨⟨cap, []⟩, none, xs, os, R⟩ =
        lvsSteps logN index (lvsAt logN index levels s cap R xs os ds)
  | [level], index, s, cap, R, xs, os, w, [LvD.fin rw W], r, hc, hlv, hD, _, h, hq => by
    have hl := hlv level (by simp)
    obtain ⟨hrl, hrok, hxs, hos, hfin, -⟩ := hD
    rw [lvsSteps_fin]
    rw [whirLevelsOpen] at h hq ⊢
    obtain ⟨p, st1, h1, h2⟩ := rT_bind_some h
    have hq2 := allQ_bind h1 hq
    refine (qstT_bind_noQ (noQ_foldRounds _ _) h1).trans ?_
    rw [hxs] at h1
    obtain ⟨rfl, rfl⟩ := rounds_plain hc hrl hrok h1
    set mu := logN - (rsSt level s cap rw).alphas.length with hmu
    set d := mu + level.logInvRate with hd
    obtain ⟨fold, xs1, hfl, hs1, h, hq⟩ := rq_readScalars (2 ^ mu + level.fold) _ _ rfl h2 hq2
    refine (qe_readScalars (2 ^ mu + level.fold) fold xs1 _ hfl hs1 rfl).trans ?_
    have h0 := h
    obtain ⟨nn, xs2, hs2, hg2, h, hq⟩ := rq_grindPoW (by decide) h hq
    refine (qe_grindPoW (by decide) h0 hs2 hg2).trans ?_
    obtain ⟨qs', st2, hq1, h⟩ := rT_bind_some h
    have hq := allQ_bind hq1 hq
    refine (qstT_bind_noQ (noQ_sampleQueries _ _) hq1).trans ?_
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
      (capOf (W.qS (rsF level cap rw))) (challengeOf (W.qS (rsF level cap rw)))) hcq
      (noPacked_sampleQueries _ _) xs2 os R
    have e := hq1.symm.trans hfq
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨root', height', width', phase, orest, rows, hR', hos', hop, -, -, -⟩ := rq_queryB h hq
    refine (qe_queryB hR' hos' hop).trans ?_
    rw [qstT_noQ _ ?hn _]
    case hn => exact NoQ.bind' (noQ_require _) fun _ => NoQ.bind' (noQ_sumcheck _ _ _) fun _ => trivial
    simp only at hR' hos'
    rw [hos] at hos'
    simp only [List.cons.injEq] at hos'
    obtain ⟨rfl, -⟩ := hos'
    rw [hR']
    rfl
  | level :: next :: rest, index, s, cap, R, xs, os, w, LvD.next rw W :: ds, r, hc, hlv, hD, hRb, h, hq => by
    have hl := hlv level (by simp)
    obtain ⟨xs', os', hrl, hrok, hxs, hos, hnext, hD'⟩ := hD
    have hxs' : xs.drop (rw.length + W.words.length) = xs' := by rw [hxs]; exact drop_words
    have hos2 : os.tail = os' := by rw [hos]; rfl
    rw [lvsSteps_next, hxs', hos2]
    rw [whirLevelsOpen] at h hq ⊢
    obtain ⟨p, st1, h1, h2⟩ := rT_bind_some h
    have hq2 := allQ_bind h1 hq
    refine (qstT_bind_noQ (noQ_foldRounds _ _) h1).trans ?_
    rw [hxs, List.append_assoc] at h1
    obtain ⟨rfl, rfl⟩ := rounds_plain hc hrl hrok h1
    set mu := logN - (rsSt level s cap rw).alphas.length with hmu
    set d := mu + level.logInvRate with hd
    obtain ⟨x0, x1, xs1, hs1, hg1, h, hq⟩ := rq_commitB h2 hq2
    refine (qe_commitB hs1 hg1).trans ?_
    obtain ⟨high, xs2, hhl, hs2, h, hq⟩ := rq_readScalars level.fold _ _ rfl h hq
    refine (qe_readScalars level.fold high xs2 _ hhl hs2 rfl).trans ?_
    have h0 := h
    obtain ⟨n1, xs3, hs3, hg3, h, hq⟩ := rq_grindPoW (by decide) h hq
    refine (qe_grindPoW (by decide) h0 hs3 hg3).trans ?_
    obtain ⟨m, hm⟩ : ∃ m, mu = m + 1 := ⟨mu - 1, by have := hnext.mu1; omega⟩
    rw [← hmu, hm] at h hq ⊢
    obtain ⟨h, hq⟩ := rq_sampleChallengesG m rfl h hq
    refine (qe_sampleChallengesG m rfl).trans ?_
    rw [← hm] at h hq ⊢
    obtain ⟨y0, xs4, hs4, hg4, h, hq⟩ := rq_readE h hq
    refine (qe_readE hs4 hg4).trans ?_
    have h0 := h
    obtain ⟨nn, xs5, hs5, hg5, h, hq⟩ := rq_grindPoW (by decide) h hq
    refine (qe_grindPoW (by decide) h0 hs5 hg5).trans ?_
    obtain ⟨qs', st2, hq1, h⟩ := rT_bind_some h
    have hq := allQ_bind hq1 hq
    refine (qstT_bind_noQ (noQ_sampleQueries _ _) hq1).trans ?_
    simp only at hs1 hs2 hs3 hs4 hs5
    have hw := hs1
    rw [hs2, hs3, hs4, hs5] at hw
    simp only [NextW.words, List.cons_append, List.append_assoc, List.cons.injEq,
      List.nil_append] at hw
    obtain ⟨rfl, rfl, hw⟩ := hw
    obtain ⟨e1, e2⟩ := List.append_inj hw (by rw [hhl, hnext.hlen])
    subst e1
    simp only [List.cons.injEq] at e2
    obtain ⟨rfl, rfl, rfl, e3⟩ := e2
    subst e3
    have hPt := oodPt_eq (rsF level cap rw) (W.x0 :: W.x1 :: W.high) W.n1 mu
    rw [hm, Nat.add_sub_cancel] at hPt
    have eS2 : (((⟨capOf (((((rsF level cap rw).absorb W.x0 dsObserve).absorb W.x1
        dsObserve).absorbAll W.high dsObserve).nonceState W.n1), []⟩ : Fs).squeezeN m).2.absorb W.y0
        dsObserve).nonceState W.nn = W.qS (rsF level cap rw) mu := by
      show _ = ((oodPt (rsF level cap rw) (W.x0 :: W.x1 :: W.high) W.n1 mu).2.absorbAll [W.y0]
        dsObserve).nonceState W.nn
      rw [hm, hPt]
      rfl
    rw [eS2] at hq1
    have hcq : ∃ sp, Fs.CarriesGround (capOf (W.qS (rsF level cap rw) mu))
        (challengeOf (W.qS (rsF level cap rw) mu)) sp :=
      ⟨⟨W.qS (rsF level cap rw) mu, [], some (challengeOf (W.qS (rsF level cap rw) mu))⟩, rfl, rfl, rfl⟩
    have hfq := runT_of_runsFromG (sampleQueries_runG d level.queries hl.hP hl.2.2
      (capOf (W.qS (rsF level cap rw) mu)) (challengeOf (W.qS (rsF level cap rw) mu))) hcq
      (noPacked_sampleQueries _ _) xs' os (R ++ [(digestFromHalves (W.x0, W.x1), levelShape mu next (2 * 2 ^ next.fold))])
    have e := hq1.symm.trans hfq
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨h, hq⟩ := rq_sampleE_none h hq rfl
    refine (qe_sampleE_none rfl).trans ?_
    obtain ⟨root', height', width', phase, orest, rows, hR', hos', hop, h, -, hq⟩ := rq_queryB h hq
    refine (qe_queryB hR' hos' hop).trans ?_
    simp only at hos' hR'
    rw [hos] at hos'
    simp only [List.cons.injEq] at hos'
    obtain ⟨rfl, rfl⟩ := hos'
    obtain ⟨-, -, -, rfl⟩ := phase_of_some hop
    have hood : challengeOf (((((rsF level cap rw).absorb W.x0 dsObserve).absorb W.x1
        dsObserve).absorbAll W.high dsObserve).nonceState W.n1) ::
        ((⟨capOf (((((rsF level cap rw).absorb W.x0 dsObserve).absorb W.x1
        dsObserve).absorbAll W.high dsObserve).nonceState W.n1), []⟩ : Fs).squeezeN m).1 =
          W.ood (rsF level cap rw) mu := by
      show _ = (oodPt (rsF level cap rw) (W.x0 :: W.x1 :: W.high) W.n1 mu).1
      rw [hm, hPt]
      rfl
    rw [hood] at h hq ⊢
    have ih := qstT_levels logN lane (next :: rest) (index + 1) _ _ _ xs' os' w ds r (carries_capOf _)
      (fun l hl' ↦ hlv l (List.mem_cons_of_mem _ hl')) hD' (by simp [NextW.roots]; omega) h hq
    rw [List.getElem?_append_left hRb] at hR'
    rw [hR']
    exact congrArg₂ List.cons rfl ih
  | [], _, _, _, _, _, _, _, _, _, _, _, hD, _, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, [], _, _, _, hD, _, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.next _ _ :: _, _, _, _, hD, _, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.fin _ _ :: _ :: _, _, _, _, hD, _, _, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, [], _, _, _, hD, _, _, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, LvD.fin _ _ :: _, _, _, _, hD, _, _, _ => by simp [LvsRunD] at hD

/-- **The opening's steps, level by level**, on the honest run. -/
theorem whirOpen_steps {μ r : ℕ} {target : E} {S : KeccakState} {xs : List E}
    {os : List (List Opening)} {root : Digest} {w w' : WhirEnd} {s' : Fs}
    {roots' : List (Digest × ℕ × ℕ)} {cfg : List Whir.Level} {ds : List LvD} (hlad : LadderOk μ r)
    (hcfg : Whir.ladder μ r = some cfg)
    (hD : LvsRunD μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [], []⟩ (capOf S)
      [(root, stackShape μ r)] xs os w ds)
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w' s' roots')
    (hcaps : CapsAgree μ r target S xs os root) :
    Limits.queryStepsOf (whirOpen μ r target) ⟨⟨S, [], none⟩, xs, os, [(root, stackShape μ r)]⟩ =
      lvsSteps μ 0 (lvsAt μ 0 cfg ⟨target, [], []⟩ (capOf S) [(root, stackShape μ r)] xs os ds) := by
  have e := runT_of_runsWith hrun (carries_capOf S) (noPacked_whirOpen _ _ _) [] []
  simp only [List.append_nil] at e
  have hq : AllQ (whirOpen μ r target) ⟨⟨capOf S, []⟩, none, xs, os, [(root, stackShape μ r)]⟩ := by
    intro b hb
    rw [← qstT_eq _ (noPacked_whirOpen _ _ _) _ ⟨S, [], none⟩ ⟨rfl, rfl, rfl⟩] at hb
    exact hcaps b hb
  rw [qstT_eq _ (noPacked_whirOpen _ _ _) ⟨⟨capOf S, []⟩, none, xs, os, [(root, stackShape μ r)]⟩
    ⟨S, [], none⟩ ⟨rfl, rfl, rfl⟩]
  unfold whirOpen at e hq ⊢
  obtain ⟨cfg', hc', e⟩ := rT_liftOption e
  rw [hcfg, Option.some.injEq] at hc'
  subst hc'
  rw [hcfg] at hq ⊢
  exact qstT_levels μ _ cfg 0 _ _ _ xs os w ds _ (carries_capOf S) (hlad cfg hcfg) hD (by simp) e hq

/-- **Every accepting run has its honest data**, `honRun_of`, with the opening's steps its levels'. -/
theorem honRun_steps {μ r : ℕ} (h1 : minOpenLog ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4)
    {S : KeccakState} {root : Digest} {target : E} {xs : List E} {os : List (List Opening)} {w : WhirEnd}
    {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hca : CapsAgree μ r target S xs os root) :
    ∃ cfg Ls, HonRun μ r target S root xs os w cfg Ls ∧
      Limits.queryStepsOf (whirOpen μ r target) ⟨⟨S, [], none⟩, xs, os, [(root, stackShape μ r)]⟩ =
        lvsSteps μ 0 Ls := by
  obtain ⟨cfg, hcfg, hL⟩ := whirOpen_honest h1 h2 h3 h4 hrun
  obtain ⟨ds, hD⟩ := LvsRun.data _ _ _ _ _ _ _ _ _ _ hL
  obtain ⟨cfg', hcfg', hC⟩ := candB_sound (candB_all (μ - minOpenLog) (r - 1) (by unfold ligNSizes minOpenLog at *; omega)
    (by omega))
  rw [show μ - minOpenLog + minOpenLog = μ by omega, show r - 1 + 1 = r by omega, hcfg] at hcfg'
  rw [show μ - minOpenLog + minOpenLog = μ by omega, show r - 1 + 1 = r by omega] at hC
  cases hcfg'
  have hA := whirOpen_agree (ladderOk_of h1 h2 h3 h4) hcfg hD hrun hca
  refine ⟨cfg, _, ⟨by unfold minOpenLog at *; omega, by omega, hcfg, hC, lvsAt_run _ _ _ _ _ _ _ _ _ _ _ hD,
    fun i hi ↦ ?_⟩, whirOpen_steps (ladderOk_of h1 h2 h3 h4) hcfg hD hrun hca⟩
  have := lvsAt_agree _ _ _ _ _ _ _ _ _ _ _ hD hA i hi
  simpa using this

/-- `lvsSteps`, indexed. -/
theorem lvsSteps_eq (logN : ℕ) : ∀ (Ls : List LvAt) (i : ℕ),
    lvsSteps logN i Ls = (List.range Ls.length).map fun l =>
      (((((Ls.getD l default).R)[i + l]?).map (·.2.1)).getD 0,
        ((Ls.getD l default).qs logN).zip (Ls.getD l default).phase)
  | [], _ => rfl
  | L :: Ls, i => by
    rw [lvsSteps, lvsSteps_eq logN Ls (i + 1), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    refine congrArg₂ List.cons (by simp) (List.map_congr_left fun l _ => ?_)
    simp only [Function.comp_apply, List.getD_cons_succ]
    rw [show i + 1 + l = i + (l + 1) by omega]

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **Level `l`'s step is at the level's depth, on `os`'s `l`-th phase**, each opening at its leaf
index. -/
theorem steps_os : lvsSteps μ 0 Ls = (List.range (osCfgR (μ - minOpenLog) (r - 1)).levels.length).map
    fun l => ((osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth,
      (os.getD l []).map fun o => (o.leafIndex, o)) := by
  rw [lvsSteps_eq, hR.len]
  refine List.map_congr_left fun l hl => ?_
  have hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length := List.mem_range.mp hl
  have hlL : l < Ls.length := by rw [hR.len]; exact hl
  have hidx := hR.run.phase_idx l hlL
  rw [hR.run.phase_eq l hlL] at hidx
  rw [Nat.zero_add, (hR.roots l hl).2, hR.run.phase_eq l hlL, ← hidx, zip_map_self]
  rfl

end HonRun

/-! ## The recorded queries and the Merkle hints -/

/-- **`merkleHints` over one query a phase**, the queries at the phases' leaf indices: the phases'
`levelHints`, the first `first`. -/
theorem merkleHints_range (d : ℕ → ℕ) : ∀ (os : List (List Opening)) (b : Bool),
    Prover.merkleHints b ((List.range os.length).map fun l => (d l, (os.getD l []).map Opening.leafIndex)) os =
      (List.range os.length).flatMap fun l =>
        Prover.levelHints (b && l == 0) (d l) (os.getD l []).length (os.getD l [])
  | [], _ => rfl
  | o :: os, b => by
    have ih := merkleHints_range (fun l => d (l + 1)) os false
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.flatMap_cons]
    simp only [Prover.merkleHints, List.getD_cons_zero, List.length_map, beq_self_eq_true,
      Bool.and_true]
    congr 1
    rw [List.flatMap_map]
    have e1 : ((fun l => (d l, ((o :: os).getD l []).map Opening.leafIndex)) ∘ Nat.succ) =
        fun l => (d (l + 1), (os.getD l []).map Opening.leafIndex) := by
      funext l
      simp
    rw [e1, ih]
    refine List.flatMap_congr fun l _ => ?_
    simp

/-- **`OpenRunQueries`' queries**, one a level: at the level's depth, at its openings' leaf
indices. -/
theorem openRunQueries_levels {μ r : ℕ} (h1 : minOpenLog ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4)
    {S : KeccakState} {root : Digest} {target : E} {xs : List E} {os : List (List Opening)} {w : WhirEnd}
    {s' : Fs} {roots' : List (Digest × ℕ × ℕ)} {qs : List (ℕ × List ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hq : VsC.OpenRunQueries μ r root target ⟨capOf S, []⟩ xs os qs) :
    os.length = (osCfgR (μ - minOpenLog) (r - 1)).levels.length ∧
      qs = (List.range (osCfgR (μ - minOpenLog) (r - 1)).levels.length).map fun l =>
        ((osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth, (os.getD l []).map Opening.leafIndex) := by
  have hq0 := hq ⟨S, [], none⟩ ⟨rfl, rfl, rfl⟩ [] []
  simp only [List.append_nil] at hq0
  obtain ⟨hagree, a, qr, stf, hrq, hqs⟩ := hq0
  obtain ⟨cfg, Ls, hR, hsteps⟩ := honRun_steps h1 h2 h3 h4 hrun hagree
  obtain ⟨-, -, hmap⟩ := runId_recordQueries _ (noPacked_whirOpen _ _ _) _ a qr stf hrq
  refine ⟨hR.os_len, ?_⟩
  rw [hqs, hmap, hsteps, hR.steps_os, List.map_map]
  refine List.map_congr_left fun l _ => ?_
  simp

/-- **`merkleHints true qs os` is the levels' `levelHints`**, level `l` at its depth on `os`'s
`l`-th phase, the first level's first: the form `HonRun.lqPops_os` gives. -/
theorem merkleHints_levels {μ r : ℕ} (h1 : minOpenLog ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4)
    {S : KeccakState} {root : Digest} {target : E} {xs : List E} {os : List (List Opening)} {w : WhirEnd}
    {s' : Fs} {roots' : List (Digest × ℕ × ℕ)} {qs : List (ℕ × List ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hq : VsC.OpenRunQueries μ r root target ⟨capOf S, []⟩ xs os qs) :
    Prover.merkleHints true qs os = (List.range (osCfgR (μ - minOpenLog) (r - 1)).levels.length).flatMap
      fun l => Hints.levelHints (l == 0) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth
        (os.getD l []).length (os.getD l []) := by
  obtain ⟨hlen, rfl⟩ := openRunQueries_levels h1 h2 h3 h4 hrun hq
  rw [← hlen, merkleHints_range]
  simp only [Bool.true_and]

end
end LeanVM.Guest.B1.Whir

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **At a call of `open_stacked__L{m}`**, on `OpenStackedCompleteA`'s hypotheses: `os` has a phase a
level, `qs` a query a level, at the level's depth and its openings' leaf indices, and
`merkleHints true qs os` is the levels' `levelHints` (`HonRun.lqPops_os`' form, at the arm
`minOpenLog + m - minOpenLog`). -/
theorem merkleHints_open {m r : ℕ} {root : Digest} {fsv : List E} {target : E} {xs : List E}
    {os : List (List Opening)} {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    {qs : List (ℕ × List ℕ)} (hm : m ≤ 14) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (hcar : ∃ sp : Sponge, (⟨fsv, []⟩ : Fs).Carries sp)
    (hrun : RunsWith (whirOpen (minOpenLog + m) r target) ⟨fsv, []⟩ xs os
      [(root, stackShape (minOpenLog + m) r)] w s' roots')
    (hq : OpenRunQueries (minOpenLog + m) r root target ⟨fsv, []⟩ xs os qs) :
    os.length = (osCfgR (minOpenLog + m - minOpenLog) (r - 1)).levels.length ∧
      qs = (List.range (osCfgR (minOpenLog + m - minOpenLog) (r - 1)).levels.length).map (fun l =>
        ((osLvA (osCfgR (minOpenLog + m - minOpenLog) (r - 1)) l).depth,
          (os.getD l []).map Opening.leafIndex)) ∧
      Prover.merkleHints true qs os =
        (List.range (osCfgR (minOpenLog + m - minOpenLog) (r - 1)).levels.length).flatMap fun l =>
          Hints.levelHints (l == 0) (osLvA (osCfgR (minOpenLog + m - minOpenLog) (r - 1)) l).depth
            (os.getD l []).length (os.getD l []) := by
  obtain ⟨⟨st, pe, gr⟩, hc, hp, hg⟩ := hcar
  change capOf st = fsv at hc
  change pe = [] at hp
  change gr = none at hg
  subst hc hp hg
  have h1 : minOpenLog ≤ minOpenLog + m := Nat.le_add_right _ _
  have h2 : minOpenLog + m ≤ 30 := by show 16 + m ≤ 30; omega
  obtain ⟨hlen, hqs⟩ := openRunQueries_levels h1 h2 hr1 hr4 hrun hq
  exact ⟨hlen, hqs, merkleHints_levels h1 h2 hr1 hr4 hrun hq⟩

end
end LeanVM.Guest.B1.VsC
