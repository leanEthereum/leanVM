/-
  LeanVM.Guest.B1.Whir.CCapsRun

  `CapsAgree` read at the honest run's levels: each level's openings agree wherever they meet.
-/

module

public import LeanVM.Guest.B1.Whir.CInvNZ
public import LeanVM.Guest.B1.VerifySub.NZRun

/-!
# The caps agree, level by level

`CapsAgree` speaks of the deployed run's query steps (`Limits.queryStepsOf`); `qstT` lists the
same steps along the carried run (`Tables.runT`), and they are equal on a carried sponge
(`qstT_eq`). They split at a `bind` past a run of its first part (`qstT_bind`). `AllQ p st`: every
step of `p` from `st` has agreeing openings; the `rq_*` lemmas read a run and `AllQ` together,
primitive by primitive.

`LvsAgree`: at each level of the honest run (`LvsRunD`), its openings at its positions agree
wherever they meet, at its root's height; `lvsAgree_of_run`, `whirOpen_agree`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none
  runT_bind)

@[expose] public section

variable {α : Type}

/-! ## Query steps along the carried run -/

/-- **The query steps of the carried run**: each `query` as its tree's height and its positions,
each with its opening. -/
def qstT : VerifierProgram α → TSt → List (ℕ × List (ℕ × Opening))
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, s => match s.stream, s.ground with
    | x :: xs, none => qstT (k x) { s with sponge := s.sponge.absorb x dsObserve, stream := xs }
    | _, _ => []
  | .sample k, s => match s.ground with
    | some c => qstT (k c) { s with ground := none }
    | none => qstT (k s.sponge.squeeze.1) { s with sponge := s.sponge.squeeze.2 }
  | .grind bits k, s => match s.stream, s.ground with
    | n :: xs, none =>
      if powOk bits (Keccak.lane (s.sponge.nonceState n) 2) then
        qstT k { s with
          sponge := Fs.mk (capOf (s.sponge.nonceState n)) []
          ground := some (challengeOf (s.sponge.nonceState n))
          stream := xs }
      else []
    | _, _ => []
  | .commit height width k, s => match s.stream, s.ground with
    | x0 :: x1 :: xs, none =>
      qstT k { s with
        sponge := (s.sponge.absorb x0 dsObserve).absorb x1 dsObserve
        stream := xs
        roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)] }
    | _, _ => []
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
      | some rows => (height, ps.zip phase) :: qstT (k rows) { s with openings := rest }
      | none => []
    | _, _ => []

/-- The deployed grind's steps from a carried sponge. -/
theorem qs_grind_carried (bits : ℕ) (k : VerifierProgram α) {s : Fs} {sp : Sponge}
    (hs : s.Carries sp) (n : E) (rest : List E) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)) :
    Guest.Limits.queryStepsOf (.grind bits k) ⟨sp, n :: rest, os, roots⟩ =
      if powOk bits (Keccak.lane (s.nonceState n) 2) = true then
        Guest.Limits.queryStepsOf k
          ⟨⟨s.nonceState n, [], some (challengeOf (s.nonceState n))⟩, rest, os, roots⟩
      else [] := by
  have ha := carries_absorb hs n dsPowNonce
  have hp := perm_eq ha
  obtain ⟨st, p, g⟩ := sp
  have h3 : g = none := hs.2.2
  subst h3
  rw [Fs.nonceState, ← hp]
  rfl

/-- **The carried run's steps are the deployed run's** on every sponge the state carries. -/
theorem qstT_eq (p : VerifierProgram α) : ∀ (st : TSt) (sp : Sponge),
    TCar st.sponge st.ground sp →
    Guest.Limits.queryStepsOf p ⟨sp, st.stream, st.openings, st.roots⟩ = qstT p st := by
  induction p with
  | ret b => intro st sp _; rfl
  | fail => intro st sp _; rfl
  | read k ih =>
    intro st sp hs
    obtain ⟨s, g, stream, os, R⟩ := st
    obtain ⟨S, P, G⟩ := sp
    obtain ⟨h1, h2, h3⟩ := hs
    simp only at h1 h2 h3
    subst G
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | x :: xs, none =>
      exact ih x ⟨s.absorb x dsObserve, none, xs, os, R⟩ _
        (carries_absorb (s := s) (sp := ⟨S, P, none⟩) ⟨h1, h2, rfl⟩ x dsObserve)
  | sample k ih =>
    intro st sp hs
    obtain ⟨s, g, stream, os, R⟩ := st
    obtain ⟨S, P, G⟩ := sp
    obtain ⟨h1, h2, h3⟩ := hs
    simp only at h1 h2 h3
    subst G
    cases g with
    | some c => exact ih c ⟨s, none, stream, os, R⟩ ⟨S, P, none⟩ ⟨h1, h2, rfl⟩
    | none =>
      have hs' : s.Carries ⟨S, P, none⟩ := ⟨h1, h2, rfl⟩
      obtain ⟨e1, e2⟩ := carries_squeeze hs'
      have c2 := ih s.squeeze.1 ⟨s.squeeze.2, none, stream, os, R⟩ _ e2
      show Guest.Limits.queryStepsOf (k (Id.run (Compile.squeeze (m := Id) keccakF1600 ⟨S, P, none⟩)).1)
        ⟨(Id.run (Compile.squeeze (m := Id) keccakF1600 ⟨S, P, none⟩)).2, stream, os, R⟩ = _
      rw [e1]; exact c2
  | grind b k ih =>
    intro st sp hs
    obtain ⟨s, g, stream, os, R⟩ := st
    obtain ⟨S, P, G⟩ := sp
    obtain ⟨h1, h2, h3⟩ := hs
    simp only at h1 h2 h3
    subst G
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | n :: xs, none =>
      rw [qs_grind_carried b k (s := s) (sp := ⟨S, P, none⟩) ⟨h1, h2, rfl⟩ n xs os R]
      show _ = if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else _
      split
      · exact ih ⟨⟨capOf (s.nonceState n), []⟩, some (challengeOf (s.nonceState n)), xs, os, R⟩
          ⟨s.nonceState n, [], some (challengeOf (s.nonceState n))⟩ ⟨rfl, rfl, rfl⟩
      · rfl
  | commit hh ww k ih =>
    intro st sp hs
    obtain ⟨s, g, stream, os, R⟩ := st
    obtain ⟨S, P, G⟩ := sp
    obtain ⟨h1, h2, h3⟩ := hs
    simp only at h1 h2 h3
    subst G
    match stream, g with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, some _ => rfl
    | x0 :: x1 :: xs, none =>
      have c1 := carries_absorb (s := s) (sp := ⟨S, P, none⟩) ⟨h1, h2, rfl⟩ x0 dsObserve
      have c2 := carries_absorb c1 x1 dsObserve
      exact ih ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, os,
        R ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ _ c2
  | query i ps k ih =>
    intro st sp hs
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [Guest.Limits.queryStepsOf, qstT, hR]
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [Guest.Limits.queryStepsOf, qstT, hR]
      | cons phase rest =>
        simp only [Guest.Limits.queryStepsOf, qstT, hR, VerifySub.openPhase_keccak]
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => rfl
        | some rows =>
          simp only
          exact congrArg _ (ih rows ⟨s, g, stream, rest, R⟩ sp hs)

/-- **A sequence's steps split** past a carried run of its first part. -/
theorem qstT_bind {β : Type} (f : α → VerifierProgram β) : ∀ (p : VerifierProgram α) (st : TSt)
    (a : α) (st' : TSt), runT p st = some (a, st') → qstT (p.bind f) st = qstT p st ++ qstT (f a) st'
  | .ret b, st, a, st', h => by
    simp only [runT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .fail, _, _, _, h => by simp [runT] at h
  | .read k, ⟨s, g, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | x :: xs, none, h => exact qstT_bind f (k x) _ a st' h
  | .sample k, ⟨s, g, stream, os, R⟩, a, st', h => by
    cases g with
    | some c => exact qstT_bind f (k c) _ a st' h
    | none => exact qstT_bind f (k s.squeeze.1) _ a st' h
  | .grind b k, ⟨s, g, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | n :: xs, none, h =>
      simp only [runT] at h
      split at h
      · rename_i hp
        show (if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else _) =
          (if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else _) ++ _
        simp only [hp, ↓reduceIte]
        exact qstT_bind f k _ a st' h
      · simp at h
  | .commit hh ww k, ⟨s, g, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | [_], _, h => simp [runT] at h
    | _ :: _ :: _, some _, h => simp [runT] at h
    | x0 :: x1 :: xs, none, h => exact qstT_bind f k _ a st' h
  | .query i ps k, ⟨s, g, stream, os, R⟩, a, st', h => by
    cases hR : R[i]? with
    | none => simp [runT, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runT, hR] at h
      | cons phase rest =>
        simp only [runT, hR] at h
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h
          simp only [VerifierProgram.bind, qstT, hR, hop, List.cons_append]
          exact congrArg _ (qstT_bind f (k rows) _ a st' h)

/-! ## Agreeing steps, primitive by primitive -/

/-- Every step of `p` from `st` has agreeing openings. -/
def AllQ (p : VerifierProgram α) (st : TSt) : Prop :=
  ∀ b ∈ qstT p st, Guest.Limits.OpeningsAgree b.1 b.2

theorem allQ_bind {β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {st st1 : TSt}
    {a : α} (h1 : runT p st = some (a, st1)) (hq : AllQ (p.bind f) st) : AllQ (f a) st1 :=
  fun b hb ↦ hq b (by rw [qstT_bind f p st a st1 h1]; exact List.mem_append_right _ hb)

theorem rq_readE {f : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runT (VerifierProgram.readScalar.bind f) st = some r)
    (hq : AllQ (VerifierProgram.readScalar.bind f) st) :
    ∃ x xs, st.stream = x :: xs ∧ st.ground = none ∧
      runT (f x) ⟨st.sponge.absorb x dsObserve, none, xs, st.openings, st.roots⟩ = some r ∧
      AllQ (f x) ⟨st.sponge.absorb x dsObserve, none, xs, st.openings, st.roots⟩ := by
  replace h : runT (.read f) st = some r := h
  replace hq : AllQ (.read f) st := hq
  obtain ⟨s, g, stream, os, R⟩ := st
  match stream, g, h, hq with
  | [], _, h, _ => simp [runT] at h
  | _ :: _, some _, h, _ => simp [runT] at h
  | x :: xs, none, h, hq => exact ⟨x, xs, rfl, rfl, h, hq⟩

theorem rq_sampleE_none {f : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runT (VerifierProgram.sampleChallenge.bind f) st = some r)
    (hq : AllQ (VerifierProgram.sampleChallenge.bind f) st) (hg : st.ground = none) :
    runT (f st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, none, st.stream, st.openings, st.roots⟩ =
      some r ∧
    AllQ (f st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, none, st.stream, st.openings, st.roots⟩ := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  exact ⟨h, hq⟩

theorem rq_sampleE_some {f : E → VerifierProgram α} {st : TSt} {r : α × TSt} {c : E}
    (h : runT (VerifierProgram.sampleChallenge.bind f) st = some r)
    (hq : AllQ (VerifierProgram.sampleChallenge.bind f) st) (hg : st.ground = some c) :
    runT (f c) ⟨st.sponge, none, st.stream, st.openings, st.roots⟩ = some r ∧
      AllQ (f c) ⟨st.sponge, none, st.stream, st.openings, st.roots⟩ := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  exact ⟨h, hq⟩

theorem rq_grindPoW {b : ℕ} (hb : b ≠ 0) {f : Unit → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runT ((VerifierProgram.grindProofOfWork b).bind f) st = some r)
    (hq : AllQ ((VerifierProgram.grindProofOfWork b).bind f) st) :
    ∃ n xs, st.stream = n :: xs ∧ st.ground = none ∧
      runT (f ()) ⟨⟨capOf (st.sponge.nonceState n), []⟩, some (challengeOf (st.sponge.nonceState n)),
        xs, st.openings, st.roots⟩ = some r ∧
      AllQ (f ()) ⟨⟨capOf (st.sponge.nonceState n), []⟩, some (challengeOf (st.sponge.nonceState n)),
        xs, st.openings, st.roots⟩ := by
  unfold VerifierProgram.grindProofOfWork at h hq
  simp only [hb, ↓reduceIte] at h hq
  replace h : runT (.grind b (f ())) st = some r := h
  replace hq : AllQ (.grind b (f ())) st := hq
  obtain ⟨s, g, stream, os, R⟩ := st
  match stream, g, h, hq with
  | [], _, h, _ => simp [runT] at h
  | _ :: _, some _, h, _ => simp [runT] at h
  | n :: xs, none, h, hq =>
    simp only [runT] at h
    by_cases hp : powOk b (Keccak.lane (s.nonceState n) 2) = true
    · simp only [hp, ↓reduceIte] at h
      refine ⟨n, xs, rfl, rfl, h, fun x hx ↦ hq x ?_⟩
      show x ∈ (if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else _)
      simp only [hp, ↓reduceIte]
      exact hx
    · simp [hp] at h

theorem rq_commitB {hh ww : ℕ} {f : Unit → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runT ((VerifierProgram.readCommitment hh ww).bind f) st = some r)
    (hq : AllQ ((VerifierProgram.readCommitment hh ww).bind f) st) :
    ∃ x0 x1 xs, st.stream = x0 :: x1 :: xs ∧ st.ground = none ∧
      runT (f ()) ⟨(st.sponge.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, st.openings,
        st.roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ = some r ∧
      AllQ (f ()) ⟨(st.sponge.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, st.openings,
        st.roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ := by
  replace h : runT (.commit hh ww (f ())) st = some r := h
  replace hq : AllQ (.commit hh ww (f ())) st := hq
  obtain ⟨s, g, stream, os, R⟩ := st
  match stream, g, h, hq with
  | [], _, h, _ => simp [runT] at h
  | [_], _, h, _ => simp [runT] at h
  | _ :: _ :: _, some _, h, _ => simp [runT] at h
  | x0 :: x1 :: xs, none, h, hq => exact ⟨x0, x1, xs, rfl, rfl, h, hq⟩

/-- **A query's step**: its openings agree, and so do the steps after it. -/
theorem rq_queryB {i : ℕ} {ps : List ℕ} {f : List (List K) → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runT ((VerifierProgram.queryOpenings i ps).bind f) st = some r)
    (hq : AllQ ((VerifierProgram.queryOpenings i ps).bind f) st) :
    ∃ root height width phase rest rows, st.roots[i]? = some (root, height, width) ∧
      st.openings = phase :: rest ∧
      Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) = some rows ∧
      runT (f rows) ⟨st.sponge, st.ground, st.stream, rest, st.roots⟩ = some r ∧
      Guest.Limits.OpeningsAgree height (ps.zip phase) ∧
      AllQ (f rows) ⟨st.sponge, st.ground, st.stream, rest, st.roots⟩ := by
  obtain ⟨s, g, stream, os, R⟩ := st
  cases hR : R[i]? with
  | none => simp [VerifierProgram.queryOpenings, VerifierProgram.bind, runT, hR] at h
  | some v =>
    obtain ⟨root, height, width⟩ := v
    cases os with
    | nil => simp [VerifierProgram.queryOpenings, VerifierProgram.bind, runT, hR] at h
    | cons phase rest =>
      simp only [VerifierProgram.queryOpenings, VerifierProgram.bind, runT, hR] at h
      unfold AllQ at hq
      simp only [VerifierProgram.queryOpenings, VerifierProgram.bind, qstT, hR] at hq
      cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
          phase) with
      | none => simp [hop] at h
      | some rows =>
        simp only [hop] at h hq
        exact ⟨root, height, width, phase, rest, rows, rfl, rfl, hop, h,
          hq _ (List.mem_cons_self ..), fun b hb ↦ hq b (List.mem_cons_of_mem _ hb)⟩

theorem rq_readScalars {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runT ((VerifierProgram.readScalars n).bind f) st = some r →
      AllQ ((VerifierProgram.readScalars n).bind f) st →
      ∃ ys xs, ys.length = n ∧ st.stream = ys ++ xs ∧
        runT (f ys) ⟨st.sponge.absorbAll ys dsObserve, none, xs, st.openings, st.roots⟩ = some r ∧
        AllQ (f ys) ⟨st.sponge.absorbAll ys dsObserve, none, xs, st.openings, st.roots⟩
  | 0, st, r, hg, h, hq => by
    refine ⟨[], st.stream, rfl, rfl, ?_⟩
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only at hg
    subst hg
    exact ⟨h, hq⟩
  | n + 1, st, r, hg, h, hq => by
    have e : (VerifierProgram.readScalars (n + 1)).bind f =
        VerifierProgram.readScalar.bind fun x ↦ (VerifierProgram.readScalars n).bind fun xs ↦
          f (x :: xs) := by
      show ((VerifierProgram.read VerifierProgram.ret).bind fun x ↦
        ((VerifierProgram.readScalars n).bind fun xs ↦ VerifierProgram.ret (x :: xs))).bind f = _
      simp only [VerifierProgram.bind_assoc]
      rfl
    rw [e] at h hq
    obtain ⟨x, xs, hs, -, h1, hq1⟩ := rq_readE h hq
    obtain ⟨ys, zs, hl, hz, h2, hq2⟩ := rq_readScalars n _ r rfl h1 hq1
    simp only at hz
    exact ⟨x :: ys, zs, by simp [hl], by rw [hs, hz]; rfl, h2, hq2⟩

theorem rq_sampleChallenges {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runT ((VerifierProgram.sampleChallenges n).bind f) st = some r →
      AllQ ((VerifierProgram.sampleChallenges n).bind f) st →
      runT (f (st.sponge.squeezeN n).1)
        ⟨(st.sponge.squeezeN n).2, none, st.stream, st.openings, st.roots⟩ = some r ∧
      AllQ (f (st.sponge.squeezeN n).1)
        ⟨(st.sponge.squeezeN n).2, none, st.stream, st.openings, st.roots⟩
  | 0, st, r, hg, h, hq => by
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only at hg
    subst hg
    exact ⟨h, hq⟩
  | n + 1, st, r, hg, h, hq => by
    have e : (VerifierProgram.sampleChallenges (n + 1)).bind f =
        VerifierProgram.sampleChallenge.bind fun x ↦ (VerifierProgram.sampleChallenges n).bind
          fun xs ↦ f (x :: xs) := by
      show ((VerifierProgram.sample VerifierProgram.ret).bind fun x ↦
        ((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x :: xs))).bind f = _
      simp only [VerifierProgram.bind_assoc]
      rfl
    rw [e] at h hq
    obtain ⟨h1, hq1⟩ := rq_sampleE_none h hq hg
    exact rq_sampleChallenges n _ r rfl h1 hq1

theorem rq_sampleOod2 {mu : ℕ} {f : List (List E) → VerifierProgram α} {st : TSt}
    {r : α × TSt} (hg : st.ground = none)
    (h : runT ((sampleOodPoints mu 2).bind f) st = some r)
    (hq : AllQ ((sampleOodPoints mu 2).bind f) st) :
    runT (f [(st.sponge.squeezeN mu).1, ((st.sponge.squeezeN mu).2.squeezeN mu).1])
      ⟨((st.sponge.squeezeN mu).2.squeezeN mu).2, none, st.stream, st.openings, st.roots⟩ = some r ∧
    AllQ (f [(st.sponge.squeezeN mu).1, ((st.sponge.squeezeN mu).2.squeezeN mu).1])
      ⟨((st.sponge.squeezeN mu).2.squeezeN mu).2, none, st.stream, st.openings, st.roots⟩ := by
  have e : (sampleOodPoints mu 2).bind f = (VerifierProgram.sampleChallenges mu).bind fun p1 ↦
      (VerifierProgram.sampleChallenges mu).bind fun p2 ↦ f [p1, p2] := by
    simp only [sampleOodPoints, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rw [e] at h hq
  obtain ⟨h1, hq1⟩ := rq_sampleChallenges mu st r hg h hq
  exact rq_sampleChallenges mu _ r rfl h1 hq1

/-! ## The levels -/

/-- **At each level of the honest run, the openings agree** at the level's positions, at its
root's height. -/
def LvsAgree (logN : ℕ) : ℕ → List Whir.Level → WhirState → List E → List (Digest × ℕ × ℕ) →
    List LvD → Prop
  | index, [level], s, cap, R, [LvD.fin rw W] =>
    ∀ root height width, R[index]? = some (root, height, width) →
      Guest.Limits.OpeningsAgree height ((W.qs (rsF level cap rw)
        (logN - (rsSt level s cap rw).gammas.length + level.logInvRate) level.queries).zip W.phase)
  | index, level :: next :: rest, s, cap, R, LvD.next rw W :: ds =>
    (∀ root height width, R[index]? = some (root, height, width) →
      Guest.Limits.OpeningsAgree height ((W.qs (rsF level cap rw)
        (logN - (rsSt level s cap rw).gammas.length)
        (logN - (rsSt level s cap rw).gammas.length + level.logInvRate) level.queries).zip W.phase)) ∧
    LvsAgree logN (index + 1) (next :: rest)
      (W.glued logN index level (rsSt level s cap rw) (rsF level cap rw) (rsRounds level s cap rw))
      (capOf ((W.F3 (rsF level cap rw) (logN - (rsSt level s cap rw).gammas.length)
        (logN - (rsSt level s cap rw).gammas.length + level.logInvRate) level.queries).nonceState W.n2))
      (W.roots (logN - (rsSt level s cap rw).gammas.length) next R) ds
  | _, _, _, _, _, _ => True

/-- The fold rounds of a level of the honest run, carried. -/
theorem rounds_plain {n : ℕ} {s : WhirState} {cap rw rest : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {p : WhirState × List FoldRound} {st1 : TSt}
    (hc : ∃ sp, (⟨cap, []⟩ : Fs).Carries sp) (hrl : rw.length = 7 * n) (hok : RoundsOk n cap rw)
    (h : runT (foldRounds n s) ⟨⟨cap, []⟩, none, rw ++ rest, os, R⟩ = some (p, st1)) :
    p = roundsSpec n s cap rw ∧ st1 = ⟨⟨roundsCap n cap rw, []⟩, none, rest, os, R⟩ := by
  rw [runT_of_runsTo (foldRounds_run n s cap rw hrl hok) hc rest os R] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- **The honest run's levels, their openings agreeing**, from a run whose steps all agree. -/
theorem lvsAgree_of_run (logN lane : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (cap : List E)
      (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (w : WhirEnd)
      (ds : List LvD) (r : WhirEnd × TSt), (∃ sp, (⟨cap, []⟩ : Fs).Carries sp) →
      (∀ l ∈ levels, LvOk logN l) → LvsRunD logN lane index levels s cap R xs os w ds →
      runT (whirLevelsOpen logN lane index levels s) ⟨⟨cap, []⟩, none, xs, os, R⟩ = some r →
      AllQ (whirLevelsOpen logN lane index levels s) ⟨⟨cap, []⟩, none, xs, os, R⟩ →
      LvsAgree logN index levels s cap R ds
  | [level], index, s, cap, R, xs, os, w, [LvD.fin rw W], r, hc, hlv, hD, h, hq => by
    have hl := hlv level (by simp)
    obtain ⟨hrl, hrok, hxs, hos, hfin, -⟩ := hD
    rw [whirLevelsOpen] at h hq
    obtain ⟨p, st1, h1, h2⟩ := rT_bind_some h
    have hq2 := allQ_bind h1 hq
    rw [hxs] at h1
    obtain ⟨rfl, rfl⟩ := rounds_plain hc hrl hrok h1
    set mu := logN - (rsSt level s cap rw).gammas.length with hmu
    set d := mu + level.logInvRate with hd
    obtain ⟨fold, xs1, hfl, hs1, h, hq⟩ := rq_readScalars (2 ^ mu + level.fold) _ _ rfl h2 hq2
    obtain ⟨nn, xs2, hs2, -, h, hq⟩ := rq_grindPoW (by decide) h hq
    obtain ⟨qs', st2, hq1, h⟩ := rT_bind_some h
    have hq := allQ_bind hq1 hq
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
    obtain ⟨root', height', width', phase, orest, rows, hR', hos', -, -, hag, -⟩ := rq_queryB h hq
    intro root height width hR
    simp only at hR' hos'
    rw [hR] at hR'
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨-, rfl, -⟩ := hR'
    rw [hos] at hos'
    simp only [List.cons.injEq] at hos'
    obtain ⟨rfl, -⟩ := hos'
    exact hag
  | level :: next :: rest, index, s, cap, R, xs, os, w, LvD.next rw W :: ds, r, hc, hlv, hD, h, hq => by
    have hl := hlv level (by simp)
    obtain ⟨xs', os', hrl, hrok, hxs, hos, hnext, hD'⟩ := hD
    rw [whirLevelsOpen] at h hq
    obtain ⟨p, st1, h1, h2⟩ := rT_bind_some h
    have hq2 := allQ_bind h1 hq
    rw [hxs, List.append_assoc] at h1
    obtain ⟨rfl, rfl⟩ := rounds_plain hc hrl hrok h1
    set mu := logN - (rsSt level s cap rw).gammas.length with hmu
    set d := mu + level.logInvRate with hd
    obtain ⟨x0, x1, xs1, hs1, -, h, hq⟩ := rq_commitB h2 hq2
    obtain ⟨high, xs2, hhl, hs2, h, hq⟩ := rq_readScalars level.fold _ _ rfl h hq
    obtain ⟨h, hq⟩ := rq_sampleOod2 rfl h hq
    obtain ⟨ys, xs3, hyl, hs3, h, hq⟩ := rq_readScalars Whir.oodSamples _ _ rfl h hq
    obtain ⟨y0, y1, rfl⟩ : ∃ y0 y1, ys = [y0, y1] := by
      match ys, hyl with
      | [y0, y1], _ => exact ⟨y0, y1, rfl⟩
    obtain ⟨nn, xs4, hs4, -, h, hq⟩ := rq_grindPoW (by decide) h hq
    obtain ⟨qs', st2, hq1, h⟩ := rT_bind_some h
    have hq := allQ_bind hq1 hq
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
    obtain ⟨n2, xs5, hs5, -, h, hq⟩ := rq_grindPoW (by decide) h hq
    simp only [List.cons.injEq] at hs5
    obtain ⟨rfl, rfl⟩ := hs5
    obtain ⟨h, hq⟩ := rq_sampleE_some h hq rfl
    obtain ⟨root', height', width', phase, orest, rows, hR', hos', hop, h, hag, hq⟩ := rq_queryB h hq
    simp only at hos' hR'
    rw [hos] at hos'
    simp only [List.cons.injEq] at hos'
    obtain ⟨rfl, rfl⟩ := hos'
    obtain ⟨-, -, -, rfl⟩ := phase_of_some hop
    refine ⟨fun root height width hR ↦ ?_, lvsAgree_of_run logN lane (next :: rest) (index + 1) _ _ _
      xs' os' w ds r (carries_capOf _) (fun l hl' ↦ hlv l (List.mem_cons_of_mem _ hl')) hD' h hq⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hR).1, hR] at hR'
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨-, rfl, -⟩ := hR'
    exact hag
  | [], _, _, _, _, _, _, _, _, _, _, _, hD, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, [], _, _, _, hD, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.next _ _ :: _, _, _, _, hD, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.fin _ _ :: _ :: _, _, _, _, hD, _, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, [], _, _, _, hD, _, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, LvD.fin _ _ :: _, _, _, _, hD, _, _ => by simp [LvsRunD] at hD

/-- **`CapsAgree` at the honest run**: every level's openings agree wherever they meet. -/
theorem whirOpen_agree {μ r : ℕ} {target : E} {S : KeccakState} {xs : List E}
    {os : List (List Opening)} {root : Digest} {w w' : WhirEnd} {s' : Fs}
    {roots' : List (Digest × ℕ × ℕ)} {cfg : List Whir.Level} {ds : List LvD} (hlad : LadderOk μ r)
    (hcfg : Whir.ladder μ r = some cfg)
    (hD : LvsRunD μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [], []⟩ (capOf S)
      [(root, stackShape μ r)] xs os w ds)
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w' s' roots')
    (hcaps : CapsAgree μ r target S xs os root) :
    LvsAgree μ 0 cfg ⟨target, [], []⟩ (capOf S) [(root, stackShape μ r)] ds := by
  have e := runT_of_runsWith hrun (carries_capOf S) [] []
  simp only [List.append_nil] at e
  have hq : AllQ (whirOpen μ r target) ⟨⟨capOf S, []⟩, none, xs, os, [(root, stackShape μ r)]⟩ := by
    intro b hb
    rw [← qstT_eq _ _ ⟨S, [], none⟩ ⟨rfl, rfl, rfl⟩] at hb
    exact hcaps b hb
  unfold whirOpen at e hq
  obtain ⟨cfg', hc', e⟩ := rT_liftOption e
  rw [hcfg, Option.some.injEq] at hc'
  subst hc'
  rw [hcfg] at hq
  exact lvsAgree_of_run μ _ cfg 0 _ _ _ xs os w ds _ (carries_capOf S) (hlad cfg hcfg) hD e hq

end
end LeanVM.Guest.B1.Whir
