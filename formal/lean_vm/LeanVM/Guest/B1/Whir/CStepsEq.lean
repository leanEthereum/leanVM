/-
  LeanVM.Guest.B1.Whir.CStepsEq

  The query steps of the honest run of the stacked opening, as a list: level by level, each level's root's height and its positions zipped with its phase.
-/

module

public import LeanVM.Guest.B1.Whir.CHonRun
public import LeanVM.Guest.Child.Range

/-!
# The honest run's query steps

`qstT_nil_of_nc`: a program with no commitment and no query has no step. The `rqe_*` lemmas read a run primitive by primitive, as `CCapsRun`'s `rq_*` do, tracking the steps as an equation. `lvSteps logN index Ls`: the steps of the levels `Ls`, level `index` first, each its root's height and its positions zipped with its phase. `lvSteps_of_run`: the equality version of `lvsAgree_of_run`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none
  runT_bind)
open LeanVM.Guest.B1.VerifySub (NoCommitA NoCommit noCommit_iff)

@[expose] public section

variable {α : Type}

/-! ## No step without a query -/

/-- **A program with no commitment and no query has no step.** -/
theorem qstT_nil_of_nc : ∀ (p : VerifierProgram α), NoCommitA p → ∀ st, qstT p st = []
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .read k, hp, ⟨s, g, stream, os, R⟩ => by
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | x :: xs, none => exact qstT_nil_of_nc (k x) (hp x) _
  | .sample k, hp, ⟨s, g, stream, os, R⟩ => by
    cases g with
    | some c => exact qstT_nil_of_nc (k c) (hp c) _
    | none => exact qstT_nil_of_nc (k _) (hp _) _
  | .grind b k, hp, ⟨s, g, stream, os, R⟩ => by
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | n :: xs, none =>
      show (if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else []) = []
      split
      · exact qstT_nil_of_nc k hp _
      · rfl
  | .commit _ _ _, hp, _ => hp.elim
  | .query _ _ _, hp, _ => hp.elim

/-- **Past a run of a part with no commitment, a sequence's steps are its rest's.** -/
theorem qstT_bind_nc {β : Type} (f : α → VerifierProgram β) {p : VerifierProgram α} (hp : NoCommit p)
    {st : TSt} {a : α} {st' : TSt} (h : runT p st = some (a, st')) : qstT (p.bind f) st = qstT (f a) st' := by
  rw [qstT_bind f p st a st' h, qstT_nil_of_nc p ((noCommit_iff p).1 hp) st, List.nil_append]

/-! ## Primitive by primitive -/

variable {T : List (ℕ × List (ℕ × Opening))}

theorem rqe_readE {f : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runT (VerifierProgram.readScalar.bind f) st = some r)
    (hq : qstT (VerifierProgram.readScalar.bind f) st = T) :
    ∃ x xs, st.stream = x :: xs ∧ st.ground = none ∧
      runT (f x) ⟨st.sponge.absorb x dsObserve, none, xs, st.openings, st.roots⟩ = some r ∧
      qstT (f x) ⟨st.sponge.absorb x dsObserve, none, xs, st.openings, st.roots⟩ = T := by
  replace h : runT (.read f) st = some r := h
  replace hq : qstT (.read f) st = T := hq
  obtain ⟨s, g, stream, os, R⟩ := st
  match stream, g, h, hq with
  | [], _, h, _ => simp [runT] at h
  | _ :: _, some _, h, _ => simp [runT] at h
  | x :: xs, none, h, hq => exact ⟨x, xs, rfl, rfl, h, hq⟩

theorem rqe_sampleE_none {f : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runT (VerifierProgram.sampleChallenge.bind f) st = some r)
    (hq : qstT (VerifierProgram.sampleChallenge.bind f) st = T) (hg : st.ground = none) :
    runT (f st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, none, st.stream, st.openings, st.roots⟩ = some r ∧
    qstT (f st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, none, st.stream, st.openings, st.roots⟩ = T := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  exact ⟨h, hq⟩

theorem rqe_sampleE_some {f : E → VerifierProgram α} {st : TSt} {r : α × TSt} {c : E}
    (h : runT (VerifierProgram.sampleChallenge.bind f) st = some r)
    (hq : qstT (VerifierProgram.sampleChallenge.bind f) st = T) (hg : st.ground = some c) :
    runT (f c) ⟨st.sponge, none, st.stream, st.openings, st.roots⟩ = some r ∧
      qstT (f c) ⟨st.sponge, none, st.stream, st.openings, st.roots⟩ = T := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  exact ⟨h, hq⟩

theorem rqe_grindPoW {b : ℕ} (hb : b ≠ 0) {f : Unit → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runT ((VerifierProgram.grindProofOfWork b).bind f) st = some r)
    (hq : qstT ((VerifierProgram.grindProofOfWork b).bind f) st = T) :
    ∃ n xs, st.stream = n :: xs ∧ st.ground = none ∧
      runT (f ()) ⟨⟨capOf (st.sponge.nonceState n), []⟩, some (challengeOf (st.sponge.nonceState n)),
        xs, st.openings, st.roots⟩ = some r ∧
      qstT (f ()) ⟨⟨capOf (st.sponge.nonceState n), []⟩, some (challengeOf (st.sponge.nonceState n)),
        xs, st.openings, st.roots⟩ = T := by
  unfold VerifierProgram.grindProofOfWork at h hq
  simp only [hb, ↓reduceIte] at h hq
  replace h : runT (.grind b (f ())) st = some r := h
  replace hq : qstT (.grind b (f ())) st = T := hq
  obtain ⟨s, g, stream, os, R⟩ := st
  match stream, g, h, hq with
  | [], _, h, _ => simp [runT] at h
  | _ :: _, some _, h, _ => simp [runT] at h
  | n :: xs, none, h, hq =>
    simp only [runT] at h
    by_cases hp : powOk b (Keccak.lane (s.nonceState n) 2) = true
    · simp only [hp, ↓reduceIte] at h
      refine ⟨n, xs, rfl, rfl, h, ?_⟩
      change (if powOk b (Keccak.lane (s.nonceState n) 2) = true then _ else _) = T at hq
      simp only [hp, ↓reduceIte] at hq
      exact hq
    · simp [hp] at h

theorem rqe_commitB {hh ww : ℕ} {f : Unit → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runT ((VerifierProgram.readCommitment hh ww).bind f) st = some r)
    (hq : qstT ((VerifierProgram.readCommitment hh ww).bind f) st = T) :
    ∃ x0 x1 xs, st.stream = x0 :: x1 :: xs ∧ st.ground = none ∧
      runT (f ()) ⟨(st.sponge.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, st.openings,
        st.roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ = some r ∧
      qstT (f ()) ⟨(st.sponge.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, st.openings,
        st.roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ = T := by
  replace h : runT (.commit hh ww (f ())) st = some r := h
  replace hq : qstT (.commit hh ww (f ())) st = T := hq
  obtain ⟨s, g, stream, os, R⟩ := st
  match stream, g, h, hq with
  | [], _, h, _ => simp [runT] at h
  | [_], _, h, _ => simp [runT] at h
  | _ :: _ :: _, some _, h, _ => simp [runT] at h
  | x0 :: x1 :: xs, none, h, hq => exact ⟨x0, x1, xs, rfl, rfl, h, hq⟩

/-- **A query's step**, then the steps after it. -/
theorem rqe_queryB {i : ℕ} {ps : List ℕ} {f : List (List K) → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runT ((VerifierProgram.queryOpenings i ps).bind f) st = some r)
    (hq : qstT ((VerifierProgram.queryOpenings i ps).bind f) st = T) :
    ∃ root height width phase rest rows, st.roots[i]? = some (root, height, width) ∧
      st.openings = phase :: rest ∧
      Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) = some rows ∧
      runT (f rows) ⟨st.sponge, st.ground, st.stream, rest, st.roots⟩ = some r ∧
      T = (height, ps.zip phase) :: qstT (f rows) ⟨st.sponge, st.ground, st.stream, rest, st.roots⟩ := by
  obtain ⟨s, g, stream, os, R⟩ := st
  cases hR : R[i]? with
  | none => simp [VerifierProgram.queryOpenings, VerifierProgram.bind, runT, hR] at h
  | some v =>
    obtain ⟨root, height, width⟩ := v
    cases os with
    | nil => simp [VerifierProgram.queryOpenings, VerifierProgram.bind, runT, hR] at h
    | cons phase rest =>
      simp only [VerifierProgram.queryOpenings, VerifierProgram.bind, runT, hR] at h
      simp only [VerifierProgram.queryOpenings, VerifierProgram.bind, qstT, hR] at hq
      cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
          phase) with
      | none => simp [hop] at h
      | some rows =>
        simp only [hop] at h hq
        exact ⟨root, height, width, phase, rest, rows, rfl, rfl, hop, h, hq.symm⟩

theorem rqe_readScalars {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runT ((VerifierProgram.readScalars n).bind f) st = some r →
      qstT ((VerifierProgram.readScalars n).bind f) st = T →
      ∃ ys xs, ys.length = n ∧ st.stream = ys ++ xs ∧
        runT (f ys) ⟨st.sponge.absorbAll ys dsObserve, none, xs, st.openings, st.roots⟩ = some r ∧
        qstT (f ys) ⟨st.sponge.absorbAll ys dsObserve, none, xs, st.openings, st.roots⟩ = T
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
    obtain ⟨x, xs, hs, -, h1, hq1⟩ := rqe_readE h hq
    obtain ⟨ys, zs, hl, hz, h2, hq2⟩ := rqe_readScalars n _ r rfl h1 hq1
    simp only at hz
    exact ⟨x :: ys, zs, by simp [hl], by rw [hs, hz]; rfl, h2, hq2⟩

theorem rqe_sampleChallenges {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runT ((VerifierProgram.sampleChallenges n).bind f) st = some r →
      qstT ((VerifierProgram.sampleChallenges n).bind f) st = T →
      runT (f (st.sponge.squeezeN n).1)
        ⟨(st.sponge.squeezeN n).2, none, st.stream, st.openings, st.roots⟩ = some r ∧
      qstT (f (st.sponge.squeezeN n).1)
        ⟨(st.sponge.squeezeN n).2, none, st.stream, st.openings, st.roots⟩ = T
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
    obtain ⟨h1, hq1⟩ := rqe_sampleE_none h hq hg
    exact rqe_sampleChallenges n _ r rfl h1 hq1

theorem rqe_sampleChallengesG {f : List E → VerifierProgram α} (m : ℕ) {st : TSt} {r : α × TSt}
    {c : E} (hg : st.ground = some c)
    (h : runT ((VerifierProgram.sampleChallenges (m + 1)).bind f) st = some r)
    (hq : qstT ((VerifierProgram.sampleChallenges (m + 1)).bind f) st = T) :
    runT (f (c :: (st.sponge.squeezeN m).1))
      ⟨(st.sponge.squeezeN m).2, none, st.stream, st.openings, st.roots⟩ = some r ∧
    qstT (f (c :: (st.sponge.squeezeN m).1))
      ⟨(st.sponge.squeezeN m).2, none, st.stream, st.openings, st.roots⟩ = T := by
  have e : (VerifierProgram.sampleChallenges (m + 1)).bind f =
      VerifierProgram.sampleChallenge.bind fun x ↦
        (VerifierProgram.sampleChallenges m).bind fun xs ↦ f (x :: xs) := by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rw [e] at h hq
  obtain ⟨h1, hq1⟩ := rqe_sampleE_some h hq hg
  exact rqe_sampleChallenges m _ r rfl h1 hq1

/-- A part with no commitment, run first. -/
theorem rqe_bind_nc {β : Type} {p : VerifierProgram β} {f : β → VerifierProgram α} (hp : NoCommit p) {st : TSt}
    {r : α × TSt} (h : runT (p.bind f) st = some r) (hq : qstT (p.bind f) st = T) :
    ∃ a st1, runT p st = some (a, st1) ∧ runT (f a) st1 = some r ∧ qstT (f a) st1 = T := by
  obtain ⟨a, st1, h1, h2⟩ := rT_bind_some h
  exact ⟨a, st1, h1, h2, (qstT_bind_nc f hp h1).symm.trans hq⟩

/-! ## The levels' steps -/

/-- **The steps of the levels `Ls`**, level `index` first: its root's height, its positions zipped with its
phase. -/
def lvSteps (logN : ℕ) : ℕ → List LvAt → List (ℕ × List (ℕ × Opening))
  | _, [] => []
  | index, L :: Ls => ((L.R.getD index default).2.1, (L.qs logN).zip L.phase) :: lvSteps logN (index + 1) Ls

theorem getD_of_getElem? {β : Type} {l : List β} {i : ℕ} {d b : β} (h : l[i]? = some b) : l.getD i d = b := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

/-- **The honest run's steps are its levels'**: the equality version of `lvsAgree_of_run`. -/
theorem lvSteps_of_run (logN lane : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (cap : List E)
      (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (w : WhirEnd)
      (ds : List LvD) (r : WhirEnd × TSt), (∃ sp, (⟨cap, []⟩ : Fs).Carries sp) →
      (∀ l ∈ levels, LvOk logN l) → LvsRunD logN lane index levels s cap R xs os w ds →
      runT (whirLevelsOpen logN lane index levels s) ⟨⟨cap, []⟩, none, xs, os, R⟩ = some r →
      qstT (whirLevelsOpen logN lane index levels s) ⟨⟨cap, []⟩, none, xs, os, R⟩ =
        lvSteps logN index (lvsAt logN index levels s cap R xs os ds)
  | [level], index, s, cap, R, xs, os, w, [LvD.fin rw W], r, hc, hlv, hD, h => by
    have hl := hlv level (by simp)
    obtain ⟨hrl, hrok, hxs, hos, hfin, -⟩ := hD
    generalize hT : qstT (whirLevelsOpen logN lane index [level] s) ⟨⟨cap, []⟩, none, xs, os, R⟩ = T
    rw [whirLevelsOpen] at h hT
    obtain ⟨p, st1, h1, h2, hq⟩ := rqe_bind_nc (Child.noCommit_foldRounds _ _) h hT
    rw [hxs] at h1
    obtain ⟨rfl, rfl⟩ := rounds_plain hc hrl hrok h1
    set mu := logN - (rsSt level s cap rw).alphas.length with hmu
    set d := mu + level.logInvRate with hd
    obtain ⟨fold, xs1, hfl, hs1, h, hq⟩ := rqe_readScalars (2 ^ mu + level.fold) _ _ rfl h2 hq
    obtain ⟨nn, xs2, hs2, -, h, hq⟩ := rqe_grindPoW (by decide) h hq
    obtain ⟨qs', st2, hq1, h, hq⟩ := rqe_bind_nc
      ((noCommit_iff _).2 ((noCommit_iff _).1 (Child.noCommit_sampleQueriesAux _ _ _))) h hq
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
    obtain ⟨root', height', width', phase, orest, rows, hR', hos', -, h, hT'⟩ := rqe_queryB h hq
    simp only at hR' hos'
    rw [hos] at hos'
    simp only [List.cons.injEq] at hos'
    obtain ⟨rfl, rfl⟩ := hos'
    rw [hT', qstT_nil_of_nc _ ?nc _]
    case nc =>
      refine (noCommit_iff _).1 (VerifySub.NoCommit.bind (VerifySub.noCommit_require _) fun _ ↦
        VerifySub.NoCommit.bind (VerifySub.noCommit_sumcheck _ _ _) fun x ↦ ?_)
      obtain ⟨_, _⟩ := x
      exact VerifySub.noCommit_ret _
    show _ = [((R.getD index default).2.1, _)]
    rw [getD_of_getElem? hR']
    rfl
  | level :: next :: rest, index, s, cap, R, xs, os, w, LvD.next rw W :: ds, r, hc, hlv, hD, h => by
    have hl := hlv level (by simp)
    obtain ⟨xs', os', hrl, hrok, hxs, hos, hnext, hD'⟩ := hD
    have hxs' : xs.drop (rw.length + W.words.length) = xs' := by rw [hxs]; exact drop_words
    have hos'' : os.tail = os' := by rw [hos]; rfl
    generalize hT : qstT (whirLevelsOpen logN lane index (level :: next :: rest) s)
      ⟨⟨cap, []⟩, none, xs, os, R⟩ = T
    rw [whirLevelsOpen] at h hT
    obtain ⟨p, st1, h1, h2, hq⟩ := rqe_bind_nc (Child.noCommit_foldRounds _ _) h hT
    rw [hxs, List.append_assoc] at h1
    obtain ⟨rfl, rfl⟩ := rounds_plain hc hrl hrok h1
    set mu := logN - (rsSt level s cap rw).alphas.length with hmu
    set d := mu + level.logInvRate with hd
    obtain ⟨x0, x1, xs1, hs1, -, h, hq⟩ := rqe_commitB h2 hq
    obtain ⟨high, xs2, hhl, hs2, h, hq⟩ := rqe_readScalars level.fold _ _ rfl h hq
    obtain ⟨n1, xs3, hs3, -, h, hq⟩ := rqe_grindPoW (by decide) h hq
    obtain ⟨m, hm⟩ : ∃ m, mu = m + 1 := ⟨mu - 1, by have := hnext.mu1; omega⟩
    rw [← hmu, hm] at h hq
    obtain ⟨h, hq⟩ := rqe_sampleChallengesG m rfl h hq
    rw [← hm] at h hq
    obtain ⟨y0, xs4, hs4, -, h, hq⟩ := rqe_readE h hq
    obtain ⟨nn, xs5, hs5, -, h, hq⟩ := rqe_grindPoW (by decide) h hq
    obtain ⟨qs', st2, hq1, h, hq⟩ := rqe_bind_nc
      ((noCommit_iff _).2 ((noCommit_iff _).1 (Child.noCommit_sampleQueriesAux _ _ _))) h hq
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
      xs' os (R ++ [(digestFromHalves (W.x0, W.x1), levelShape mu next (2 * 2 ^ next.fold))])
    have e := hq1.symm.trans hfq
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨h, hq⟩ := rqe_sampleE_none h hq rfl
    obtain ⟨root', height', width', phase, orest, rows, hR', hos', hop, h, hT'⟩ := rqe_queryB h hq
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
    rw [hood] at h hT'
    have ih := lvSteps_of_run logN lane (next :: rest) (index + 1)
      (W.glued logN index level (rsSt level s cap rw) (rsF level cap rw) (rsRounds level s cap rw))
      (W.F3 (rsF level cap rw) mu d level.queries).squeeze.2.cap (W.roots mu next R) xs' os' w ds r (carries_capOf _)
      (fun l hl' ↦ hlv l (List.mem_cons_of_mem _ hl')) hD' h
    rw [hT']
    refine Eq.trans (congrArg (List.cons _) ih) ?_
    obtain ⟨rt, ht, wd, hRi, -⟩ := hnext.root
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hRi).1, hRi] at hR'
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨-, rfl, -⟩ := hR'
    show _ = ((R.getD index default).2.1, _) :: lvSteps logN (index + 1) (lvsAt logN (index + 1) (next :: rest)
      _ _ _ (xs.drop (rw.length + W.words.length)) os.tail ds)
    rw [hxs', hos'', getD_of_getElem? hRi]
    rfl
  | [], _, _, _, _, _, _, _, _, _, _, _, hD, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, [], _, _, _, hD, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.next _ _ :: _, _, _, _, hD, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.fin _ _ :: _ :: _, _, _, _, hD, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, [], _, _, _, hD, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, LvD.fin _ _ :: _, _, _, _, hD, _ => by simp [LvsRunD] at hD

end
end LeanVM.Guest.B1.Whir
