/-
  LeanVM.Guest.B1.Whir.CInvLevel

  A non-final level after its folds (`levelNext`), read backwards from an accepting run.
-/

module

public import LeanVM.Guest.B1.Whir.CInvRound
public import LeanVM.Guest.B1.Whir.LevelRun

/-!
# A non-final level, backwards

`NextW`: what a non-final level reads after its folds: the next root's cells `x0, x1`, the high
part, the out-of-domain values `y0, y1`, the query nonce `nn`, the batching nonce `n2` and its
phase of openings; `NextW.ood`, `NextW.qS`, `NextW.qs`, `NextW.F3`, `NextW.lam`: the out-of-domain
points, the query grind's permutation, the positions, the sponge after the positions' squeezes,
`λ` (`levelNext_run`'s vocabulary).

`levelNext_inv`: an accepting run of `levelNext` from a carried sponge with nothing waiting read a
`NextW`, every hypothesis of `levelNext_run` holding at it, `λ` and the points' coordinates
nonzero; it returns `levelNext_run`'s glued state, sponge and roots.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none)

@[expose] public section

variable {α : Type}

/-! ## More primitives -/

theorem runTz_commitB {hh ww : ℕ} {f : Unit → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTz ((VerifierProgram.readCommitment hh ww).bind f) st = some r) :
    ∃ x0 x1 xs, st.stream = x0 :: x1 :: xs ∧ st.ground = none ∧
      runTz (f ()) ⟨(st.sponge.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, st.openings,
        st.roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ = some r :=
  runTz_commit (k := f ()) h

theorem runTz_queryB {i : ℕ} {ps : List ℕ} {f : List (List K) → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runTz ((VerifierProgram.queryOpenings i ps).bind f) st = some r) :
    ∃ root height width phase rest rows, st.roots[i]? = some (root, height, width) ∧
      st.openings = phase :: rest ∧
      Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) = some rows ∧
      runTz (f rows) ⟨st.sponge, st.ground, st.stream, rest, st.roots⟩ = some r :=
  runTz_query (k := f) h

/-- Two out-of-domain points from no ground, backwards. -/
theorem runTz_sampleOod2 {mu : ℕ} {f : List (List E) → VerifierProgram α} {st : TSt}
    {r : α × TSt} (hg : st.ground = none)
    (h : runTz ((sampleOodPoints mu 2).bind f) st = some r) :
    (∀ c ∈ (st.sponge.squeezeN mu).1, c ≠ 0) ∧
      (∀ c ∈ ((st.sponge.squeezeN mu).2.squeezeN mu).1, c ≠ 0) ∧
      runTz (f [(st.sponge.squeezeN mu).1, ((st.sponge.squeezeN mu).2.squeezeN mu).1])
        ⟨((st.sponge.squeezeN mu).2.squeezeN mu).2, none, st.stream, st.openings, st.roots⟩ = some r := by
  have e : (sampleOodPoints mu 2).bind f = (VerifierProgram.sampleChallenges mu).bind fun p1 ↦
      (VerifierProgram.sampleChallenges mu).bind fun p2 ↦ f [p1, p2] := by
    simp only [sampleOodPoints, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rw [e] at h
  obtain ⟨n1, h1⟩ := runTz_sampleChallenges mu st r hg h
  obtain ⟨n2, h2⟩ := runTz_sampleChallenges mu _ r rfl h1
  exact ⟨n1, n2, h2⟩

/-- **A forward run from a grind's ground challenge is the carried run** on any rest. -/
theorem runT_of_runsFromG {p : VerifierProgram α} {cap : List E} {c : E} {F' : Fs} {xs : List E}
    {a : α} (h : RunsFromG p cap c xs a F') (hc : ∃ sp, Fs.CarriesGround cap c sp)
    (rest : List E) (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    runT p ⟨⟨cap, []⟩, some c, xs ++ rest, os, R⟩ = some (a, ⟨F', none, rest, os, R⟩) := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp', hc', e⟩ := h sp hsp rest os R
  have := runT_of_runId p ⟨⟨cap, []⟩, some c, xs ++ rest, os, R⟩ sp hsp a _ e
  obtain ⟨e1, e2⟩ := eq_fsOfT (tcar_none.mpr hc')
  rw [this, ← e1, ← e2]

/-- An accepted phase: one opening per position, each accepted at its position, at the positions,
its leaves the rows. -/
theorem phase_of_some {root : Digest} {height width : ℕ} {ps : List ℕ} {phase : List Opening}
    {rows : List (List K)}
    (h : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) = some rows) :
    phase.length = ps.length ∧
      (∀ k (hk : k < ps.length) (ho : k < phase.length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width ps[k] phase[k]) = true) ∧
      phase.map Opening.leafIndex = ps ∧ rows = phase.map (·.leaf) := by
  obtain ⟨-, hidx, hall⟩ := openPhase_some keccak256 h
  have hl := (openAll_length keccak256 ps phase rows [] hall)
  have hlen : phase.length = ps.length := by simpa using hl.1
  have hok := openAll_openOne keccak256 ps phase rows [] hall
  refine ⟨hlen, hok, hidx, ?_⟩
  have := openPhase_eq_leaves keccak256 hlen hok hidx
  rw [h] at this
  exact Option.some.inj this

/-! ## What a non-final level reads -/

/-- **A non-final level's reads after its folds.** -/
structure NextW where
  x0 : E
  x1 : E
  high : List E
  y0 : E
  y1 : E
  nn : E
  n2 : E
  phase : List Opening

namespace NextW

variable (W : NextW) (F : Fs) (mu d Q : ℕ)

/-- Its words, in stream order. -/
def words : List E := W.x0 :: W.x1 :: W.high ++ [W.y0, W.y1, W.nn, W.n2]

/-- The sponge after the message. -/
def F1 : Fs := F.absorbAll (W.x0 :: W.x1 :: W.high) dsObserve

/-- The two out-of-domain points. -/
def ood : List (List E) :=
  [((W.F1 F).squeezeN mu).1, (((W.F1 F).squeezeN mu).2.squeezeN mu).1]

/-- The query grind's permutation. -/
def qS : KeccakState :=
  ((((W.F1 F).squeezeN mu).2.squeezeN mu).2.absorbAll [W.y0, W.y1] dsObserve).nonceState W.nn

/-- The positions, at the depth `d`, `Q` of them. -/
def qs : List ℕ := sqPositions d (sqSample (challengeOf (W.qS F mu)) (capOf (W.qS F mu))) Q

/-- The sponge after the positions' squeezes. -/
def F3 : Fs :=
  ((⟨capOf (W.qS F mu), []⟩ : Fs).squeezeN (sqCount (128 / d) Q - 1)).2

/-- `λ`. -/
def lam : E := challengeOf ((W.F3 F mu d Q).nonceState W.n2)

end NextW

/-- **`levelNext_run`'s hypotheses at what a non-final level read**, and its `λ` and points
nonzero. -/
structure NextOk (logN index : ℕ) (level : Whir.Level) (s : WhirState) (F : Fs)
    (R : List (Digest × ℕ × ℕ)) (W : NextW) : Prop where
  root : ∃ root height width, R[index]? = some (root, height, width) ∧
    (∀ k (hk : k < (W.qs F (logN - s.gammas.length) (logN - s.gammas.length + level.logInvRate)
        level.queries).length) (ho : k < W.phase.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width
        (W.qs F (logN - s.gammas.length) (logN - s.gammas.length + level.logInvRate)
          level.queries)[k] W.phase[k]) = true)
  hlen : W.high.length = level.fold
  ok1 : powOk Whir.queryGrindingBits (Keccak.lane (W.qS F (logN - s.gammas.length)) 2) = true
  ok2 : powOk Whir.batchGrindingBits (Keccak.lane ((W.F3 F (logN - s.gammas.length)
    (logN - s.gammas.length + level.logInvRate) level.queries).nonceState W.n2) 2) = true
  plen : W.phase.length = (W.qs F (logN - s.gammas.length)
    (logN - s.gammas.length + level.logInvRate) level.queries).length
  idx : W.phase.map Opening.leafIndex = W.qs F (logN - s.gammas.length)
    (logN - s.gammas.length + level.logInvRate) level.queries
  lam : W.lam F (logN - s.gammas.length) (logN - s.gammas.length + level.logInvRate)
    level.queries ≠ 0
  ood : ∀ p ∈ W.ood F (logN - s.gammas.length), ∀ c ∈ p, c ≠ 0

/-- What `levelNext_run` returns. -/
def NextW.glued (W : NextW) (logN index : ℕ) (level : Whir.Level) (s : WhirState) (F : Fs)
    (rounds : List FoldRound) : WhirState :=
  let mu := logN - s.gammas.length
  let d := mu + level.logInvRate
  glueLevel s (W.lam F mu d level.queries) mu (W.ood F mu) [W.y0, W.y1] (W.qs F mu d level.queries)
    (powers (W.lam F mu d level.queries) (W.qs F mu d level.queries).length)
    (levelBatched mu index rounds W.high (W.qs F mu d level.queries) (W.phase.map (·.leaf))
      (W.lam F mu d level.queries))


/-- The roots after a non-final level. -/
def NextW.roots (W : NextW) (mu : ℕ) (next : Whir.Level) (R : List (Digest × ℕ × ℕ)) :
    List (Digest × ℕ × ℕ) :=
  R ++ [(digestFromHalves (W.x0, W.x1), levelShape mu next (2 * 2 ^ next.fold))]

/-- **A non-final level after its folds, backwards.** -/
theorem levelNext_inv {logN index : ℕ} {level next : Whir.Level} {s : WhirState}
    {rounds : List FoldRound} {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : WhirState} {st1 : TSt}
    (hc : ∃ sp, F.Carries sp) (hR : index < R.length)
    (hP : 1 ≤ 128 / (logN - s.gammas.length + level.logInvRate)) (hQ : 0 < level.queries)
    (h : runTz (levelNext logN index level next s rounds) ⟨F, none, xs, os, R⟩ = some (a, st1)) :
    ∃ (W : NextW) (xs' : List E) (orest : List (List Opening)),
      xs = W.words ++ xs' ∧ os = W.phase :: orest ∧ NextOk logN index level s F R W ∧
      a = W.glued logN index level s F rounds ∧
      st1 = ⟨⟨capOf ((W.F3 F (logN - s.gammas.length) (logN - s.gammas.length + level.logInvRate)
        level.queries).nonceState W.n2), []⟩, none, xs', orest,
        W.roots (logN - s.gammas.length) next R⟩ := by
  have h0 := h
  set mu := logN - s.gammas.length with hmu
  set d := mu + level.logInvRate with hd
  unfold levelNext at h
  obtain ⟨x0, x1, xs1, hs1, -, h⟩ := runTz_commitB h
  obtain ⟨high, xs2, hhl, hs2, h⟩ := runTz_readScalars level.fold _ _ rfl h
  obtain ⟨nz1, nz2, h⟩ := runTz_sampleOod2 rfl h
  obtain ⟨ys, xs3, hyl, hs3, h⟩ := runTz_readScalars Whir.oodSamples _ _ rfl h
  obtain ⟨y0, y1, rfl⟩ : ∃ y0 y1, ys = [y0, y1] := by
    match ys, hyl with
    | [y0, y1], _ => exact ⟨y0, y1, rfl⟩
  obtain ⟨nn, xs4, hs4, -, hp1, h⟩ := runTz_grindPoW (by decide) h
  obtain ⟨qs', st2, hq1, h⟩ := runTz_bind_some h
  simp only at hs1 hs2 hs3 hs4
  set W0 : NextW := ⟨x0, x1, high, y0, y1, nn, 0, []⟩ with hW0
  have eS2 : ((((((F.absorb x0 dsObserve).absorb x1 dsObserve).absorbAll high dsObserve).squeezeN
      mu).2.squeezeN mu).2.absorbAll [y0, y1] dsObserve).nonceState nn = W0.qS F mu := rfl
  have hq2 := runTz_runT _ _ _ hq1
  rw [show xs4 = [] ++ xs4 from rfl] at hq2
  have hfq := runT_of_runsFromG (sampleQueries_runG d level.queries hP hQ (capOf (W0.qS F mu))
    (challengeOf (W0.qS F mu))) ⟨⟨W0.qS F mu, [], some (challengeOf (W0.qS F mu))⟩, rfl, rfl, rfl⟩
    xs4 os (R ++ [(digestFromHalves (x0, x1), levelShape mu next (2 * 2 ^ next.fold))])
  rw [eS2] at hq2
  rw [hq2] at hfq
  simp only [Option.some.injEq, Prod.mk.injEq] at hfq
  obtain ⟨eqs, est2⟩ := hfq
  subst eqs est2
  obtain ⟨n2, xs5, hs5, -, hp2, h⟩ := runTz_grindPoW (by decide) h
  obtain ⟨hlam, h⟩ := runTz_sampleE_some h rfl
  obtain ⟨root, height, width, phase, orest, rows, hroot, hos, hop, -⟩ := runTz_queryB h
  simp only at hs5 hos hroot hlam hp2
  set W : NextW := ⟨x0, x1, high, y0, y1, nn, n2, phase⟩ with hW
  have hqs : sqPositions d (fun j ↦ if j = 0 then challengeOf (W0.qS F mu) else
      ((⟨capOf (W0.qS F mu), []⟩ : Fs).squeezeN (j - 1)).2.squeeze.1) level.queries =
      W.qs F mu d level.queries := rfl
  rw [hqs] at hop
  obtain ⟨hl, hopen, hidx, -⟩ := phase_of_some hop
  have hroot' : R[index]? = some (root, height, width) := by
    rw [List.getElem?_append_left hR] at hroot; exact hroot
  have hxs : xs = W.words ++ xs5 := by
    rw [hs1, hs2, hs3, hs4, hs5]; simp [NextW.words, hW]
  have hfw := levelNext_run logN index level next s rounds F R hroot' x0 x1 high hhl y0 y1 nn n2
    (by decide) (by decide) hP hQ hp1 (W.qs F mu d level.queries) rfl (W.F3 F mu d level.queries) rfl
    hp2 phase hl hopen hidx
  rw [hxs, hos, show phase :: orest = [phase] ++ orest from rfl] at h0
  obtain ⟨ea, est⟩ := runTz_det h0 hfw hc
  refine ⟨W, xs5, orest, hxs, hos, ⟨⟨root, height, width, hroot', hopen⟩, hhl, hp1, hp2, hl, hidx,
    hlam, ?_⟩, ea, est⟩
  intro p hp c hc'
  simp only [NextW.ood, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact nz1 c hc'
  · exact nz2 c hc'

end
end LeanVM.Guest.B1.Whir
