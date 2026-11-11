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
part, the OOD nonce `n1`, the OOD value `y0`, the query nonce `nn` and its phase of openings;
`NextW.ood`, `NextW.qS`, `NextW.qs`, `NextW.F3`, `NextW.lam`: the OOD point, the query grind's
permutation, the positions, the sponge after the positions' squeezes, `λ` (`levelNext_run`'s
vocabulary).

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

/-- `m + 1` challenges from a ground challenge `c`, backwards. -/
theorem runTz_sampleChallengesG {f : List E → VerifierProgram α} (m : ℕ) {st : TSt} {r : α × TSt}
    {c : E} (hg : st.ground = some c)
    (h : runTz ((VerifierProgram.sampleChallenges (m + 1)).bind f) st = some r) :
    c ≠ 0 ∧ (∀ x ∈ (st.sponge.squeezeN m).1, x ≠ 0) ∧
      runTz (f (c :: (st.sponge.squeezeN m).1))
        ⟨(st.sponge.squeezeN m).2, none, st.stream, st.openings, st.roots⟩ = some r := by
  have e : (VerifierProgram.sampleChallenges (m + 1)).bind f =
      VerifierProgram.sampleChallenge.bind fun x ↦
        (VerifierProgram.sampleChallenges m).bind fun xs ↦ f (x :: xs) := by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rw [e] at h
  obtain ⟨hc, h⟩ := runTz_sampleE_some h hg
  obtain ⟨hn, h⟩ := runTz_sampleChallenges m _ r rfl h
  exact ⟨hc, hn, h⟩

/-- **A non-final level's reads after its folds.** -/
structure NextW where
  x0 : E
  x1 : E
  high : List E
  n1 : E
  y0 : E
  nn : E
  phase : List Opening

namespace NextW

variable (W : NextW) (F : Fs) (mu d Q : ℕ)

/-- Its words, in stream order. -/
def words : List E := W.x0 :: W.x1 :: W.high ++ [W.n1, W.y0, W.nn]

/-- The sponge after the message. -/
def F1 : Fs := F.absorbAll (W.x0 :: W.x1 :: W.high) dsObserve

/-- The out-of-domain point. -/
def ood : List E := (oodPt F (W.x0 :: W.x1 :: W.high) W.n1 mu).1

/-- The query grind's permutation. -/
def qS : KeccakState := oodQ F (W.x0 :: W.x1 :: W.high) W.n1 mu W.y0 W.nn

/-- The positions, at the depth `d`, `Q` of them. -/
def qs : List ℕ := sqPositions d (sqSample (challengeOf (W.qS F mu)) (capOf (W.qS F mu))) Q

/-- The sponge after the positions' squeezes. -/
def F3 : Fs :=
  ((⟨capOf (W.qS F mu), []⟩ : Fs).squeezeN (sqCount (128 / d) Q - 1)).2

/-- `λ`. -/
def lam : E := (W.F3 F mu d Q).squeeze.1

end NextW

/-- **`levelNext_run`'s hypotheses at what a non-final level read**, and its `λ` and point
nonzero. -/
structure NextOk (logN index : ℕ) (level : Whir.Level) (s : WhirState) (F : Fs)
    (R : List (Digest × ℕ × ℕ)) (W : NextW) : Prop where
  root : ∃ root height width, R[index]? = some (root, height, width) ∧
    (∀ k (hk : k < (W.qs F (logN - s.alphas.length) (logN - s.alphas.length + level.logInvRate)
        level.queries).length) (ho : k < W.phase.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width
        (W.qs F (logN - s.alphas.length) (logN - s.alphas.length + level.logInvRate)
          level.queries)[k] W.phase[k]) = true)
  hlen : W.high.length = level.fold
  ok0 : (W.F1 F).GrindOk levelOodGrind W.n1
  ok1 : powOk Whir.queryGrindingBits (Keccak.lane (W.qS F (logN - s.alphas.length)) 2) = true
  plen : W.phase.length = (W.qs F (logN - s.alphas.length)
    (logN - s.alphas.length + level.logInvRate) level.queries).length
  idx : W.phase.map Opening.leafIndex = W.qs F (logN - s.alphas.length)
    (logN - s.alphas.length + level.logInvRate) level.queries
  lam : W.lam F (logN - s.alphas.length) (logN - s.alphas.length + level.logInvRate)
    level.queries ≠ 0
  ood : ∀ c ∈ W.ood F (logN - s.alphas.length), c ≠ 0
  mu1 : 1 ≤ logN - s.alphas.length

/-- What `levelNext_run` returns. -/
def NextW.glued (W : NextW) (logN index : ℕ) (level : Whir.Level) (s : WhirState) (F : Fs)
    (rounds : List FoldRound) : WhirState :=
  let mu := logN - s.alphas.length
  let d := mu + level.logInvRate
  glueLevel s (W.lam F mu d level.queries) mu (W.ood F mu) W.y0 (W.qs F mu d level.queries)
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
    (hc : ∃ sp, F.Carries sp) (hR : index < R.length) (hmu : 1 ≤ logN - s.alphas.length)
    (hP : 1 ≤ 128 / (logN - s.alphas.length + level.logInvRate)) (hQ : 0 < level.queries)
    (h : runTz (levelNext logN index level next s rounds) ⟨F, none, xs, os, R⟩ = some (a, st1)) :
    ∃ (W : NextW) (xs' : List E) (orest : List (List Opening)),
      xs = W.words ++ xs' ∧ os = W.phase :: orest ∧ NextOk logN index level s F R W ∧
      a = W.glued logN index level s F rounds ∧
      st1 = ⟨(W.F3 F (logN - s.alphas.length) (logN - s.alphas.length + level.logInvRate)
        level.queries).squeeze.2, none, xs', orest, W.roots (logN - s.alphas.length) next R⟩ := by
  have h0 := h
  set mu := logN - s.alphas.length with hmud
  set d := mu + level.logInvRate with hd
  obtain ⟨m, hm⟩ : ∃ m, mu = m + 1 := ⟨mu - 1, by omega⟩
  unfold levelNext at h
  obtain ⟨x0, x1, xs1, hs1, -, h⟩ := runTz_commitB h
  obtain ⟨high, xs2, hhl, hs2, h⟩ := runTz_readScalars level.fold _ _ rfl h
  obtain ⟨n1, xs3, hs3, -, hp0, h⟩ := runTz_grindPoW (by decide) h
  rw [← hmud, hm] at h
  obtain ⟨nz0, nzs, h⟩ := runTz_sampleChallengesG m rfl h
  rw [← hm] at h
  obtain ⟨y0, xs4, hs4, -, h⟩ := runTz_readE h
  obtain ⟨nn, xs5, hs5, -, hp1, h⟩ := runTz_grindPoW (by decide) h
  obtain ⟨qs', st2, hq1, h⟩ := runTz_bind_some h
  simp only at hs1 hs2 hs3 hs4 hs5
  set W0 : NextW := ⟨x0, x1, high, n1, y0, nn, []⟩ with hW0
  have hF1 : ((F.absorb x0 dsObserve).absorb x1 dsObserve).absorbAll high dsObserve =
      F.absorbAll (x0 :: x1 :: high) dsObserve := rfl
  have hPt := oodPt_eq F (x0 :: x1 :: high) n1 mu
  rw [hm, Nat.add_sub_cancel] at hPt
  have eS2 : (((⟨capOf ((((F.absorb x0 dsObserve).absorb x1 dsObserve).absorbAll high
      dsObserve).nonceState n1), []⟩ : Fs).squeezeN m).2.absorb y0 dsObserve).nonceState nn =
        W0.qS F mu := by
    show _ = ((oodPt F (x0 :: x1 :: high) n1 mu).2.absorbAll [y0] dsObserve).nonceState nn
    rw [hm, hPt]
    rfl
  have hp1' : powOk Whir.queryGrindingBits (Keccak.lane (W0.qS F mu) 2) = true := by
    rw [← eS2]; exact hp1
  have hq2 := runTz_runT _ _ _ hq1
  rw [show xs5 = [] ++ xs5 from rfl] at hq2
  have hfq := runT_of_runsFromG (sampleQueries_runG d level.queries hP hQ (capOf (W0.qS F mu))
    (challengeOf (W0.qS F mu))) ⟨⟨W0.qS F mu, [], some (challengeOf (W0.qS F mu))⟩, rfl, rfl, rfl⟩
    xs5 os (R ++ [(digestFromHalves (x0, x1), levelShape mu next (2 * 2 ^ next.fold))])
  rw [eS2] at hq2
  rw [hq2] at hfq
  simp only [Option.some.injEq, Prod.mk.injEq] at hfq
  obtain ⟨eqs, est2⟩ := hfq
  subst eqs est2
  obtain ⟨hlam, h⟩ := runTz_sampleE_none h rfl
  obtain ⟨root, height, width, phase, orest, rows, hroot, hos, hop, -⟩ := runTz_queryB h
  simp only at hos hroot hlam
  set W : NextW := ⟨x0, x1, high, n1, y0, nn, phase⟩ with hW
  have hqs : sqPositions d (fun j ↦ if j = 0 then challengeOf (W0.qS F mu) else
      ((⟨capOf (W0.qS F mu), []⟩ : Fs).squeezeN (j - 1)).2.squeeze.1) level.queries =
      W.qs F mu d level.queries := rfl
  rw [hqs] at hop
  obtain ⟨hl, hopen, hidx, -⟩ := phase_of_some hop
  have hroot' : R[index]? = some (root, height, width) := by
    rw [List.getElem?_append_left hR] at hroot; exact hroot
  have hxs : xs = W.words ++ xs5 := by
    rw [hs1, hs2, hs3, hs4, hs5]
    show _ = (x0 :: x1 :: high ++ [n1, y0, nn]) ++ xs5
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  have hok0 : (W.F1 F).GrindOk levelOodGrind n1 := Or.inr (by
    rw [levelOodGrind_eq]; simpa [NextW.F1, hW, hF1] using hp0)
  have hfw := levelNext_run logN index level next s rounds F R hroot' x0 x1 high hhl n1 y0 nn
    hmu hP hQ hok0 hp1' (W.qs F mu d level.queries) rfl (W.F3 F mu d level.queries) rfl
    phase hl hopen hidx
  rw [hxs, hos, show phase :: orest = [phase] ++ orest from rfl] at h0
  obtain ⟨ea, est⟩ := runTz_det h0 hfw hc
  refine ⟨W, xs5, orest, hxs, hos, ⟨⟨root, height, width, hroot', hopen⟩, hhl, hok0, hp1', hl, hidx,
    hlam, ?_, hmu⟩, ea, est⟩
  intro x hx
  have e : W.ood F mu = (oodPt F (x0 :: x1 :: high) n1 mu).1 := rfl
  rw [e, hm, hPt, List.mem_cons] at hx
  rcases hx with rfl | hx
  · simpa [hF1] using nz0
  · exact nzs x (by simpa [hF1] using hx)

end
end LeanVM.Guest.B1.Whir
