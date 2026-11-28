/-
  LeanVM.Guest.B1.VsC.VsNatOpen

  An accepted child's run to its end, natively: the ring switch's packed draw from the grind's
  ground, the memory term, the stacked claims, and the stacked opening as `RunsWith` with its
  recorded queries the child's.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatTail
public import LeanVM.Guest.B1.VsC.VsNatSteps
public import LeanVM.Guest.B1.VsC.OpenStackedA
public import LeanVM.Guest.B1.Stack.Interface
public import LeanVM.Guest.B1.VerifySub.PhOodRingRun

/-!
# The run to its end

* `natFront_at'`: `natFront_at` with the stack's root among the roots and the out-of-domain claim.
* `ringChs S`, `ringF`, `ringG`, `ringRho`, `ringLam`, `ringCap`: the ring switch's packed draw from
  the grind's permutation `S` (the ground challenge, `S`'s cells `2 .. 7`, then eleven of two
  permutations of its capacity), split as `ringSwitch` splits it, and the capacity it leaves;
  **`runsTo_ringSwitch2`**: the grind and the draw, forward.
* `natMemoryTerm`, `runTc_bindPublicInput_val`, **`natVSO`**: `memoryTermClaim` is `memoryTermPure`'s,
  `bindPublicInput` returns `publicClaimsPure`'s claims, `verifyStackedOpening` is `whirOpen` then
  the terminal's check, its steps `whirOpen`'s.
* **`natOpen`** (`NatOpen`, `NatOpen.Ok`): on an accepted child, `natTail`'s facts, then the stacked
  claims (`stackedClaims … = some claims`, the list `verifyExecution` stacks), the stacked opening
  as a `RunsWith` from the capacity `ringCap` of the ring grind's permutation, at the stack's root,
  its `OpenRunQueries` at `childQueries`, and the terminal's identity with `stackedBasis`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Complete LeanVM.Guest.B1.Stack
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none NoPacked RunsG)
open LeanVM.Guest.B1.VerifySub (runId_bind_some)

@[expose] public section

variable {α β : Type}

/-! ## The front, with the root and the out-of-domain claim -/

/-- `commitStack`, backwards, with the root it appends. -/
theorem runTc_commitStack_roots {μ r : ℕ} {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {st1 : TSt}
    (h : runTc (commitStack μ r) ⟨F, none, xs, os, R⟩ = some ((), st1)) :
    ∃ x0 x1 xs', xs = x0 :: x1 :: xs' ∧
      st1 = ⟨(F.absorb x0 dsObserve).absorb x1 dsObserve, none, xs', os,
        R ++ [(digestFromHalves (x0, x1), stackShape μ r)]⟩ := by
  unfold commitStack at h
  obtain ⟨cfg, hcfg, h⟩ := runTc_liftOption' h
  rcases cfg with _ | ⟨level, _⟩
  · simp [runTc] at h
  · obtain ⟨x0, x1, xs', hs, -, h⟩ := runTc_commit (k := VerifierProgram.ret ()) h
    have e := runTc_ret_inv h
    simp only [Prod.mk.injEq] at e
    refine ⟨x0, x1, xs', hs, ?_⟩
    have hsh : stackShape μ r = levelShape μ level (2 ^ level.fold) := by simp only [stackShape, hcfg]
    rw [e.2, hsh]
    rfl

/-- **`natFront_at`, with the stack's root and the out-of-domain claim.** -/
theorem natFront_at' {bytecode : List K} {seed : Digest} {c : Child} {layout : Layout} {r : ℕ} {ood : StackClaim}
    {st1 st2 st3 : VerifierProgramState}
    (hS : runId (readAnnouncedSizes bytecode) (Coverage.childVerifierStart seed c) = some ((layout, r), st1))
    (hC : runId (commitStack layout.stackLog r) st1 = some ((), st2))
    (hO : runId (readOod layout.stackLog) st2 = some (ood, st3)) (hμ : 1 ≤ layout.stackLog) :
    TCar (natF3 seed c layout.stackLog) none st3.sponge ∧ st3.stream = c.proof.stream.drop 12 ∧
      st3.openings = c.proof.openings ∧
      st3.roots = [(digestFromHalves (c.proof.stream.getD 8 0, c.proof.stream.getD 9 0),
        stackShape layout.stackLog r)] ∧
      ood = (fun y ↦ eqEval (natOodZ seed c layout.stackLog) y, c.proof.stream.getD 11 0) := by
  set xs := c.proof.stream with hxs
  have h0 : TCar (natF0 seed c) none (Coverage.childVerifierStart seed c).sponge := ⟨rfl, rfl, rfl⟩
  have t1 := runTc_of_runId (noPacked_readAnnouncedSizes _) h0 hS
  obtain ⟨-, e1⟩ := runTc_sizes t1
  simp only [TSt.mk.injEq] at e1
  obtain ⟨f1, g1, s1, o1, r1⟩ := e1
  have c1 : TCar (natF1 seed c) none st1.sponge := tcar_of_eq f1 g1
  have t2 := runTc_of_runId (noPacked_commitStack _ _) c1 (show runId _ ⟨st1.sponge, st1.stream, st1.openings,
    st1.roots⟩ = _ from hC)
  rw [s1, o1] at t2
  obtain ⟨x0, x1, xs2, hx, e2⟩ := runTc_commitStack_roots t2
  simp only [TSt.mk.injEq] at e2
  obtain ⟨f2, g2, s2, o2, r2⟩ := e2
  have hx8 : xs.getD 8 0 = x0 := getD_of_drop hx 0
  have hx9 : xs.getD 9 0 = x1 := getD_of_drop hx 1
  have hF2 : fsOfT st2.sponge = natF2 seed c := by rw [f2, natF2, hx8, hx9]
  have c2 : TCar (natF2 seed c) none st2.sponge := tcar_of_eq hF2 g2
  have t3 := runTc_of_runId (noPacked_readOod _) c2 (show runId _ ⟨st2.sponge, st2.stream, st2.openings,
    st2.roots⟩ = _ from hO)
  rw [s2, o2] at t3
  obtain ⟨n, v, xs3, hx3, -, hv, hz, e3⟩ := runTc_readOod hμ t3
  simp only [TSt.mk.injEq] at e3
  obtain ⟨f3, g3, s3, o3, r3⟩ := e3
  have hd10 : xs.drop 10 = n :: v :: xs3 := (drop_of_drop hx 2).trans hx3
  have hx10 : xs.getD 10 0 = n := getD_of_drop hd10 0
  have hx11 : xs.getD 11 0 = v := getD_of_drop hd10 1
  have hd12 : xs.drop 12 = xs3 := drop_of_drop hd10 2
  refine ⟨?_, ?_, o3, ?_, ?_⟩
  · refine tcar_of_eq ?_ g3
    rw [f3, natF3, natOodS, hx10, hx11]
  · rw [s3, hd12]
  · rw [r3, r2, r1, hx8, hx9]
    rfl
  · refine Prod.ext ?_ ?_
    · rw [hz, natOodZ, natOodS, hx10]
    · rw [hv, hx11]

/-! ## The ring switch, forward -/

/-- The ring switch's packed draw from the grind's permutation `S`. -/
def ringChs (S : KeccakState) : List E :=
  challengeOf S :: (List.range 6).map (packedChallengeOf S ∘ (· + 2)) ++ (Link.pkSqueeze 2 (capOf S)).1.take 11

/-- The map's first challenges `f`. -/
def ringF (S : KeccakState) : List E := (ringChs S).take ringMapWidth

/-- The map's second challenges `g`. -/
def ringG (S : KeccakState) : List E := ((ringChs S).drop ringMapWidth).take ringMapWidth

/-- The merging challenge `ρ`. -/
def ringRho (S : KeccakState) : E := ((ringChs S).drop (2 * ringMapWidth)).getD 0 0

/-- The stacked opening's batching challenge `λ`. -/
def ringLam (S : KeccakState) : E := ((ringChs S).drop (2 * ringMapWidth)).getD 1 0

/-- The capacity the draw leaves. -/
def ringCap (S : KeccakState) : List E := (Link.pkSqueeze 2 (capOf S)).2

theorem ringCap_length (S : KeccakState) : (ringCap S).length = 5 := rfl

/-- **The ring switch on two claims, forward**: the grind on the nonce `n`, then the packed draw from its
permutation's ground. -/
theorem runsTo_ringSwitch2 (s : Fs) (n : E)
    (hok : powOk Whir.batchGrindingBits (Keccak.lane (s.nonceState n) 2) = true) (a b : RingClaim) :
    RunsTo (ringSwitch [a, b]) s [n]
      (ringMerge [a, b] (ringF (s.nonceState n)) (ringG (s.nonceState n)) (ringRho (s.nonceState n)),
        ringLam (s.nonceState n)) ⟨ringCap (s.nonceState n), []⟩ := by
  unfold ringSwitch
  exact VerifySub.runsTo_grindPacked (by decide) s n hok _ (runsTo_ret _ _)

/-! ## The memory term, the public input, the stacked opening -/

/-- **`memoryTermClaim`, backwards**: `memoryTermPure`'s claim, nothing read. -/
theorem natMemoryTerm {layout : Layout} {link : LinkEnd} {st : VerifierProgramState} {mt : StackClaim}
    {st' : VerifierProgramState} (h : runId (memoryTermClaim layout link) st = some (mt, st')) :
    memoryTermPure layout link = some mt ∧ st' = st := by
  unfold memoryTermClaim at h
  obtain ⟨p0, h0, h⟩ := natLiftOption h
  obtain ⟨p1, h1, h⟩ := natLiftOption h
  have e := natRet h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine ⟨?_, rfl⟩
  simp only [memoryTermPure, h0, h1]

/-- The public input's value on limb `j`'s line at the challenge `rm`. -/
def pubV (d : Digest) (rm : E) (j : Fin 2) : E :=
  multilinearEval [ofK ((digestHalves d).1.limb j), ofK ((digestHalves d).2.limb j)] [rm]

/-- **`bindPublicInput`'s claims** are `publicClaimsPure`'s at its challenge, the values the public input's
limbs on their lines. -/
theorem runTc_bindPublicInput_val {layout : Layout} {d : Digest} {F : Fs} {xs : List E}
    {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {a : List ColumnClaim} {st : TSt}
    (h : runTc (bindPublicInput layout d) ⟨F, none, xs, os, R⟩ = some (a, st)) :
    ∃ v0 v1, a = publicClaimsPure layout F.squeeze.1 v0 v1 ∧ v0 = pubV d F.squeeze.1 0 ∧
      v1 = pubV d F.squeeze.1 1 := by
  unfold bindPublicInput at h
  have h1 := runTc_sample_none h rfl
  obtain ⟨m, hm, h2⟩ := runTc_liftOption' h1
  have e := runTc_ret_inv h2
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, -⟩ := e
  refine ⟨pubV d F.squeeze.1 0, pubV d F.squeeze.1 1, ?_, rfl, rfl⟩
  simp only [publicClaimsPure, hm, Option.map_some, Option.getD_some]
  rfl

/-- **`verifyStackedOpening`, backwards**: the claims' bound, `whirOpen` at the batched target to the
end, the terminal's identity on `stackedBasis`, and its steps `whirOpen`'s. -/
theorem natVSO {μ r : ℕ} {claims : List StackClaim} {batching : E} {st st9 : VerifierProgramState} {u : Unit}
    (h : runId (verifyStackedOpening μ r claims batching) st = some (u, st9)) :
    claims.length ≤ maxStackedClaims ∧ ∃ wE : WhirEnd,
      runId (whirOpen μ r (dot (powers batching claims.length) (claims.map (·.2)))) st = some (wE, st9) ∧
      (wE.inner + stackedBasis claims batching wE.point) * wE.residual = wE.target ∧
      Limits.queryStepsOf (verifyStackedOpening μ r claims batching) st =
        Limits.queryStepsOf (whirOpen μ r (dot (powers batching claims.length) (claims.map (·.2)))) st := by
  unfold verifyStackedOpening at h ⊢
  simp only [verifyWhir_split] at h ⊢
  obtain ⟨u1, st', hq, h1, e1⟩ := runId_bind_q h
  have hc : claims.length ≤ maxStackedClaims := by
    by_contra hc
    unfold VerifierProgram.require at hq
    simp [hc, runId, Compile.runWithHash] at hq
  have hq' := hq
  unfold VerifierProgram.require at hq'
  simp only [hc, ↓reduceIte] at hq'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (natRet hq')
  obtain ⟨wE, st'', hW, h2, e2⟩ := runId_bind_q h1
  have hacc : wE.Accepts fun point ↦ dot (powers batching claims.length) (claims.map fun c ↦ c.1 point) := by
    by_contra hn
    unfold VerifierProgram.require at h2
    simp [hn, runId, Compile.runWithHash] at h2
  have h3 := h2
  unfold VerifierProgram.require at h3
  simp only [hacc, ↓reduceIte] at h3
  obtain ⟨-, rfl⟩ := Prod.mk.inj (natRet h3)
  refine ⟨hc, wE, hW, hacc, ?_⟩
  refine e1.trans ?_
  rw [steps_nil hq rfl, List.nil_append]
  exact e2.trans (by rw [steps_nil h2 rfl, List.append_nil])

/-! ## The run to its end -/

/-- What an accepted child's run past the link reads and returns, natively. -/
structure NatOpen where
  layout : Layout
  r : ℕ
  link : LinkEnd
  L : LinkNat
  rest : List E
  lanes : List E
  xs : List E
  n : E
  ws : List E
  outs : List ColumnClaim
  kp : List E
  ks : List E
  s' : Fs
  qp : Placement
  v0 : E
  v1 : E
  mt : StackClaim
  wE : WhirEnd
  s9 : Fs
  roots9 : List (Digest × ℕ × ℕ)

namespace NatOpen

variable (N : NatOpen) (seed : Digest) (c : Child)

/-- The ring grind's permutation. -/
def S : KeccakState := N.s'.nonceState N.n

/-- The public input's challenge. -/
noncomputable def rm : E := (N.L.F4 N.layout (natF3 seed c N.layout.stackLog)).squeeze.1

/-- The out-of-domain claim. -/
noncomputable def ood : StackClaim := (fun y ↦ eqEval (natOodZ seed c N.layout.stackLog) y, c.proof.stream.getD 11 0)

/-- The claims `verifyExecution` stacks. -/
noncomputable def claims : List StackClaim :=
  ringMerge [keccakRingClaim N.qp N.kp N.ks, N.link.ring] (ringF N.S) (ringG N.S) (ringRho N.S) :: N.mt ::
    ((linkColumnClaims N.link ++ publicClaimsPure N.layout (N.rm seed c) N.v0 N.v1) ++ N.outs).filterMap
      (·.onStack N.layout) ++ [N.ood seed c]

/-- The stacked opening's target. -/
noncomputable def target : E := dot (powers (ringLam N.S) (N.claims seed c).length) ((N.claims seed c).map (·.2))

end NatOpen

/-- The stack's root. -/
def natRoot (c : Child) : Digest := digestFromHalves (c.proof.stream.getD 8 0, c.proof.stream.getD 9 0)

/-- **An accepted child's run to its end, natively**: `natTail`'s facts, the stacked claims, the stacked
opening's run and recorded queries, the terminal's identity. -/
structure NatOpen.Ok (N : NatOpen) (seed : Digest) (c : Child) : Prop where
  hann : announcedLayoutAndRate guestBytecode c.proof.stream = some (N.layout, N.r)
  shape : VsShape guestBytecode N.layout N.r
  hw : c.proof.stream.drop 12 = N.L.words N.layout ++ N.rest
  hL : N.L.Ok N.layout (natF3 seed c N.layout.stackLog) c.freshClaim N.link
  hln : kLanes N.link = some N.lanes
  hrest : N.rest = N.xs ++ N.n :: N.ws
  hrun : RunsTo (verifyKeccak (N.layout.tableLogHeights.getD opKeccak 0) (N.link.columns.getD opKeccak ([], [])).1
    N.lanes) (N.L.F4 N.layout (natF3 seed c N.layout.stackLog)).squeeze.2 N.xs (N.outs, N.kp, N.ks) N.s'
  hpow : powOk Whir.batchGrindingBits (Keccak.lane (N.s'.nonceState N.n) 2) = true
  hqp : N.layout.placements.getD qkeccak none = some N.qp
  hmt : memoryTermPure N.layout N.link = some N.mt
  hcl : stackedClaims N.layout N.link (publicClaimsPure N.layout (N.rm seed c) N.v0 N.v1) N.outs N.kp N.ks
    (ringF N.S) (ringG N.S) (ringRho N.S) (fun y ↦ eqEval (natOodZ seed c N.layout.stackLog) y,
      c.proof.stream.getD 11 0) = some (N.claims seed c)
  hmax : (N.claims seed c).length ≤ maxStackedClaims
  hos : RunsWith (whirOpen N.layout.stackLog N.r (N.target seed c)) ⟨ringCap N.S, []⟩ N.ws c.proof.openings
    [(natRoot c, stackShape N.layout.stackLog N.r)] N.wE N.s9 N.roots9
  hq : OpenRunQueries N.layout.stackLog N.r (natRoot c) (N.target seed c) ⟨ringCap N.S, []⟩ N.ws c.proof.openings
    (Prover.childQueries guestBytecode seed c)
  hacc : (N.wE.inner + stackedBasis (N.claims seed c) (ringLam N.S) N.wE.point) * N.wE.residual = N.wE.target
  hv0 : N.v0 = pubV (statementDigest seed c.statement) (N.rm seed c) 0
  hv1 : N.v1 = pubV (statementDigest seed c.statement) (N.rm seed c) 1

theorem skipL {γ : Type} {A B C : List γ} (q : A = B ++ C) (n : B = []) : A = C := by rw [q, n, List.nil_append]

theorem skipR {γ : Type} {A B C : List γ} (q : A = B ++ C) (n : C = []) : A = B := by rw [q, n, List.append_nil]

theorem steps_nil_of_count {γ : Type} {l : List γ} {a b : ℕ} (h : l.length + a = b) (hab : a = b) : l = [] :=
  List.eq_nil_of_length_eq_zero (by omega)

/-- **The stacked opening's queries, from one accepting run**: on a longer stream and more phases, from any
sponge carried as `s`, its steps are the run's and its recorded queries `qs`. -/
theorem openRunQueries_of {μ r : ℕ} {root : Digest} {target : E} {s : Fs} {sp0 : Sponge} (hs0 : s.Carries sp0)
    {xs : List E} {os : List (List Opening)} {w : WhirEnd} {t : VerifierProgramState}
    (hW : runId (whirOpen μ r target) ⟨sp0, xs, os, [(root, stackShape μ r)]⟩ = some (w, t))
    (hst : t.stream = []) (hos : t.openings = []) (hg : t.sponge.ground = none) {qr qs : List (ℕ × List ℕ)}
    (hrec : runId (Prover.recordQueries (whirOpen μ r target)) ⟨sp0, xs, os, [(root, stackShape μ r)]⟩ =
      some ((w, qr), t))
    (hqs : qs = qr.map (hgtAt t.roots))
    (hag : ∀ step ∈ Limits.queryStepsOf (whirOpen μ r target) ⟨sp0, xs, os, [(root, stackShape μ r)]⟩,
      Limits.OpeningsAgree step.1 step.2) :
    OpenRunQueries μ r root target s xs os qs := by
  intro sp hs rest orest
  have hnp := Tables.noPacked_whirOpen μ r target
  refine ⟨fun step hstep => hag step ?_, ?_⟩
  · have hT := runT_of_runId _ hnp ⟨s, none, xs, os, [(root, stackShape μ r)]⟩ sp0 hs0 w t hW
    have eA : Limits.queryStepsOf (whirOpen μ r target) ⟨sp, xs ++ rest, os ++ orest, [(root, stackShape μ r)]⟩ =
        qstT (whirOpen μ r target) ⟨s, none, xs ++ rest, os ++ orest, [(root, stackShape μ r)]⟩ :=
      Whir.qstT_eq _ hnp ⟨s, none, xs ++ rest, os ++ orest, [(root, stackShape μ r)]⟩ sp hs
    have eB : Limits.queryStepsOf (whirOpen μ r target) ⟨sp0, xs, os, [(root, stackShape μ r)]⟩ =
        qstT (whirOpen μ r target) ⟨s, none, xs, os, [(root, stackShape μ r)]⟩ :=
      Whir.qstT_eq _ hnp ⟨s, none, xs, os, [(root, stackShape μ r)]⟩ sp0 hs0
    have eF : qstT (whirOpen μ r target) ⟨s, none, xs ++ rest, os ++ orest, [(root, stackShape μ r)]⟩ =
        qstT (whirOpen μ r target) ⟨s, none, xs, os, [(root, stackShape μ r)]⟩ :=
      qstT_frame _ _ _ _ hT rest orest
    rw [eB, ← eF, ← eA]
    exact hstep
  · obtain ⟨sp', -, e⟩ := VerifySub.runsWith_of_runId hs0 hrec hst hos hg (noPacked_recordQueries _ hnp) sp hs
      rest orest
    exact ⟨w, qr, _, e, hqs⟩

/-- The compiled run is the deployed one. -/
theorem run_keccak_eq {γ : Type} (X : VerifierProgram γ) (st : VerifierProgramState) :
    Id.run (Compile.run (m := Id) keccakF1600 X st) = runId X st :=
  Compile.run_eq_withHash (m := Id) keccakF1600 X st

/-- **The child's recorded queries**, from an accepting run of the deferring verifier. -/
theorem childQueries_eq {seed : Digest} {c : Child} {s : VerifierProgramState} {qr : List (ℕ × List ℕ)}
    (h : runId (Prover.recordQueries (deferringVerifierProgram c.freshClaim guestBytecode
      (statementDigest seed c.statement))) (Coverage.childVerifierStart seed c) = some ((true, qr), s)) :
    Prover.childQueries guestBytecode seed c = qr.map (hgtAt s.roots) := by
  unfold Prover.childQueries
  rw [run_keccak_eq, show runId (Prover.recordQueries (deferringVerifierProgram c.freshClaim guestBytecode
      (statementDigest seed c.statement))) ⟨⟨keccakF1600 (seedInput seed (statementDigest seed c.statement)), [], none⟩,
        c.proof.stream, c.proof.openings, []⟩ = some ((true, qr), s) from h]
  exact List.map_congr_left fun q _ => by obtain ⟨i, ps⟩ := q; rfl

/-- **An accepted child's run to its end.** -/
theorem natOpen {seed : Digest} {c : Child} (hc : VsChildOk guestBytecode seed c) : ∃ N : NatOpen, N.Ok seed c := by
  have hv := hc.1
  rw [verifyDeferred_eq_withHash] at hv
  change runProofWithHash (m := Id) keccak256 keccakF1600
    (deferringVerifierProgram c.freshClaim guestBytecode (statementDigest seed c.statement))
    (keccakF1600 (seedInput seed (statementDigest seed c.statement))) c.proof = true at hv
  obtain ⟨s4, hr, hse⟩ : ∃ s, runId (deferringVerifierProgram c.freshClaim guestBytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c) = some (true, s) ∧
      (s.stream.isEmpty && s.openings.isEmpty) = true := by
    change (match runId (deferringVerifierProgram c.freshClaim guestBytecode (statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false) = true at hv
    split at hv
    · exact ⟨_, by assumption, hv⟩
    · simp at hv
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hse
  have hr0 := hr
  -- the phases, with their steps
  unfold deferringVerifierProgram at hr
  obtain ⟨u, s4', hE, hT, q0⟩ := runId_bind_q hr
  rw [verifyExecution_eq] at hE
  obtain ⟨⟨layout, r⟩, st1, hS, hR, q1⟩ := runId_bind_q hE
  obtain ⟨u2, st2, hC, hR, q2⟩ := runId_bind_q hR
  obtain ⟨ood, st3, hO, hR, q3⟩ := runId_bind_q hR
  obtain ⟨link, st4, hL, hR, q4⟩ := runId_bind_q hR
  obtain ⟨pub, st5, hP, hR, q5⟩ := runId_bind_q hR
  obtain ⟨⟨outs, kp, ks⟩, st6, hK, hR, q6⟩ := runId_bind_q hR
  change runId ((liftOption (layout.placements.getD qkeccak none)).bind fun qp =>
    (ringSwitch [keccakRingClaim qp kp ks, link.ring]).bind fun rb =>
      (memoryTermClaim layout link).bind fun mt =>
        verifyStackedOpening layout.stackLog r
          (rb.1 :: mt :: ((linkColumnClaims link ++ pub) ++ outs).filterMap (·.onStack layout) ++ [ood]) rb.2)
    st6 = some (u, s4') at hR
  obtain ⟨qp, st6', hQ, hR6, q7⟩ := runId_bind_q hR
  have hqp : layout.placements.getD qkeccak none = some qp ∧ st6' = st6 := by
    revert hQ
    cases layout.placements.getD qkeccak none with
    | none =>
      intro hQ
      change runId VerifierProgram.fail st6 = _ at hQ
      simp [Compile.runWithHash] at hQ
    | some q =>
      intro hQ
      have e := Option.some.inj hQ
      simp only [Prod.mk.injEq] at e
      exact ⟨congrArg some e.1, e.2.symm⟩
  obtain ⟨hqp, hst6⟩ := hqp
  subst st6'
  obtain ⟨⟨ring, batching⟩, st7, hG, hR, q8⟩ := runId_bind_q hR6
  obtain ⟨mt, st8, hM, hV, q9⟩ := runId_bind_q hR
  -- the openings each phase consumes
  have c1 := (runSteps _ _ _ _ hS).2.1
  have c2 := (runSteps _ _ _ _ hC).2.1
  have c3 := (runSteps _ _ _ _ hO).2.1
  have c4 := (runSteps _ _ _ _ hL).2.1
  have c5 := (runSteps _ _ _ _ hP).2.1
  have c6 := (runSteps _ _ _ _ hK).2.1
  have c7 := (runSteps _ _ _ _ hQ).2.1
  have c8 := (runSteps _ _ _ _ hG).2.1
  have c9 := (runSteps _ _ _ _ hM).2.1
  -- the shape
  obtain ⟨layout', r', hann', S⟩ := vsShape_of_verifyDeferred hc.1
  have hann : announcedLayoutAndRate guestBytecode c.proof.stream = some (layout, r) := by
    rw [show c.proof.stream = (Coverage.childVerifierStart seed c).stream from rfl,
      announced_eq_run keccak256 keccakF1600 guestBytecode (s := Coverage.childVerifierStart seed c) rfl]
    change (runId (readAnnouncedSizes guestBytecode) (Coverage.childVerifierStart seed c)).map Prod.fst = _
    rw [hS]
    rfl
  rw [hann] at hann'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hann')
  have h16 : 16 ≤ layout.stackLog := S.stack_ge
  have h30 : layout.stackLog ≤ 30 := S.stack_le
  have hμ : 1 ≤ layout.stackLog := by omega
  -- the front and the link
  obtain ⟨c3', s3, o3, r3, hood⟩ := natFront_at' hS hC hO hμ
  obtain ⟨sp3, xs3, os3, R3⟩ := st3
  simp only at c3' s3 o3 r3
  obtain ⟨L, rest, hx, hok, sp4, c4', rfl⟩ := natLink_inv (announced_tables hann) c3' hL
  -- the public input's draw
  have t5 := runTc_of_runId (noPacked_bindPublicInput _ _) (tcar_none.mpr c4') hP
  obtain ⟨v0, v1, hpub, hv0, hv1⟩ := runTc_bindPublicInput_val t5
  obtain ⟨c5', hst5⟩ := natEnd (runTc_bindPublicInput t5)
  have hK' := hK
  rw [hst5] at hK'
  -- the Keccak reduction
  rw [keccakValidity_eq] at hK'
  obtain ⟨lanes, hln, hK'⟩ := natLiftOption hK'
  have hsh : ((link.columns.getD opKeccak ([], [])).1.length = layout.tableLogHeights.getD opKeccak 0 ∧
      lanes.length = keccakStateLanes ∧ 4 ≤ layout.tableLogHeights.getD opKeccak 0) := by
    have hK'' := hK'
    unfold verifyKeccak at hK''
    exact (natRequire hK'').1
  obtain ⟨ys, hys, ho6, hr6, hRG⟩ := runsG_of_runId (plain_verifyKeccak hsh) c5' hK'
  -- the ring switch's grind, then its draw forward
  obtain ⟨sp6, xs6, os6, R6⟩ := st6
  simp only at hys ho6 hr6 hRG
  have hG0 := hG
  unfold ringSwitch at hG
  have hb : Whir.batchGrindingBits ≠ 0 := by decide
  obtain ⟨u6, st1', t6, -⟩ := natBind_np (Tables.noPacked_grindProofOfWork _) (tcar_of_eq rfl rfl) hG
  unfold VerifierProgram.grindProofOfWork at t6
  simp only [hb, ↓reduceIte] at t6
  obtain ⟨n, ws, hx6, hg6, hpw, -⟩ := runTc_grind t6
  simp only at hx6 hg6 hpw
  rw [hg6] at hRG
  have c6' : (fsOfT sp6).Carries sp6 := ⟨rfl, rfl, hg6⟩
  obtain ⟨sp7, c7', e7⟩ := runsTo_ringSwitch2 (fsOfT sp6) n hpw (keccakRingClaim qp kp ks) link.ring sp6 c6' ws os6 R6
  rw [hx6] at hG0
  rw [show [n] ++ ws = n :: ws from rfl, hG0] at e7
  obtain ⟨hrb, rfl⟩ := Prod.mk.inj (Option.some.inj e7)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrb
  -- the memory term
  obtain ⟨hmt, rfl⟩ := natMemoryTerm hM
  -- the stacked opening
  obtain ⟨hmax, wE, hW, hacc, hstW⟩ := natVSO hV
  have e4 := natRet hT
  obtain ⟨-, rfl⟩ := Prod.mk.inj e4
  subst ho6 hr6 o3 r3 hpub hood
  -- every phase before the opening consumes no openings, so has no step
  have o5 : st5.openings = c.proof.openings := by rw [hst5]
  have c1' : (Limits.queryStepsOf (readAnnouncedSizes guestBytecode) (Coverage.childVerifierStart seed c)).length +
      st1.openings.length = c.proof.openings.length := c1
  have c3' : (Limits.queryStepsOf (readOod layout.stackLog) st2).length + c.proof.openings.length =
      st2.openings.length := c3
  have n1 : Limits.queryStepsOf (readAnnouncedSizes guestBytecode) (Coverage.childVerifierStart seed c) = [] :=
    List.eq_nil_of_length_eq_zero (by omega)
  have n2 : Limits.queryStepsOf (commitStack layout.stackLog r) st1 = [] :=
    List.eq_nil_of_length_eq_zero (by omega)
  have n3 : Limits.queryStepsOf (readOod layout.stackLog) st2 = [] :=
    List.eq_nil_of_length_eq_zero (by omega)
  have n4 := steps_nil_of_count c4 rfl
  have n5 := steps_nil_of_count c5 (by rw [o5])
  have n6 := steps_nil_of_count c6 (by rw [o5])
  have n7 := steps_nil_of_count c7 rfl
  have n8 := steps_nil_of_count c8 rfl
  have n9 := steps_nil_of_count c9 rfl
  have hsteps := (skipR q0 rfl).trans ((skipL q1 n1).trans ((skipL q2 n2).trans ((skipL q3 n3).trans
    ((skipL q4 n4).trans ((skipL q5 n5).trans ((skipL q6 n6).trans ((skipL q7 n7).trans ((skipL q8 n8).trans
      ((skipL q9 n9).trans hstW)))))))))
  -- the stacked opening's run and its recorded queries
  have hgW := endsAny_whirOpen h16 h30 S.rate_ge S.rate_le _ _ _ _ hW
  have hRW := VerifySub.runsWith_of_runId c7' hW hse.1 hse.2 hgW (Tables.noPacked_whirOpen _ _ _)
  obtain ⟨-, -, qrW, hrecW, hmapW⟩ := runSteps _ _ _ _ hW
  obtain ⟨-, -, qrP, hrecP, hmapP⟩ := runSteps _ _ _ _ hr0
  have hcq : Prover.childQueries guestBytecode seed c = qrW.map (hgtAt s4.roots) :=
    (childQueries_eq hrecP).trans (hmapP.trans ((congrArg (List.map stepPos) hsteps).trans hmapW.symm))
  have hq := openRunQueries_of c7' hW hse.1 hse.2 hgW hrecW hcq fun step hstep =>
    hc.2.2.2 step (Eq.mp (congrArg (step ∈ ·) hsteps.symm) hstep)
  refine ⟨⟨layout, r, link, L, rest, lanes, ys, n, ws, outs, kp, ks, fsOfT sp6, qp, v0, v1, mt, wE,
    fsOfT s4.sponge, s4.roots⟩, hann, S, by rw [← s3]; exact hx, hok, hln, by rw [hys, hx6],
    Tables.RunsG.toRunsTo hRG, hpw, hqp, hmt, ?_, hmax, hRW, hq, hacc, hv0, hv1⟩
  unfold stackedClaims
  rw [hqp, hmt]
  rfl

end
end LeanVM.Guest.B1.VsC
