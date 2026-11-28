/-
  LeanVM.Guest.B1.VsC.VsNatFront

  An accepted child's run replayed up to the link: the seed, the announced sizes, the stack's root,
  the out-of-domain grind, point and value, as the guest's carried sponge.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatChain
public import LeanVM.Guest.B1.VsC.Announced
public import LeanVM.Guest.B1.VsC.Os.NoPacked
public import LeanVM.Guest.B1.VsC.Os.RunId
public import LeanVM.Guest.Complete.CallComplete
public import LeanVM.Guest.B1.VsC.Shape

/-!
# The front of an accepted child's run

`natRun_phases`: an accepted child's deployed run is `readAnnouncedSizes` to the announced layout
and rate, then `commitStack`, `readOod` and `verifyLink`, each a deployed run from where the last
stopped. Read backwards on the carried sponge (`runTc_sizes`, `runTc_commitStack`, `runTc_readOod`):
from the seed's capacity `natF0`, the first eight words absorbed (`natF1`), the root's two
(`natF2`), the out-of-domain nonce (word `10`) passing its grind, the point `natOodZ` (the grind's
challenge, then squeezes), the value (word `11`) waiting (`natF3`). **`natFront`**: the link's run
starts on a sponge carried as `natF3`, on the stream past its first `12` words.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Complete
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none NoPacked
  noPacked_readScalars noPacked_liftOption noPacked_readCommitment noPacked_grindProofOfWork
  noPacked_sampleChallenges noPacked_readScalar)
open LeanVM.Guest.B1.VerifySub (runId_bind_some)

@[expose] public section

variable {α β : Type}

/-! ## The deployed run, by phase -/

/-- **An accepted child's deployed run, by phase**: the announced sizes, the stack's root, the
out-of-domain sample, the link, each run from where the last stopped. -/
theorem natRun_phases {bytecode : List K} {seed : Digest} {c : Child} (hc : VsChildOk bytecode seed c) :
    ∃ (layout : Layout) (r : ℕ) (ood : StackClaim) (link : LinkEnd)
      (st1 st2 st3 st4 : VerifierProgramState),
      announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) ∧
      runId (readAnnouncedSizes bytecode) (Coverage.childVerifierStart seed c) = some ((layout, r), st1) ∧
      runId (commitStack layout.stackLog r) st1 = some ((), st2) ∧
      runId (readOod layout.stackLog) st2 = some (ood, st3) ∧
      runId (verifyLink (freshSplit c.freshClaim) layout) st3 = some (link, st4) := by
  have hv := hc.1
  rw [verifyDeferred_eq_withHash] at hv
  change runProofWithHash (m := Id) keccak256 keccakF1600
    (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
    (keccakF1600 (seedInput seed (statementDigest seed c.statement))) c.proof = true at hv
  obtain ⟨s, hr⟩ : ∃ s, runId (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) = some (true, s) := by
    change (match runId (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false) = true at hv
    split at hv
    · exact ⟨_, by assumption⟩
    · simp at hv
  unfold deferringVerifierProgram at hr
  obtain ⟨u, s4, hE, -⟩ := runId_bind_some hr
  rw [verifyExecution_eq] at hE
  obtain ⟨⟨layout, r⟩, st1, hS, hR⟩ := runId_bind_some hE
  obtain ⟨u2, st2, hC, hR⟩ := runId_bind_some hR
  obtain ⟨ood, st3, hO, hR⟩ := runId_bind_some hR
  obtain ⟨link, st4, hL, -⟩ := runId_bind_some hR
  refine ⟨layout, r, ood, link, st1, st2, st3, st4, ?_, hS, hC, hO, hL⟩
  rw [show c.proof.stream = (Coverage.childVerifierStart seed c).stream from rfl,
    announced_eq_run keccak256 keccakF1600 bytecode (s := Coverage.childVerifierStart seed c) rfl]
  change (runId (readAnnouncedSizes bytecode) (Coverage.childVerifierStart seed c)).map Prod.fst = _
  rw [hS]
  rfl

/-- **An accepted child's deployed run, every phase**: past the link, the public input's claims, the Keccak
reduction, the Keccak slot's placement, the ring switch, the memory term and the stacked opening, the
stream and the openings used up. -/
theorem natRun_all {bytecode : List K} {seed : Digest} {c : Child} (hc : VsChildOk bytecode seed c) :
    ∃ (layout : Layout) (r : ℕ) (ood : StackClaim) (link : LinkEnd)
      (st1 st2 st3 st4 : VerifierProgramState),
      announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) ∧
      runId (readAnnouncedSizes bytecode) (Coverage.childVerifierStart seed c) = some ((layout, r), st1) ∧
      runId (commitStack layout.stackLog r) st1 = some ((), st2) ∧
      runId (readOod layout.stackLog) st2 = some (ood, st3) ∧
      runId (verifyLink (freshSplit c.freshClaim) layout) st3 = some (link, st4) ∧
      ∃ (pub : List ColumnClaim) (st5 : VerifierProgramState),
        runId (bindPublicInput layout (statementDigest seed c.statement)) st4 = some (pub, st5) ∧
      ∃ (outs : List ColumnClaim) (kp ks : List E) (st6 : VerifierProgramState),
        runId (keccakValidity layout link) st5 = some ((outs, kp, ks), st6) ∧
      ∃ qp : Placement, layout.placements.getD qkeccak none = some qp ∧
      ∃ (ring : StackClaim) (batching : E) (st7 : VerifierProgramState),
        runId (ringSwitch [keccakRingClaim qp kp ks, link.ring]) st6 = some ((ring, batching), st7) ∧
      ∃ (mt : StackClaim) (st8 : VerifierProgramState),
        runId (memoryTermClaim layout link) st7 = some (mt, st8) ∧
      ∃ st9 : VerifierProgramState,
        runId (verifyStackedOpening layout.stackLog r
          (ring :: mt :: ((linkColumnClaims link ++ pub) ++ outs).filterMap (·.onStack layout) ++ [ood])
          batching) st8 = some ((), st9) ∧
        st9.stream = [] ∧ st9.openings = [] := by
  have hv := hc.1
  rw [verifyDeferred_eq_withHash] at hv
  change runProofWithHash (m := Id) keccak256 keccakF1600
    (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
    (keccakF1600 (seedInput seed (statementDigest seed c.statement))) c.proof = true at hv
  obtain ⟨s, hr, hse⟩ : ∃ s, runId (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) = some (true, s) ∧ (s.stream.isEmpty && s.openings.isEmpty) = true := by
    change (match runId (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false) = true at hv
    split at hv
    · exact ⟨_, by assumption, hv⟩
    · simp at hv
  unfold deferringVerifierProgram at hr
  obtain ⟨u, s4, hE, hT⟩ := runId_bind_some hr
  have eT := Option.some.inj hT
  simp only [Prod.mk.injEq] at eT
  obtain ⟨-, rfl⟩ := eT
  rw [verifyExecution_eq] at hE
  obtain ⟨⟨layout, r⟩, st1, hS, hR⟩ := runId_bind_some hE
  obtain ⟨u2, st2, hC, hR⟩ := runId_bind_some hR
  obtain ⟨ood, st3, hO, hR⟩ := runId_bind_some hR
  obtain ⟨link, st4, hL, hR⟩ := runId_bind_some hR
  obtain ⟨pub, st5, hP, hR⟩ := runId_bind_some hR
  obtain ⟨⟨outs, kp, ks⟩, st6, hK, hR⟩ := runId_bind_some hR
  change runId ((liftOption (layout.placements.getD qkeccak none)).bind fun qp =>
    (ringSwitch [keccakRingClaim qp kp ks, link.ring]).bind fun rb =>
      (memoryTermClaim layout link).bind fun mt =>
        verifyStackedOpening layout.stackLog r
          (rb.1 :: mt :: ((linkColumnClaims link ++ pub) ++ outs).filterMap (·.onStack layout) ++ [ood]) rb.2)
    st6 = some (u, s4) at hR
  obtain ⟨qp, st6', hQ, hR6⟩ := runId_bind_some hR
  clear hR
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
  obtain ⟨hq, rfl⟩ := hqp
  obtain ⟨⟨ring, batching⟩, st7, hG, hR⟩ := runId_bind_some hR6
  obtain ⟨mt, st8, hM, hR⟩ := runId_bind_some hR
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hse
  refine ⟨layout, r, ood, link, st1, st2, st3, st4, ?_, hS, hC, hO, hL, pub, st5, hP, outs, kp, ks, _, hK,
    qp, hq, ring, batching, st7, hG, mt, st8, hM, s4, hR, hse.1, hse.2⟩
  rw [show c.proof.stream = (Coverage.childVerifierStart seed c).stream from rfl,
    announced_eq_run keccak256 keccakF1600 bytecode (s := Coverage.childVerifierStart seed c) rfl]
  change (runId (readAnnouncedSizes bytecode) (Coverage.childVerifierStart seed c)).map Prod.fst = _
  rw [hS]
  rfl

/-! ## The carried sponge, by phase -/

/-- The seed's state. -/
def natSeed (seed : Digest) (c : Child) : KeccakState :=
  keccakF1600 (seedInput seed (statementDigest seed c.statement))

/-- The carried sponge at the start: the seed's capacity, nothing waiting. -/
def natF0 (seed : Digest) (c : Child) : Fs := ⟨capOf (natSeed seed c), []⟩

/-- After the announced sizes: the stream's first eight words absorbed. -/
def natF1 (seed : Digest) (c : Child) : Fs := (natF0 seed c).absorbAll (c.proof.stream.take 8) dsObserve

/-- After the stack's root: words `8`, `9` absorbed. -/
def natF2 (seed : Digest) (c : Child) : Fs :=
  ((natF1 seed c).absorb (c.proof.stream.getD 8 0) dsObserve).absorb (c.proof.stream.getD 9 0) dsObserve

/-- The out-of-domain grind's permutation: word `10` absorbed as the nonce. -/
def natOodS (seed : Digest) (c : Child) : KeccakState := (natF2 seed c).nonceState (c.proof.stream.getD 10 0)

/-- The out-of-domain point: the grind's challenge, then `μ - 1` squeezes of its capacity. -/
def natOodZ (seed : Digest) (c : Child) (μ : ℕ) : List E :=
  challengeOf (natOodS seed c) :: ((⟨capOf (natOodS seed c), []⟩ : Fs).squeezeN (μ - 1)).1

/-- After the out-of-domain sample: the squeezes' sponge, the value (word `11`) waiting. -/
def natF3 (seed : Digest) (c : Child) (μ : ℕ) : Fs :=
  ((⟨capOf (natOodS seed c), []⟩ : Fs).squeezeN (μ - 1)).2.absorb (c.proof.stream.getD 11 0) dsObserve

/-- A deployed run of a program with no packed step, from a carried sponge, is the carried run. -/
theorem runTc_of_runId {p : VerifierProgram α} (hnp : NoPacked p) {F : Fs} {g : Option E} {sp : Sponge}
    (hs : TCar F g sp) {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {a : α}
    {t : VerifierProgramState} (h : runId p ⟨sp, xs, os, R⟩ = some (a, t)) :
    runTc p ⟨F, g, xs, os, R⟩ = some (a, ⟨fsOfT t.sponge, t.sponge.ground, t.stream, t.openings, t.roots⟩) := by
  rw [runTc_eq_runT]
  exact runT_of_runId p hnp ⟨F, g, xs, os, R⟩ sp hs a t h

/-- A carried run's end state is that of the deployed run's sponge. -/
theorem tcar_of_eq {F : Fs} {g : Option E} {sp : Sponge} (h : fsOfT sp = F) (hg : sp.ground = g) :
    TCar F g sp := by
  subst h hg; exact ⟨rfl, rfl, rfl⟩

/-- `liftOption`, backwards. -/
theorem runTc_liftOption' {o : Option α} {f : α → VerifierProgram β} {st : TSt}
    {r : β × TSt} (h : runTc ((liftOption o).bind f) st = some r) :
    ∃ a, o = some a ∧ runTc (f a) st = some r := by
  cases o with
  | none =>
    change runTc VerifierProgram.fail st = some r at h
    simp [runTc] at h
  | some a => exact ⟨a, rfl, h⟩

/-- **The announced sizes, backwards**: eight words absorbed. -/
theorem runTc_sizes {bytecode : List K} {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : Layout × ℕ} {st1 : TSt}
    (h : runTc (readAnnouncedSizes bytecode) ⟨F, none, xs, os, R⟩ = some (a, st1)) :
    8 ≤ xs.length ∧ st1 = ⟨F.absorbAll (xs.take 8) dsObserve, none, xs.drop 8, os, R⟩ := by
  rw [readSizes_eq] at h
  obtain ⟨ys, zs, hl, hs, h⟩ := runTc_readScalars (2 + nTables) _ _ rfl h
  have h8 : ys.length = 8 := hl
  simp only at hs
  subst hs
  cases hso : sizesOf bytecode ys with
  | none => rw [hso, liftOption_none] at h; simp [runTc] at h
  | some b =>
    rw [hso, liftOption_some] at h
    have e := runTc_ret_inv h
    simp only [Prod.mk.injEq] at e
    refine ⟨by simp [h8], ?_⟩
    rw [e.2, List.take_left' h8, List.drop_left' h8]

/-- **The stack's root, backwards**: two words absorbed. -/
theorem runTc_commitStack {μ r : ℕ} {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {st1 : TSt}
    (h : runTc (commitStack μ r) ⟨F, none, xs, os, R⟩ = some ((), st1)) :
    ∃ x0 x1 xs' R', xs = x0 :: x1 :: xs' ∧
      st1 = ⟨(F.absorb x0 dsObserve).absorb x1 dsObserve, none, xs', os, R'⟩ := by
  unfold commitStack at h
  obtain ⟨cfg, -, h⟩ := runTc_liftOption' h
  rcases cfg with _ | ⟨level, _⟩
  · simp [runTc] at h
  · obtain ⟨x0, x1, xs', hs, -, h⟩ := runTc_commit (k := VerifierProgram.ret ()) h
    have e := runTc_ret_inv h
    simp only [Prod.mk.injEq] at e
    exact ⟨x0, x1, xs', _, hs, e.2⟩

theorem oodGrind_ne : Whir.oodGrindingBits ≠ 0 := by decide

/-- `n + 1` samples from a ground challenge: the challenge, then `n` squeezes. -/
theorem runTc_sampleChallengesG {f : List E → VerifierProgram α} (n : ℕ) {F : Fs} {c : E} {xs : List E}
    {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {r : α × TSt}
    (h : runTc ((VerifierProgram.sampleChallenges (n + 1)).bind f) ⟨F, some c, xs, os, R⟩ = some r) :
    runTc (f (c :: (F.squeezeN n).1)) ⟨(F.squeezeN n).2, none, xs, os, R⟩ = some r := by
  have e : (VerifierProgram.sampleChallenges (n + 1)).bind f =
      .sample fun x ↦ (VerifierProgram.sampleChallenges n).bind fun ys ↦ f (x :: ys) := by
    show ((VerifierProgram.sample VerifierProgram.ret).bind fun x ↦
      ((VerifierProgram.sampleChallenges n).bind fun ys ↦ VerifierProgram.ret (x :: ys))).bind f = _
    simp only [VerifierProgram.bind_assoc]
    rfl
  rw [e] at h
  exact runTc_sampleChallenges n _ r rfl (runTc_sample_some (k := fun x ↦
    (VerifierProgram.sampleChallenges n).bind fun ys ↦ f (x :: ys)) h rfl)

/-- **The out-of-domain sample, backwards**: the nonce passing its grind, the point, the value
waiting. -/
theorem runTc_readOod {μ : ℕ} (hμ : 1 ≤ μ) {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : StackClaim} {st1 : TSt}
    (h : runTc (readOod μ) ⟨F, none, xs, os, R⟩ = some (a, st1)) :
    ∃ n v xs', xs = n :: v :: xs' ∧
      powOk Whir.oodGrindingBits (Keccak.lane (F.nonceState n) 2) = true ∧
      a.2 = v ∧
      a.1 = (fun x ↦ eqEval (challengeOf (F.nonceState n) ::
        ((⟨capOf (F.nonceState n), []⟩ : Fs).squeezeN (μ - 1)).1) x) ∧
      st1 = ⟨((⟨capOf (F.nonceState n), []⟩ : Fs).squeezeN (μ - 1)).2.absorb v dsObserve, none, xs', os, R⟩ := by
  unfold readOod at h
  obtain ⟨n, xs1, hs1, -, hp, h⟩ := runTc_grindPoW oodGrind_ne h
  obtain ⟨k, rfl⟩ : ∃ k, μ = k + 1 := ⟨μ - 1, by omega⟩
  have h2 := runTc_sampleChallengesG k h
  obtain ⟨v, xs2, hs2, -, h3⟩ := runTc_readE h2
  have e := runTc_ret_inv h3
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  simp only at hs1 hs2
  subst hs1 hs2
  exact ⟨n, v, xs2, rfl, hp, rfl, rfl, rfl⟩

/-! ## The front, composed -/

theorem noPacked_readAnnouncedSizes (bytecode : List K) : NoPacked (readAnnouncedSizes bytecode) := by
  rw [readSizes_eq]
  exact NoPacked.bind (noPacked_readScalars _) fun _ => noPacked_liftOption _

theorem noPacked_commitStack (μ r : ℕ) : NoPacked (commitStack μ r) := by
  unfold commitStack
  refine NoPacked.bind (noPacked_liftOption _) fun cfg => ?_
  rcases cfg with _ | ⟨level, _⟩
  · exact trivial
  · exact noPacked_readCommitment _ _

theorem noPacked_readOod (μ : ℕ) : NoPacked (readOod μ) :=
  NoPacked.bind' (noPacked_grindProofOfWork _) fun _ => NoPacked.bind' (noPacked_sampleChallenges _) fun _ =>
    NoPacked.bind' noPacked_readScalar fun _ => trivial

theorem getD_of_drop {xs ys : List E} {i : ℕ} (h : xs.drop i = ys) (j : ℕ) :
    xs.getD (i + j) 0 = ys.getD j 0 := by
  rw [← h]; simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem drop_of_drop {xs ys : List E} {i : ℕ} (h : xs.drop i = ys) (j : ℕ) :
    xs.drop (i + j) = ys.drop j := by
  rw [← h, List.drop_drop]

/-- **The front of an accepted child's run**: the stream announces the layout and rate, the
out-of-domain nonce passes its grind, the sample is the point `natOodZ` and the value at word `11`,
and the link runs from a sponge carried as `natF3`, on the stream past its first `12` words. -/
theorem natFront {bytecode : List K} {seed : Digest} {c : Child} (hc : VsChildOk bytecode seed c) :
    ∃ (layout : Layout) (r : ℕ), announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) ∧
      VsShape bytecode layout r ∧ 12 ≤ c.proof.stream.length ∧
      powOk Whir.oodGrindingBits (Keccak.lane (natOodS seed c) 2) = true ∧
      ∃ (ood : StackClaim) (link : LinkEnd) (st3 st4 : VerifierProgramState),
        ood.2 = c.proof.stream.getD 11 0 ∧
        ood.1 = (fun x ↦ eqEval (natOodZ seed c layout.stackLog) x) ∧
        TCar (natF3 seed c layout.stackLog) none st3.sponge ∧ st3.stream = c.proof.stream.drop 12 ∧
        st3.openings = c.proof.openings ∧
        runId (verifyLink (freshSplit c.freshClaim) layout) st3 = some (link, st4) := by
  obtain ⟨layout, r, ood, link, st1, st2, st3, st4, hann, hS, hC, hO, hL⟩ := natRun_phases hc
  obtain ⟨layout', r', hann', S⟩ := vsShape_of_verifyDeferred hc.1
  rw [hann] at hann'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hann')
  have hμ : 1 ≤ layout.stackLog := le_trans (by decide) S.stack_ge
  set xs := c.proof.stream with hxs
  -- the sizes
  have h0 : TCar (natF0 seed c) none (Coverage.childVerifierStart seed c).sponge := ⟨rfl, rfl, rfl⟩
  have t1 := runTc_of_runId (noPacked_readAnnouncedSizes _) h0 hS
  obtain ⟨hl8, e1⟩ := runTc_sizes t1
  simp only [TSt.mk.injEq] at e1
  obtain ⟨f1, g1, s1, o1, r1⟩ := e1
  have c1 : TCar (natF1 seed c) none st1.sponge := tcar_of_eq f1 g1
  -- the root
  have t2 := runTc_of_runId (noPacked_commitStack _ _) c1 (show runId _ ⟨st1.sponge, st1.stream, st1.openings,
    st1.roots⟩ = _ from hC)
  rw [s1, o1] at t2
  obtain ⟨x0, x1, xs2, R2, hx, e2⟩ := runTc_commitStack t2
  simp only [TSt.mk.injEq] at e2
  obtain ⟨f2, g2, s2, o2, -⟩ := e2
  have hx8 : xs.getD 8 0 = x0 := getD_of_drop hx 0
  have hx9 : xs.getD 9 0 = x1 := getD_of_drop hx 1
  have c2 : TCar (natF2 seed c) none st2.sponge := by
    refine tcar_of_eq ?_ g2
    rw [f2, natF2, hx8, hx9]
  -- the out-of-domain sample
  have t3 := runTc_of_runId (noPacked_readOod _) c2 (show runId _ ⟨st2.sponge, st2.stream, st2.openings,
    st2.roots⟩ = _ from hO)
  rw [s2, o2] at t3
  obtain ⟨n, v, xs3, hx3, hp, hv, hz, e3⟩ := runTc_readOod hμ t3
  simp only [TSt.mk.injEq] at e3
  obtain ⟨f3, g3, s3, o3, -⟩ := e3
  have hd10 : xs.drop 10 = n :: v :: xs3 := (drop_of_drop hx 2).trans hx3
  have hx10 : xs.getD 10 0 = n := getD_of_drop hd10 0
  have hx11 : xs.getD 11 0 = v := getD_of_drop hd10 1
  have hd12 : xs.drop 12 = xs3 := drop_of_drop hd10 2
  have hlen : 12 ≤ xs.length := by
    have := congrArg List.length hd10; simp at this; omega
  refine ⟨layout, r, hann, S, hlen, ?_, ood, link, st3, st4, by rw [hv, hx11], ?_, ?_, ?_, ?_, hL⟩
  · rw [natOodS, hx10]; exact hp
  · rw [hz, natOodZ, natOodS, hx10]
  · refine tcar_of_eq ?_ g3
    rw [f3, natF3, natOodS, hx10, hx11]
  · rw [s3, hd12]
  · exact o3

end
end LeanVM.Guest.B1.VsC
