/-
  LeanVM.Guest.B1.Whir.CRecChild

  A child's query steps are its stacked opening's, so its Merkle hints are, stream by stream, what the levels' `level_queries` pop at the honest witness.
-/

module

public import LeanVM.Guest.B1.Whir.CRecLevels
public import LeanVM.Guest.B1.VerifySub.Segments

/-!
# The child's query steps

* `NoQueryA`: no `query` on any path; such a program has no step (`queryStepsOf_nil_of_nq`), `flatPre` among them;
* `SegSteps S`: the child's query steps are those of the stacked opening of its segments `S`;
* `child_segments_steps`: `child_segments`, its segments with `SegSteps`;
* `child_merkle_sameStreams`: on an honest run of the segments' opening whose steps are its levels', the child's Merkle hints are, stream by stream, its levels' `level_queries` entries (`lvPops`), level 0 first.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory

@[expose] public section

/-! ## Programs with no query -/

/-- No `query` on any path. -/
def NoQueryA {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoQueryA (k x)
  | .sample k => ∀ c, NoQueryA (k c)
  | .grind _ k => NoQueryA k
  | .commit _ _ k => NoQueryA k
  | .query _ _ _ => False

theorem NoQueryA.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : NoQueryA p) (hf : ∀ a, NoQueryA (f a)) : NoQueryA (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit _ _ _ ih => exact ih hp
  | query _ _ _ _ => exact hp.elim

/-- **No `query` on any path.** Irreducible, as `NoCommit`. -/
@[irreducible] def NoQuery {α : Type} (p : VerifierProgram α) : Prop := NoQueryA p

theorem noQuery_iff {α : Type} (p : VerifierProgram α) : NoQuery p ↔ NoQueryA p := by
  unfold NoQuery; rfl

theorem NoQuery.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : NoQuery p) (hf : ∀ a, NoQuery (f a)) : NoQuery (p.bind f) :=
  (noQuery_iff _).2 (NoQueryA.bind ((noQuery_iff _).1 hp) fun a ↦ (noQuery_iff _).1 (hf a))

theorem noQueryA_of_nc {α : Type} {p : VerifierProgram α} (h : NoCommit p) : NoQueryA p := by
  have h' := (noCommit_iff p).1 h
  clear h
  induction p with
  | ret _ => trivial
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (h' x)
  | sample k ih => exact fun c ↦ ih c (h' c)
  | grind b k ih => exact ih h'
  | commit _ _ _ _ => exact h'.elim
  | query _ _ _ _ => exact h'.elim

theorem noQuery_of_nc {α : Type} {p : VerifierProgram α} (h : NoCommit p) : NoQuery p :=
  (noQuery_iff p).2 (noQueryA_of_nc h)

/-- **A program with no query has no step.** -/
theorem queryStepsOf_nil_of_nq {α : Type} : ∀ (p : VerifierProgram α), NoQueryA p → ∀ st,
    Limits.queryStepsOf p st = []
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .read k, hp, ⟨⟨S0, P0, g⟩, stream, os, R⟩ => by
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | x :: xs, none => exact queryStepsOf_nil_of_nq (k x) (hp x) _
  | .sample k, hp, _ => queryStepsOf_nil_of_nq (k _) (hp _) _
  | .grind b k, hp, ⟨⟨S0, P0, g⟩, stream, os, R⟩ => by
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | n :: xs, none =>
      simp only [Limits.queryStepsOf]
      generalize absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n = N
      obtain ⟨pw, sp'⟩ := N
      change (if powOk b pw = true then _ else []) = []
      split
      · exact queryStepsOf_nil_of_nq k hp _
      · rfl
  | .commit _ _ k, hp, ⟨⟨S0, P0, g⟩, stream, os, R⟩ => by
    match stream, g with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, some _ => rfl
    | x0 :: x1 :: xs, none => exact queryStepsOf_nil_of_nq k hp _
  | .query _ _ _, hp, _ => hp.elim

theorem noQuery_commitStack (μ r : ℕ) : NoQuery (commitStack μ r) := by
  rw [noQuery_iff]
  unfold commitStack
  cases Whir.ladder μ r with
  | none => trivial
  | some cfg =>
    cases cfg with
    | nil => trivial
    | cons level _ => trivial

theorem noQuery_flatPre (c : BytecodeClaim) (bytecode : List K) (pi : Digest) : NoQuery (flatPre c bytecode pi) := by
  unfold flatPre
  refine NoQuery.bind (noQuery_of_nc (noCommit_readSizes bytecode)) fun ls ↦ ?_
  refine NoQuery.bind (noQuery_commitStack ls.1.stackLog ls.2) fun _ ↦ ?_
  refine NoQuery.bind (noQuery_of_nc (noCommit_readOod ls.1.stackLog)) fun ood ↦ ?_
  refine NoQuery.bind (noQuery_of_nc (noCommit_require (busDepth ls.1 < 64))) fun _ ↦ ?_
  refine NoQuery.bind (noQuery_of_nc (noCommit_busChallenges (busDepth ls.1))) fun wb ↦ ?_
  refine NoQuery.bind (noQuery_of_nc (noCommit_gkrPhase (busDepth ls.1))) fun rg ↦ ?_
  refine NoQuery.bind (noQuery_of_nc (noCommit_tablesSeg c ls.1 pi wb.1 wb.2 rg.2.1
    rg.2.2)) fun bc ↦ ?_
  refine NoQuery.bind (noQuery_of_nc (noCommit_keccakPhaseClaims ls.1 bc.2)) fun kc ↦ ?_
  refine NoQuery.bind (noQuery_of_nc (noCommit_ringSwitch kc.2.1 kc.2.2)) fun rs ↦ ?_
  exact (noQuery_iff _).2 trivial

theorem queryStepsOf_require (c : Prop) [Decidable c] (st : VerifierProgramState) :
    Limits.queryStepsOf (VerifierProgram.require c) st = [] := by
  unfold VerifierProgram.require
  split <;> rfl

/-! ## The child's steps are its opening's -/

/-- **The child's query steps are its segments' stacked opening's.** -/
def SegSteps {bytecode : List K} {seed : Digest} {c : Node.Child} (S : ChildSegs bytecode seed c) : Prop :=
  Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode (Node.statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) =
    Limits.queryStepsOf (Whir.whirOpen S.layout.stackLog S.rate
      (batchTarget (stackClaims S.layout S.kc.1 S.rs.1 S.rs.2 S.ood) S.s7.squeeze.1))
      ⟨⟨S.s7.perm, [], none⟩, S.xsW, c.proof.openings, [(S.root, Whir.stackShape S.layout.stackLog S.rate)]⟩

/-- **An honest child's run, in segments, its query steps its stacked opening's** (`child_segments`). -/
theorem child_segments_steps {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (seed : Digest)
    (c : Node.Child)
    (hmu : ∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (Node.statementDigest seed c.statement)
      c.freshClaim c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf
      (deferringVerifierProgram c.freshClaim bytecode (Node.statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c), Limits.OpeningsAgree b.1 b.2) :
    ∃ S : ChildSegs bytecode seed c, SegSteps S := by
  obtain ⟨q, stq, t, hpre, hop, ht1, ht2⟩ := accept_rz hrz
  have hpre0 := hpre
  unfold flatPre at hpre
  obtain ⟨ls, st1, hA, h⟩ := runId_bind_some hpre
  obtain ⟨L, r⟩ := ls
  obtain ⟨logMem, rowsN, hsA, hL, hlm1, h30, hrowsL, hrows30, hr1, hr4, -, hst30⟩ :=
    readSizes_inv hbl hA
  obtain ⟨xs1, hxs1, hO1, hR1, hg1, runS⟩ :=
    seg_runsTo (noCommit_readSizes _) (endsClear_readSizes _) rfl hA
  have exs1 : xs1 = sizeWords logMem rowsN r := by
    have := hsA.symm.trans hxs1
    exact (List.append_cancel_right this).symm
  subst exs1
  have hann : Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (L, r) :=
    announced_eq (sp := ⟨keccakF1600 (seedInput seed (Node.statementDigest seed c.statement)), [],
      none⟩) rfl hA
  have hmu20 : 20 ≤ L.stackLog := hmu L r hann
  obtain ⟨u, st2, hB, h⟩ := runId_bind_some h
  obtain ⟨x0, x1, hsB, -, hspB, hrB, hoB⟩ := commitStack_runId hB
  have hg2 : st2.sponge.ground = none := by
    rw [hspB, absorb_ground, absorb_ground]; exact hg1
  have hc2 : ((Tables.fsOfT st1.sponge).absorb x0 dsObserve).absorb x1 dsObserve =
      Tables.fsOfT st2.sponge := by
    have := carries_absorb (carries_absorb (carries_fsOfT hg1) x0 dsObserve) x1 dsObserve
    rw [← hspB] at this
    exact fs_eq_of_carries this
  obtain ⟨ood, st3, hC, h⟩ := runId_bind_some h
  obtain ⟨xsO, hxsO, hO3, hR3, hg3, runO⟩ :=
    seg_runsTo (noCommit_readOod _) (endsAny_readOod _).clear hg2 hC
  obtain ⟨hdepth, h⟩ := runId_require_bind h
  obtain ⟨wb, st4, hD, h⟩ := runId_bind_some h
  obtain ⟨xsB, hxsB, hO4, hR4, hg4, runB⟩ :=
    seg_runsTo (noCommit_busChallenges _) (endsAny_busChallenges _).clear hg3 hD
  obtain ⟨rG, st5, hE, h⟩ := runId_bind_some h
  obtain ⟨xsG, hxsG, hO5, hR5, hg5, runG⟩ :=
    seg_runsTo (noCommit_gkrPhase _) (endsClear_gkrPhase _) hg4 hE
  obtain ⟨bc, st6, hF, h⟩ := runId_bind_some h
  obtain ⟨bus, claims⟩ := bc
  obtain ⟨xsT, hxsT, hO6, hR6, hg6, runT⟩ :=
    seg_runsTo (noCommit_tablesSeg _ _ _ _ _ _ _) (endsAny_tablesSeg _ _ _ _ _ _ _).clear hg5 hF
  obtain ⟨kc, st7, hG, h⟩ := runId_bind_some h
  obtain ⟨xsK, hxsK, hO7, hR7, hg7, runK⟩ :=
    seg_runsTo (noCommit_keccakPhaseClaims _ _) (endsAny_keccakPhaseClaims _ _).clear hg6 hG
  obtain ⟨rs, st8, hH, h⟩ := runId_bind_some h
  obtain ⟨xsR, hxsR, hO8, hR8, hg8, runR⟩ :=
    seg_runsTo (noCommit_ringSwitch _ _) (endsAny_ringSwitch _ _).clear hg7 hH
  obtain ⟨hq, hst⟩ := runId_ret_inv h
  subst q
  subst stq
  simp only at hop
  obtain ⟨hcl, w, hW, hWz, hacc⟩ := opening_rz hop
  set s7 := Tables.fsOfT st8.sponge with hs7
  have hc8 : s7.Carries st8.sponge := carries_fsOfT hg8
  obtain ⟨hlam, -⟩ := carries_squeeze hc8
  have hsq : Id.run (squeeze keccakF1600 st8.sponge) = (s7.squeeze.1, ⟨s7.perm, [], none⟩) := by
    rw [Keccak.squeeze_id st8.sponge hg8, perm_eq hc8]
    rfl
  rw [hsq] at hW hWz hacc
  have hcS : (⟨capOf s7.perm, []⟩ : Fs).Carries ⟨s7.perm, [], none⟩ := ⟨rfl, rfl, rfl⟩
  have hO : st8.openings = c.proof.openings := by
    rw [hO8, hO7, hO6, hO5, hO4, hO3, hoB, hO1]; rfl
  have hR : st8.roots = [(digestFromHalves (x0, x1), Whir.stackShape L.stackLog r)] := by
    rw [hR8, hR7, hR6, hR5, hR4, hR3, hrB, hR1]; rfl
  obtain ⟨sp8, stream8, os8, roots8⟩ := st8
  simp only at hO hR hW hWz hxsR
  subst hO hR
  have runW := runsWith_of_runId hcS hW ht1 ht2 (endsAny_whirOpen _ _ _ _ _ _ hW)
  have nzW := runsWith_of_runId hcS hWz ht1 ht2
    (endsAny_rz (endsAny_whirOpen _ _ _) _ _ _ hWz)
  -- the steps
  have hsteps : Limits.queryStepsOf
      (deferringVerifierProgram c.freshClaim bytecode (Node.statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) =
      Limits.queryStepsOf (Whir.whirOpen L.stackLog r
        (batchTarget (stackClaims L kc.1 rs.1 rs.2 ood) s7.squeeze.1))
        ⟨⟨s7.perm, [], none⟩, stream8, c.proof.openings, [(digestFromHalves (x0, x1),
          Whir.stackShape L.stackLog r)]⟩ := by
    have e0 : Coverage.childVerifierStart seed c =
        deferStart seed (Node.statementDigest seed c.statement) c.proof := rfl
    have hvs := runId_of_rz _ _ _ hop
    rw [e0, deferred_pre, queryStepsOf_bind _ _ _ _ _ hpre0,
      queryStepsOf_nil_of_nq _ ((noQuery_iff _).1 (noQuery_flatPre _ _ _)), List.nil_append]
    rw [queryStepsOf_bind _ _ _ _ _ hvs, queryStepsOf_nil_of_nq (VerifierProgram.ret true) trivial,
      List.append_nil]
    have hreq : runId (VerifierProgram.require (StackedOk (stackClaims L kc.1 rs.1 rs.2 ood)))
        ⟨sp8, stream8, c.proof.openings, [(digestFromHalves (x0, x1),
          Whir.stackShape L.stackLog r)]⟩ =
        some ((), ⟨sp8, stream8, c.proof.openings, [(digestFromHalves (x0, x1),
          Whir.stackShape L.stackLog r)]⟩) := by
      unfold VerifierProgram.require
      simp only [stackedOk_of hcl, ↓reduceIte]
      rfl
    rw [verifyStackedOpening_split, queryStepsOf_bind _ _ _ _ _ hreq, queryStepsOf_require, List.nil_append]
    change Limits.queryStepsOf ((Whir.whirOpen L.stackLog r (batchTarget
      (stackClaims L kc.1 rs.1 rs.2 ood) (Id.run (squeeze keccakF1600 sp8)).1)).bind _)
      ⟨(Id.run (squeeze keccakF1600 sp8)).2, stream8, c.proof.openings, _⟩ = _
    rw [hsq, queryStepsOf_bind _ _ _ _ _ hW, queryStepsOf_require, List.append_nil]
  have capsW : Whir.CapsAgree L.stackLog r
      (batchTarget (stackClaims L kc.1 rs.1 rs.2 ood) s7.squeeze.1) s7.perm stream8
      c.proof.openings (digestFromHalves (x0, x1)) := by
    intro b hb
    apply hcaps
    rw [hsteps]
    exact hb
  refine ⟨⟨logMem, rowsN, r, L, hL, hlm1, h30, hrowsL, hrows30, hr1, hr4, hmu20, hst30,
    Tables.fsOfT st1.sponge, runS, x0, x1, _, rfl, xsO, ood, Tables.fsOfT st3.sponge,
    hc2 ▸ runO, hdepth, xsB, wb, _, runB, xsG, rG, _, runG, xsT, bus, claims, _, runT, xsK, kc, _,
    runK, xsR, rs, s7, runR, hcl, stream8, w, _, _, runW, ⟨w, _, _, nzW⟩,
    capsW, hacc, ?_, hann⟩, hsteps⟩
  have h0 : c.proof.stream = (deferStart seed (Node.statementDigest seed c.statement)
    c.proof).stream := rfl
  rw [h0, hxs1, hsB, hxsO, hxsB, hxsG, hxsT, hxsK, hxsR]
  simp only [List.append_assoc, List.cons_append, List.nil_append, sizeWords]

/-- A child the deferring verifier accepts, refusing zero challenges, has an accepting run. -/
theorem deferring_run {bytecode : List K} {seed : Digest} {c : Node.Child}
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (Node.statementDigest seed c.statement)
      c.freshClaim c.proof = true) :
    ∃ st', runId (deferringVerifierProgram c.freshClaim bytecode (Node.statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) = some (true, st') := by
  obtain ⟨q, stq, t, hpre, hop, -, -⟩ := accept_rz hrz
  have hvs := runId_of_rz _ _ _ hop
  refine ⟨t, ?_⟩
  have e0 : Coverage.childVerifierStart seed c =
      deferStart seed (Node.statementDigest seed c.statement) c.proof := rfl
  rw [e0, deferred_pre, run_bind, hpre]
  show runId ((verifyStackedOpening q.1.stackLog q.2.1 q.2.2).bind fun _ ↦ VerifierProgram.ret true) stq = _
  rw [run_bind, hvs]
  rfl

/-- **The child's Merkle hints are its levels' `level_queries` entries**, stream by stream, level 0 first, on an
honest run of its segments' stacked opening whose steps are its levels'. -/
theorem child_merkle_sameStreams {bytecode : List K} {seed : Digest} {c : Node.Child}
    (S : ChildSegs bytecode seed c) (hS : SegSteps S)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (Node.statementDigest seed c.statement)
      c.freshClaim c.proof = true)
    {target : E} {w : Whir.WhirEnd} {cfg : List Whir.Level} {Ls : List Whir.LvAt}
    (hR : Whir.HonRun S.layout.stackLog S.rate target S.s7.perm S.root S.xsW c.proof.openings w cfg Ls)
    (ht : target = batchTarget (stackClaims S.layout S.kc.1 S.rs.1 S.rs.2 S.ood) S.s7.squeeze.1)
    (hst : Limits.queryStepsOf (Whir.whirOpen S.layout.stackLog S.rate target)
      ⟨⟨S.s7.perm, [], none⟩, S.xsW, c.proof.openings, [(S.root, Whir.stackShape S.layout.stackLog S.rate)]⟩ =
        Whir.lvSteps S.layout.stackLog 0 Ls) :
    SameStreams ((List.range (Whir.osCfgR (S.layout.stackLog - Whir.minOpenLog) (S.rate - 1)).levels.length).flatMap
        (Whir.lvPops Ls S.layout.stackLog S.rate))
      (Hints.merkleHints true (Hints.childQueries bytecode seed c) c.proof.openings) := by
  obtain ⟨st', hrun⟩ := deferring_run hrz
  subst ht
  rw [Whir.childMerkleHints_eq hrun, hS, hst]
  exact hR.steps_sameStreams

end
end LeanVM.Guest.B1.VerifySub
