/-
  LeanVM.Guest.B1.VsC.VsNatTail

  An accepted child's run past the link, natively: the public input's draw, the Keccak reduction as a forward
  run, the ring switch's grind.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatLink
public import LeanVM.Guest.B1.KeccakGkr.VkSpec

/-!
# The run past the link

`Plain p`: no packed step, no commitment, no query. A plain program's carried run reads neither the roots nor
the openings (`runTc_plain`), so one accepting deployed run is a run from any roots and openings
(**`runsG_of_runId`**), the roots the stack's commitment left included (`runT_noRoots` takes none).
`verifyKeccak` is plain past its shape check (`plain_verifyKeccak`).

**`natTail`**: on an accepted child, past `natChildLink`'s link: `bindPublicInput` draws once from the link's
end sponge `LinkNat.F4` (`pkAbsorb 18 msg endC.cap`), then the Keccak reduction runs forward (`RunsTo`) from
`F4.squeeze.2` on the table's point and lanes (`kLanes`), and the ring switch's grind passes on the next word.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Complete
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none NoPacked RunsG)
open LeanVM.Guest.B1.VerifySub (runId_bind_some)

@[expose] public section

variable {α β : Type}

/-! ## Plain programs -/

/-- **No packed step, no commitment, no query.** -/
inductive Plain : {α : Type} → VerifierProgram α → Prop
  | ret {α : Type} (a : α) : Plain (.ret a)
  | fail {α : Type} : Plain (.fail : VerifierProgram α)
  | read {α : Type} {k : E → VerifierProgram α} : (∀ x, Plain (k x)) → Plain (.read k)
  | sample {α : Type} {k : E → VerifierProgram α} : (∀ x, Plain (k x)) → Plain (.sample k)
  | grind {α : Type} {b : ℕ} {k : VerifierProgram α} : Plain k → Plain (.grind b k)

theorem Plain.noPacked {p : VerifierProgram α} (h : Plain p) : NoPacked p := by
  induction h with
  | ret a => trivial
  | fail => trivial
  | read _ ih => exact fun x => ih x
  | sample _ ih => exact fun x => ih x
  | grind _ ih => exact ih

theorem plain_bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : Plain p) (hf : ∀ a, Plain (f a)) :
    Plain (p >>= f) := by
  induction hp with
  | ret a => exact hf a
  | fail => exact .fail
  | read _ ih => exact .read fun x ↦ ih x
  | sample _ ih => exact .sample fun x ↦ ih x
  | grind _ ih => exact .grind ih

theorem plain_pure (a : α) : Plain (pure a : VerifierProgram α) := .ret a

theorem plain_require (c : Prop) [Decidable c] : Plain (VerifierProgram.require c) := by
  unfold VerifierProgram.require; split
  · exact .ret _
  · exact .fail

theorem plain_readScalar : Plain VerifierProgram.readScalar := .read fun _ ↦ .ret _

theorem plain_sampleChallenge : Plain VerifierProgram.sampleChallenge := .sample fun _ ↦ .ret _

theorem plain_readScalars : ∀ n, Plain (VerifierProgram.readScalars n)
  | 0 => .ret _
  | n + 1 => plain_bind plain_readScalar fun _ ↦ plain_bind (plain_readScalars n) fun _ ↦ .ret _

theorem plain_sampleChallenges : ∀ n, Plain (VerifierProgram.sampleChallenges n)
  | 0 => .ret _
  | n + 1 => plain_bind plain_sampleChallenge fun _ ↦ plain_bind (plain_sampleChallenges n) fun _ ↦ .ret _

theorem plain_grind (b : ℕ) : Plain (VerifierProgram.grindProofOfWork b) := by
  unfold VerifierProgram.grindProofOfWork; split
  · exact .ret _
  · exact .grind (.ret _)

theorem plain_liftOption (o : Option α) : Plain (liftOption o) := by
  cases o
  · exact .fail
  · exact .ret _

/-- A program built of plain pieces is plain. -/
macro "plain_tac" : tactic => `(tactic| repeat' (first
  | exact plain_pure _ | exact plain_require _ | exact plain_readScalar | exact plain_sampleChallenge
  | exact plain_readScalars _ | exact plain_sampleChallenges _ | exact plain_grind _
  | refine plain_bind ?_ ?_ | intro _ | split))

theorem plain_sumcheckRoundPoly (count : ℕ) (claim : E) (e : Option E) : Plain (sumcheckRoundPoly count claim e) := by
  cases e <;> unfold sumcheckRoundPoly <;> plain_tac

theorem plain_sumcheck (claim : E) (count : ℕ) (eqs : List (Option E)) : Plain (sumcheck claim count eqs) := by
  induction eqs generalizing claim with
  | nil => exact .ret _
  | cons e es ih =>
    unfold sumcheck
    refine plain_bind (plain_sumcheckRoundPoly _ _ _) fun _ ↦ ?_
    refine plain_bind plain_sampleChallenge fun _ ↦ ?_
    refine plain_bind (ih _) fun _ ↦ ?_
    split
    exact .ret _

/-- `plain_tac` with the sumcheck. -/
macro "plain_tac1" : tactic => `(tactic| repeat' (first
  | exact plain_sumcheck _ _ _ | exact plain_pure _ | exact plain_require _ | exact plain_readScalar
  | exact plain_sampleChallenge | exact plain_readScalars _ | exact plain_sampleChallenges _
  | exact plain_grind _ | refine plain_bind ?_ ?_ | intro _ | split))

theorem plain_layer (logSteps step : ℕ) (claim : KeccakClaim) : Plain (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  plain_tac1

theorem plain_layers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    Plain (keccakLayers logSteps steps claim)
  | [], _ => .ret _
  | step :: steps, claim => plain_bind (plain_layer logSteps step claim) fun c ↦ plain_layers logSteps steps c

theorem plain_open (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    Plain (keccakOpen logSteps claim first count value) := by
  unfold keccakOpen
  plain_tac1

/-- **`verifyKeccak` is plain**, past its shape check. -/
theorem plain_verifyKeccak {τ : ℕ} {inst outs : List E}
    (hs : inst.length = τ ∧ outs.length = keccakStateLanes ∧ 4 ≤ τ) : Plain (verifyKeccak τ inst outs) := by
  rw [VerifySub.verifyKeccak_body τ inst outs hs]
  refine plain_bind (plain_sampleChallenges _) fun _ ↦ ?_
  refine plain_bind (plain_sampleChallenges _) fun _ ↦ ?_
  refine plain_bind plain_readScalar fun _ ↦ ?_
  refine plain_bind (plain_layers _ _ _) fun _ ↦ ?_
  refine plain_bind (plain_open _ _ _ _ _) fun _ ↦ ?_
  refine plain_bind plain_readScalar fun _ ↦ ?_
  refine plain_bind (plain_require _) fun _ ↦ ?_
  refine plain_bind (plain_sumcheck _ _ _) fun _ ↦ ?_
  refine plain_bind (plain_open _ _ _ _ _) fun _ ↦ ?_
  refine plain_bind (plain_readScalars _) fun _ ↦ ?_
  refine plain_bind (plain_require _) fun _ ↦ ?_
  exact plain_pure _

/-! ## A plain run is a run on any roots and openings -/

/-- **A plain carried run keeps the openings and the roots, and runs on any.** -/
theorem runTc_plain {p : VerifierProgram α} (hp : Plain p) : ∀ (st : TSt) (a : α) (st' : TSt),
    runTc p st = some (a, st') → st'.openings = st.openings ∧ st'.roots = st.roots ∧
      ∀ os R, runTc p ⟨st.sponge, st.ground, st.stream, os, R⟩ =
        some (a, ⟨st'.sponge, st'.ground, st'.stream, os, R⟩) := by
  induction hp with
  | ret b =>
    intro st a st' h
    have e := runTc_ret_inv h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨rfl, rfl, fun os R => rfl⟩
  | fail => intro st a st' h; exact absurd h (by simp [runTc])
  | @read k _ ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os0, R0⟩ := st
    match stream, g, h with
    | [], _, h => exact absurd h (by simp [runTc])
    | _ :: _, some _, h => exact absurd h (by simp [runTc])
    | x :: xs, none, h =>
      obtain ⟨h1, h2, hf⟩ := ih x ⟨s.absorb x dsObserve, none, xs, os0, R0⟩ a st' h
      exact ⟨h1, h2, fun os R => hf os R⟩
  | @sample k _ ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os0, R0⟩ := st
    cases g with
    | none =>
      obtain ⟨h1, h2, hf⟩ := ih _ ⟨s.squeeze.2, none, stream, os0, R0⟩ a st' h
      exact ⟨h1, h2, fun os R => hf os R⟩
    | some c =>
      obtain ⟨h1, h2, hf⟩ := ih c ⟨s, none, stream, os0, R0⟩ a st' h
      exact ⟨h1, h2, fun os R => hf os R⟩
  | @grind b k _ ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os0, R0⟩ := st
    match stream, g, h with
    | [], _, h => exact absurd h (by simp [runTc])
    | _ :: _, some _, h => exact absurd h (by simp [runTc])
    | n :: xs, none, h =>
      simp only [runTc] at h
      split at h
      · rename_i hpw
        obtain ⟨h1, h2, hf⟩ := ih ⟨Fs.mk (capOf (s.nonceState n)) [], some (challengeOf (s.nonceState n)), xs,
          os0, R0⟩ a st' h
        refine ⟨h1, h2, fun os R => ?_⟩
        show (if powOk b (Keccak.lane (s.nonceState n) 2) = true then
          runTc k ⟨Fs.mk (capOf (s.nonceState n)) [], some (challengeOf (s.nonceState n)), xs, os, R⟩
          else none) = _
        simp only [hpw, ↓reduceIte]
        exact hf os R
      · simp at h

/-- **One accepting deployed run of a plain program is a run on any rest, openings and roots.** -/
theorem runsG_of_runId {p : VerifierProgram α} (hp : Plain p) {F : Fs} {g : Option E} {sp : Sponge}
    (hs : TCar F g sp) {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {a : α}
    {t : VerifierProgramState} (h : runId p ⟨sp, xs, os, R⟩ = some (a, t)) :
    ∃ ys, xs = ys ++ t.stream ∧ t.openings = os ∧ t.roots = R ∧
      RunsG p F g ys a (fsOfT t.sponge) t.sponge.ground := by
  have hT := runTc_of_runId hp.noPacked hs h
  obtain ⟨h1, h2, -⟩ := runTc_plain hp _ a _ hT
  simp only at h1 h2
  rw [runTc_eq_runT] at hT
  obtain ⟨pre, opre, hs1, ho1, hf⟩ := Tables.runT_frame p _ a _ hT
  simp only at hs1 ho1
  have hop : opre = [] := by
    rw [h1] at ho1
    have hl := congrArg List.length ho1
    simp only [List.length_append] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  refine ⟨pre, hs1, h1, h2, fun sp0 hs0 rest os' R' => ?_⟩
  have e := hf rest os'
  rw [hop, List.nil_append, ← runTc_eq_runT] at e
  obtain ⟨-, -, e2⟩ := runTc_plain hp _ a _ e
  have e3 := e2 os' R'
  rw [runTc_eq_runT] at e3
  obtain ⟨sp1, c1, c2⟩ := runId_of_runT p _ sp0 (by exact hs0) a _ e3
  exact ⟨sp1, c1, c2⟩

/-! ## The front, at given runs -/

/-- **`natFront`'s carried sponge at given runs** of the sizes, the root and the out-of-domain sample. -/
theorem natFront_at {bytecode : List K} {seed : Digest} {c : Child} {layout : Layout} {r : ℕ} {ood : StackClaim}
    {st1 st2 st3 : VerifierProgramState}
    (hS : runId (readAnnouncedSizes bytecode) (Coverage.childVerifierStart seed c) = some ((layout, r), st1))
    (hC : runId (commitStack layout.stackLog r) st1 = some ((), st2))
    (hO : runId (readOod layout.stackLog) st2 = some (ood, st3)) (hμ : 1 ≤ layout.stackLog) :
    TCar (natF3 seed c layout.stackLog) none st3.sponge ∧ st3.stream = c.proof.stream.drop 12 ∧
      st3.openings = c.proof.openings := by
  set xs := c.proof.stream with hxs
  have h0 : TCar (natF0 seed c) none (Coverage.childVerifierStart seed c).sponge := ⟨rfl, rfl, rfl⟩
  have t1 := runTc_of_runId (noPacked_readAnnouncedSizes _) h0 hS
  obtain ⟨-, e1⟩ := runTc_sizes t1
  simp only [TSt.mk.injEq] at e1
  obtain ⟨f1, g1, s1, o1, -⟩ := e1
  have c1 : TCar (natF1 seed c) none st1.sponge := tcar_of_eq f1 g1
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
  have t3 := runTc_of_runId (noPacked_readOod _) c2 (show runId _ ⟨st2.sponge, st2.stream, st2.openings,
    st2.roots⟩ = _ from hO)
  rw [s2, o2] at t3
  obtain ⟨n, v, xs3, hx3, -, -, -, e3⟩ := runTc_readOod hμ t3
  simp only [TSt.mk.injEq] at e3
  obtain ⟨f3, g3, s3, o3, -⟩ := e3
  have hd10 : xs.drop 10 = n :: v :: xs3 := (drop_of_drop hx 2).trans hx3
  have hx10 : xs.getD 10 0 = n := getD_of_drop hd10 0
  have hx11 : xs.getD 11 0 = v := getD_of_drop hd10 1
  have hd12 : xs.drop 12 = xs3 := drop_of_drop hd10 2
  refine ⟨?_, ?_, o3⟩
  · refine tcar_of_eq ?_ g3
    rw [f3, natF3, natOodS, hx10, hx11]
  · rw [s3, hd12]

/-! ## Past the link -/

/-- The sponge the link leaves (`natLink_inv`'s end). -/
noncomputable def LinkNat.F4 (L : LinkNat) (layout : Layout) (F : Fs) : Fs :=
  ⟨Link.pkAbsorb 18 L.msg (L.endC layout F).cap, []⟩

/-- The `KECCAK` table's output lanes among the link's values (`keccakValidity`). -/
def kLanes (link : LinkEnd) : Option (List E) :=
  (List.range keccakStateLanes).mapM fun lane ↦
    ((link.columns.getD opKeccak ([], [])).2.find? fun value ↦ value.1 = keccakOut + lane).map (·.2)

theorem keccakValidity_eq (layout : Layout) (link : LinkEnd) :
    keccakValidity layout link = (liftOption (kLanes link)).bind
      (verifyKeccak (layout.tableLogHeights.getD opKeccak 0) (link.columns.getD opKeccak ([], [])).1) := by
  unfold keccakValidity kLanes
  split
  rename_i point values heq
  rw [heq]
  rfl

theorem noPacked_bindPublicInput (layout : Layout) (d : Digest) : NoPacked (bindPublicInput layout d) := by
  apply Plain.noPacked
  unfold bindPublicInput
  exact plain_bind plain_sampleChallenge fun _ => plain_bind (plain_liftOption _) fun _ => plain_pure _

/-- **`bindPublicInput`, backwards**: one draw, nothing read. -/
theorem runTc_bindPublicInput {layout : Layout} {d : Digest} {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : List ColumnClaim} {st : TSt}
    (h : runTc (bindPublicInput layout d) ⟨F, none, xs, os, R⟩ = some (a, st)) :
    st = ⟨F.squeeze.2, none, xs, os, R⟩ := by
  unfold bindPublicInput at h
  have h1 := runTc_sample_none h rfl
  obtain ⟨m, -, h2⟩ := runTc_liftOption' h1
  have e := runTc_ret_inv h2
  simp only [Prod.mk.injEq] at e
  exact e.2

/-- **An accepted child past the link**: the public input's draw, the Keccak reduction as a forward run from
the link's end sponge squeezed once, on the table's point and lanes, and the ring switch's grind on the next
word. -/
theorem natTail {seed : Digest} {c : Child} (hc : VsChildOk guestBytecode seed c) :
    ∃ (layout : Layout) (r : ℕ), announcedLayoutAndRate guestBytecode c.proof.stream = some (layout, r) ∧
      VsShape guestBytecode layout r ∧
      ∃ (link : LinkEnd) (L : LinkNat) (rest : List E), c.proof.stream.drop 12 = L.words layout ++ rest ∧
        L.Ok layout (natF3 seed c layout.stackLog) c.freshClaim link ∧
      ∃ lanes, kLanes link = some lanes ∧
      ∃ (xs : List E) (n : E) (rest' : List E), rest = xs ++ n :: rest' ∧
      ∃ (outs : List ColumnClaim) (kp ks : List E) (s' : Fs),
        RunsTo (verifyKeccak (layout.tableLogHeights.getD opKeccak 0) (link.columns.getD opKeccak ([], [])).1
          lanes) (L.F4 layout (natF3 seed c layout.stackLog)).squeeze.2 xs (outs, kp, ks) s' ∧
        powOk Whir.batchGrindingBits (Keccak.lane (s'.nonceState n) 2) = true := by
  obtain ⟨layout, r, ood, link, st1, st2, st3, st4, hann, hS, hC, hO, hL, pub, st5, hP, outs, kp, ks, st6, hK,
    qp, -, ring, batching, st7, hG, -⟩ := natRun_all hc
  obtain ⟨layout', r', hann', S⟩ := vsShape_of_verifyDeferred hc.1
  rw [hann] at hann'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hann')
  have hμ : 1 ≤ layout.stackLog := le_trans (by decide) S.stack_ge
  obtain ⟨c3, s3, o3⟩ := natFront_at hS hC hO hμ
  obtain ⟨sp3, xs3, os3, R3⟩ := st3
  simp only at c3 s3 o3
  obtain ⟨L, rest, hx, hok, sp4, c4, rfl⟩ := natLink_inv (announced_tables hann) c3 hL
  -- the public input's draw
  have t5 := runTc_bindPublicInput (runTc_of_runId (noPacked_bindPublicInput _ _) (tcar_none.mpr c4) hP)
  obtain ⟨c5, hst5⟩ := natEnd t5
  rw [hst5] at hK
  -- the Keccak reduction
  rw [keccakValidity_eq] at hK
  obtain ⟨lanes, hln, hK⟩ := natLiftOption hK
  have hsh : ((link.columns.getD opKeccak ([], [])).1.length = layout.tableLogHeights.getD opKeccak 0 ∧
      lanes.length = keccakStateLanes ∧ 4 ≤ layout.tableLogHeights.getD opKeccak 0) := by
    have hK' := hK
    unfold verifyKeccak at hK'
    exact (natRequire hK').1
  obtain ⟨ys, hys, -, -, hRG⟩ := runsG_of_runId (plain_verifyKeccak hsh) c5 hK
  -- the ring switch's grind
  obtain ⟨sp6, xs6, os6, R6⟩ := st6
  simp only at hys
  unfold ringSwitch at hG
  have hb : Whir.batchGrindingBits ≠ 0 := by decide
  obtain ⟨u, st1', t6, -⟩ := natBind_np (Tables.noPacked_grindProofOfWork _) (tcar_of_eq rfl rfl) hG
  unfold VerifierProgram.grindProofOfWork at t6
  simp only [hb, ↓reduceIte] at t6
  obtain ⟨n, rest', hx6, hg6, hpw, -⟩ := runTc_grind t6
  simp only at hx6 hg6 hpw
  rw [hg6] at hRG
  refine ⟨layout, r, hann, S, link, L, rest, by rw [← s3]; exact hx, hok, lanes, hln, ys, n, rest', ?_,
    outs, kp, ks, _, Tables.RunsG.toRunsTo hRG, hpw⟩
  rw [hys, hx6]

end
end LeanVM.Guest.B1.VsC
