module

public import NativeVm.Code.Refine
public import NativeVm.Code.ErrFrame
public import NativeVm.Equiv.Transcript

/-!
# The transcript gadgets against the model

Each gadget's spec against the statement's step (`NativeVm.Transcript`), its failure frame
(`NativeVm.Code.ErrFrame`) and the model's simulation of the step (`NativeVm.Equiv`, `Sim.*`) give
its spec against the model's operation, from `CodeRel` to `CodeRel` (`lift`):

| gadget | model | spec | as `Refines` |
|---|---|---|---|
| `readScalar` | `Model.readScalar` | `readScalarM_spec` | `readScalar_refines` |
| `sampleChallenge` | `Model.sampleChallenge` | `sampleChallengeM_spec` | `sampleChallenge_refines` |
| `grind` | `Model.grind bits`, `bits ≠ 0` | `grindM_spec` | `grind_refines` |
| `commit` | `Model.readCommitment height width` | `readCommitmentM_spec` | `readCommitment_refines` |
| `query` | `Model.queryOpenings i positions` | `queryOpeningsM_spec`, from a spec of `query` | |
| `finish` | `Model.verify`'s last check | `finishM_spec` | |

A grind of `0` bits is no code (`grind_zero_run`). The model's operations read the stream and the
openings and never change them (`*_input`), which `CodeRel` needs. In the `Refines` forms, `R` is
what the phase keeps through the gadget: anything `Keeps clobbers (Foot env)` preserves, the failure
exit's invariant among it.
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript NativeVm.Equiv LeanVM.Parameters LeanVM.Semantics
open LeanVM.Protocol LeanVM.Protocol.Compile

variable {env : Env} {t t' : TState} {s : QState}

/-! ## The model keeps the input -/

/-- `t'` has `t`'s stream and openings. -/
def SameInput (t t' : TState) : Prop := t'.stream = t.stream ∧ t'.openings = t.openings

theorem nextScalar_input {x : EW} (h : Model.nextScalar.run t = some (x, t')) : SameInput t t' := by
  rw [nextScalar_run] at h
  split at h
  · cases h
  · cases hx : t.stream[t.cursor]? with
    | none => rw [hx] at h; cases h
    | some y =>
      rw [hx] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨rfl, rfl⟩

theorem readScalar_input {x : EW} (h : Model.readScalar.run t = some (x, t')) : SameInput t t' := by
  rw [readScalar_run] at h
  cases hn : Model.nextScalar.run t with
  | none => rw [hn] at h; cases h
  | some p =>
    obtain ⟨y, t₁⟩ := p
    rw [hn] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨e1, e2⟩ := nextScalar_input hn
    exact ⟨e1, e2⟩

theorem sampleChallenge_input {x : EW} (h : Model.sampleChallenge.run t = some (x, t')) :
    SameInput t t' := by
  rw [sampleChallenge_run] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨rfl, rfl⟩

theorem grind_input {bits : Nat} (hb : bits ≠ 0) (h : (Model.grind bits).run t = some ((), t')) :
    SameInput t t' := by
  rw [grind_run hb] at h
  cases hn : Model.nextScalar.run t with
  | none => rw [hn] at h; cases h
  | some p =>
    obtain ⟨y, t₁⟩ := p
    rw [hn, Option.bind_some] at h
    split at h
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨e1, e2⟩ := nextScalar_input hn
      exact ⟨e1, e2⟩
    · cases h

theorem readCommitment_input {height width : Nat}
    (h : (Model.readCommitment height width).run t = some ((), t')) : SameInput t t' := by
  rw [readCommitment_run] at h
  cases h₁ : Model.readScalar.run t with
  | none => rw [h₁] at h; cases h
  | some p =>
    obtain ⟨y, t₁⟩ := p
    rw [h₁, Option.bind_some] at h
    cases h₂ : Model.readScalar.run t₁ with
    | none => rw [h₂] at h; cases h
    | some q =>
      obtain ⟨z, t₂⟩ := q
      rw [h₂, Option.bind_some] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨e1, e2⟩ := readScalar_input h₁
      obtain ⟨e3, e4⟩ := readScalar_input h₂
      exact ⟨e3.trans e1, e4.trans e2⟩

theorem queryOpenings_input {i : Nat} {ps : Array UInt64} {rows : Array (Array UInt64)}
    (h : (Model.queryOpenings i ps).run t = some (rows, t')) : SameInput t t' := by
  rw [queryOpenings_run] at h
  split at h
  · cases ho : openPhase _ _ _ ps _ with
    | none => rw [ho] at h; cases h
    | some r =>
      rw [ho] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨rfl, rfl⟩
  · cases h

/-! ## From the statement's step to the model's operation -/

/-- **The lift**: a gadget simulating the statement's step `step` (from every `SimState`), whose
program `p` the model's `m` simulates, refines `m` from `CodeRel` to `CodeRel`. -/
theorem lift {α β : Type} {c : Stmt} {m : VM α} {p : VerifierProgram β} {R : α → β → Prop}
    {step : VerifierProgramState → Option (β × VerifierProgramState)}
    {Q : β → QState → Prop} {F : QState → Prop}
    (hsim : Sim m p R) (hstep : ∀ st, runSpec p st = step st)
    (hin : ∀ x t', m.run t = some (x, t') → SameInput t t') (h : CodeRel env t s)
    (hc : ∀ st, t.Rel st → SimState env st s →
      WP c s (fun s' ↦ ∃ y st', step st = some (y, st') ∧ SimState env st' s' ∧ Q y s')
        (fun s' ↦ step st = none ∧ F s')) :
    WP c s (fun s' ↦ ∃ x t', m.run t = some (x, t') ∧ CodeRel env t' s' ∧ ∃ y, R x y ∧ Q y s')
      (fun s' ↦ m.run t = none ∧ F s') := by
  obtain ⟨st, hr, hs, hstream, hop⟩ := h
  have hrel := hsim t st hr
  rw [hstep] at hrel
  refine WP.mono (hc st hr hs) ?_ ?_
  · rintro s' ⟨y, st', he, hs', hq⟩
    rw [he] at hrel
    cases hmr : m.run t with
    | none => rw [hmr] at hrel; cases hrel
    | some r =>
      rw [hmr] at hrel
      obtain ⟨x, t'⟩ := r
      cases hrel with
      | some hxy =>
        obtain ⟨e1, e2⟩ := hin x t' hmr
        exact ⟨x, t', rfl, ⟨st', hxy.2, hs', e1 ▸ hstream, e2 ▸ hop⟩, y, hxy.1, hq⟩
  · rintro s' ⟨he, hf⟩
    rw [he] at hrel
    cases hmr : m.run t with
    | none => exact ⟨rfl, hf⟩
    | some r => rw [hmr] at hrel; cases hrel

theorem lane_limb0 (x : EW) : (x.toE.limb 0).lane = x.c0 := by rw [EW.limb0_toE]; rfl

theorem lane_limb1 (x : EW) : (x.toE.limb 1).lane = x.c1 := by rw [EW.limb1_toE]; rfl

/-! ## The gadgets -/

theorem runSpec_readScalar (st : VerifierProgramState) :
    runSpec VerifierProgram.readScalar st = readStep st := by
  show runK (.read .ret) st = _
  rw [run_read]
  rcases readStep st with _ | ⟨x, st'⟩ <;> rfl

/-- **`read`** against `Model.readScalar`: the scalar's limbs in `r9`, `r10`. -/
theorem readScalarM_spec (h : CodeRel env t s) :
    WP Transcript.readScalar s (fun s' ↦ ∃ x t', Model.readScalar.run t = some (x, t') ∧
      CodeRel env t' s' ∧ s'.reg .r9 = x.c0 ∧ s'.reg .r10 = x.c1 ∧ Keeps clobbers (Foot env) s s')
      (fun s' ↦ Model.readScalar.run t = none ∧ Keeps clobbers (Foot env) s s') := by
  refine WP.mono (lift Sim.readScalar runSpec_readScalar (fun _ _ ↦ readScalar_input) h
    fun _ _ hs ↦ (readScalar_spec hs).withErr (readScalar_err hs)) ?_ fun _ h ↦ h
  rintro s' ⟨x, t', hr, hc, y, rfl, h9, h10, hk⟩
  exact ⟨x, t', hr, hc, by rw [h9, lane_limb0], by rw [h10, lane_limb1], hk⟩

theorem runSpec_sampleChallenge (st : VerifierProgramState) :
    runSpec VerifierProgram.sampleChallenge st = some (sampleStep st) := by
  show runK (.sample .ret) st = _
  rw [run_sample]
  rfl

/-- **`sample`** against `Model.sampleChallenge`: the challenge's limbs in `r9`, `r10`; it never
fails. -/
theorem sampleChallengeM_spec (h : CodeRel env t s) :
    WP Transcript.sampleChallenge s (fun s' ↦ ∃ x t', Model.sampleChallenge.run t = some (x, t') ∧
      CodeRel env t' s' ∧ s'.reg .r9 = x.c0 ∧ s'.reg .r10 = x.c1 ∧ Keeps clobbers (Foot env) s s')
      (fun _ ↦ False) := by
  refine WP.mono (lift (F := fun _ ↦ False) (Q := fun y s' ↦ s'.reg .r9 = (y.limb 0).lane ∧
      s'.reg .r10 = (y.limb 1).lane ∧ Keeps clobbers (Foot env) s s') Sim.sampleChallenge
    runSpec_sampleChallenge (fun _ _ ↦ sampleChallenge_input) h fun st _ hs ↦
      WP.mono (sampleChallenge_spec hs) (fun s' h' ↦ ⟨_, _, rfl, h'.1, h'.2⟩)
        fun _ (h : False) ↦ h.elim) ?_ fun _ h ↦ h.2
  rintro s' ⟨x, t', hr, hc, y, rfl, h9, h10, hk⟩
  exact ⟨x, t', hr, hc, by rw [h9, lane_limb0], by rw [h10, lane_limb1], hk⟩

theorem runSpec_grind {bits : Nat} (hb : bits ≠ 0) (st : VerifierProgramState) :
    runSpec (VerifierProgram.grindProofOfWork bits) st = (grindStep bits st).map ((), ·) := by
  simp only [VerifierProgram.grindProofOfWork, hb, ↓reduceIte]
  show runK (.grind bits (.ret ())) st = _
  rw [run_grind]
  rcases grindStep bits st with _ | st' <;> rfl

/-- A grind of no bits is nothing. -/
theorem grind_zero_run (t : TState) : (Model.grind 0).run t = some ((), t) := rfl

/-- **`grind bits`**, `bits ≠ 0` in `rsi`, against `Model.grind bits`. -/
theorem grindM_spec {bits : Nat} (h : CodeRel env t s) (hb0 : bits ≠ 0) (hb : bits < 2 ^ 64)
    (hrsi : s.reg .rsi = bits.toUInt64) :
    WP Transcript.grind s (fun s' ↦ ∃ t', (Model.grind bits).run t = some ((), t') ∧
      CodeRel env t' s' ∧ Keeps clobbers (Foot env) s s')
      (fun s' ↦ (Model.grind bits).run t = none ∧ Keeps clobbers (Foot env) s s') := by
  refine WP.mono (lift (Q := fun _ s' ↦ Keeps clobbers (Foot env) s s')
    (F := Keeps clobbers (Foot env) s) (Sim.grind bits) (runSpec_grind hb0)
    (fun _ _ ↦ grind_input hb0) h
    fun st _ hs ↦ WP.mono ((grind_spec hs hb hrsi).withErr (grind_err hs hb hrsi))
      (fun _ ⟨st', he, hs', hk⟩ ↦ ⟨(), st', by rw [he]; rfl, hs', hk⟩)
      (fun _ ⟨he, hk⟩ ↦ ⟨by rw [he]; rfl, hk⟩)) ?_ fun _ h ↦ h
  rintro s' ⟨⟨⟩, t', hr, hc, -, -, hk⟩
  exact ⟨t', hr, hc, hk⟩

theorem runSpec_readCommitment (height width : Nat) (st : VerifierProgramState) :
    runSpec (VerifierProgram.readCommitment height width) st =
      (commitStep height width st).map ((), ·) := by
  show runK (.commit height width (.ret ())) st = _
  rw [run_commit]
  rcases commitStep height width st with _ | st' <;> rfl

/-- **`commit height width`**, `height` in `rsi` and `width` in `rbx`, against
`Model.readCommitment height width`, room for one more root. -/
theorem readCommitmentM_spec {height width : Nat} (h : CodeRel env t s)
    (hroom : t.roots.size < maxRoots) (hh : height < 2 ^ 64) (hw : width < 2 ^ 64)
    (hrsi : s.reg .rsi = height.toUInt64) (hrbx : s.reg .rbx = width.toUInt64) :
    WP Transcript.commit s (fun s' ↦ ∃ t', (Model.readCommitment height width).run t = some ((), t') ∧
      CodeRel env t' s' ∧ Keeps clobbers (Foot env) s s')
      (fun s' ↦ (Model.readCommitment height width).run t = none ∧
        Keeps clobbers (Foot env) s s') := by
  refine WP.mono (lift (Q := fun _ s' ↦ Keeps clobbers (Foot env) s s')
    (F := Keeps clobbers (Foot env) s) (Sim.readCommitment height width)
    (runSpec_readCommitment height width)
    (fun _ _ ↦ readCommitment_input) h fun st hr hs ↦ ?_) ?_ fun _ h ↦ h
  · have hroom' : st.roots.length < maxRoots := by
      rw [← hr.roots, List.length_map, Array.length_toList]
      exact hroom
    exact WP.mono ((commit_spec hs hroom' hh hw hrsi hrbx).withErr (commit_err hs hroom'))
      (fun _ ⟨st', he, hs', hk⟩ ↦ ⟨(), st', by rw [he]; rfl, hs', hk⟩)
      (fun _ ⟨he, hk⟩ ↦ ⟨by rw [he]; rfl, hk⟩)
  · rintro s' ⟨⟨⟩, t', hr, hc, -, -, hk⟩
    exact ⟨t', hr, hc, hk⟩

theorem runSpec_queryOpenings (i : Nat) (ps : List Nat) (st : VerifierProgramState) :
    runSpec (VerifierProgram.queryOpenings i ps) st = queryStep i ps st := by
  show runK (.query i ps .ret) st = _
  rw [run_query]
  rcases queryStep i ps st with _ | ⟨rows, st'⟩ <;> rfl

/-- **`query i positions`** against `Model.queryOpenings i positions`, from a spec of `query`
against the statement's `queryStep` (its frames `Q`, `F` carried through). -/
theorem queryOpeningsM_spec {i : Nat} {ps : Array UInt64} {Q : List (List K) → QState → Prop}
    {F : QState → Prop} (h : CodeRel env t s)
    (hq : ∀ st, SimState env st s → WP Transcript.query s
      (fun s' ↦ ∃ rows st', queryStep i (ps.toList.map UInt64.toNat) st = some (rows, st') ∧
        SimState env st' s' ∧ Q rows s')
      (fun s' ↦ queryStep i (ps.toList.map UInt64.toNat) st = none ∧ F s')) :
    WP Transcript.query s (fun s' ↦ ∃ rows t', (Model.queryOpenings i ps).run t = some (rows, t') ∧
      CodeRel env t' s' ∧ Q (rows.toList.map (·.toList.map K.ofLane)) s')
      (fun s' ↦ (Model.queryOpenings i ps).run t = none ∧ F s') := by
  refine WP.mono (lift (Sim.queryOpenings i rfl) (runSpec_queryOpenings i _)
    (fun _ _ ↦ queryOpenings_input) h fun st _ hs ↦ hq st hs) ?_ fun _ h ↦ h
  rintro s' ⟨rows, t', hr, hc, y, rfl, hq'⟩
  exact ⟨rows, t', hr, hc, hq'⟩

/-! ## The end -/

theorem stream_consumed {st : VerifierProgramState} (h : t.Rel st) :
    (t.cursor == t.stream.size) = st.stream.isEmpty := by
  have := h.cursor_le
  rw [← h.stream, Bool.eq_iff_iff, beq_iff_eq, List.isEmpty_iff, List.map_eq_nil_iff,
    List.drop_eq_nil_iff, Array.length_toList]
  omega

theorem openings_consumed {st : VerifierProgramState} (h : t.Rel st) :
    (t.phase == t.openings.size) = st.openings.isEmpty := by
  have := h.phase_le
  rw [← h.openings, Bool.eq_iff_iff, beq_iff_eq, List.isEmpty_iff, List.map_eq_nil_iff,
    List.drop_eq_nil_iff, Array.length_toList]
  omega

/-- **`finish`** against `Model.verify`'s last check: the stream and the openings consumed. It
writes no word. -/
theorem finishM_spec (h : CodeRel env t s) :
    WP Transcript.finish s (fun s' ↦ (t.cursor == t.stream.size && t.phase == t.openings.size) = true ∧
      s'.mem = s.mem ∧ RegsFrame [.rax, .rcx, .rdx, .r11] s s')
      (fun s' ↦ (t.cursor == t.stream.size && t.phase == t.openings.size) = false ∧
        s'.mem = s.mem ∧ RegsFrame [.rax, .rcx, .rdx, .r11] s s') := by
  obtain ⟨st, hr, hs, -⟩ := h
  rw [stream_consumed hr, openings_consumed hr]
  exact WP.mono ((finish_spec hs).withErr finish_err) (fun _ h ↦ h) fun _ ⟨he, hf⟩ ↦ ⟨he, hf⟩

/-! ## As refinements -/

variable {R : QState → Prop}

/-- `read` as a refinement, `R` kept. -/
theorem readScalar_refines (hR : ∀ s s', R s → Keeps clobbers (Foot env) s s' → R s') :
    Refines (fun t s ↦ CodeRel env t s ∧ R s) Transcript.readScalar Model.readScalar
      (fun x t' s' ↦ CodeRel env t' s' ∧ R s' ∧ s'.reg .r9 = x.c0 ∧ s'.reg .r10 = x.c1) R :=
  fun _ s ⟨h, hRs⟩ ↦ WP.mono (readScalarM_spec h)
    (fun _ ⟨x, t', hr, hc, h9, h10, hk⟩ ↦ ⟨x, t', hr, hc, hR s _ hRs hk, h9, h10⟩)
    (fun _ ⟨hr, hk⟩ ↦ ⟨hr, hR s _ hRs hk⟩)

/-- `sample` as a refinement, `R` kept. -/
theorem sampleChallenge_refines (hR : ∀ s s', R s → Keeps clobbers (Foot env) s s' → R s') :
    Refines (fun t s ↦ CodeRel env t s ∧ R s) Transcript.sampleChallenge Model.sampleChallenge
      (fun x t' s' ↦ CodeRel env t' s' ∧ R s' ∧ s'.reg .r9 = x.c0 ∧ s'.reg .r10 = x.c1) R :=
  fun _ s ⟨h, hRs⟩ ↦ WP.mono (sampleChallengeM_spec h)
    (fun _ ⟨x, t', hr, hc, h9, h10, hk⟩ ↦ ⟨x, t', hr, hc, hR s _ hRs hk, h9, h10⟩)
    (fun _ h ↦ h.elim)

/-- `grind bits`, `bits ≠ 0` in `rsi`, as a refinement, `R` kept. -/
theorem grind_refines {bits : Nat} (hb0 : bits ≠ 0) (hb : bits < 2 ^ 64)
    (hR : ∀ s s', R s → Keeps clobbers (Foot env) s s' → R s') :
    Refines (fun t s ↦ CodeRel env t s ∧ R s ∧ s.reg .rsi = bits.toUInt64) Transcript.grind
      (Model.grind bits) (fun _ t' s' ↦ CodeRel env t' s' ∧ R s') R :=
  fun _ s ⟨h, hRs, hrsi⟩ ↦ WP.mono (grindM_spec h hb0 hb hrsi)
    (fun _ ⟨t', hr, hc, hk⟩ ↦ ⟨(), t', hr, hc, hR s _ hRs hk⟩)
    (fun _ ⟨hr, hk⟩ ↦ ⟨hr, hR s _ hRs hk⟩)

/-- `commit height width`, `height` in `rsi` and `width` in `rbx`, as a refinement, `R` kept. -/
theorem readCommitment_refines {height width : Nat} (hh : height < 2 ^ 64) (hw : width < 2 ^ 64)
    (hR : ∀ s s', R s → Keeps clobbers (Foot env) s s' → R s') :
    Refines (fun t s ↦ CodeRel env t s ∧ R s ∧ t.roots.size < maxRoots ∧
        s.reg .rsi = height.toUInt64 ∧ s.reg .rbx = width.toUInt64) Transcript.commit
      (Model.readCommitment height width) (fun _ t' s' ↦ CodeRel env t' s' ∧ R s') R :=
  fun _ s ⟨h, hRs, hroom, hrsi, hrbx⟩ ↦ WP.mono (readCommitmentM_spec h hroom hh hw hrsi hrbx)
    (fun _ ⟨t', hr, hc, hk⟩ ↦ ⟨(), t', hr, hc, hR s _ hRs hk⟩)
    (fun _ ⟨hr, hk⟩ ↦ ⟨hr, hR s _ hRs hk⟩)

end NativeVm.Code
