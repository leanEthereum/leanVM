/-
  LeanVM.Guest.Child.Stream

  A proof the deferring verifier accepts has a stream of at most `leanVmStream = 4792` scalars,
  within `STREAM_CAP = 8192` (`Coverage.childStreamCap`), on every bytecode.
-/

module

public import LeanVM.Wire.HonestShape
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Guest.AcceptableChild

/-!
# The stream an accepted proof carries

`Wired p hs n c Q` (`LeanVM.Wire.HonestRun`) bounds the stream elements every run of `p` reads by
`c`. A run of such a program consumes at most `c` scalars of the stream (`run_stream_of_wired`),
and an accepted run consumes the whole stream (`runProof`), so an accepted proof's stream has at
most `c` scalars (`stream_le_of_runProofWithHash`).

The deferring verifier program is wired with `leanVmStream` stream elements, as the verifier
program is (`wired_leanVmProgram`): it is `verify_execution` split at the link's call of the
program's split (`verifyExecution_split`), and its split (`freshSplit`) reads nothing
(`wired_deferringProgram`). `leanVmStream = 4792 ≤ 8192`, so every proof the deferring verifier
accepts, on any bytecode, has a stream of at most `STREAM_CAP` scalars
(`stream_le_of_verifyDeferred`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Verifier.Defers LeanVM.Protocol.KeccakHash
open LeanVM.Wire

@[expose] public section

/-! ## A run reads at most its program's stream -/

/-- **A run of a wired program consumes at most its stream bound**: the stream it starts on is
what it read, at most `c` scalars, then the stream it leaves. -/
theorem run_stream_of_wired (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState) {α : Type}
    {Q : α → List ℕ → ℕ → Prop} {p : VerifierProgram α} :
    ∀ {hts : List ℕ} {n c : ℕ}, Wired p hts n c Q →
      ∀ {s : VerifierProgramState} {a : α} {s' : VerifierProgramState},
        runWithHash H F p s = some (a, s') → ∃ xs, s.stream = xs ++ s'.stream ∧ xs.length ≤ c := by
  induction p with
  | ret b =>
    intro hts n c _ s a s' h
    simp only [runWithHash] at h
    cases h
    exact ⟨[], rfl, Nat.zero_le _⟩
  | fail => intro hts n c _ s a s' h; simp [runWithHash] at h
  | read k ih =>
    intro hts n c hw s a s' h
    simp only [runWithHash] at h
    rcases hs : s.stream with _ | ⟨x, xs⟩ <;> rcases hg : s.sponge.ground with _ | g <;>
      simp only [hs, hg] at h
    · simp [pure] at h
    · simp [pure] at h
    · obtain ⟨ys, hys, hl⟩ := ih x (hw.2 x) h
      refine ⟨x :: ys, ?_, ?_⟩
      · exact congrArg (x :: ·) hys
      · simp only [List.length_cons]; have := hw.1; omega
    · simp [pure] at h
  | sample k ih =>
    intro hts n c hw s a s' h
    simp only [runWithHash] at h
    obtain ⟨ys, hys, hl⟩ := ih _ (hw _) h
    exact ⟨ys, hys, hl⟩
  | readPacked m k ih =>
    intro hts n c hw s a s' h
    simp only [runWithHash] at h
    split at h
    · obtain ⟨ys, hys, hl⟩ := ih _ (hw.2 _) h
      refine ⟨s.stream.take m ++ ys, ?_, ?_⟩
      · rw [List.append_assoc, ← show s.stream.drop m = ys ++ s'.stream from hys,
          List.take_append_drop]
      · simp only [List.length_append, List.length_take]; have := hw.1; omega
    · simp [pure] at h
  | samplePacked m k ih =>
    intro hts n c hw s a s' h
    simp only [runWithHash] at h
    obtain ⟨ys, hys, hl⟩ := ih _ (hw _) h
    exact ⟨ys, hys, hl⟩
  | grind bits k ih =>
    intro hts n c hw s a s' h
    simp only [runWithHash] at h
    rcases hs : s.stream with _ | ⟨x, xs⟩ <;> rcases hg : s.sponge.ground with _ | g <;>
      simp only [hs, hg] at h
    · simp [pure] at h
    · simp [pure] at h
    · revert h
      generalize absorbNonce F s.sponge x = pr
      obtain ⟨pow, sp⟩ := pr
      intro h
      change (if _ then _ else _) = _ at h
      split at h
      · obtain ⟨ys, hys, hl⟩ := ih hw.2 h
        refine ⟨x :: ys, ?_, ?_⟩
        · exact congrArg (x :: ·) hys
        · simp only [List.length_cons]; have := hw.1; omega
      · simp [pure] at h
    · simp [pure] at h
  | commit height width k ih =>
    intro hts n c hw s a s' h
    simp only [runWithHash] at h
    rcases hs : s.stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;>
      rcases hg : s.sponge.ground with _ | g <;> simp only [hs, hg] at h
    · simp [pure] at h
    · simp [pure] at h
    · simp [pure] at h
    · simp [pure] at h
    · obtain ⟨ys, hys, hl⟩ := ih hw.2 h
      refine ⟨x0 :: x1 :: ys, ?_, ?_⟩
      · exact congrArg (x0 :: x1 :: ·) hys
      · simp only [List.length_cons]; have := hw.1; omega
    · simp [pure] at h
  | query i ps k ih =>
    intro hts n c hw s a s' h
    obtain ⟨_, _, _, _, _, rows, _, _, _, hk⟩ :=
      (runWithHash_query_eq_some_iff H F i ps k s _).mp h
    obtain ⟨ys, hys, hl⟩ := ih rows (hw.2.2 rows) hk
    exact ⟨ys, hys, hl⟩

/-- **An accepted proof's stream has at most the program's stream bound**: the run consumes the
whole stream. -/
theorem stream_le_of_runProofWithHash (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    {P : VerifierProgram Bool} {hts : List ℕ} {n c : ℕ} {Q : Bool → List ℕ → ℕ → Prop}
    (hP : Wired P hts n c Q) {seed : KeccakState} {π : Proof}
    (h : runProofWithHash (m := Id) H F P seed π = true) : π.stream.length ≤ c := by
  unfold runProofWithHash at h
  revert h
  match hr : runWithHash (m := Id) H F P ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ with
  | some (true, s) =>
    intro h
    obtain ⟨xs, hxs, hl⟩ := run_stream_of_wired H F hP hr
    have he : s.stream = [] := by
      have h' : (s.stream.isEmpty && s.openings.isEmpty) = true := h
      simp only [Bool.and_eq_true, List.isEmpty_iff] at h'
      exact h'.1
    rw [he, List.append_nil] at hxs
    have e : π.stream = xs := hxs
    rw [e]
    exact hl
  | some (false, _) => intro h; simp at h
  | none => intro h; simp at h

/-! ## The deferring verifier program -/

/-- The deferring verifier's split reads nothing. -/
theorem freshSplitP (fresh : FreshClaim) (bytecode : List K) (point : List E)
    (pc : List (ℕ × ℕ)) : CostLE (freshSplit fresh bytecode point pc) 0 := by
  unfold freshSplit
  exact CostLE.seq (CostLE.require _) (fun _ _ ↦ trivial) le_rfl

/-- **The deferring verifier program's openings and stream are within the wire bounds**, from no
commitment, with `wireMaxPhases` openings and `leanVmStream` stream elements, as the verifier
program's (`wired_leanVmProgram`). -/
theorem wired_deferringProgram (fresh : FreshClaim) (bytecode : List K) (publicInput : Digest) :
    Wired (deferringVerifierProgram fresh bytecode publicInput) [] wireMaxPhases leanVmStream
      fun _ _ _ ↦ True := by
  rw [deferringVerifierProgram_eq, verifyExecution_split]
  refine (Wired.bind (f := fun _ ↦ VerifierProgram.ret true) (a := leanVmStream) (b := 0)
    (Q := fun _ _ _ ↦ True) (R := fun _ _ _ ↦ True) ?_ fun _ _ _ _ ↦ trivial).mono
    (fun _ _ _ h ↦ h) le_rfl
  refine Wired.seq (wired_execPre bytecode) (fun z hs n hz ↦ ?_) (by unfold leanVmStream; omega)
  obtain ⟨rfl, hsz, ⟨w, hc⟩, level, rest, hl, rfl⟩ := hz
  refine Wired.cost_seq (freshSplitP _ _ _ _) (fun split _ ↦ ?_) (Nat.zero_le _)
  exact (wired_execSuf publicInput z split hsz hc level rest hl).mono (fun _ _ _ h ↦ h)
    (by unfold leanVmStream; omega)

/-- The verifier program's stream bound: `4792` scalars. -/
theorem leanVmStream_eq : leanVmStream = 4792 := by
  unfold leanVmStream linkSufCost keccakStream keccakStreamOf keccakLayerStream whirStreamBound
  decide

/-- **The stream bound is within `STREAM_CAP`**: `4792 ≤ 8192`. -/
theorem leanVmStream_le_childStreamCap : leanVmStream ≤ Coverage.childStreamCap := by
  rw [leanVmStream_eq]
  decide

/-- **A proof the deferring verifier accepts has a stream of at most `leanVmStream` scalars**, on
every bytecode, IV, public input and fresh claim. -/
theorem stream_le_leanVmStream_of_verifyDeferred {bytecode : List K} {iv publicInput : Digest}
    {fresh : FreshClaim} {proof : Proof}
    (h : verifyDeferred bytecode iv publicInput fresh proof = true) :
    proof.stream.length ≤ leanVmStream := by
  rw [verifyDeferred_eq_withHash] at h
  exact stream_le_of_runProofWithHash _ _ (wired_deferringProgram fresh bytecode publicInput) h

/-- **A proof the deferring verifier accepts has a stream of at most `STREAM_CAP = 8192`
scalars** (`Coverage.childStreamCap`), on every bytecode. -/
theorem stream_le_of_verifyDeferred {bytecode : List K} {iv publicInput : Digest}
    {fresh : FreshClaim} {proof : Proof}
    (h : verifyDeferred bytecode iv publicInput fresh proof = true) :
    proof.stream.length ≤ Coverage.childStreamCap :=
  (stream_le_leanVmStream_of_verifyDeferred h).trans leanVmStream_le_childStreamCap

end

end LeanVM.Guest.Child
