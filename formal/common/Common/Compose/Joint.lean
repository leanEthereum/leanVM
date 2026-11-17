module

public import Common.Compose.Defs
public import Common.Compose.Swap

@[expose] public section

/-!
# The joint world: both permutations in one state

The composed experiment's candidate and verdict are those of the joint world (`jointGame`): one
stateful simulation over coins whose state holds both permutations' edges, `π`'s queries with
their answers (its record) and the request log (twice: the forgery game keeps its own copy,
`Forger.lean`). `composed_evalDistEq_jointGame`: the knowledge-soundness world's transcript, read
through its permutation queries, is the joint world's record of `π` (`run_loggedOracles`); the
honest side's `π_h`, sampled with coins, is the joint world's second permutation (`run_nest`,
`honest_step`); and the verifier's run over `π`, whose result the candidate and the verdict do
not read, drops out. The extractor reads the record, not the coins
(`ExtractorReadsPermutationQueries`).
-/

open OracleComp OracleSpec
open scoped ENNReal
open LeanVM LeanVM.Node LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open Common.SufCma

namespace Common.Compose

variable {Seed PK SK Req Resp F : Type}

/-- `π`'s queries with their answers, oldest first. -/
abbrev PermutationRecord := List (PermutationQuery KeccakState × KeccakState)

/-- A log of signing requests to `k` keys, with their answers. -/
abbrev RequestLog (k : ℕ) (Req Resp : Type) := QueryLog (Fin k × Req →ₒ Resp)

/-- **The joint state**: `π`'s edges, `π_h`'s edges, `π`'s record, the request log and the forgery
game's copy of it. -/
abbrev JointState (k : ℕ) (Req Resp : Type) :=
  PermutationEdges KeccakState × PermutationEdges KeccakState × PermutationRecord ×
    RequestLog k Req Resp × RequestLog k Req Resp

variable (scheme : Scheme Seed PK SK Req Resp F) (k : ℕ)

/-- **The joint world's answers**: a coin drawn; `π` and `π_h` each lazily sampled on its own
edges, `π`'s queries recorded; a request `(j, r)` answered by key `j`'s signer over `π_h`, and
logged in both logs. -/
noncomputable def jointOracles (sks : Fin k → SK) :
    QueryImpl (ComposedOracles k Req Resp) (StateT (JointState k Req Resp) ProbComp)
  | .inl (.inl (.inl n)) => StateT.lift (liftM (unifSpec.query n))
  | .inl (.inl (.inr q)) => StateT.mk fun s ↦
      (fun z ↦ (z.1, (z.2, s.2.1, s.2.2.1 ++ [(q, z.1)], s.2.2.2))) <$>
        (lazyRandomPermutation q).run s.1
  | .inl (.inr q) => StateT.mk fun s ↦
      (fun z ↦ (z.1, (s.1, z.2, s.2.2))) <$> (lazyRandomPermutation q).run s.2.1
  | .inr r => StateT.mk fun s ↦
      (fun z ↦ (z.1, (s.1, z.2, s.2.2.1, s.2.2.2.1 ++ [⟨r, z.1⟩], s.2.2.2.2 ++ [⟨r, z.1⟩]))) <$>
        (simulateQ lazyRandomPermutationOracles (scheme.sign (sks r.1) r.2)).run s.2.1

/-- The outcome the candidate reads: the statement and proof, no verdict, and `π`'s record as the
transcript. -/
def outcomeOf (out : ProgramAndInput × Proof) (record : PermutationRecord) : ExperimentOutcome :=
  ⟨out.1.1, out.1.2, out.2, false, record.map fun e ↦ ⟨.inr e.1, e.2⟩⟩

theorem permutationQueries_outcomeOf (out : ProgramAndInput × Proof) (record : PermutationRecord) :
    permutationQueries (outcomeOf out record).transcript = record := by
  induction record with
  | nil => rfl
  | cons e record ih =>
    change permutationQueries ((⟨.inr e.1, e.2⟩ :
      (t : RandomPermutationOracles.Domain) × RandomPermutationOracles.Range t) ::
        (outcomeOf out record).transcript) = e :: record
    simp only [permutationQueries, List.filterMap_cons] at ih ⊢
    rw [ih]

variable (guest : LeanIsaProgram) (decoder : Cost.MachineProgram)
  (extractor : StraightLineExtractor) (raws : NodeWitness → List (PK × F))
  (deployedVerify : PK → F → Bool)

/-- **The candidate reads the outcome's statement, proof and permutation queries**, when the
extractor reads only the latter of the transcript. -/
theorem candidate_congr (hext : ExtractorReadsPermutationQueries extractor)
    {o o' : ExperimentOutcome} (hp : o.program = o'.program) (hi : o.input = o'.input)
    (hpr : o.proof = o'.proof)
    (ht : permutationQueries o.transcript = permutationQueries o'.transcript)
    (pks : Fin k → PK) (log : RequestLog k Req Resp) :
    candidate scheme k guest decoder extractor raws deployedVerify o pks log =
      candidate scheme k guest decoder extractor raws deployedVerify o' pks log := by
  obtain ⟨p, i, pr, a, t⟩ := o
  obtain ⟨p', i', pr', a', t'⟩ := o'
  dsimp only at hp hi hpr ht
  subst hp hi hpr
  have e : IsCandidate scheme k guest decoder extractor raws deployedVerify ⟨p, i, pr, a, t⟩ =
      IsCandidate scheme k guest decoder extractor raws deployedVerify ⟨p, i, pr, a', t'⟩ := by
    funext pks log j f
    simp only [IsCandidate, hext p i t t' pr ht]
  have key : ∀ P Q : (Fin k → PK) → RequestLog k Req Resp → Fin k → F → Prop, P = Q →
      (open Classical in if h : ∃ j f, P pks log j f then some (h.choose, h.choose_spec.choose)
        else none) =
      (open Classical in if h : ∃ j f, Q pks log j f then some (h.choose, h.choose_spec.choose)
        else none) := by
    rintro P _ rfl
    rfl
  exact key _ _ e

/-- **The joint game**: the honest keys, the adversary answered by the joint world from `π`'s
empty edges and `π_h`'s edges after key generation, then the candidate and its verdict. -/
noncomputable def jointGame (A : ComposedAdversary k PK Req Resp) :
    ProbComp (Option (Fin k × F) × Bool) :=
  honestKeys scheme k >>= fun keys ↦
    (simulateQ (jointOracles scheme k keys.1.2) (A keys.1.1)).run ([], keys.2, [], [], []) >>=
      fun y ↦
        (candidate scheme k guest decoder extractor raws deployedVerify (outcomeOf y.1 y.2.2.2.1)
          keys.1.1 y.2.2.2.2.1, ·) <$>
        verdictRun scheme k keys.1.1 (candidate scheme k guest decoder extractor raws
          deployedVerify (outcomeOf y.1 y.2.2.2.1) keys.1.1 y.2.2.2.2.1) y.2.2.1

/-! ## The knowledge-soundness world is the joint world -/

/-- The joint state of the honest side's state and the recording permutation's. -/
def honestProj (s : (PermutationEdges KeccakState × RequestLog k Req Resp) ×
    (PermutationRecord × PermutationEdges KeccakState)) : JointState k Req Resp :=
  (s.2.2, s.1.1, s.2.1, s.1.2, s.1.2)

/-- **The honest side's answers, run by the recording permutation, are the joint world's.** -/
theorem honest_step (sks : Fin k → SK) (t : (ComposedOracles k Req Resp).Domain)
    (s : (PermutationEdges KeccakState × RequestLog k Req Resp) ×
      (PermutationRecord × PermutationEdges KeccakState)) :
    Prod.map id (honestProj k) <$>
        (nest (honestOracles scheme k sks) recordingPermutation t).run s =
      (jointOracles scheme k sks t).run (honestProj k s) := by
  rcases t with ((n | q) | q) | r
  · simp [nest, honestOracles, recordingPermutation, jointOracles, honestProj]
  · simp [nest, honestOracles, recordingPermutation, jointOracles, honestProj]
  · simp [nest, honestOracles, jointOracles, honestProj,
      run_liftM_of_coins recordingPermutation (fun _ _ ↦ rfl)]
  · simp [nest, honestOracles, jointOracles, honestProj,
      run_liftM_of_coins recordingPermutation (fun _ _ ↦ rfl)]

/-- **The wrapped adversary, run by the recording permutation, is the joint world's run.** -/
theorem run_honest_recording (A : ComposedAdversary k PK Req Resp) :
    (simulateQ recordingPermutation (honest scheme k A)).run ([], []) =
      honestKeys scheme k >>= fun keys ↦
        (fun y ↦ ((y.1, keys.1.1, y.2.2.2.2.1, y.2.2.1), (y.2.2.2.1, y.2.1))) <$>
          (simulateQ (jointOracles scheme k keys.1.2) (A keys.1.1)).run
            ([], keys.2, [], [], []) := by
  unfold honest
  rw [simulateQ_bind, StateT.run_bind, run_liftM_of_coins recordingPermutation (fun _ _ ↦ rfl),
    bind_map_left]
  refine bind_congr fun keys ↦ ?_
  dsimp only
  have h := map_run_simulateQ_eq_of_query_map_eq_inv' (nest (honestOracles scheme k keys.1.2)
    recordingPermutation) (jointOracles scheme k keys.1.2) (fun _ ↦ True) (honestProj k)
    (fun _ _ _ _ _ ↦ trivial) (fun t s _ ↦ honest_step scheme k keys.1.2 t s) (A keys.1.1)
    ((keys.2, []), ([], [])) trivial
  rw [simulateQ_map, StateT.run_map, run_nest, Functor.map_map,
    show (([], keys.2, [], [], []) : JointState k Req Resp) = honestProj k ((keys.2, []), ([], []))
      from rfl, ← h, Functor.map_map]
  rfl

/-- **The composed experiment's candidate and verdict are the joint game's.** -/
theorem composed_evalDistEq_jointGame (hext : ExtractorReadsPermutationQueries extractor)
    (A : ComposedAdversary k PK Req Resp) :
    (fun z ↦ (z.2.2.2.1, z.2.2.2.2)) <$>
        composedExperiment scheme k guest decoder extractor raws deployedVerify A =ᵈ
      jointGame scheme k guest decoder extractor raws deployedVerify A := by
  let g : ((ProgramAndInput × Proof) × (Fin k → PK) × RequestLog k Req Resp ×
      PermutationEdges KeccakState) × (PermutationRecord × PermutationEdges KeccakState) →
      ProbComp (Option (Fin k × F) × Bool) := fun w ↦
    (candidate scheme k guest decoder extractor raws deployedVerify (outcomeOf w.1.1 w.2.1)
      w.1.2.1 w.1.2.2.1, ·) <$>
    verdictRun scheme k w.1.2.1 (candidate scheme k guest decoder extractor raws deployedVerify
      (outcomeOf w.1.1 w.2.1) w.1.2.1 w.1.2.2.1) w.1.2.2.2
  unfold composedExperiment runWithRandomPermutation
  rw [StateT.run'_eq, Functor.map_map, simulateQ_bind, StateT.run_bind, map_bind]
  calc _ =ᵈ (simulateQ lazyRandomPermutationOracles
        ((simulateQ loggedOracles (honest scheme k A)).run [])).run [] >>=
          fun p ↦ g (p.1.1, (permutationQueries p.1.2, p.2)) := by
        refine EvalDistEq.bind_congr EvalDistEq.rfl fun p ↦ ?_
        obtain ⟨⟨⟨⟨⟨program, input⟩, proof⟩, pks, log, edges⟩, transcript⟩, E⟩ := p
        have hc : ∀ accepted, candidate scheme k guest decoder extractor raws deployedVerify
            ⟨program, input, proof, accepted, transcript⟩ pks log =
            candidate scheme k guest decoder extractor raws deployedVerify
              (outcomeOf ((program, input), proof) (permutationQueries transcript)) pks log :=
          fun accepted ↦ candidate_congr scheme k guest decoder extractor raws deployedVerify hext
            (o := ⟨program, input, proof, accepted, transcript⟩)
            (o' := outcomeOf ((program, input), proof) (permutationQueries transcript))
            rfl rfl rfl (permutationQueries_outcomeOf _ _).symm pks log
        simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind,
          map_pure, run_lazy_liftM, bind_map_left, hc, g]
        rw [← bind_pure_comp]
        exact EvalDistEq.bind_const _ _
    _ = (simulateQ recordingPermutation (honest scheme k A)).run ([], []) >>= g := by
        rw [show (([], []) : PermutationRecord × PermutationEdges KeccakState) =
            (permutationQueries [], []) from rfl, ← run_loggedOracles, bind_map_left]
    _ = _ := by
        rw [run_honest_recording, bind_assoc]
        refine bind_congr fun keys ↦ ?_
        rw [bind_map_left]

end Common.Compose
