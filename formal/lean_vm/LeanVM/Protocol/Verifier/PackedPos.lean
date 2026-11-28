/-
  LeanVM.Protocol.Verifier.PackedPos

  Every packed message of the leanVM verifier program has at least one scalar: the root condition
  the random-oracle theorem asks of the program (`RootOk`).
-/

module

public import Statement.Verifier.Lib
public import LeanVM.Protocol.Compile.Rom.Decode

/-!
# The verifier's packed messages are nonempty

The random-oracle theorem (`LeanVM.Protocol.Compile.Rom.romSound`) asks that the program's node at
a seed's root history has every packed message nonempty (`VerifierProgram.PackedPos`, in
`RootOk`). The leanVM verifier has four: the link's challenges (`packedChallenges`, at least `5`),
its five fresh coefficients, its message of the values and `kBits = 64` bit-slices, and ring
switching's draw of `2·16 + 1` or more. Everything else reads, draws and opens one at a time.

`packedPos_leanVmVerifierProgram`, `packedPos_deferringVerifierProgram` for every bytecode, digest
and split; `rootOk_leanVmVerifierProgram`: the empty history is a root of the program.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Protocol.Verifier VerifierProgram

@[expose] public section

variable {α β : Type}

namespace VerifierProgram.PackedPos

theorem bind' {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : p.PackedPos)
    (hf : ∀ a, (f a).PackedPos) : (p >>= f).PackedPos := hp.bind hf

theorem pure' (a : α) : (pure a : VerifierProgram α).PackedPos := trivial

theorem fail' : (fail : VerifierProgram α).PackedPos := trivial

theorem readScalars' : ∀ n, (readScalars n).PackedPos
  | 0 => trivial
  | n + 1 => fun _ ↦ (readScalars' n).bind fun _ ↦ trivial

theorem sampleChallenges' : ∀ n, (sampleChallenges n).PackedPos
  | 0 => trivial
  | n + 1 => fun _ ↦ (sampleChallenges' n).bind fun _ ↦ trivial

theorem liftOption' (o : Option α) : (liftOption o).PackedPos := by
  cases o <;> trivial

/-- `require`, its decision procedure read off the goal. -/
theorem requireI {c : Prop} {inst : Decidable c} : (@require c inst).PackedPos := by
  unfold require; split <;> trivial

end VerifierProgram.PackedPos

/-- Prove `PackedPos` of a `do`-block of the verifier's pieces, every lemma applied at reducible
transparency (`PackedPos` is a function of the program: unfolding it would evaluate the block);
the packed leaves' positivity is left as goals. -/
scoped macro "packed_pos" : tactic => `(tactic| (
  repeat' (first
    | split
    | with_reducible apply PackedPos.bind'
    | with_reducible apply PackedPos.bind
    | intro _
    | dsimp only
    | with_reducible exact PackedPos.readScalar'
    | with_reducible exact PackedPos.sampleChallenge'
    | with_reducible exact PackedPos.readScalars' _
    | with_reducible exact PackedPos.sampleChallenges' _
    | with_reducible exact PackedPos.grindProofOfWork' _
    | with_reducible exact PackedPos.requireI
    | with_reducible exact PackedPos.liftOption' _
    | with_reducible exact PackedPos.readCommitment' _ _
    | with_reducible exact PackedPos.queryOpenings' _ _
    | with_reducible apply PackedPos.readScalarsPacked'
    | with_reducible apply PackedPos.sampleChallengesPacked'
    | with_reducible exact PackedPos.ret' _
    | with_reducible exact PackedPos.pure' _
    | with_reducible exact PackedPos.fail')))

/-! ## The verifier's loops -/

theorem packedPos_sumcheckRoundPoly (count : ℕ) (claim : E) (e : Option E) :
    (sumcheckRoundPoly count claim e).PackedPos := by
  cases e <;> (unfold sumcheckRoundPoly; packed_pos)

theorem packedPos_sumcheck (count : ℕ) :
    ∀ (eqs : List (Option E)) (claim : E), (sumcheck claim count eqs).PackedPos
  | [], _ => by unfold sumcheck; exact PackedPos.pure' _
  | e :: es, claim => by
    unfold sumcheck
    exact (packedPos_sumcheckRoundPoly _ _ _).bind' fun _ ↦
      PackedPos.sampleChallenge'.bind' fun _ ↦
        (packedPos_sumcheck count es _).bind' fun _ ↦ PackedPos.pure' _

theorem packedPos_sampleQueriesAux (depth : ℕ) :
    ∀ (fuel remaining : ℕ), (sampleQueriesAux depth fuel remaining).PackedPos
  | 0, _ => by unfold sampleQueriesAux; exact PackedPos.pure' _
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    split
    · exact PackedPos.pure' _
    · exact PackedPos.sampleChallenge'.bind' fun _ ↦
        (packedPos_sampleQueriesAux depth fuel _).bind' fun _ ↦ PackedPos.pure' _

theorem packedPos_sampleQueries (depth count : ℕ) : (sampleQueries depth count).PackedPos :=
  packedPos_sampleQueriesAux depth count count

theorem packedPos_foldRounds : ∀ (n : ℕ) (s : WhirState), (foldRounds n s).PackedPos
  | 0, _ => by unfold foldRounds; exact PackedPos.pure' _
  | n + 1, s => by
    unfold foldRounds foldRound
    packed_pos
    exact packedPos_foldRounds n _

theorem packedPos_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      (whirLevels logN laneFolds evaluateBasis index levels s).PackedPos
  | _, [], _ => by unfold whirLevels; exact PackedPos.fail'
  | index, level :: rest, s => by
    unfold whirLevels
    refine (packedPos_foldRounds _ _).bind' fun _ ↦ ?_
    packed_pos
    all_goals first
      | exact packedPos_sampleQueries _ _
      | exact packedPos_sumcheck _ _ _
      | exact packedPos_whirLevels logN laneFolds evaluateBasis _ _ _

theorem packedPos_verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) :
    (verifyWhir logN logInvRate target evaluateBasis).PackedPos := by
  unfold verifyWhir
  exact (PackedPos.liftOption' _).bind' fun _ ↦ packedPos_whirLevels _ _ _ _ _ _

/-! ## The phases -/

theorem packedPos_readAnnouncedSizes (bytecode : List K) :
    (readAnnouncedSizes bytecode).PackedPos := by
  unfold readAnnouncedSizes
  packed_pos

theorem packedPos_commitStack (logN logInvRate : ℕ) : (commitStack logN logInvRate).PackedPos := by
  unfold commitStack
  packed_pos

theorem packedPos_readOod (stackLog : ℕ) : (readOod stackLog).PackedPos := by
  unfold readOod
  packed_pos

theorem packedPos_bindPublicInput (layout : Layout) (pd : Digest) :
    (bindPublicInput layout pd).PackedPos := by
  unfold bindPublicInput
  packed_pos

/-- The link's packed messages: its challenges (at least `5`), its five fresh coefficients, and
its message of the values and `kBits` bit-slices. -/
theorem packedPos_verifyLink {bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split}
    (hsplit : ∀ b p pc, (bytecodeSplit b p pc).PackedPos) (layout : Layout) :
    (verifyLink bytecodeSplit layout).PackedPos := by
  unfold verifyLink
  packed_pos
  all_goals first
    | exact packedPos_sumcheck _ _ _
    | exact hsplit _ _ _
    | (unfold packedChallenges; dsimp only; omega)
    | (simp only [kBits]; omega)
    | omega

theorem packedPos_computedSplit (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ)) :
    (computedSplit bytecode point pc).PackedPos := by
  unfold computedSplit
  packed_pos

theorem packedPos_freshSplit (fresh : FreshClaim) (bytecode : List K) (point : List E)
    (pc : List (ℕ × ℕ)) : (freshSplit fresh bytecode point pc).PackedPos := by
  unfold freshSplit
  packed_pos

/-! The Keccak reduction's blocks are proved step by step: the tactic's failed attempts on their
heavy terms exhaust the elaborator. -/

theorem packedPos_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    (verifyKeccakLayer logSteps step claim).PackedPos := by
  unfold verifyKeccakLayer
  dsimp only
  with_reducible refine PackedPos.bind' (PackedPos.readScalars' _) fun _ ↦ ?_
  with_reducible refine PackedPos.bind' PackedPos.requireI fun _ ↦ ?_
  with_reducible refine PackedPos.bind' (PackedPos.grindProofOfWork' _) fun _ ↦ ?_
  with_reducible refine PackedPos.bind' PackedPos.sampleChallenge' fun _ ↦ ?_
  with_reducible refine PackedPos.bind' (packedPos_sumcheck _ _ _) ?_
  rintro ⟨_, _⟩
  dsimp only
  with_reducible refine PackedPos.bind' (packedPos_sumcheck _ _ _) ?_
  rintro ⟨_, _⟩
  dsimp only
  with_reducible refine PackedPos.bind' (PackedPos.readScalars' _) fun _ ↦ ?_
  with_reducible refine PackedPos.bind' PackedPos.requireI fun _ ↦ ?_
  with_reducible refine PackedPos.bind' (PackedPos.grindProofOfWork' _) fun _ ↦ ?_
  with_reducible refine PackedPos.bind' PackedPos.sampleChallenge' fun _ ↦ ?_
  exact PackedPos.pure' _

theorem packedPos_keccakLayers (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : KeccakClaim), (keccakLayers logSteps steps claim).PackedPos
  | [], _ => by unfold keccakLayers; exact PackedPos.pure' _
  | step :: steps, claim => by
    unfold keccakLayers
    with_reducible exact (packedPos_verifyKeccakLayer _ _ _).bind' fun _ ↦ packedPos_keccakLayers logSteps steps _

theorem packedPos_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    (keccakOpen logSteps claim first count value).PackedPos := by
  unfold keccakOpen
  with_reducible refine PackedPos.bind' (packedPos_sumcheck _ _ _) ?_
  rintro ⟨_, _⟩
  with_reducible exact PackedPos.pure' _

theorem packedPos_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    (verifyKeccak logSteps inst output).PackedPos := by
  unfold verifyKeccak
  dsimp only
  with_reducible refine PackedPos.bind' PackedPos.requireI fun _ ↦ ?_
  with_reducible refine PackedPos.bind' (PackedPos.grindProofOfWork' _) fun _ ↦ ?_
  with_reducible refine PackedPos.bind' (PackedPos.sampleChallenges' _) fun _ ↦ ?_
  with_reducible refine PackedPos.bind' (PackedPos.sampleChallenges' _) fun _ ↦ ?_
  split <;> repeat' (first
    | with_reducible refine PackedPos.bind' (packedPos_keccakLayers _ _ _) fun _ ↦ ?_
    | with_reducible refine PackedPos.bind' (packedPos_keccakOpen _ _ _ _ _) fun _ ↦ ?_
    | with_reducible refine PackedPos.bind' (packedPos_sumcheck _ _ _) fun _ ↦ ?_
    | with_reducible refine PackedPos.bind' PackedPos.readScalar' fun _ ↦ ?_
    | with_reducible refine PackedPos.bind' (PackedPos.readScalars' _) fun _ ↦ ?_
    | with_reducible refine PackedPos.bind' PackedPos.requireI fun _ ↦ ?_
    | with_reducible refine PackedPos.bind' (PackedPos.pure' _) fun _ ↦ ?_
    | with_reducible exact PackedPos.pure' _)

theorem packedPos_keccakValidity (layout : Layout) (link : LinkEnd) :
    (keccakValidity layout link).PackedPos := by
  unfold keccakValidity
  split
  with_reducible exact (PackedPos.liftOption' _).bind' fun _ ↦ packedPos_verifyKeccak _ _ _

/-- Ring switching's packed draw: its `2·16` map challenges, the merging challenge if any, and
the stacked opening's batching challenge. -/
theorem packedPos_ringSwitch (claims : List RingClaim) : (ringSwitch claims).PackedPos := by
  unfold ringSwitch
  packed_pos
  all_goals omega

theorem packedPos_memoryTermClaim (layout : Layout) (link : LinkEnd) :
    (memoryTermClaim layout link).PackedPos := by
  unfold memoryTermClaim
  packed_pos

theorem packedPos_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (batching : E) : (verifyStackedOpening stackLog logInvRate claims batching).PackedPos := by
  unfold verifyStackedOpening
  exact (PackedPos.require' _).bind' fun _ ↦ packedPos_verifyWhir _ _ _ _

/-! ## The verifier -/

theorem packedPos_verifyExecution {bytecodeSplit : List K → List E → List (ℕ × ℕ) →
    VerifierProgram Split} (hsplit : ∀ b p pc, (bytecodeSplit b p pc).PackedPos)
    (bytecode : List K) (pd : Digest) :
    (verifyExecution bytecodeSplit bytecode pd).PackedPos := by
  unfold verifyExecution
  refine (packedPos_readAnnouncedSizes _).bind' fun _ ↦ ?_
  split
  refine (packedPos_commitStack _ _).bind' fun _ ↦ (packedPos_readOod _).bind' fun _ ↦
    (packedPos_verifyLink hsplit _).bind' fun _ ↦ (packedPos_bindPublicInput _ _).bind' fun _ ↦
      (packedPos_keccakValidity _ _).bind' fun _ ↦ ?_
  split
  refine (PackedPos.liftOption' _).bind' fun _ ↦ (packedPos_ringSwitch _).bind' fun _ ↦ ?_
  split
  exact (packedPos_memoryTermClaim _ _).bind' fun _ ↦ packedPos_verifyStackedOpening _ _ _ _

/-- **Every packed message of the leanVM verifier program has a scalar.** -/
theorem packedPos_leanVmVerifierProgram (bytecode : List K) (pd : Digest) :
    (leanVmVerifierProgram bytecode pd).PackedPos := by
  unfold leanVmVerifierProgram
  exact (packedPos_verifyExecution packedPos_computedSplit _ _).bind' fun _ ↦ PackedPos.pure' _

/-- **Every packed message of the deferring verifier program has a scalar.** -/
theorem packedPos_deferringVerifierProgram (fresh : FreshClaim) (bytecode : List K)
    (pd : Digest) : (deferringVerifierProgram fresh bytecode pd).PackedPos := by
  unfold deferringVerifierProgram
  exact (packedPos_verifyExecution (packedPos_freshSplit fresh) _ _).bind' fun _ ↦
    PackedPos.pure' _

open _root_.LeanVM.Protocol.Compile.Rom in
/-- **The empty history is a root of the leanVM verifier program** (`RootOk`). -/
theorem rootOk_leanVmVerifierProgram (bytecode : List K) (pd : Digest) :
    RootOk (leanVmVerifierProgram bytecode pd) [] :=
  ⟨.nil, trivial, rfl, rfl, rfl, packedPos_leanVmVerifierProgram bytecode pd⟩

open _root_.LeanVM.Protocol.Compile.Rom in
/-- **The empty history is a root of the deferring verifier program** (`RootOk`). -/
theorem rootOk_deferringVerifierProgram (fresh : FreshClaim) (bytecode : List K) (pd : Digest) :
    RootOk (deferringVerifierProgram fresh bytecode pd) [] :=
  ⟨.nil, trivial, rfl, rfl, rfl, packedPos_deferringVerifierProgram fresh bytecode pd⟩

end

end LeanVM.Protocol.Compile
