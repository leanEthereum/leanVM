/-
  LeanVM.Protocol.EndToEnd.Sound.SkelPhases

  The skeletons of the cut verifier's phases: fixed by the announced sizes.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.SkelLeaves

/-!
# The phases' skeletons

Each phase of the cut verifier (`Relation.leanVmProgramCut`) has the skeleton `SkelDefs.lean`
gives it, on a built layout's sizes: the opening's (`skel_whirLevelsGF`,
`skel_verifyStackedOpeningCut`), the stack's commitment and out-of-domain sample, the link's
(`skel_verifyLink`), the Keccak reduction's (`skel_verifyKeccak`), ring switching's; the body's
(`skel_veBodyCut`) and the announced sizes' (`skel_readAnnouncedSizes`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.Relation

@[expose] public section

/-! ## The opening -/

theorem skel_foldRound (s : WhirState) :
    SkelP (foldRound s) skFoldRound fun r ↦ r.1.alphas.length = s.alphas.length + 1 := by
  unfold foldRound
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact (skel_readScalar.bind fun _ _ ↦ skel_readScalar.bind fun _ _ ↦ skel_readScalar.bind
    fun _ _ ↦ skel_readScalar.bind fun _ _ ↦ (skel_grindProofOfWork _).bind fun _ _ ↦
    skel_sampleChallenge.bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    SkelP.ret (Q := fun r : WhirState × FoldRound ↦ r.1.alphas.length = s.alphas.length + 1)
      (by simp)).mono (by simp [skFoldRound]) fun _ h ↦ h

theorem skel_foldRounds : ∀ (n : ℕ) (s : WhirState),
    SkelP (foldRounds n s) (skFoldRounds n) fun r ↦ r.1.alphas.length = s.alphas.length + n
  | 0, s => SkelP.ret rfl
  | n + 1, s => by
    unfold foldRounds
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact ((skel_foldRound s).bind fun r hr ↦ (skel_foldRounds n r.1).bind fun r' hr' ↦
      SkelP.ret (Q := fun r : WhirState × List FoldRound ↦
        r.1.alphas.length = s.alphas.length + (n + 1))
        (by show r'.1.alphas.length = s.alphas.length + (n + 1); omega)).mono
      (by simp [skFoldRounds]) fun _ h ↦ h

theorem skel_midTailPre (logN index : ℕ) (level next : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) :
    SkelP (midTailPre logN index level next s rounds) (skMidTail logN s.alphas.length level next)
      fun p ↦ p.2.alphas = s.alphas := by
  unfold midTailPre midTailC
  simp only [VerifierProgram.bind_eq]
  exact ((skel_readCommitment _ _).bind fun _ _ ↦ (skel_readScalars _).bind fun _ _ ↦
    (skel_grindProofOfWork _).bind fun _ _ ↦ (skel_sampleChallenges _).bind fun _ _ ↦
    skel_readScalar.bind fun _ _ ↦ (skel_grindProofOfWork _).bind fun _ _ ↦
    (skel_sampleQueries _ _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    (skel_queryOpenings _ _).bind fun _ _ ↦
    SkelP.ret (Q := fun p : List E × WhirState ↦ p.2.alphas = s.alphas) rfl).mono
    (by simp [skMidTail, List.append_assoc]) fun _ h ↦ h

theorem skel_whirLevelsGF (logN : ℕ) : ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
    SkelP (whirLevelsGF logN (finCut logN) index levels s) (skLevels logN s.alphas.length levels)
      fun _ ↦ True
  | _, [], _ => SkelP.fail _ _
  | index, [level], s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    exact ((skel_foldRounds level.fold s).bind fun r hr ↦
      ((by
        unfold finCut
        simp only [VerifierProgram.bind_eq]
        exact (skel_readScalars _).bind fun _ _ ↦
          SkelP.ret (Q := fun _ : WhirTrace ↦ True) trivial :
        SkelP (finCut logN index level r.1 r.2)
          (List.replicate (2 ^ (logN - r.1.alphas.length) + level.fold) .read ++ []) _).mono
        (sk' := List.replicate (2 ^ (logN - (s.alphas.length + level.fold)) + level.fold) .read)
        (by rw [hr, List.append_nil]) fun _ h ↦ h)).mono (by simp [skLevels]) fun _ h ↦ h
  | index, level :: next :: rest, s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    rw [show (fun r : WhirState × List FoldRound ↦ midTailC logN index level next (fun high s' ↦
        (whirLevelsGF logN (finCut logN) (index + 1) (next :: rest) s').bind fun tr ↦
          VerifierProgram.ret (WhirTrace.mid r.2 high tr)) r.1 r.2) =
        fun r ↦ (midTailPre logN index level next r.1 r.2).bind fun p ↦
          (whirLevelsGF logN (finCut logN) (index + 1) (next :: rest) p.2).bind fun tr ↦
            VerifierProgram.ret (WhirTrace.mid r.2 p.1 tr) from
      funext fun r ↦ midTailC_eq_pre _ _ _ _ _ _ _]
    exact ((skel_foldRounds level.fold s).bind fun r hr ↦
      ((skel_midTailPre logN index level next r.1 r.2).mono
        (sk' := skMidTail logN (s.alphas.length + level.fold) level next) (by rw [hr])
        fun _ h ↦ h).bind fun p hp ↦
      ((skel_whirLevelsGF logN (index + 1) (next :: rest) p.2).mono
        (sk' := skLevels logN (s.alphas.length + level.fold) (next :: rest))
        (by rw [hp, hr]) fun _ h ↦ h).bind fun _ _ ↦
      SkelP.ret (Q := fun _ : WhirTrace ↦ True) trivial).mono
      (by simp [skLevels, List.append_assoc]) fun _ h ↦ h

theorem skel_commitStack (logN logInvRate : ℕ) :
    SkelP (commitStack logN logInvRate) (skCommitStack logN logInvRate) fun _ ↦ True := by
  unfold commitStack
  simp only [VerifierProgram.bind_eq]
  exact ((skel_liftOption _).bind fun config hc ↦ (by
    rcases config with _ | ⟨level, rest⟩
    · exact SkelP.fail (skCommitStack logN logInvRate) _
    · exact (skel_readCommitment _ _).mono (sk' := skCommitStack logN logInvRate)
        (by rw [skCommitStack, hc]) fun _ h ↦ h)).mono (by simp) fun _ h ↦ h

theorem skel_verifyStackedOpeningCut (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (batching : E) :
    SkelP (verifyStackedOpeningCut stackLog logInvRate claims batching)
      (skWhir stackLog logInvRate) fun _ ↦ True := by
  unfold verifyStackedOpeningCut verifyWhirCut
  simp only [VerifierProgram.bind_eq]
  exact ((skel_require _).bind fun _ _ ↦ (skel_liftOption _).bind fun config hc ↦
      (skel_whirLevelsGF stackLog 0 config ⟨_, [], []⟩).mono (sk' := skWhir stackLog logInvRate)
        (by rw [skWhir, hc]; rfl) fun _ h ↦ h).mono (by simp) fun _ h ↦ h

/-! ## Around the front -/

theorem skel_readOod (stackLog : ℕ) : SkelP (readOod stackLog) (skOod stackLog) fun _ ↦ True := by
  unfold readOod
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_grindProofOfWork _).bind fun _ _ ↦ (skel_sampleChallenges _).bind fun _ _ ↦
    skel_readScalar.bind fun _ _ ↦ SkelP.ret (Q := fun _ : StackClaim ↦ True) trivial).mono
    (by simp [skOod]) fun _ h ↦ h

theorem skel_ringSwitch (a b : RingClaim) :
    SkelP (ringSwitch [a, b]) skRing fun _ ↦ True := by
  unfold ringSwitch
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_grindProofOfWork _).bind fun _ _ ↦ (skel_sampleChallengesPacked _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : StackClaim × E ↦ True) trivial).mono (by simp [skRing]) fun _ h ↦ h

theorem skel_bindPublicInput (layout : Layout) (publicInput : Digest) :
    SkelP (bindPublicInput layout publicInput) [.sample] fun _ ↦ True := by
  unfold bindPublicInput
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact (skel_sampleChallenge.bind fun _ _ ↦ (skel_liftOption _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : List ColumnClaim ↦ True) trivial).mono (by simp) fun _ h ↦ h

/-! ## The Keccak reduction -/

theorem map_comp_isSome_some (l : List E) :
    l.map (Option.isSome ∘ some) = List.replicate l.length true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, List.replicate_succ]

theorem skel_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    SkelP (verifyKeccakLayer logSteps step claim) (skKeccakLayer claim.point.length)
      fun c ↦ c.point.length = claim.point.length := by
  unfold verifyKeccakLayer
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_readScalars _).bind fun _ _ ↦ (skel_require _).bind fun _ _ ↦
    (skel_grindProofOfWork _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    (skel_sumcheck 3 _ (claim.point.map some)).bind fun r hr ↦ (skel_sumcheck 4 _ _).bind
      fun r' _ ↦ (skel_readScalars 3).bind fun _ _ ↦ (skel_require _).bind fun _ _ ↦
    (skel_grindProofOfWork _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    SkelP.ret (Q := fun c : KeccakClaim ↦ c.point.length = claim.point.length)
      (by simpa using hr)).mono
    (by simp [skKeccakLayer, map_comp_isSome_some, List.append_assoc]) fun _ h ↦ h

theorem skel_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    SkelP (keccakLayers logSteps steps claim) (steps.flatMap fun _ ↦ skKeccakLayer claim.point.length)
      fun c ↦ c.point.length = claim.point.length
  | [], claim => SkelP.ret rfl
  | step :: steps, claim => by
    unfold keccakLayers
    simp only [VerifierProgram.bind_eq]
    exact ((skel_verifyKeccakLayer logSteps step claim).bind fun c hc ↦
      ((skel_keccakLayers logSteps steps c).mono (by rw [hc]) fun _ h ↦ h.trans hc)).mono
      (by simp) fun _ h ↦ h

theorem skel_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    SkelP (keccakOpen logSteps claim first count value) skKeccakOpen fun _ ↦ True := by
  unfold keccakOpen
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_sumcheck 3 _ _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : List E × List E × E ↦ True) trivial).mono (by simp [skKeccakOpen])
    fun _ h ↦ h


theorem skel_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    SkelP (verifyKeccak logSteps inst output) (skKeccak logSteps) fun _ ↦ True := by
  have h1 : 1 < keccakSegments := by decide
  unfold verifyKeccak
  simp only [h1, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_require _).bind fun _ hreq ↦ (skel_grindProofOfWork _).bind fun _ _ ↦
    (skel_sampleChallenges _).bind fun seg hseg ↦
    (skel_sampleChallenges _).bind fun _ _ ↦ skel_readScalar.bind fun _ _ ↦
    ((skel_keccakLayers logSteps (List.range keccakDepth) _).mono
      (sk' := (List.range keccakDepth).flatMap fun _ ↦
        skKeccakLayer (logSteps - 4 + keccakSegmentBits))
      (by simp [keccakFirstClaim, hseg, hreq.1]) fun _ h ↦ h).bind fun claim _ ↦
    (skel_keccakOpen _ _ _ _ _).bind fun _ _ ↦ skel_readScalar.bind fun _ _ ↦
    (skel_require _).bind fun _ _ ↦ (skel_sumcheck 3 _ _).bind fun _ _ ↦
    (skel_keccakOpen _ _ _ _ _).bind fun _ _ ↦ (skel_readScalars kBits).bind fun _ _ ↦
    (skel_require _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : List ColumnClaim × List E × List E ↦ True) trivial).mono
    (by simp only [skKeccak, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil, List.map_replicate, Option.isSome_none]) fun _ h ↦ h

theorem skel_keccakValidity (layout : Layout) (link : LinkEnd) :
    SkelP (keccakValidity layout link) (skKeccak (layout.tableLogHeights.getD opKeccak 0))
      fun _ ↦ True := by
  unfold keccakValidity
  rcases link.columns.getD opKeccak ([], []) with ⟨point, values⟩
  simp only [VerifierProgram.bind_eq]
  exact ((skel_liftOption _).bind fun _ _ ↦ skel_verifyKeccak _ _ _).mono (by simp) fun _ h ↦ h

/-! ## The link -/

theorem nAccesses_eq : (tables.map (·.links.memory.length)).sum = nAccessesL := by decide +kernel

theorem nPointers_eq : (tables.map (·.links.pointers.length)).sum = nPointersL := by decide +kernel

theorem packedChallenges_eq (nRows width : ℕ) :
    packedChallenges tables nRows width = packedChallengesL nRows width := by
  unfold packedChallenges packedChallengesL
  rw [nAccesses_eq, nPointers_eq]

theorem skel_computedSplit (b : List K) (p : List E) (pc : List (ℕ × ℕ)) :
    SkelP (computedSplit b p pc) [] fun _ ↦ True := by
  unfold computedSplit
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_require _).bind fun _ _ ↦ SkelP.ret (Q := fun _ : Split ↦ True) trivial).mono
    (by simp) fun _ h ↦ h

theorem skel_verifyLink (layout : Layout) (ht : layout.tables = tables) :
    SkelP (verifyLink computedSplit layout) (skLink layout.lite) fun _ ↦ True := by
  unfold verifyLink
  rw [ht]
  rcases hc : Chunks.new (pointerWidth layout.logMemory layout.logBytecode
    (layout.tableRows.foldl (· + ·) 0)) with _ | chunks
  · simp only [hc, Verifier.liftOption, VerifierProgram.bind_eq]
    exact SkelP.fail _ _
  · simp only [skLink, chunksL, Layout.lite, hc, Verifier.liftOption, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq, VerifierProgram.ret_bind]
    exact ((skel_grindProofOfWork _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
      (skel_sampleChallengesPacked _).bind fun _ _ ↦ (skel_sumcheck 3 _ _).bind fun _ _ ↦
      skel_readScalar.bind fun _ _ ↦ (skel_sampleChallengesPacked 5).bind fun _ _ ↦
      (skel_computedSplit _ _ _).bind fun _ _ ↦ (skel_sumcheck _ _ _).bind fun _ _ ↦
      (skel_sumcheck _ _ _).bind fun _ _ ↦ (skel_readScalarsPacked _).bind fun _ _ ↦
      (skel_require _).bind fun _ _ ↦
      SkelP.ret (Q := fun _ : LinkEnd ↦ True) trivial).mono
      (by simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
        List.map_replicate, Option.isSome_none, packedChallenges_eq]; rfl)
      fun _ h ↦ h

/-! ## The body -/

theorem skel_frontProg (layout : Layout) (input : PublicInput) (ht : layout.tables = tables) :
    SkelP (frontProg layout input)
      (skLink layout.lite ++ [.sample] ++ skKeccak (layout.tableLogHeights.getD opKeccak 0))
      fun _ ↦ True := by
  unfold frontProg
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_verifyLink layout ht).bind fun _ _ ↦ (skel_bindPublicInput _ _).bind fun _ _ ↦
    (skel_keccakValidity _ _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E) ↦
      True) trivial).mono (by simp) fun _ h ↦ h

theorem skel_memoryTermClaim (layout : Layout) (link : LinkEnd) :
    SkelP (memoryTermClaim layout link) [] fun _ ↦ True := by
  unfold memoryTermClaim
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_liftOption _).bind fun _ _ ↦ (skel_liftOption _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : StackClaim ↦ True) trivial).mono (by simp) fun _ h ↦ h

/-- **The cut body's skeleton**, fixed by the layout's sizes and the rate. -/
theorem skel_veBodyCut (layout : Layout) (ρ : ℕ) (input : PublicInput)
    (ht : layout.tables = tables) :
    SkelP (veBodyCut layout ρ input) (skBody layout.lite ρ) fun _ ↦ True := by
  unfold veBodyCut
  simp only [VerifierProgram.bind_eq]
  exact ((skel_commitStack _ _).bind fun _ _ ↦ (skel_readOod _).bind fun _ _ ↦
    (skel_frontProg layout input ht).bind fun _ _ ↦ (skel_liftOption _).bind fun _ _ ↦
    (skel_ringSwitch _ _).bind fun _ _ ↦ (skel_memoryTermClaim _ _).bind fun _ _ ↦
    skel_verifyStackedOpeningCut _ _ _ _).mono
    (by simp [skBody, skBodyHead, Layout.lite, List.append_assoc]) fun _ h ↦ h

/-- **The announced sizes' skeleton**; their layout is built. -/
theorem skel_readAnnouncedSizes (bytecode : List K) :
    SkelP (readAnnouncedSizes bytecode) skSizes
      fun a ↦ ∃ lm rows, buildLayout bytecode lm rows = some a.1 := by
  unfold readAnnouncedSizes
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_readScalars _).bind fun _ _ ↦ (skel_require _).bind fun _ _ ↦
    (skel_require _).bind fun _ _ ↦ (skel_liftOption _).bind fun _ hl ↦
    (skel_require _).bind fun _ _ ↦
    SkelP.ret (Q := fun a : Layout × ℕ ↦ ∃ lm rows, buildLayout bytecode lm rows = some a.1)
      ⟨_, _, hl⟩).mono (by simp [skSizes]) fun _ h ↦ h

end
end LeanVM.Protocol.EndToEnd.Sound
