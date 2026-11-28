/-
  LeanVM.Prover.Complete.CostWalk

  The leanVM verifier program's events besides its stream, over every size the verifier accepts:
  a constant bound, its commitments at most `32` high and `128` wide.
-/

module

public import LeanVM.Prover.Complete.CostCalc

/-!
# The verifier program's other events

`sampLE_leanVmProgram`: `SampLE (leanVmVerifierProgram bytecode publicInput) leanVmSamples`,
the program walked phase by phase as `LeanVM.Wire.HonestShape` walks its stream, over the sizes
`readAnnouncedSizes` returns (`SizesOK`): the link's challenges (its packed draws at most `200`,
its sum-checks over at most `24` and `30` rounds), the Keccak reduction's (its point of at most
`27` coordinates), ring switching's, and the WHIR levels', decided over the admissible ladders
(`ladder_cost`: every fold at most `6`, so every commitment at most `128` wide).
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Verifier.Defers LeanVM.Wire

variable {α β : Type}

local notation "SL" => SampLE

/-! ## The WHIR ladders -/

/-- The events of the WHIR levels from a message of `μ` variables. -/
def whirSamples : ℕ → List Whir.Level → ℕ
  | _, [] => 0
  | μ, [level] => level.fold * 3 + 1 + level.queries + (μ - level.fold) * 2
  | μ, level :: next :: rest =>
    level.fold * 3 + 4 + (μ - level.fold) + level.queries + whirSamples (μ - level.fold) (next :: rest)

/-- The WHIR levels' events, at most. -/
def whirSamplesBound : ℕ := 4096

/-- Every level folds at most `6` variables. -/
def foldsLE : List Whir.Level → Bool
  | [] => true
  | level :: rest => decide (level.fold ≤ 6) && foldsLE rest

/-- **Every admissible ladder** folds at most `6` variables a level and has at most
`whirSamplesBound` events; decided over the admissible pairs. -/
theorem ladder_cost (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) :
    foldsLE levels = true ∧ whirSamples μ levels ≤ whirSamplesBound := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels →
          (foldsLE levels && decide (whirSamples μ levels ≤ whirSamplesBound)) = true := by
      decide +kernel
    have hk := key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2)
      hadm levels h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    exact hk
  · simp [Whir.ladder, hadm] at h

theorem foldsLE_head {level : Whir.Level} {rest : List Whir.Level}
    (h : foldsLE (level :: rest) = true) : level.fold ≤ 6 ∧ foldsLE rest = true := by
  simp only [foldsLE, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem width_le {f : ℕ} (h : f ≤ 6) : 2 * 2 ^ f ≤ 128 := by
  have : 2 ^ f ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) h
  omega

theorem width_le' {f : ℕ} (h : f ≤ 6) : 2 ^ f ≤ 128 := by
  have : 2 ^ f ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) h
  omega

/-! ## The WHIR levels -/

theorem foldRoundS (s : WhirState) : SL (foldRound s) 3 := by
  unfold foldRound
  exact SampLE.seq SampLE.readE (fun _ _ ↦ SampLE.seq SampLE.readE (fun _ _ ↦
    SampLE.seq SampLE.readE (fun _ _ ↦ SampLE.seq SampLE.readE (fun _ _ ↦
      SampLE.seq (SampLE.grindP _) (fun _ _ ↦ SampLE.seq SampLE.sampleE (fun _ _ ↦
        SampLE.seq SampLE.sampleE (fun _ _ ↦ trivial) (by omega)) (by omega))
        (by omega)) (Nat.zero_le _)) (Nat.zero_le _)) (Nat.zero_le _)) (Nat.zero_le _)

theorem foldRoundsS : ∀ (n : ℕ) (s : WhirState), SL (foldRounds n s) (n * 3)
  | 0, _ => trivial
  | n + 1, s => by
    unfold foldRounds
    refine SampLE.seq (foldRoundS s) (fun x _ ↦ ?_) (by omega)
    obtain ⟨s', round⟩ := x
    exact SampLE.seq (foldRoundsS n _) (fun y _ ↦ by obtain ⟨_, _⟩ := y; trivial) (by
      rw [Nat.succ_mul]; omega)

theorem sampleQueriesAuxS (depth : ℕ) : ∀ (fuel remaining : ℕ),
    SL (sampleQueriesAux depth fuel remaining) fuel
  | 0, _ => trivial
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    split
    · trivial
    · exact SampLE.seq SampLE.sampleE (fun _ _ ↦ SampLE.seq (sampleQueriesAuxS depth fuel _)
        (fun _ _ ↦ trivial) (by omega)) (by omega)

/-- **The WHIR levels' events.** -/
theorem whirLevelsS (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState),
      levelsWired (logN - s.alphas.length) levels = true → foldsLE levels = true →
      SL (whirLevels logN laneFolds evaluateBasis index levels s)
        (whirSamples (logN - s.alphas.length) levels)
  | [], _, _, _, _ => trivial
  | level :: rest, index, s, hw, hf => by
    simp only [levelsWired, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨-, hrest⟩ := hw
    obtain ⟨-, hfr⟩ := foldsLE_head hf
    unfold whirLevels
    cases rest with
    | nil =>
      simp only [whirSamples]
      refine SampLE.seq (foldRoundsS _ _) (fun r hr ↦ ?_) (by omega)
      obtain ⟨s', rounds⟩ := r
      have hf' := foldRounds_returns _ _ hr
      simp only at hf'
      have hmu : logN - s'.alphas.length = logN - s.alphas.length - level.fold := by omega
      refine SampLE.seq (SampLE.readN _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine SampLE.seq (SampLE.grindP _) (fun _ _ ↦ ?_) (by omega)
      refine SampLE.seq (sampleQueriesAuxS _ _ _) (fun _ _ ↦ ?_) (by omega)
      refine SampLE.seq (SampLE.queryP _ _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine SampLE.seq (SampLE.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine SampLE.seq (SampLE.sumcheckP 3 _ _) (fun r _ ↦ ?_) ?_
      · exact (SampLE.require _).mono (Nat.zero_le _)
      · rw [List.length_replicate, hmu]; omega
    | cons next rest' =>
      obtain ⟨hnf, -⟩ := foldsLE_head hfr
      simp only [levelsWired, Bool.and_eq_true, decide_eq_true_eq] at hrest
      obtain ⟨⟨hq1, hq2, hd1, hd2⟩, hrest'⟩ := hrest
      simp only [whirSamples]
      refine SampLE.seq (foldRoundsS _ _) (fun r hr ↦ ?_) (by omega)
      obtain ⟨s', rounds⟩ := r
      have hf' := foldRounds_returns _ _ hr
      simp only at hf'
      have hmu : logN - s'.alphas.length = logN - s.alphas.length - level.fold := by omega
      simp only [levelShape]
      refine SampLE.seq (SampLE.commitP (h := logN - s'.alphas.length - next.fold +
        next.logInvRate) (by rw [hmu]; unfold wireMaxHeight at hd2; unfold commitMaxHeight; omega)
        (by unfold commitMaxWidth; exact width_le hnf))
        (fun _ _ ↦ ?_) (by omega)
      refine SampLE.seq (SampLE.readN _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine SampLE.seq (SampLE.grindP _) (fun _ _ ↦ ?_) (by omega)
      refine SampLE.seq (SampLE.sampleN _) (fun _ _ ↦ ?_) (by rw [hmu]; omega)
      refine SampLE.seq SampLE.readE (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine SampLE.seq (SampLE.grindP _) (fun _ _ ↦ ?_) (by rw [hmu]; omega)
      refine SampLE.seq (sampleQueriesAuxS _ _ _) (fun _ _ ↦ ?_) (by rw [hmu]; omega)
      refine SampLE.seq SampLE.sampleE (fun _ _ ↦ ?_) (by rw [hmu]; omega)
      refine SampLE.seq (SampLE.queryP _ _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine (whirLevelsS logN laneFolds evaluateBasis (next :: rest') (index + 1) _ ?_ hfr).mono ?_
      · rw [glueLevel_alphas, hmu]
        simp only [levelsWired, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hq1, hq2, hd1, hd2⟩, hrest'⟩
      · rw [glueLevel_alphas, hmu]
        omega

/-- The stack's commitment: the first level's height and width. -/
theorem commitStackS (μ r : ℕ) : SL (commitStack μ r) 1 := by
  unfold commitStack
  refine SampLE.seq (SampLE.liftOptionP _) (fun config hc ↦ ?_) (Nat.zero_le _)
  have hc := returnsAny_liftOption hc
  cases config with
  | nil => trivial
  | cons level rest =>
    obtain ⟨-, hlw, -⟩ := ladder_wire _ _ _ hc
    obtain ⟨hf, -⟩ := ladder_cost _ _ _ hc
    obtain ⟨hf0, -⟩ := foldsLE_head hf
    simp only [levelsWired, Bool.and_eq_true, decide_eq_true_eq] at hlw
    obtain ⟨⟨-, -, -, hd2⟩, -⟩ := hlw
    exact SampLE.commitP (by unfold wireMaxHeight at hd2; unfold commitMaxHeight; exact hd2)
      (by unfold commitMaxWidth; exact width_le' hf0)

/-- The stacked opening's events. -/
theorem verifyStackedOpeningS (μ r : ℕ) (claims : List StackClaim) (batching : E) :
    SL (verifyStackedOpening μ r claims batching) whirSamplesBound := by
  unfold verifyStackedOpening
  refine SampLE.seq (SampLE.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  unfold verifyWhir
  refine SampLE.seq (SampLE.liftOptionP _) (fun config hc ↦ ?_) (Nat.zero_le _)
  have hc := returnsAny_liftOption hc
  obtain ⟨-, hlw, -⟩ := ladder_wire _ _ _ hc
  obtain ⟨hf, hst⟩ := ladder_cost _ _ _ hc
  exact (whirLevelsS _ _ _ config 0 ⟨_, [], []⟩ (by simpa using hlw) hf).mono (by simpa using hst)

/-! ## The other phases -/

theorem readSizesS (bytecode : List K) : SL (readAnnouncedSizes bytecode) 0 := by
  unfold readAnnouncedSizes
  exact SampLE.seq (SampLE.readN _) (fun _ _ ↦ SampLE.seq (SampLE.require _) (fun _ _ ↦
    SampLE.seq (SampLE.require _) (fun _ _ ↦ SampLE.seq (SampLE.liftOptionP _) (fun _ _ ↦
      SampLE.seq (SampLE.require _) (fun _ _ ↦ trivial) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl

theorem readOodS (stackLog : ℕ) : SL (readOod stackLog) (1 + stackLog) := by
  unfold readOod
  exact SampLE.seq (SampLE.grindP _) (fun _ _ ↦ SampLE.seq (SampLE.sampleN _) (fun _ _ ↦
    SampLE.seq SampLE.readE (fun _ _ ↦ trivial) (Nat.zero_le _)) (by omega)) (by omega)

theorem packedChallenges_le {layout : Layout} (hs : SizesOK layout) {nRows width : ℕ}
    (hr : nRows ≤ 30) (hw : width ≤ 24) : packedChallenges layout.tables nRows width ≤ 200 := by
  have hd : ((Chunks.new width).map Chunks.d).getD 0 ≤ 25 := by
    rcases hc : Chunks.new width with _ | c
    · simp
    · simpa using (Chunks.new_le hc).2
  have h1 : (tables.map (·.links.memory.length)).sum = 39 := by decide
  have h2 : (tables.map (·.links.pointers.length)).sum = 33 := by decide
  have h3 : bytecodeSlotBits = 4 := by decide
  unfold packedChallenges
  rw [hs.tables_eq, h1, h2, h3]
  simp only [nTables]
  omega

/-- The link's prefix's events. -/
theorem linkPreS {layout : Layout} (hs : SizesOK layout) : SL (linkPre layout) 256 := by
  have hrows : layout.tableLogHeights.foldl max 0 ≤ 30 := foldl_max_le hs.heights_le 0 (by omega)
  unfold linkPre
  refine SampLE.seq (SampLE.liftOptionP _) (fun chunks hc ↦ ?_) (Nat.zero_le _)
  have hw := (Chunks.new_le (returnsAny_liftOption hc)).1
  unfold maxPointerWidth at hw
  refine SampLE.seq (SampLE.grindP _) (fun _ _ ↦ ?_) (by omega)
  refine SampLE.seq SampLE.sampleE (fun _ _ ↦ ?_) (by omega)
  have hp := packedChallenges_le hs hrows hw
  refine SampLE.seq (SampLE.samplePackedP _) (fun _ _ ↦ ?_) (by omega)
  refine SampLE.seq (SampLE.sumcheckP 3 _ _) (fun _ _ ↦ ?_) ?_
  · refine SampLE.seq SampLE.readE (fun _ _ ↦ ?_) (Nat.zero_le _)
    refine SampLE.seq (SampLE.samplePackedP _) (fun _ _ ↦ trivial) ?_
    simp only [List.length_replicate]; omega
  · simp only [List.length_replicate]; omega

/-- The link's suffix's events. -/
theorem linkSufOfS {layout : Layout} (hs : SizesOK layout) (y : LinkPre) (ps : E × E) :
    SL (linkSufOf layout y ps) 128 := by
  have hrows : layout.tableLogHeights.foldl max 0 ≤ 30 := foldl_max_le hs.heights_le 0 (by omega)
  have hq : log2Ceil ((layout.tables.map (·.links.pointers)).map List.length).sum = 6 := by
    rw [hs.tables_eq]; decide
  obtain ⟨p1, p2⟩ := ps
  unfold linkSufOf
  refine SampLE.seq (SampLE.sumcheckP _ _ _) (fun _ _ ↦ ?_) ?_
  · refine SampLE.seq (SampLE.sumcheckP _ _ _) (fun _ _ ↦ ?_) ?_
    · refine SampLE.seq (SampLE.readPackedP _) (fun _ _ ↦ ?_) ?_
      · exact SampLE.seq (SampLE.require _) (fun _ _ ↦ trivial) (Nat.zero_le _)
      · simp only [List.length_replicate, hq] at hrows ⊢; omega
    · simp only [List.length_replicate, hq] at hrows ⊢; omega
  · simp only [List.length_replicate] at hrows ⊢; omega

theorem computedSplitS (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ)) :
    SL (computedSplit bytecode point pc) 0 := by
  unfold computedSplit
  exact SampLE.seq (SampLE.require _) (fun _ _ ↦ trivial) le_rfl

theorem bindPublicInputS (layout : Layout) (publicInput : Digest) :
    SL (bindPublicInput layout publicInput) 1 := by
  unfold bindPublicInput
  exact SampLE.seq SampLE.sampleE (fun _ _ ↦ SampLE.seq (SampLE.liftOptionP _)
    (fun _ _ ↦ trivial) (Nat.zero_le _)) le_rfl

/-- One Keccak layer's events, at a point of `L` coordinates. -/
def keccakLayerSamples (L : ℕ) : ℕ := 4 + L * 2 + keccakLocalBits * 2

theorem verifyKeccakLayerS (logSteps step : ℕ) (claim : KeccakClaim) :
    SL (verifyKeccakLayer logSteps step claim) (keccakLayerSamples claim.point.length) := by
  unfold verifyKeccakLayer
  refine SampLE.seq (SampLE.readN _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine SampLE.seq (SampLE.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine SampLE.seq (SampLE.grindP _) (fun _ _ ↦ ?_) (by unfold keccakLayerSamples; omega)
  refine SampLE.seq SampLE.sampleE (fun _ _ ↦ ?_) (by unfold keccakLayerSamples; omega)
  refine SampLE.seq (SampLE.sumcheckP 3 _ _) (fun r _ ↦ ?_) ?_
  · obtain ⟨point, value⟩ := r
    refine SampLE.seq (SampLE.sumcheckP 4 _ _) (fun r _ ↦ ?_) ?_
    · obtain ⟨localPoint, value⟩ := r
      refine SampLE.seq (SampLE.readN 3) (fun _ _ ↦ ?_) (Nat.zero_le _)
      exact SampLE.seq (SampLE.require _) (fun _ _ ↦ SampLE.seq (SampLE.grindP _)
        (fun _ _ ↦ SampLE.seq SampLE.sampleE (fun _ _ ↦ trivial) (by
          simp only [List.length_map, List.length_replicate, keccakLayerSamples]; omega)) (by
          simp only [List.length_map, List.length_replicate, keccakLayerSamples]; omega))
        (Nat.zero_le _)
    · simp only [List.length_map, List.length_replicate, keccakLayerSamples]; omega
  · simp only [List.length_map, keccakLayerSamples]; omega

theorem keccakLayersS (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    SL (keccakLayers logSteps steps claim) (steps.length * keccakLayerSamples claim.point.length)
  | [], _ => trivial
  | s :: ss, claim => by
    refine SampLE.seq (verifyKeccakLayerS logSteps s claim) (fun c hc ↦ ?_) ?_
    · rw [show (s :: ss).length * keccakLayerSamples claim.point.length -
        keccakLayerSamples claim.point.length = ss.length * keccakLayerSamples c.point.length by
        rw [verifyKeccakLayer_point hc, List.length_cons, Nat.succ_mul, Nat.add_sub_cancel]]
      exact keccakLayersS logSteps ss c
    · simp only [List.length_cons, Nat.succ_mul]; omega

theorem keccakOpenS (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    SL (keccakOpen logSteps claim first count value) 12 := by
  unfold keccakOpen
  exact SampLE.seq (SampLE.sumcheckP 3 _ _) (fun _ _ ↦ trivial)
    (by simp only [List.length_replicate, show qkeccakSlotBits = 6 by decide]; omega)

/-- `KECCAK`'s reduction's events, at most. -/
def keccakSamples : ℕ := 1 + 6 + 12 * keccakLayerSamples 27 + 12 + 8 + 12

theorem verifyKeccakS (logSteps : ℕ) (inst output : List E) (hl : logSteps ≤ 30) :
    SL (verifyKeccak logSteps inst output) keccakSamples := by
  have h1 : 1 < keccakSegments := by decide
  have hseg : keccakSegmentBits = 1 := by decide
  have hlane : keccakLaneBits = 5 := by decide
  have hk : keccakSamples = 7 + 12 * keccakLayerSamples 27 + 32 := by
    unfold keccakSamples; omega
  unfold verifyKeccak
  simp only [h1, ↓reduceIte]
  refine SampLE.seq (SampLE.require _) (fun _ hreq ↦ ?_) (Nat.zero_le _)
  have hreq := VerifierProgram.returnsAny_require hreq
  refine SampLE.seq (SampLE.grindP _) (fun _ _ ↦ ?_) (by rw [hk]; omega)
  refine SampLE.seq (SampLE.sampleN _) (fun segment hs ↦ ?_) (by rw [hk, hseg]; omega)
  have hs := returns_sampleN hs
  refine SampLE.seq (SampLE.sampleN _) (fun lanePoint _ ↦ ?_) (by rw [hk, hseg, hlane]; omega)
  refine SampLE.seq SampLE.readE (fun committed _ ↦ ?_) (Nat.zero_le _)
  have hL : (keccakFirstClaim inst segment lanePoint output committed).point.length ≤ 27 := by
    simp only [keccakFirstClaim, List.length_append, List.length_drop, hs, hseg]
    omega
  have hlay : keccakDepth * keccakLayerSamples
      (keccakFirstClaim inst segment lanePoint output committed).point.length ≤
        12 * keccakLayerSamples 27 := by
    refine Nat.mul_le_mul (by decide) ?_
    unfold keccakLayerSamples
    omega
  refine SampLE.seq (keccakLayersS logSteps (List.range keccakDepth) _) (fun claim _ ↦ ?_) ?_
  · refine SampLE.seq (keccakOpenS _ _ _ _ _) (fun _ _ ↦ ?_) ?_
    · refine SampLE.seq SampLE.readE (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine SampLE.seq (SampLE.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine SampLE.seq (SampLE.pure' _ 0) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine SampLE.seq (SampLE.sumcheckP 3 _ _) (fun _ _ ↦ ?_) ?_
      · refine SampLE.seq (keccakOpenS _ _ _ _ _) (fun _ _ ↦ ?_) ?_
        · exact SampLE.seq (SampLE.readN _) (fun _ _ ↦ SampLE.seq (SampLE.require _)
            (fun _ _ ↦ trivial) (Nat.zero_le _)) (Nat.zero_le _)
        · rw [List.length_range, hk, hseg, hlane] at *
          rw [List.length_replicate]; omega
      · rw [List.length_range, hk, hseg, hlane] at *; rw [List.length_replicate]; omega
    · rw [List.length_range, hk, hseg, hlane] at *; omega
  · rw [List.length_range, hk, hseg, hlane]
    omega

theorem keccakValidityS {layout : Layout} (hs : SizesOK layout) (link : LinkEnd) :
    SL (keccakValidity layout link) keccakSamples := by
  have hl : layout.tableLogHeights.getD opKeccak 0 ≤ 30 := by
    rw [List.getD_eq_getElem?_getD]
    rcases he : layout.tableLogHeights[opKeccak]? with _ | x
    · simp
    · exact hs.heights_le x (List.mem_of_getElem? he)
  unfold keccakValidity
  exact SampLE.seq (SampLE.liftOptionP _) (fun _ _ ↦ verifyKeccakS _ _ _ hl) (Nat.zero_le _)

theorem ringSwitchS (claims : List RingClaim) : SL (ringSwitch claims) 20 := by
  unfold ringSwitch
  refine SampLE.seq (SampLE.grindP _) (fun _ _ ↦ SampLE.seq (SampLE.samplePackedP _)
    (fun _ _ ↦ trivial) ?_) (by omega)
  simp only [ringMapWidth]
  split <;> omega

theorem memoryTermClaimS (layout : Layout) (link : LinkEnd) :
    SL (memoryTermClaim layout link) 0 := by
  unfold memoryTermClaim
  exact SampLE.seq (SampLE.liftOptionP _) (fun _ _ ↦ SampLE.seq (SampLE.liftOptionP _)
    (fun _ _ ↦ trivial) le_rfl) le_rfl

/-! ## The whole program -/

/-- The leanVM verifier program's events besides its stream, at most. -/
def leanVmSamples : ℕ := 1 + 31 + 256 + 128 + 1 + keccakSamples + 20 + whirSamplesBound

theorem execPreS (bytecode : List K) :
    SL (execPre bytecode) (1 + 31 + 256) := by
  unfold execPre
  refine SampLE.seq (readSizesS bytecode) (fun sizes hsz ↦ ?_) (Nat.zero_le _)
  have hok := (readSizes_ok hsz).1
  refine SampLE.seq (commitStackS _ _) (fun _ _ ↦ ?_) (by omega)
  have hst := hok.stack_le
  unfold Whir.maxLogStack at hst
  refine SampLE.seq (readOodS _) (fun _ _ ↦ ?_) (by omega)
  exact SampLE.seq (linkPreS hok) (fun _ _ ↦ trivial) (by omega)

theorem execSufS (publicInput : Digest) (z : ExecPre) (split : Split) (hsz : SizesOK z.layout) :
    SL (execSuf publicInput z split) (128 + 1 + keccakSamples + 20 + whirSamplesBound) := by
  unfold execSuf linkSuf
  refine SampLE.seq (linkSufOfS hsz _ _) (fun link _ ↦ ?_) (by omega)
  refine SampLE.seq (bindPublicInputS _ _) (fun _ _ ↦ ?_) (by omega)
  refine SampLE.seq (keccakValidityS hsz _) (fun x _ ↦ ?_) (by omega)
  obtain ⟨outputs, keccakPoint, keccakSlices⟩ := x
  refine SampLE.seq (SampLE.liftOptionP _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine SampLE.seq (ringSwitchS _) (fun x _ ↦ ?_) (by omega)
  obtain ⟨ring, batching⟩ := x
  refine SampLE.seq (memoryTermClaimS _ _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  exact (verifyStackedOpeningS _ _ _ _).mono (by omega)

/-- **The leanVM verifier program's events besides its stream**: at most `leanVmSamples`, its
commitments at most `32` high and `128` wide. -/
theorem sampLE_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    SampLE (leanVmVerifierProgram bytecode publicInput) leanVmSamples := by
  rw [leanVmVerifierProgram_eq, verifyExecution_split]
  refine (SampLE.bind (a := leanVmSamples) (b := 0) (f := fun _ ↦ VerifierProgram.ret true) ?_
    fun _ _ ↦ trivial).mono (by omega)
  refine SampLE.seq (execPreS bytecode) (fun z hz ↦ ?_) (by unfold leanVmSamples; omega)
  have hsz : SizesOK z.layout := by
    unfold execPre at hz
    obtain ⟨sizes, hs, h⟩ := VerifierProgram.returnsAny_bind hz
    obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
    obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
    obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
    rw [VerifierProgram.returnsAny_ret h]
    exact (readSizes_ok hs).1
  refine SampLE.seq (computedSplitS _ _ _) (fun split _ ↦ ?_) (Nat.zero_le _)
  exact (execSufS publicInput z split hsz).mono (by unfold leanVmSamples; omega)

end LeanVM.Prover.Complete.Cost

end
