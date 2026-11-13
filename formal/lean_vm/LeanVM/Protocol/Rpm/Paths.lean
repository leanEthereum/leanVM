/-
  LeanVM.Protocol.Rpm.Paths

  The Keccak-256 evaluations a transcript holds (`keccakEvaluationsOfTranscript`, `Statement/LeanVm.lean`,
  on lane states) are `common`'s (`Common.pathsOf`, on byte states) read on lanes.
-/

module

public import Common.Lanes
public import Statement.LeanVm
public import LeanVM.Protocol.WithHash

@[expose] public section

/-!
# The transcript's paths on lanes and on bytes

`Statement/LeanVm.lean` replays a transcript on lane states (`TranscriptReplay.step`): a chain's state
carries the bytes its path absorbed, a capacity is lanes `17 … 24`, a block the bytes of the
rates' XOR, a path's message the one Keccak-256's padding (`padded`) takes to its bytes (`unpad`).
`common` replays it on byte states (`Common.replayStep`: a chain carries its blocks, a capacity
is bytes `136 … 199`, the message `keccakUnpad`'s). The two bookkeepings correspond step by step
(`step_replayOf`), so the paths are the same, the digests read on lanes
(`transcriptPaths_eq`).
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- The simulator's bookkeeping on byte states. -/
abbrev KSimB := Common.SimState Common.DigestBytes Common.KRest Common.KCap

/-- **The sponge paths a transcript holds, on bytes**: `common`'s bookkeeping (`Common.pathsOf`)
replayed on the bytes of the transcript's states. -/
def transcriptPathsB (T : PermutationTranscript) : List (Bytes × Common.DigestBytes) :=
  Common.pathsOf Common.keccakPadding Common.KState.zero
    (T.map fun e ↦ (permQueryToRpm e.1, KState.toRpm e.2))

/-- The evaluation of `x` among byte paths, its digest read on lanes. -/
def hashesOfB (P : List (Bytes × Common.DigestBytes)) (x : Bytes) : Option Digest :=
  (P.find? (·.1 = x)).map fun p ↦ Digest.ofRpm p.2

/-! ## Bytes and lanes of a state -/

theorem leLane_congr {l l' : List UInt8} {i : ℕ}
    (h : ∀ k < 8, l.getD (8 * i + k) 0 = l'.getD (8 * i + k) 0) : littleEndianLane l i =
        littleEndianLane l' i := by
  unfold littleEndianLane
  refine List.foldl_ext _ _ _ fun a k hk ↦ ?_
  simp only [List.mem_range] at hk
  rw [h k hk]

theorem getD_toBytes_cap (s : Common.KState) (j : ℕ) (hj : j < 64) :
    s.toBytes.getD (136 + j) 0 = s.2[j] := by
  rw [Common.KState.toBytes, List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_append_right (by simp)]
  simp

/-- **Two lane states share their bytes' capacity iff they share lanes `17 … 24`.** -/
theorem cap_toRpm_iff (a b : KeccakState) :
    (KState.toRpm a).2 = (KState.toRpm b).2 ↔ a.toList.drop 17 = b.toList.drop 17 := by
  constructor
  · intro h
    have hl : ∀ i (hi : 17 ≤ i) (hi' : i < 25), a[i] = b[i] := by
      intro i hi hi'
      have ea : a[i] = littleEndianLane (KState.toRpm a).toBytes i := by
        conv_lhs => rw [← ofRpm_toRpm a]
        simp [KState.ofRpm]
      have eb : b[i] = littleEndianLane (KState.toRpm b).toBytes i := by
        conv_lhs => rw [← ofRpm_toRpm b]
        simp [KState.ofRpm]
      rw [ea, eb]
      refine leLane_congr fun k hk ↦ ?_
      rw [show 8 * i + k = 136 + (8 * i + k - 136) by omega, getD_toBytes_cap _ _ (by omega),
        getD_toBytes_cap _ _ (by omega), h]
    refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
    simp only [List.getElem_drop, Vector.getElem_toList]
    simp only [List.length_drop, Vector.length_toList] at h1
    exact hl (17 + j) (by omega) (by omega)
  · intro h
    refine Vector.ext fun j hj ↦ ?_
    rw [toRpm_snd _ _ hj, toRpm_snd _ _ hj]
    have e : a[(136 + j) / 8] = b[(136 + j) / 8] := by
      have := congrArg (fun l : List UInt64 ↦ l[(136 + j) / 8 - 17]?) h
      simp only [List.getElem?_drop, Vector.getElem?_toList] at this
      rw [show 17 + ((136 + j) / 8 - 17) = (136 + j) / 8 by omega] at this
      simpa [Vector.getElem?_eq_getElem (show (136 + j) / 8 < 25 by omega)] using this
    rw [e]

/-- Byte `j` of the block that takes `toRpm s` to `toRpm x`: the XOR of their bytes `j`. -/
theorem toBytes_blockTo_getD (s x : KeccakState) (j : ℕ) (hj : j < 136) :
    (Common.KBlock.toBytes (Common.blockTo (KState.toRpm s) (KState.toRpm x))).getD j 0 =
      (wordBytes (s[j / 8]'(by omega))).getD (j % 8) 0 ^^^
        (wordBytes (x[j / 8]'(by omega))).getD (j % 8) 0 := by
  simp only [Common.KBlock.toBytes, Common.blockTo, Common.rxor]
  by_cases hj' : j < 32
  · rw [List.getD_append _ _ _ _ (by simpa using hj'), List.getD_eq_getElem _ _ (by simpa using hj'),
      Vector.getElem_toList]
    change (Vector.zipWith (· ^^^ ·) (KState.toRpm s).1.1 (KState.toRpm x).1.1)[j] = _
    rw [Vector.getElem_zipWith, toRpm_fst_fst _ _ hj', toRpm_fst_fst _ _ hj']
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [Vector.length_toList]
    rw [List.getD_eq_getElem _ _ (by simp; omega), Vector.getElem_toList]
    change (Vector.zipWith (· ^^^ ·) (KState.toRpm s).1.2 (KState.toRpm x).1.2)[j - 32] = _
    rw [Vector.getElem_zipWith, toRpm_fst_snd _ _ (by omega), toRpm_fst_snd _ _ (by omega)]
    simp only [show 32 + (j - 32) = j by omega]

/-- The bytes of the block that takes `toRpm s` to `toRpm x`: the bytes of their rates' XOR. -/
theorem toBytes_blockTo (s x : KeccakState) :
    Common.KBlock.toBytes (Common.blockTo (KState.toRpm s) (KState.toRpm x)) =
      (List.range 17).flatMap fun i ↦ wordBytes (Keccak.lane s i ^^^ Keccak.lane x i) := by
  have hr : ((List.range 17).flatMap fun i ↦ wordBytes (Keccak.lane s i ^^^ Keccak.lane x i)) =
      lanesBytes ((List.range 17).map fun i ↦ Keccak.lane s i ^^^ Keccak.lane x i) := by
    simp [lanesBytes, List.flatMap_map]
  rw [hr]
  refine List.ext_getElem (by simp [Common.KBlock.toBytes]) fun j h1 h2 ↦ ?_
  have hj : j < 136 := by simpa using h2
  rw [← List.getD_eq_getElem _ (0 : UInt8) h1, ← List.getD_eq_getElem _ (0 : UInt8) h2,
    toBytes_blockTo_getD s x j hj, getD_lanesBytes _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [lane_eq_getElem s _ (by omega), lane_eq_getElem x _ (by omega),
    wordBytes_xor_getD _ _ _ (by omega)]

/-- The digest of a path's last state: its first four lanes are the digest bytes read on lanes. -/
theorem digest_ofRpm (s : Common.KState) :
    (#v[(KState.ofRpm s)[0], (KState.ofRpm s)[1], (KState.ofRpm s)[2], (KState.ofRpm s)[3]] :
      Digest) = Digest.ofRpm s.1.1 := by
  have e : ∀ i (hi : i < 4), (KState.ofRpm s)[i] = littleEndianLane s.1.1.toList i := by
    intro i hi
    rw [KState.ofRpm, Vector.getElem_ofFn]
    show littleEndianLane (s.1.1.toList ++ s.1.2.toList ++ s.2.toList) i = _
    rw [List.append_assoc, leLane_append_left _ _ _ (by simp only [Vector.length_toList]; omega)]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
  rfl

/-! ## The padding -/

theorem length_padded (m : Bytes) : (keccakPadded m).length = 136 * (m.length / 136 + 1) := by
  simp only [keccakPadded, rate, List.length_append, List.length_take]
  rw [length_padBlock _ (by simp only [List.length_drop]; omega)]
  rw [Nat.min_eq_left (Nat.mul_div_le _ _)]
  ring

/-- Keccak-256's padded bytes are `padded`. -/
theorem keccakPadBytes_eq_padded (m : Bytes) : Common.keccakPadBytes m = keccakPadded m := by
  induction h : m.length / 136 generalizing m with
  | zero =>
    have hl : m.length < 136 := by omega
    rw [keccakPadBytes_eq_padBlock m hl]
    simp [keccakPadded, rate, h]
  | succ n ih =>
    have hl : 136 ≤ m.length := by omega
    have hd : (m.drop 136).length / 136 = n := by rw [List.length_drop]; omega
    rw [keccakPadBytes_of_le m hl, ih _ hd]
    simp only [keccakPadded, rate, h, hd]
    rw [show 136 * (n + 1) = 136 + 136 * n by ring, List.take_add, List.drop_drop,
      List.append_assoc]

theorem padded_injective : Function.Injective keccakPadded := fun m m' h ↦ by
  have := congrArg Common.stripPad h
  rwa [← keccakPadBytes_eq_padded, ← keccakPadBytes_eq_padded, Common.stripPad_keccakPadBytes,
    Common.stripPad_keccakPadBytes] at this

theorem padBlock_take (rest : Bytes) (h : rest.length < 136) :
    (padBlock rest).take rest.length = rest := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take]
  split_ifs with hj
  · simp [padBlock, List.getElem?_append_left hj,
      show rest.length ≠ j by omega, show (136 : ℕ) - 1 ≠ j by omega, rate]
  · rw [List.getElem?_eq_none (by omega)]

theorem padded_prefix (m : Bytes) : (keccakPadded m).take m.length = m := by
  have hk : 136 * (m.length / 136) ≤ m.length := Nat.mul_div_le _ _
  simp only [keccakPadded, rate]
  rw [List.take_append, List.take_of_length_le (by simp), List.length_take,
    Nat.min_eq_left hk,
    show m.length - 136 * (m.length / 136) = (m.drop (136 * (m.length / 136))).length by simp,
    padBlock_take _ (by simp; omega), List.take_append_drop]

/-- **The decoder of `padded`.** -/
theorem unpad_eq_some_iff (bs m : Bytes) : keccakUnpadded bs = some m ↔ keccakPadded m = bs := by
  constructor
  · intro h
    have := List.find?_some h
    simpa using this
  · intro h
    have hlen := length_padded m
    rw [h] at hlen
    have hmem : m ∈ (List.range rate).map fun k ↦ bs.take (bs.length - 1 - k) := by
      refine List.mem_map.mpr ⟨bs.length - 1 - m.length, List.mem_range.mpr ?_, ?_⟩
      · simp only [rate]
        have : m.length < bs.length := by rw [hlen]; omega
        have : bs.length ≤ m.length + 136 := by rw [hlen]; omega
        omega
      · have : m.length < bs.length := by rw [hlen]; omega
        rw [show bs.length - 1 - (bs.length - 1 - m.length) = m.length by omega, ← h,
          padded_prefix]
    obtain ⟨m', hm'⟩ : ∃ m', keccakUnpadded bs = some m' :=
      Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨m, hmem, by simp [h]⟩)
    have h' := List.find?_some hm'
    simp only [decide_eq_true_eq] at h'
    rw [hm', Option.some_inj]
    exact padded_injective (h'.trans h.symm)

theorem ofBytes_toBytes_block (B : Common.KBlock) : Common.KBlock.ofBytes B.toBytes = B := by
  obtain ⟨a, b⟩ := B
  simp only [Common.KBlock.ofBytes, Common.KBlock.toBytes, Prod.mk.injEq]
  refine ⟨Vector.ext fun i hi ↦ ?_, Vector.ext fun i hi ↦ ?_⟩ <;> simp only [Vector.getElem_ofFn]
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simpa using hi)]
    simp
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp)]
    simp

theorem toBlocks_blocksToBytes (β : List Common.KBlock) :
    Common.toBlocks (Common.blocksToBytes β) = β := by
  induction β with
  | nil => simp [Common.blocksToBytes, Common.toBlocks]
  | cons B β ih =>
    have hB : B.toBytes.length = 136 := by simp [Common.KBlock.toBytes]
    simp only [Common.blocksToBytes, List.flatMap_cons] at ih ⊢
    rw [toBlocks_of_le _ (by simp [hB]), List.take_left' hB, List.drop_left' hB,
      ofBytes_toBytes_block, ih]

/-- **The decoder on bytes is `common`'s on blocks.** -/
theorem unpad_blocksToBytes (β : List Common.KBlock) :
    keccakUnpadded (Common.blocksToBytes β) = Common.keccakUnpad β := by
  refine Option.ext fun m ↦ ?_
  rw [unpad_eq_some_iff]
  have hc := Common.Padding.unpad_eq_some_iff (P := Common.keccakPadding) β m
  change Common.keccakUnpad β = some m ↔ Common.keccakPad m = β at hc
  rw [hc, Common.keccakPad, keccakPadBytes_eq_padded]
  constructor
  · intro h
    rw [h, toBlocks_blocksToBytes]
  · intro h
    rw [← h, Common.blocksToBytes_toBlocks _ (by rw [length_padded]; omega)]

/-! ## The two bookkeepings -/

/-- The byte bookkeeping read on lanes: edges and chains' states on lanes, blocks as bytes. -/
def replayOf (σ : KSimB) : TranscriptReplay :=
  ⟨projLog σ.edges, σ.chains.map fun p ↦ (KState.ofRpm p.1, Common.blocksToBytes p.2)⟩

/-- **One step of the lane bookkeeping is one step of the byte bookkeeping, read on lanes.** -/
theorem step_replayOf (σ : KSimB) (e : Common.PermutationQuery KeccakState × KeccakState) :
    TranscriptReplay.step (replayOf σ) e =
      replayOf (Common.replayStep σ (permQueryToRpm e.1, KState.toRpm e.2)) := by
  obtain ⟨q, y⟩ := e
  cases q with
  | forward x =>
    have hl := fwdLookup_logMap stateEquiv σ.edges x
    simp only [stateEquiv_apply] at hl
    simp only [TranscriptReplay.step, replayOf, permQueryToRpm, Common.replayStep, projLog, hl]
    rcases hf : Common.forwardLookup σ.edges (KState.toRpm x) with _ | z
    · simp only [Option.map_none, List.find?_map]
      have hP : ((fun p : KeccakState × Bytes ↦ decide (p.1.toList.drop 17 = x.toList.drop 17)) ∘
          fun p : Common.KState × List Common.KBlock ↦ (KState.ofRpm p.1, Common.blocksToBytes p.2)) =
            fun p ↦ decide (p.1.2 = (KState.toRpm x).2) := by
        funext p
        simp only [Function.comp_apply, decide_eq_decide]
        rw [← cap_toRpm_iff, toRpm_ofRpm]
      rw [hP]
      unfold Common.chainOf
      rcases hc : σ.chains.find? (fun p ↦ decide (p.1.2 = (KState.toRpm x).2)) with _ | ⟨s, β⟩
      · simp [hc, logMap, ofRpm_toRpm]
      · simp only [hc, Option.map_some, logMap, List.map_cons, stateEquiv_symm_apply, ofRpm_toRpm,
          Common.blocksToBytes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        rw [← toBytes_blockTo (KState.ofRpm s) x, toRpm_ofRpm]
    · simp
  | inverse y' =>
    have hl := invLookup_logMap stateEquiv σ.edges y'
    simp only [stateEquiv_apply] at hl
    simp only [TranscriptReplay.step, replayOf, permQueryToRpm, Common.replayStep, projLog, hl]
    rcases hf : Common.inverseLookup σ.edges (KState.toRpm y') with _ | z
    · simp [logMap, ofRpm_toRpm]
    · simp

theorem foldl_replayOf (T : PermutationTranscript) (σ : KSimB) :
    T.foldl TranscriptReplay.step (replayOf σ) =
      replayOf ((T.map fun e ↦ (permQueryToRpm e.1, KState.toRpm e.2)).foldl
        Common.replayStep σ) := by
  induction T generalizing σ with
  | nil => rfl
  | cons e T ih =>
    simp only [List.foldl_cons, List.map_cons, step_replayOf, ih]

theorem replayOf_init :
    replayOf (Common.SimState.init Common.KState.zero) = ⟨[], [(Vector.replicate 25 0, [])]⟩ := by
  simp [replayOf, Common.SimState.init, projLog, logMap, ofRpm_zero, Common.blocksToBytes]

theorem foldl_replay (T : PermutationTranscript) :
    T.foldl TranscriptReplay.step ⟨[], [(Vector.replicate 25 0, [])]⟩ =
      replayOf (Common.replay Common.KState.zero
        (T.map fun e ↦ (permQueryToRpm e.1, KState.toRpm e.2))) := by
  rw [← replayOf_init, foldl_replayOf]
  rfl

theorem transcriptPaths_def (T : PermutationTranscript) :
    keccakEvaluationsOfTranscript T = (T.foldl TranscriptReplay.step ⟨[], [(Vector.replicate 25 0, [])]⟩).spongePaths.filterMap
      fun p ↦ (keccakUnpadded p.2).map fun m ↦ (m, #v[p.1[0], p.1[1], p.1[2], p.1[3]]) := rfl

theorem transcriptPathsB_def (T : PermutationTranscript) :
    transcriptPathsB T = (Common.replay Common.KState.zero
      (T.map fun e ↦ (permQueryToRpm e.1, KState.toRpm e.2))).chains.filterMap
        fun p ↦ (Common.keccakUnpad p.2).map fun m ↦ (m, p.1.1.1) := rfl

theorem chains_paths (σ : KSimB) :
    (replayOf σ).spongePaths.filterMap
        (fun p ↦ (keccakUnpadded p.2).map fun m ↦ (m, #v[p.1[0], p.1[1], p.1[2], p.1[3]])) =
      (σ.chains.filterMap fun p ↦ (Common.keccakUnpad p.2).map fun m ↦ (m, p.1.1.1)).map
        fun p ↦ (p.1, Digest.ofRpm p.2) := by
  simp only [replayOf, List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr fun p _ ↦ ?_
  simp only [Function.comp_apply, unpad_blocksToBytes]
  generalize Common.keccakUnpad p.2 = o
  cases o with
  | none => rfl
  | some m => simp only [Option.map_some, digest_ofRpm]

/-- **The transcript's paths on lanes are its paths on bytes**, their digests read on lanes. -/
theorem transcriptPaths_eq (T : PermutationTranscript) :
    keccakEvaluationsOfTranscript T = (transcriptPathsB T).map fun p ↦ (p.1, Digest.ofRpm p.2) := by
  rw [transcriptPaths_def, transcriptPathsB_def, foldl_replay, chains_paths]

/-- The evaluations of the lane paths are those of the byte paths. -/
theorem hashesOf_transcriptPaths (T : PermutationTranscript) :
    lookupEvaluation (keccakEvaluationsOfTranscript T) = hashesOfB (transcriptPathsB T) := by
  funext x
  rw [transcriptPaths_eq, lookupEvaluation, hashesOfB, List.find?_map, Option.map_map]
  rfl

end LeanVM.Rpm

end
