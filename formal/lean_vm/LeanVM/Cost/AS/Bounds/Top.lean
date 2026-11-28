module

public import LeanVM.Cost.AS.Bounds.Finish
public import LeanVM.Cost.AS.Bounds.Replay
public import LeanVM.Cost.AS.Bounds.Skeleton
public import LeanVM.Cost.AS.Glue
import all LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.Relation.ExtractorDef
import all LeanVM.Cost.AS.Bounds.TraceShape

/-!
# Bounds: the agreement-set extractor's price

* `extractL_steps`: a successful extraction's intermediate values;
* `extract_roots`, `extract_trace`: its roots' shapes (`RootsOk`) and its trace's (`TraceSmall`,
  `traceDepth`); `skelReplayP_spOk`: a replay keeps the sponge within `SpOk`;
* **`extractL_cost`**: where it succeeds, the compiled extractor's price is at most
  `headPrice` (the forward index, the seed, the replays and the decoders) and the finish's
  `finishPrice` at the layout, rate, trace and roots it reaches.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Verifier LeanVM.Extraction.AS
open LeanVM.Extraction.Fast LeanVM.Protocol.Compile LeanVM.Semantics LeanVM.Protocol.EndToEnd.Sound

public section

/-- **A successful extraction's steps.** -/
theorem extractL_steps {prog : LeanIsaProgram} {input : PublicInput}
    {qs : List (Common.PermutationQuery KeccakState × KeccakState)} {π : Proof} {t : Execution prog}
    (h : extractL prog input qs π = some t) :
    ∃ seed r₁ a r₂ tr,
      seedWithHash (KeccakHash.keccak256With (fwdF (fwdIndex qs))) (fwdF (fwdIndex qs))
          (bytecodeWords prog) (publicInputDigest input) = some seed ∧
        skelReplayP (fwdF (fwdIndex qs)) skSizes (Relation.startState π seed) = some r₁ ∧
        decSizesL (bytecodeWords prog) r₁.1 = some a ∧
        skelReplayP (fwdF (fwdIndex qs)) (skBody a.1 a.2) r₁.2 = some r₂ ∧
        decBodyL a.1 a.2 r₂.1 = some tr ∧ finishL prog qs a.1 a.2 tr r₂.2.roots = some t := by
  unfold extractL at h
  obtain ⟨seed, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r₁, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r₂, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tr, h5, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨seed, r₁, a, r₂, tr, h1, h2, h3, h4, h5, h⟩

/-- **The roots a successful replay records**: the body's commits, within `RootsOk`. -/
theorem extract_roots {F : KeccakState → Option KeccakState} {π : Proof} {seed : KeccakState}
    {bc : List K} {r₁ r₂ : List EvP × VerifierProgramState} {lay : LayoutLite} {ρ : ℕ}
    (h2 : skelReplayP F skSizes (Relation.startState π seed) = some r₁)
    (h3 : decSizesL bc r₁.1 = some (lay, ρ)) (h4 : skelReplayP F (skBody lay ρ) r₁.2 = some r₂) :
    RootsOk lay.stackLog ρ (r₂.2.roots.map Prod.snd) := by
  obtain ⟨-, hρ1, hρ2, hs1, hs2⟩ := decSizesL_facts h3
  have e1 := roots_skelReplayP F skSizes _ r₁ h2
  have e2 := roots_skelReplayP F (skBody lay ρ) _ r₂ h4
  have e0 : commitsOf skSizes = [] := commitsOf_replicate_read _
  simp only [Relation.startState, List.map_nil, List.nil_append, e0] at e1
  rw [e2, e1, List.nil_append, commitsOf_skBody]
  exact rootsOk_bodyCommits hs1 hs2 hρ1 hρ2

/-- **A successfully decoded trace is small**, of depth below six. -/
theorem extract_trace {bc : List K} {h₁ : List EvP} {lay : LayoutLite} {ρ : ℕ} {h : List EvP}
    {tr : WhirTrace} (h3 : decSizesL bc h₁ = some (lay, ρ)) (h5 : decBodyL lay ρ h = some tr) :
    TraceSmall tr ∧ traceDepth tr < 6 ∧ TraceShape lay.stackLog 0
      ((Whir.ladder lay.stackLog ρ).getD []) tr := by
  obtain ⟨-, hρ1, hρ2, hs1, hs2⟩ := decSizesL_facts h3
  obtain ⟨cfg, hc, hsh⟩ := decBodyL_shape h5
  obtain ⟨hl, hf⟩ := ladder_small hc hs1 hs2 hρ1 hρ2
  have hm : Whir.maxLogStack = 30 := rfl
  obtain ⟨h1, h2⟩ := traceSmall_of_shape lay.stackLog (by omega) 0 cfg tr hsh hf
  rw [hc, Option.getD_some]
  exact ⟨h1, by omega, hsh⟩

/-- **A replay keeps the sponge within `SpOk`.** -/
theorem skelReplayP_spOk (F : KeccakState → Option KeccakState) :
    ∀ (sk : List Op) (s : VerifierProgramState) (r : List EvP × VerifierProgramState),
      skelReplayP F sk s = some r → SpOk s.sponge → SpOk r.2.sponge
  | [], s, r, h, hs => by
    simp only [skelReplayP, Option.some.injEq] at h
    subst h
    exact hs
  | op :: sk, s, r, h, hs => by
    have ho : dsObserve < 2 ^ 64 := by decide
    cases op with
    | read =>
      simp only [skelReplayP] at h
      split at h
      · obtain ⟨sp, hsp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
        exact skelReplayP_spOk F sk _ r' h' (absorb_ok hs ho hsp)
      · simp at h
    | sample =>
      simp only [skelReplayP] at h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
      exact skelReplayP_spOk F sk _ r' h' (squeeze_ok hs hc)
    | readPacked n =>
      simp only [skelReplayP] at h
      split_ifs at h
      obtain ⟨sp, hsp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
      exact skelReplayP_spOk F sk _ r' h' (observePacked_ok hs hsp)
    | samplePacked n =>
      simp only [skelReplayP] at h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
      exact skelReplayP_spOk F sk _ r' h' (samplesPacked_ok hs hc)
    | grind b =>
      simp only [skelReplayP] at h
      split at h
      · obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
        exact skelReplayP_spOk F sk _ r' h' (absorbNonce_ok hc)
      · simp at h
    | commit ht w =>
      simp only [skelReplayP] at h
      split at h
      · obtain ⟨sp0, h0, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨sp1, h1, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
        exact skelReplayP_spOk F sk _ r' h' (absorb_ok (absorb_ok hs ho h0) ho h1)
      · simp at h
    | query =>
      simp only [skelReplayP] at h
      split at h
      · obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
        exact skelReplayP_spOk F sk _ r' h' hs
      · simp at h

/-- The price of the body's replay, `B` a permutation's. -/
@[expose] def bodyReplayPrice (B : ℕ) : ℕ :=
  40000 * (2 * B + 34000 + 11 * 40006) + 1000 * (B + 40000) + 9

/-- **The agreement-set extractor's price but its finish**, for `N` queries, `D` levels of the
sorted maps, positions of `W` limbs, a program of `2^ℓ` instructions. -/
@[expose] def headPrice (N D W ℓ : ℕ) : ℕ :=
  ((fwdStepPrice D W + 14) * N + 9) + 2 * bytecodeWordsPrice ℓ + 200 +
    (((9 + 8 * (16 * 2 ^ ℓ)) / 136 + 2) * (fwdLookupPrice D W + 430004) + 520 * (16 * 2 ^ ℓ) + 2000) +
    (8 * (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 8) + 9) +
    (80 * 8 + 8 * (16 * 2 ^ ℓ) + 10 ^ 10) + 1000000000 + bodyReplayPrice (fwdLookupPrice D W + 4) +
    2000000000 + 10000

/-- **The agreement-set extractor's price where it succeeds**: its head, and the finish at the
layout, rate, trace and roots it reaches, all within their facts. -/
theorem extractL_cost (P : MachineProgram) (hP : Includes P extractLC.costDeps) (prog : LeanIsaProgram)
    (input : PublicInput) (qs : List (Common.PermutationQuery KeccakState × KeccakState)) (π : Proof)
    {t : Execution prog} (ht : extractL prog input qs π = some t) :
    ∃ (seed : KeccakState) (r₁ : List EvP × VerifierProgramState) (lay : LayoutLite) (ρ : ℕ)
      (r₂ : List EvP × VerifierProgramState) (tr : WhirTrace),
      skelReplayP (fwdF (fwdIndex qs)) skSizes (Relation.startState π seed) = some r₁ ∧
      decSizesL (bytecodeWords prog) r₁.1 = some (lay, ρ) ∧
      skelReplayP (fwdF (fwdIndex qs)) (skBody lay ρ) r₁.2 = some r₂ ∧
      decBodyL lay ρ r₂.1 = some tr ∧
      machineCost P extractLC.costIdx [encodeValue prog, encodeValue input, encodeValue qs, encodeValue π] ≤
        headPrice qs.length (extractorSortedMapLevels qs.length)
            (limbsBelowTwoPow (extractorSortedMapLevels qs.length + 1)) prog.logSize +
          finishPrice (extractorSortedMapLevels qs.length)
            (limbsBelowTwoPow (extractorSortedMapLevels qs.length + 1)) qs.length (10 ^ 7) lay ρ tr
            r₂.2.roots := by
  obtain ⟨seed, r₁, ⟨lay, ρ⟩, r₂, tr, h1, h2, h3, h4, h5, h6⟩ := extractL_steps ht
  refine ⟨seed, r₁, lay, ρ, r₂, tr, h2, h3, h4, h5, ?_⟩
  generalize hD : extractorSortedMapLevels qs.length = D
  have hN : qs.length + 2 ≤ 2 ^ D := by
    rw [← hD]; exact Nat.le_of_lt Nat.lt_log2_self
  have hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ limbsBelowTwoPow (D + 1) := limbs_le_wl_two
  generalize limbsBelowTwoPow (D + 1) = W at hW ⊢
  obtain ⟨hg, hwt⟩ := fwdIndex_good qs
  have hB := hashLam_cost P (by includes) D W hW (fwdIndex qs) hg (by omega)
  have hF : ∀ x, RunsApp P (.closure hashMC.lam0.costIdx [encodeValue (fwdIndex qs)]) [encodeValue x]
      (encodeValue (fwdF (fwdIndex qs) x)) :=
    fun x ↦ RunsApp.of_spec (hashMC.lam0.costSpec P (by includes) (fwdIndex qs) x)
  have hbl := bytecodeWords_length prog
  have hls : prog.logSize ≤ 30 := prog.logSize_le
  have hpl : 2 ^ prog.logSize ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hls
  obtain ⟨hF0, hρ1, hρ2, hs1, hs2⟩ := decSizesL_facts h3
  have hm : Whir.maxLogStack = 30 := rfl
  have hmin : Whir.minLogStack = 16 := rfl
  have hlay : LayOk lay := hF0.layOk (by omega)
  have hroots := extract_roots h2 h3 h4
  obtain ⟨hsm, hdep, -⟩ := extract_trace h3 h5
  have hsk : skSizes.length = 8 := by decide +kernel
  have hr1 : r₁.2.roots = [] := by
    have e := roots_skelReplayP (fwdF (fwdIndex qs)) skSizes _ r₁ h2
    have e0 : commitsOf skSizes = [] := commitsOf_replicate_read _
    rw [e0] at e
    simpa [Relation.startState] using e
  have hlen1 : r₁.1.length ≤ 8 := by
    obtain ⟨-, hm1⟩ := replay_reads (fwdF (fwdIndex qs)) _ _ r₁ h2
    rw [← length_of_mapM hm1]
    simp only [List.length_take]
    have : nTables = 6 := rfl
    omega
  have hsp1 : SpOk r₁.2.sponge :=
    skelReplayP_spOk _ _ _ r₁ h2 ⟨by simp [Relation.startState], by simp [Relation.startState]⟩
  have hlb := length_skBody lay ρ hlay
  have hpk := packedSum_skBody lay ρ hlay
  have hC := chunksL_cost P (by includes) lay hlay
  -- the finish
  have k4 := bind_le P (by includes) _
    (.closure extractLC.lam0.lam0.lam0.lam0.lam0.costIdx [encodeValue prog, encodeValue qs,
      encodeValue (lay, ρ), encodeValue r₂])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.lam0.lam0.lam0.lam0.costSpec P (by includes) prog qs
      (lay, ρ) r₂ a)) (decBodyL lay ρ r₂.1)
    (finishPrice D W qs.length (10 ^ 7) lay ρ tr r₂.2.roots + 11 + 10) (fun a ha ↦ by
      rw [h5] at ha
      obtain rfl := Option.some.inj ha
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [extractLC.lam0.lam0.lam0.lam0.lam0.costEq P (by includes)]
      dsimp only
      have := finishL_cost P (by includes) prog qs D W hW hN lay ρ tr r₂.2.roots hF0 (by omega)
        (by omega) hρ1 hρ2 hroots hsm (by omega) (10 ^ 7) hC
      omega)
  -- the trace's decoder
  have k3 := bind_le P (by includes) _
    (.closure extractLC.lam0.lam0.lam0.lam0.costIdx [encodeValue prog, encodeValue qs,
      encodeValue (lay, ρ)])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.lam0.lam0.lam0.costSpec P (by includes) prog qs
      (lay, ρ) a)) (skelReplayP (fwdF (fwdIndex qs)) (skBody lay ρ) r₁.2)
    (2000000000 + finishPrice D W qs.length (10 ^ 7) lay ρ tr r₂.2.roots + 100) (fun a ha ↦ by
      rw [h4] at ha
      obtain rfl := Option.some.inj ha
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [extractLC.lam0.lam0.lam0.lam0.costEq P (by includes)]
      have := decBodyL_cost P (by includes) lay ρ r₂.1 hlay hρ2
      dsimp only at k4 ⊢
      omega)
  -- the body's skeleton and its replay
  have k2 := bind_le P (by includes) _
    (.closure extractLC.lam0.lam0.lam0.costIdx [encodeValue prog, encodeValue qs,
      encodeValue (fwdIndex qs), encodeValue r₁])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.lam0.lam0.costSpec P (by includes) prog qs (fwdIndex qs)
      r₁ a))
    (decSizesL (bytecodeWords prog) r₁.1)
    (1000000000 + bodyReplayPrice (fwdLookupPrice D W + 4) +
      (2000000000 + finishPrice D W qs.length (10 ^ 7) lay ρ tr r₂.2.roots + 100) + 100)
    (fun a ha ↦ by
      rw [h3] at ha
      obtain rfl := Option.some.inj ha
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [extractLC.lam0.lam0.lam0.costEq P (by includes)]
      dsimp only
      have c1 := skBody_cost P (by includes) lay ρ hlay hρ2
      have c2 := skelReplay_cost P (fwdF (fwdIndex qs)) _ hF _ hB (by includes) 40006 (skBody lay ρ)
        r₁.2 (by rw [hr1]; simp; omega) (by omega) hsp1
      have c3 := Nat.mul_le_mul_right (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 40006) hlb
      have c4 := Nat.mul_le_mul_right (fwdLookupPrice D W + 4 + 40000) hpk
      unfold bodyReplayPrice
      omega)
  -- the announced sizes' decoder
  have k1 := bind_le P (by includes) _
    (.closure extractLC.lam0.lam0.costIdx [encodeValue prog, encodeValue qs, encodeValue (fwdIndex qs)])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.lam0.costSpec P (by includes) prog qs (fwdIndex qs) a))
    (skelReplayP (fwdF (fwdIndex qs)) skSizes (Relation.startState π seed))
    (bytecodeWordsPrice prog.logSize + (80 * 8 + 8 * (16 * 2 ^ prog.logSize) + 10 ^ 10) +
      (1000000000 + bodyReplayPrice (fwdLookupPrice D W + 4) +
        (2000000000 + finishPrice D W qs.length (10 ^ 7) lay ρ tr r₂.2.roots + 100) + 100) + 100)
    (fun a ha ↦ by
      rw [h2] at ha
      obtain rfl := Option.some.inj ha
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [extractLC.lam0.lam0.costEq P (by includes)]
      have c1 := bytecodeWordsC_cost P (by includes) prog
      have c2 := decSizesL_cost P (by includes) (bytecodeWords prog) r₁.1 (by rw [hbl]; omega) (by omega)
      rw [hbl] at c2
      have c3 := Nat.mul_le_mul_left 80 hlen1
      omega)
  -- the replay of the announced sizes
  have k0 := bind_le P (by includes) _
    (.closure extractLC.lam0.costIdx [encodeValue prog, encodeValue qs, encodeValue π,
      encodeValue (fwdIndex qs)])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.costSpec P (by includes) prog qs π (fwdIndex qs) a))
    (seedWithHash (KeccakHash.keccak256With (fwdF (fwdIndex qs))) (fwdF (fwdIndex qs))
      (bytecodeWords prog) (publicInputDigest input))
    ((8 * (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 8) + 9) +
      (bytecodeWordsPrice prog.logSize + (80 * 8 + 8 * (16 * 2 ^ prog.logSize) + 10 ^ 10) +
        (1000000000 + bodyReplayPrice (fwdLookupPrice D W + 4) +
          (2000000000 + finishPrice D W qs.length (10 ^ 7) lay ρ tr r₂.2.roots + 100) + 100) + 100) + 200)
    (fun a ha ↦ by
      rw [h1] at ha
      obtain rfl := Option.some.inj ha
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [extractLC.lam0.costEq P (by includes),
        Auto.LeanVM.Protocol.Relation.startState.c483.costEq P (by includes)]
      have hl6 : nTables = 6 := rfl
      rw [hl6, limbs_of_lt (by norm_num : 2 + 6 < 2 ^ 64), limbs_of_lt (by norm_num : 6 < 2 ^ 64)]
      have c1 := replicate_cost P (by includes) Op.read (2 + 6) (by norm_num)
      have c2 := skelReplay_cost P (fwdF (fwdIndex qs)) _ hF _ hB (by includes) 8 skSizes
        (Relation.startState π seed) (by simp [Relation.startState, hsk])
        (by unfold skSizes; simp [packedSum_replicate, packedSum]) ⟨by simp [Relation.startState],
          by simp [Relation.startState]⟩
      have hps : packedSum skSizes = 0 := by unfold skSizes; simp [packedSum_replicate, packedSum]
      rw [hsk, hps] at c2
      omega)
  have c0 := extractSeed_cost P (by includes) D W hW qs (by omega) (bytecodeWords prog)
    (by rw [hbl]; omega) (publicInputDigest input)
  rw [hbl] at c0
  have cp := publicInputDigest_cost P (by includes) input
  have cf := fwdIndex_cost P (by includes) D W hW qs (by omega)
  have cb := bytecodeWordsC_cost P (by includes) prog
  rw [extractLC.costEq P hP]
  unfold headPrice
  omega

end

end LeanVM.Cost.Bounds.AS
