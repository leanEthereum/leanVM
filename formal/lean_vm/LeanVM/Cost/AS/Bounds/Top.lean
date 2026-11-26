module

public import LeanVM.Cost.AS.Bounds.Budget
public import LeanVM.Cost.AS.Bounds.Replay
public import LeanVM.Cost.Bounds.Leaves
import LeanVM.Cost.AS.Glue
import all LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.Extraction.AS.TraceShape
import all LeanVM.Protocol.EndToEnd.Sound.SkelPairs
import all LeanVM.Protocol.EndToEnd.Sound.SkelWhir
import all LeanVM.Protocol.EndToEnd.Sound.Avail

/-!
# Bounds: the agreement-set extractor's price

* `extractL_steps`: a successful extraction's intermediate values;
* `extract_roots`, `extract_trace`: its roots' shapes (`RootsOk`) and its trace's (`TraceSmall`,
  `traceDepth`).
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Verifier LeanVM.Extraction.AS LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Semantics LeanVM.Protocol.EndToEnd.Sound

public section

/-- **A successful extraction's steps.** -/
theorem extractL_steps {prog : LeanIsaProgram} {input : PublicInput}
    {qs : List (Common.PermutationQuery KeccakState × KeccakState)} {π : Proof} {t : Execution prog}
    (h : extractL prog input qs π = some t) :
    ∃ seed r₁ a r₂ tr,
      seedWithHash (Protocol.KeccakHash.keccak256With (fwdF (fwdIndex qs))) (fwdF (fwdIndex qs))
          (bytecodeWords prog) (publicInputDigest input) = some seed ∧
        skelReplayP (fwdF (fwdIndex qs)) skSizes (startState π seed) = some r₁ ∧
        decSizesL (bytecodeWords prog) r₁.1 = some a ∧
        skelReplayP (fwdF (fwdIndex qs)) (skBodyL a.1 a.2) r₁.2 = some r₂ ∧
        decBodyL a.1 a.2 r₂.1 = some tr ∧ finishL prog input qs ((true, (a, tr)), r₂.2) = some t := by
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
    (h2 : skelReplayP F skSizes (startState π seed) = some r₁) (h3 : decSizesL bc r₁.1 = some (lay, ρ))
    (h4 : skelReplayP F (skBodyL lay ρ) r₁.2 = some r₂) :
    RootsOk lay.stackLog ρ (r₂.2.roots.map Prod.snd) := by
  obtain ⟨-, hρ1, hρ2, hs1, hs2⟩ := decSizesL_facts h3
  have e1 := roots_skelReplayP F skSizes _ r₁ h2
  have e2 := roots_skelReplayP F (skBodyL lay ρ) _ r₂ h4
  have e0 : commitsOf skSizes = [] := commitsOf_replicate_read _
  simp only [startState, List.map_nil, List.nil_append, e0] at e1
  rw [e2, e1, List.nil_append, commitsOf_skBodyL]
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

/-- **The agreement-set extractor's price but its finish**, for `N` queries, `D` levels of the
sorted maps, positions of `W` limbs, a program of `2^ℓ` instructions. -/
@[expose] def headPrice (N D W ℓ : ℕ) : ℕ :=
  ((fwdStepPrice D W + 14) * N + 9) + 2 * bytecodeWordsPrice ℓ + 200 +
    ((9 + 8 * (16 * 2 ^ ℓ)) / 136 + 2) * (fwdLookupPrice D W + 430004) + 520 * (16 * 2 ^ ℓ) + 2000 +
    (8 * (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 8) + 9) + (80 * 8 + 8 * (16 * 2 ^ ℓ) + 977124100) +
    1000000000 + (40000 * (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 40000) + 9) + 1001400000 + 10000

/-- **The agreement-set extractor's price where it succeeds**: its head, and the finish at the
layout, rate, trace and roots it reaches, all within their facts. -/
theorem extractL_cost (P : MachineProgram) (hP : Includes P extractLC.costDeps) (prog : LeanIsaProgram)
    (input : PublicInput) (qs : List (Common.PermutationQuery KeccakState × KeccakState)) (π : Proof)
    {t : Execution prog} (ht : extractL prog input qs π = some t) :
    ∃ (seed : KeccakState) (r₁ : List EvP × VerifierProgramState) (lay : LayoutLite) (ρ : ℕ)
      (r₂ : List EvP × VerifierProgramState) (tr : WhirTrace),
      skelReplayP (fwdF (fwdIndex qs)) skSizes (startState π seed) = some r₁ ∧
      decSizesL (bytecodeWords prog) r₁.1 = some (lay, ρ) ∧
      skelReplayP (fwdF (fwdIndex qs)) (skBodyL lay ρ) r₁.2 = some r₂ ∧
      decBodyL lay ρ r₂.1 = some tr ∧
      machineCost P extractLC.costIdx [encodeValue prog, encodeValue input, encodeValue qs, encodeValue π] ≤
        headPrice qs.length (extractorSortedMapLevels qs.length)
            (limbsBelowTwoPow (extractorSortedMapLevels qs.length + 1)) prog.logSize +
          finishPrice (extractorSortedMapLevels qs.length)
            (limbsBelowTwoPow (extractorSortedMapLevels qs.length + 1)) qs.length prog.logSize lay ρ tr
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
  have hlay : LayOk lay := ⟨by omega, hF0.logMemory_le, hF0.logBytecode_le, hF0.heights_length,
    hF0.heights_le⟩
  have hfx := fwdIndex_cost P (by includes) D W hW qs (by omega)
  have hbw := bytecodeWordsC_cost P (by includes) prog
  -- the facts the finish needs
  have hroots := extract_roots h2 h3 h4
  obtain ⟨hsm, hdep, -⟩ := extract_trace h3 h5
  -- the replays' facts
  have hsk : skSizes.length = 8 := by decide +kernel
  have hr1 : r₁.2.roots = [] := by
    have e := roots_skelReplayP (fwdF (fwdIndex qs)) skSizes _ r₁ h2
    have e0 : commitsOf skSizes = [] := commitsOf_replicate_read _
    rw [e0] at e
    simpa [startState] using e
  have hlen1 : r₁.1.length ≤ 8 := by
    obtain ⟨-, hm1⟩ := replay_reads (fwdF (fwdIndex qs)) _ _ r₁ h2
    rw [← length_of_mapM hm1]
    have : tables.length = 6 := by decide +kernel
    simp only [List.length_take]
    omega
  have hsp1 : SpOk r₁.2.sponge := skelReplayP_spOk _ _ _ r₁ h2 ⟨by simp [startState], by simp [startState]⟩
  have hlb := length_skBodyL lay ρ hlay
  -- the innermost continuation: the finish
  have k4 := bind_le P (by includes) _
    (.closure extractLC.lam0.lam0.lam0.lam0.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue qs,
      encodeValue (lay, ρ), encodeValue r₂])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.lam0.lam0.lam0.lam0.costSpec P (by includes) prog input qs
      (lay, ρ) r₂ a)) (decBodyL lay ρ r₂.1)
    (finishPrice D W qs.length prog.logSize lay ρ tr r₂.2.roots + 18 + 10) (fun a ha ↦ by
      rw [h5] at ha
      obtain rfl := Option.some.inj ha
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [extractLC.lam0.lam0.lam0.lam0.lam0.costEq P (by includes)]
      have := finishL_cost P (by includes) prog input qs D W hW hN true lay ρ tr r₂.2 hF0 (by omega)
        (by omega) hρ1 hρ2 hroots hsm (by omega)
      omega)
  -- the trace's decoder
  have k3 := bind_le P (by includes) _
    (.closure extractLC.lam0.lam0.lam0.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue qs,
      encodeValue (lay, ρ)])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.lam0.lam0.lam0.costSpec P (by includes) prog input qs
      (lay, ρ) a)) (skelReplayP (fwdF (fwdIndex qs)) (skBodyL lay ρ) r₁.2)
    (1001400000 + finishPrice D W qs.length prog.logSize lay ρ tr r₂.2.roots + 18 + 10 + 6 + 19 + 10) (fun a ha ↦ by
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
    (.closure extractLC.lam0.lam0.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue qs,
      encodeValue (fwdIndex qs), encodeValue r₁])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.lam0.lam0.costSpec P (by includes) prog input qs (fwdIndex qs)
      r₁ a))
    (decSizesL (bytecodeWords prog) r₁.1)
    (1000000000 +
      (40000 * (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 40000) + 9) +
      (1001400000 + finishPrice D W qs.length prog.logSize lay ρ tr r₂.2.roots + 18 + 10 + 6 + 19 + 10) + 6 + 22 + 10)
    (fun a ha ↦ by
      rw [h3] at ha
      obtain rfl := Option.some.inj ha
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [extractLC.lam0.lam0.lam0.costEq P (by includes)]
      dsimp only
      have c1 := skBodyL_cost P (by includes) lay ρ hlay hρ2
      have c2 := skelReplay_cost P (fwdF (fwdIndex qs)) _ hF _ hB (by includes) 40000 (skBodyL lay ρ) r₁.2
        (by rw [hr1]; simp; omega) hsp1
      have c3 := Nat.mul_le_mul_right (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 40000) hlb
      omega)
  -- the announced sizes' decoder
  have k1 := bind_le P (by includes) _
    (.closure extractLC.lam0.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue qs,
      encodeValue (fwdIndex qs)])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.lam0.costSpec P (by includes) prog input qs (fwdIndex qs) a))
    (skelReplayP (fwdF (fwdIndex qs)) skSizes (startState π seed))
    (bytecodeWordsPrice prog.logSize + (80 * 8 + 8 * (16 * 2 ^ prog.logSize) + 977124100) +
      (1000000000 +
        (40000 * (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 40000) + 9) +
        (1001400000 + finishPrice D W qs.length prog.logSize lay ρ tr r₂.2.roots + 18 + 10 + 6 + 19 + 10) + 6 + 22 + 10) +
      6 + 15 + 10)
    (fun a ha ↦ by
      rw [h2] at ha
      obtain rfl := Option.some.inj ha
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [extractLC.lam0.lam0.costEq P (by includes)]
      have c1 := bytecodeWordsC_cost P (by includes) prog
      have c2 := decSizesL_cost P (by includes) (bytecodeWords prog) r₁.1 (by rw [hbl]; omega) (by omega)
      rw [hbl] at c2
      omega)
  -- the replay of the announced sizes
  have k0 := bind_le P (by includes) _
    (.closure extractLC.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue qs, encodeValue π,
      encodeValue (fwdIndex qs)])
    (fun a ↦ RunsApp.of_spec (extractLC.lam0.costSpec P (by includes) prog input qs π (fwdIndex qs) a))
    (seedWithHash (Protocol.KeccakHash.keccak256With (fwdF (fwdIndex qs))) (fwdF (fwdIndex qs))
      (bytecodeWords prog) (publicInputDigest input))
    (200 + 17 + (8 * (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 8) + 9) +
      (bytecodeWordsPrice prog.logSize + (80 * 8 + 8 * (16 * 2 ^ prog.logSize) + 977124100) +
        (1000000000 +
          (40000 * (2 * (fwdLookupPrice D W + 4) + 34000 + 11 * 40000) + 9) +
          (1001400000 + finishPrice D W qs.length prog.logSize lay ρ tr r₂.2.roots + 18 + 10 + 6 + 19 + 10) + 6 + 22 + 10) +
        6 + 15 + 10) + 6 + 20 + 10)
    (fun a ha ↦ by
      rw [h1] at ha
      obtain rfl := Option.some.inj ha
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [extractLC.lam0.costEq P (by includes),
        Auto.LeanVM.Protocol.EndToEnd.Sound.startState.c536.costEq P (by includes)]
      have hl6 : tables.length = 6 := by decide +kernel
      rw [hl6, limbs_of_lt (by norm_num : 2 + 6 < 2 ^ 64), limbs_of_lt (by norm_num : 6 < 2 ^ 64)]
      have c1 := replicate_cost P (by includes) Op.read (2 + 6) (by norm_num)
      have c2 := skelReplay_cost P (fwdF (fwdIndex qs)) _ hF _ hB (by includes) 8 skSizes
        (startState π seed) (by simp [startState, hsk]) ⟨by simp [startState], by simp [startState]⟩
      rw [hsk] at c2
      omega)
  have c0 := extractSeed_cost P (by includes) D W hW qs (by omega) (bytecodeWords prog)
    (by rw [hbl]; have : 2 ^ prog.logSize ≤ 2 ^ 30 := hpl; omega) (publicInputDigest input)
  rw [hbl] at c0
  have cp := publicInputDigest_cost P (by includes) input
  rw [extractLC.costEq P hP]
  unfold headPrice
  omega

end

end LeanVM.Cost.Bounds.AS
