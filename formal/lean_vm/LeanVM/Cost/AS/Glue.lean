module

public import LeanVM.Cost.Efficient
public import LeanVM.Cost.AS.Program
import all LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.EndToEnd.Sound.SkelPairs
import all LeanVM.Protocol.EndToEnd.Sound.SkelWhir
import all LeanVM.Protocol.EndToEnd.Sound.Avail
import all LeanVM.Protocol.Extraction.Fast.AfterRoot
import all Statement.LeanVmVerifier
import all Statement.CostMachine

/-!
# The agreement-set extractor the compiled program computes

* `replay_reads`, **`announced_of_decSizesL`**: the stack size the replay's announced sizes decode
  to is the one the statement's budget reads (`announcedStackLog`);
* **`asOutput`**: in a program within a size bound `S` whose function `0` is `entryBody j`, if
  function `j` computes `extractL` at a price `cost` that, with the entry's `14`, is within a budget
  `B` wherever the extraction succeeds, the decoded output within `B` is `transcriptExtractorL`'s.
-/

namespace LeanVM.Cost.AS

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Extraction.AS
open LeanVM.Protocol.EndToEnd.Sound Common

public section

/-! ## The announced sizes -/

theorem readPure_of_ground : ∀ (n : ℕ) (s : VerifierProgramState), s.sponge.ground = none →
    n ≤ s.stream.length → (readPure n s).map (·.1) = some (s.stream.take n)
  | 0, _, _, _ => rfl
  | n + 1, ⟨sp, x :: xs, os, rs⟩, hg, hn => by
    simp only at hg
    simp only [readPure, hg]
    have ih := readPure_of_ground n ⟨absorbPure sp x dsObserve, xs, os, rs⟩ (by
      simp only [absorbPure]; split_ifs <;> exact hg) (by simp at hn ⊢; omega)
    rcases h : readPure n ⟨absorbPure sp x dsObserve, xs, os, rs⟩ with _ | r
    · rw [h] at ih; simp at ih
    · rw [h] at ih
      simp only [Option.map_some, Option.some.injEq] at ih ⊢
      rw [ih]
      rfl
  | n + 1, ⟨sp, [], os, rs⟩, _, hn => by simp at hn

/-- **A replay of reads reads the stream's head.** -/
theorem replay_reads (F : KeccakState → Option KeccakState) :
    ∀ (n : ℕ) (s : VerifierProgramState) (r : List EvP × VerifierProgramState),
      skelReplayP F (List.replicate n .read) s = some r →
        n ≤ s.stream.length ∧ r.1.mapM (fun p : EvP ↦ p.1) = some (s.stream.take n)
  | 0, s, r, h => by
    simp only [List.replicate, skelReplayP, Option.some.injEq] at h
    subst h
    simp
  | n + 1, s, r, h => by
    simp only [List.replicate, skelReplayP] at h
    split at h
    · rename_i x xs hst _
      obtain ⟨sp, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨ih1, ih2⟩ := replay_reads F n _ r' h'
      simp only at ih1 ih2
      refine ⟨by rw [hst]; simp; omega, ?_⟩
      rw [hst, List.mapM_cons, ih2]
      rfl
    · simp at h

/-- **The stack size the decoded announced sizes give is the one the budget reads.** -/
theorem announced_of_decSizesL (F : KeccakState → Option KeccakState) (prog : LeanIsaProgram)
    (π : Proof) (seed : KeccakState) {r₁ : List EvP × VerifierProgramState} {lay : LayoutLite} {ρ : ℕ}
    (hr : skelReplayP F skSizes (startState π seed) = some r₁)
    (hd : decSizesL (bytecodeWords prog) r₁.1 = some (lay, ρ)) :
    Cost.announcedStackLog prog π = lay.stackLog := by
  obtain ⟨hn, hm⟩ := replay_reads F _ _ r₁ hr
  unfold decSizesL at hd
  rw [hm, Option.bind_some, sizesOfL_eq] at hd
  obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.mp hd
  have hl : (layoutLite a.1).stackLog = lay.stackLog := congrArg (fun x ↦ x.1.stackLog) he
  unfold Cost.announcedStackLog announcedLayoutAndRate
  rw [runPure_readSizes]
  unfold readSizesPure
  have hrp := readPure_of_ground (2 + tables.length) ⟨⟨default, [], none⟩, π.stream, [], []⟩ rfl hn
  rcases h : readPure (2 + tables.length) ⟨⟨default, [], none⟩, π.stream, [], []⟩ with _ | rp
  · rw [h] at hrp; simp at hrp
  · rw [h] at hrp
    simp only [Option.map_some, Option.some.injEq] at hrp
    simp only [Option.bind_some]
    have hrp' : rp.1 = (startState π seed).stream.take (2 + tables.length) := hrp
    rw [hrp']
    simp only [startState] at ha ⊢
    rw [ha]
    simp only [Option.map_some, Option.getD_some]
    exact hl

/-! ## The output -/

/-- **The glue**: in a program within the size bound `S` whose function `0` is `entryBody j`, if
function `j` computes `extractL` at the price `cost`, with the entry's `14` within the budget `B`
wherever the extraction succeeds, the output within `B`, decoded, is `transcriptExtractorL`'s. -/
theorem asOutput (P : MachineProgram) (S : ℕ) (hsize : MachineProgram.size P ≤ S)
    (j : ℕ) (hentry : P[0]? = some (entryBody j))
    (cost : LeanIsaProgram → PublicInput → List (PermutationQuery KeccakState × KeccakState) →
      Proof → ℕ)
    (hrun : ∀ prog input qs π, RunsBody P j [encodeValue prog, encodeValue input, encodeValue qs,
      encodeValue π] (encodeValue (extractL prog input qs π)) (cost prog input qs π))
    (prog : LeanIsaProgram) (input : PublicInput) (T : OracleQueryLog) (proof : Proof) (B : ℕ)
    (hcost : ∀ t, extractL prog input (permutationQueries T) proof = some t →
      cost prog input (permutationQueries T) proof + 14 ≤ B) :
    (outputWithin P S B (encodeLeanVmKnowledgeExtractorInput prog input T proof)).bind
        (decodeExecution prog) = transcriptExtractorL prog input T proof := by
  obtain ⟨c, hc, hentryRun⟩ := runsBody_entry hentry (hrun prog input (permutationQueries T) proof)
  change _ = extractL prog input (permutationQueries T) proof
  cases ht : extractL prog input (permutationQueries T) proof with
  | none =>
    rw [ht] at hentryRun
    cases ho : outputWithin P S B (encodeLeanVmKnowledgeExtractorInput prog input T proof) with
    | none => rfl
    | some v =>
      obtain ⟨c', hv⟩ := runsBody_of_outputWithin ho
      obtain ⟨rfl, -⟩ := RunsBody.unique hv hentryRun
      exact decodeExecution_unwrap prog none
  | some t =>
    rw [ht] at hentryRun
    have hb := hcost t ht
    have hx : encodeLeanVmKnowledgeExtractorInput prog input T proof =
        .constructor 0 [encodeValue prog, encodeValue input, encodeValue (permutationQueries T),
          encodeValue proof] := rfl
    rw [hx, outputWithin_of_runs hsize hentryRun (by omega)]
    exact decodeExecution_unwrap prog (some t)

end

end LeanVM.Cost.AS
