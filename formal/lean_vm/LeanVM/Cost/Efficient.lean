module

public import LeanVM.Cost.ExtractorSize
public import LeanVM.Cost.Bounds.Top
public import LeanVM.Cost.Prices

/-!
# The extractor the compiled program computes

`LeanVM.extractorComputedBy P` (`Statement/CostMachine.lean`), the extractor of the end statement, runs
the program's function `0` on one value, `encodeLeanVmKnowledgeExtractorInput prog input T proof = .ctor 0 [encodeValue prog, encodeValue input, encodeValue qs, encodeValue proof]` with
`qs = permutationQueries T`, and decodes its output with `decodeExecution prog`, which parses an
execution's encoding. The compiled extractor (`extractorC`, `Cost/Extractor/Top.lean`, computing
`extractorTop`, `Fast/Compiled.lean`) is a function of four encoded arguments whose output encodes
an `Option (Execution prog)`. The glue is the entry body `entryBody j` (`Cost/ExtractorProgram.lean`):
it destructures the input, calls function `j` on its four fields and unwraps the option (`none` to
`.ctor 0 []`, which no execution decodes from; `some t` to `t`'s encoding), at most `14` more than
the call (`runsBody_entry`: two `case`s and their five fields, four variables, the call).

* **`extractorTop_output`**: in a program within `leanVmKnowledgeExtractorSizeBound` whose function `0`
  is `entryBody j`, if function `j`
  computes `extractorTop` at a price `cost` that is within `leanVmKnowledgeExtractorBudget` whenever the
  extraction succeeds, the decoded output within `leanVmKnowledgeExtractorBudget` is
  `transcriptExtractor`'s, on every input; **`extractorOf_eq_of_spec`**: `knowledgeExtractorOf P =
  transcriptExtractor`;
* `extractorProgram_size_le`: `compiledKnowledgeExtractor`'s size is within `leanVmKnowledgeExtractorSizeBound`
  (`Cost/ExtractorSize.lean`);
* **`extractorOf_extractorProgram`**: for `compiledKnowledgeExtractor` (its entry at `0`, its bodies held),
  the compiled extractor's spec (`extractorC.costSpec`) and its price within the budget
  (`extractorC_within`, `Cost/Bounds/Top.lean`), `knowledgeExtractorOf extractorProgram =
  transcriptExtractor`.
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Cost.Extractor Common

public section

/-! ## The entry -/

/-- The value the entry returns for an optional output. -/
@[expose] def unwrapOption {α : Type} [MachineEncoding α] : Option α → MachineValue
  | none => .constructor 0 []
  | some a => encodeValue a

theorem runsBody_entry {P : MachineProgram} {j : ℕ} (hentry : P[0]? = some (entryBody j))
    {α : Type} [MachineEncoding α] {a b c d : MachineValue} {o : Option α} {e : ℕ}
    (h : RunsBody P j [a, b, c, d] (encodeValue o) e) :
    ∃ c', c' ≤ e + 14 ∧ RunsBody P 0 [.constructor 0 [a, b, c, d]] (unwrapOption o) c' := by
  have hargs : RunsList P [a, b, c, d, .constructor 0 [a, b, c, d]] [.position 0, .position 1,
      .position 2, .position 3]
      [a, b, c, d] 4 :=
    RunsList.cons (Runs.var rfl) (RunsList.cons (Runs.var rfl) (RunsList.cons (Runs.var rfl)
      (RunsList.cons (Runs.var rfl) RunsList.nil)))
  have hcall := Runs.call hargs h
  cases o with
  | none =>
    have hcall' : Runs P [a, b, c, d, .constructor 0 [a, b, c, d]]
        (.call j [.position 0, .position 1, .position 2, .position 3]) (.constructor 0 []) (4 + e +
            1) := hcall
    have halt : Runs P ([] ++ [a, b, c, d, .constructor 0 [a, b, c, d]]) (.constructor 0 [])
        (.constructor 0 []) 1 :=
      (Runs.ctor RunsList.nil).cost_eq (by simp)
    have hinner := Runs.case (alts := [.constructor 0 [], .position 0]) hcall' rfl halt
    exact ⟨_, by simp only [List.length_cons, List.length_nil]; omega,
      RunsBody.intro hentry (Runs.case (Runs.var rfl) rfl hinner)⟩
  | some t =>
    have hcall' : Runs P [a, b, c, d, .constructor 0 [a, b, c, d]]
        (.call j [.position 0, .position 1, .position 2, .position 3]) (.constructor 1 [encodeValue
            t]) (4 + e + 1) := hcall
    have halt : Runs P ([encodeValue t] ++ [a, b, c, d, .constructor 0 [a, b, c, d]]) (.position 0) (encodeValue t) 1 :=
      Runs.var rfl
    have hinner := Runs.case (alts := [.constructor 0 [], .position 0]) hcall' rfl halt
    exact ⟨_, by simp only [List.length_cons, List.length_nil]; omega,
      RunsBody.intro hentry (Runs.case (Runs.var rfl) rfl hinner)⟩

theorem decodeExecution_unwrap (prog : Semantics.LeanIsaProgram) (o : Option (Execution prog)) :
    decodeExecution prog (unwrapOption o) = o := by
  cases o with
  | none => rfl
  | some t => exact decodeExecution_enc prog t

/-- An output within a budget is the value of a run. -/
theorem runsBody_of_outputWithin {P : MachineProgram} {s : ℕ} {x v : MachineValue} {b : ℕ}
    (h : outputWithin P s b x = some v) : ∃ c, RunsBody P 0 [x] v c := by
  unfold outputWithin runMachineProgram at h
  split at h
  · split at h
    · rename_i v' c hr
      split at h
      · obtain rfl : v' = v := Option.some.inj h
        exact ⟨c, b + 1, hr⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## The extractor's output -/

/-- Where the proof announces no shape, `transcriptExtractor` returns nothing. -/
theorem transcriptExtractor_eq_none {prog : Semantics.LeanIsaProgram} {π : Proof}
    (h : afterRoot (bytecodeWords prog) π = none) (input : PublicInput) (T : OracleQueryLog) :
    transcriptExtractor prog input T π = none := by
  unfold transcriptExtractor extract
  simp only [h]
  rfl

/-- **The glue**: in a program within the size bound whose function `0` is `entryBody j`, if
function `j` computes `extractorTop` at the price `cost`, within the budget (less the entry's `14`)
wherever the extraction succeeds, the output within `leanVmKnowledgeExtractorBudget`, decoded, is
`transcriptExtractor`'s. -/
theorem extractorTop_output (P : MachineProgram) (hsize : MachineProgram.size P ≤ leanVmKnowledgeExtractorSizeBound)
    (j : ℕ) (hentry : P[0]? = some (entryBody j))
    (cost : Semantics.LeanIsaProgram → PublicInput →
      List (PermutationQuery KeccakState × KeccakState) → Proof → ℕ)
    (hrun : ∀ prog input qs π, RunsBody P j [encodeValue prog, encodeValue input, encodeValue qs, encodeValue π]
      (encodeValue (extractorTop prog input qs π)) (cost prog input qs π))
    (hcost : ∀ prog input T π layout logInverseRate st t,
      afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st) →
      extractorTop prog input (permutationQueries T) π = some t →
      cost prog input (permutationQueries T) π + 14 ≤
        leanVmKnowledgeExtractorBudget (permutationQueries T).length)
    (prog : Semantics.LeanIsaProgram) (input : PublicInput) (T : OracleQueryLog) (proof : Proof) :
    (outputWithin P leanVmKnowledgeExtractorSizeBound
        (leanVmKnowledgeExtractorBudget (permutationQueries T).length)
        (encodeLeanVmKnowledgeExtractorInput prog input T proof)).bind (decodeExecution
            prog) =
      transcriptExtractor prog input T proof := by
  obtain ⟨c, hc, hentryRun⟩ := runsBody_entry hentry (hrun prog input (permutationQueries T) proof)
  rw [← extractorTop_eq]
  cases ht : extractorTop prog input (permutationQueries T) proof with
  | none =>
    rw [ht] at hentryRun
    cases ho : outputWithin P leanVmKnowledgeExtractorSizeBound
        (leanVmKnowledgeExtractorBudget (permutationQueries T).length)
        (encodeLeanVmKnowledgeExtractorInput prog input T proof) with
    | none => rfl
    | some v =>
      obtain ⟨c', hv⟩ := runsBody_of_outputWithin ho
      obtain ⟨rfl, -⟩ := RunsBody.unique hv hentryRun
      exact decodeExecution_unwrap prog none
  | some t =>
    rw [ht] at hentryRun
    cases ha : afterRoot (bytecodeWords prog) proof with
    | none =>
      have := transcriptExtractor_eq_none ha input T
      rw [← extractorTop_eq, ht] at this
      exact absurd this (by simp)
    | some r =>
      obtain ⟨⟨layout, R⟩, st⟩ := r
      have hb := hcost prog input T proof layout R st t ha ht
      have hx : encodeLeanVmKnowledgeExtractorInput prog input T proof =
          .constructor 0 [encodeValue prog, encodeValue input, encodeValue (permutationQueries T),
            encodeValue proof] := rfl
      rw [hx, outputWithin_of_runs hsize hentryRun (by omega)]
      exact decodeExecution_unwrap prog (some t)

/-- **The extractor a program computes is `transcriptExtractor`**, from the compiled extractor's
spec at function `j`, its price within the budget and the program within the size bound. -/
theorem extractorOf_eq_of_spec (P : MachineProgram)
    (hsize : MachineProgram.size P ≤ leanVmKnowledgeExtractorSizeBound) (j : ℕ)
    (hentry : P[0]? = some (entryBody j))
    (cost : Semantics.LeanIsaProgram → PublicInput →
      List (PermutationQuery KeccakState × KeccakState) → Proof → ℕ)
    (hrun : ∀ prog input qs π, RunsBody P j [encodeValue prog, encodeValue input, encodeValue qs, encodeValue π]
      (encodeValue (extractorTop prog input qs π)) (cost prog input qs π))
    (hcost : ∀ prog input T π layout logInverseRate st t,
      afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st) →
      extractorTop prog input (permutationQueries T) π = some t →
      cost prog input (permutationQueries T) π + 14 ≤
        leanVmKnowledgeExtractorBudget (permutationQueries T).length) :
    LeanVM.extractorComputedBy P = transcriptExtractor := by
  funext prog input T proof
  exact extractorTop_output P hsize j hentry cost hrun hcost prog input T proof

/-! ## The extractor's program -/

/-- The extractor's program holds its bodies: their indices are distinct
(`Cost/ExtractorSize.lean`). -/
theorem extractorProgram_includes_all : Includes compiledKnowledgeExtractor
    extractorProgramBodies := by
  have h := nodup_of_increasing extractorProgram_indices_increasing
  refine includes_ofList _ ?_
  rw [extractorProgramBodies_eq, List.map_cons]
  exact h

/-- **The program's size is within `leanVmKnowledgeExtractorSizeBound`** (`16048`), evaluated
(`Cost/ExtractorSize.lean`; exactly `15773`). -/
theorem extractorProgram_size_le : compiledKnowledgeExtractor.size ≤
    leanVmKnowledgeExtractorSizeBound :=
  extractorProgram_size_le_measured.trans (by decide)

/-- The extractor's program holds the compiled extractor's bodies. -/
theorem extractorProgram_includes : Includes compiledKnowledgeExtractor extractorC.costDeps :=
  extractorProgram_includes_all.mono fun _ hp ↦ by
    rw [extractorProgramBodies_eq]; exact List.mem_cons_of_mem _ hp

/-- Its function `0` is the entry calling the compiled extractor. -/
theorem extractorProgram_entry : compiledKnowledgeExtractor[0]? = some (entryBody
    extractorC.costIdx) :=
  extractorProgram_includes_all.get (by rw [extractorProgramBodies_eq]; exact List.mem_cons_self)

/-- **The compiled extractor's price is within the budget** (`extractorC_within`,
`Cost/Bounds/Top.lean`): wherever the proof announces a shape, the price in `compiledKnowledgeExtractor` and
the entry's `14` are within `leanVmKnowledgeExtractorBudget`. -/
theorem extractorPrice_within_budget : ∀ prog input T π layout logInverseRate st (t : Execution prog),
    afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st) →
    extractorTop prog input (permutationQueries T) π = some t →
    machineCost compiledKnowledgeExtractor extractorC.costIdx
        [encodeValue prog, encodeValue input, encodeValue (permutationQueries T), encodeValue π] + 14 ≤
      leanVmKnowledgeExtractorBudget (permutationQueries T).length :=
  fun prog input T π layout logInverseRate st _ ha _ ↦
    Bounds.extractorC_within compiledKnowledgeExtractor extractorProgram_includes prog input T
        π layout
      logInverseRate st ha

/-- **The extractor `compiledKnowledgeExtractor` computes is `transcriptExtractor`**: its spec and its price
within the budget. -/
theorem extractorOf_extractorProgram : LeanVM.extractorComputedBy compiledKnowledgeExtractor = transcriptExtractor :=
  extractorOf_eq_of_spec compiledKnowledgeExtractor extractorProgram_size_le extractorC.costIdx
    extractorProgram_entry
    (fun prog input qs π ↦ machineCost compiledKnowledgeExtractor extractorC.costIdx
      [encodeValue prog, encodeValue input, encodeValue qs, encodeValue π])
    (fun prog input qs π ↦ extractorC.costSpec compiledKnowledgeExtractor extractorProgram_includes
      prog input qs π)
    extractorPrice_within_budget

end

end LeanVM.Cost
