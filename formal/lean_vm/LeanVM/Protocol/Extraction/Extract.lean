/-
  LeanVM.Protocol.Extraction.Extract

  The knowledge extractor (`LeanVM.Extraction.extract`, `LeanVM/Protocol/Extraction/Extractor.lean`): what it
  returns is a valid execution; it returns one whenever a candidate of the committed word has
  one; and it does not depend on which keys it is given, as long as they cover the answers.
-/

module

public import LeanVM.Protocol.Extraction.Merkle
public import LeanVM.Protocol.Extraction.Prune
public import LeanVM.Protocol.Extraction.Run
public import Statement.LeanVm
public import LeanVM.Protocol.WithHash

/-!
# The extractor, proved

* **`extract_valid`**: whatever `extract` returns is a valid execution of the program on the
  public input (a stack's execution is one, `candidateExecution_valid`).
* **`extract_of_candidate`**: without collisions among the answers and with keys covering them,
  if the proof's steps 1 and 2 announce an admissible shape and a root, and a candidate of the word
  the root commits to (`committedWord`, the classical choice over accepted openings) has an
  execution, then `extract` returns a valid execution. The computed word is the committed word
  (`committedWordC_eq`), the candidate is among the decoded stacks
  (`candidates_subset_decodeStacks`), so the list decoder's branch finds an execution if the fast
  path does not.
* **`extract_keys_congr`**: two key lists that cover the answers give the same extraction
  (`committedWordC_keys_congr`; no injectivity needed). `supportKeys` covers a finite support
  (`keysCover_supportKeys`), and any covering list makes the support finite.
* **`extractorRpm_eq_extract`**: the extractor of the random-permutation model is `extract` on
  the transcript's evaluations and the keys of their support, so it depends on the evaluations
  only.
-/

namespace LeanVM.Extraction.ExtractProofs

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Extraction LeanVM.Extraction.MerkleProofs

@[expose] public section

/-! ## The keys -/

/-- **The computed leaves do not depend on the covering keys.** -/
theorem committedLeaves_keys_congr {answers : Bytes → Option Digest} {keys keys' : List Bytes}
    (hc : KeysCover answers keys) (hc' : KeysCover answers keys') (root : Digest)
    (height width : ℕ) :
    committedLeaves answers keys root height width =
      committedLeaves answers keys' root height width := by
  simp only [committedLeaves, subtreeLeaves_congr (preimage_keys_congr hc hc')]

/-- **The extraction does not depend on the covering keys.** -/
theorem extract_keys_congr (prog : LeanIsaProgram) (input : PublicInput) (bytecode : List K)
    {answers : Bytes → Option Digest} {keys keys' : List Bytes} (hc : KeysCover answers keys)
    (hc' : KeysCover answers keys') (π : Proof) :
    extract prog input bytecode answers keys π = extract prog input bytecode answers keys' π := by
  simp only [extract, committedLeaves_keys_congr hc hc']

/-- A covering key list makes the answers' support finite. -/
theorem finite_of_keysCover {answers : Bytes → Option Digest} {keys : List Bytes}
    (hc : KeysCover answers keys) : {x | answers x ≠ none}.Finite := by
  refine (List.finite_toSet keys).subset fun x hx ↦ ?_
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hx
  exact hc x d hd

/-- **The keys of a finite support cover it.** -/
theorem keysCover_supportKeys {answers : Bytes → Option Digest}
    (h : {x | answers x ≠ none}.Finite) : KeysCover answers (supportKeys answers) := by
  intro x d hx
  simp only [supportKeys, h, ↓reduceDIte, Finset.mem_toList, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, hx]
  exact Option.some_ne_none d

/-! ## What the extractor returns -/

/-- What a search of two lists, the second if the first finds nothing, finds is found in one of
them. -/
theorem orElse_findSome?_eq_some {α β : Type} {f : α → Option β} {l₁ l₂ : List α} {b : β}
    (h : (l₁.findSome? f <|> l₂.findSome? f) = some b) : ∃ a, (a ∈ l₁ ∨ a ∈ l₂) ∧ f a = some b := by
  rcases h₁ : l₁.findSome? f with _ | b₁
  · rw [h₁] at h
    obtain ⟨a, ha, hab⟩ := List.exists_of_findSome?_eq_some (show l₂.findSome? f = some b from h)
    exact ⟨a, Or.inr ha, hab⟩
  · rw [h₁] at h
    obtain rfl : b₁ = b := Option.some.inj h
    obtain ⟨a, ha, hab⟩ := List.exists_of_findSome?_eq_some h₁
    exact ⟨a, Or.inl ha, hab⟩

/-- A search of two lists finds something when an element of the second has a value. -/
theorem orElse_findSome?_isSome {α β : Type} {f : α → Option β} (l₁ : List α) {l₂ : List α}
    {a : α} (ha : a ∈ l₂) {b : β} (hb : f a = some b) :
    ∃ b', (l₁.findSome? f <|> l₂.findSome? f) = some b' := by
  rcases h₁ : l₁.findSome? f with _ | b₁
  · have h₂ : (l₂.findSome? f).isSome :=
      List.findSome?_isSome_iff.mpr ⟨a, ha, Option.isSome_iff_exists.mpr ⟨b, hb⟩⟩
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp h₂
    exact ⟨b', show l₂.findSome? f = some b' from hb'⟩
  · exact ⟨b₁, rfl⟩

section Extract

variable {prog : LeanIsaProgram} {input : PublicInput} {bytecode : List K}
  {answers : Bytes → Option Digest} {keys : List Bytes} {π : Proof}

/-- **The extractor, after the announced shape and root**: the fast path's stacks, then the list
decoder's, searched for an execution. -/
theorem extract_eq_of_root {layout : Layout} {R : ℕ} {st : VerifierProgramState} {root : Digest}
    {height width : ℕ} (haf : afterRoot bytecode π = some ((layout, R), st))
    (hroot : st.roots.head? = some (root, height, width)) :
    extract prog input bytecode answers keys π =
      ((fastStacks layout.stackLog R
          (leafAt (committedLeaves answers keys root height width) height width)).findSome?
            (candidateExecutionIn (powIndex layout.logMemory) (powIndex prog.logSize) prog input
              layout) <|>
        (decodeStacks layout.stackLog R
          (leafAt (committedLeaves answers keys root height width) height width)).findSome?
            (candidateExecutionIn (powIndex layout.logMemory) (powIndex prog.logSize) prog input
              layout)) := by
  unfold extract
  rw [haf]
  dsimp only [bind, Option.bind]
  rw [hroot]

/-- **Whatever the extractor returns is a valid execution.** -/
theorem extract_valid {t : Execution prog} (h : extract prog input bytecode answers keys π = some t) :
    ValidExecution prog input t := by
  rcases haf : afterRoot bytecode π with _ | ⟨⟨layout, R⟩, st⟩
  · simp [extract, haf] at h
  rcases hroot : st.roots.head? with _ | ⟨root, height, width⟩
  · simp [extract, haf, hroot] at h
  rw [extract_eq_of_root haf hroot] at h
  obtain ⟨q, -, hq⟩ := orElse_findSome?_eq_some h
  exact Halting.candidateExecutionIn_valid hq

/-- **The extractor returns a valid execution when a candidate has one**: with the announced
shape admissible, no collision among the answers and keys covering them, if a candidate of the
committed word at the Johnson threshold has an execution, the extractor returns some execution,
and it is valid. -/
theorem extract_of_candidate {layout : Layout} {R : ℕ} {st : VerifierProgramState} {root : Digest}
    {height width : ℕ} (haf : afterRoot bytecode π = some ((layout, R), st))
    (hroot : st.roots.head? = some (root, height, width)) (hinj : AnswersInj answers)
    (hc : KeysCover answers keys) {μ : ℕ} (e : layout.stackLog = μ) (hμ : 16 ≤ μ ∧ μ ≤ 32)
    (hR : 1 ≤ R ∧ R ≤ 4) {q : Vector K (2 ^ μ)}
    (hq : q ∈ Candidates μ R (johnsonThreshold μ R) (committedWord answers root height width))
    {t : Execution prog} (ht : candidateExecution prog input layout q = some t) :
    ∃ t', extract prog input bytecode answers keys π = some t' ∧ ValidExecution prog input t' := by
  subst e
  rw [← committedWordC_eq hinj hc] at hq
  have hmem := PruneProofs.candidates_subset_decodeStacks hμ hR _ hq
  simp only [Set.mem_ofPred_eq, committedWordC] at hmem
  have ht' : candidateExecutionIn (powIndex layout.logMemory) (powIndex prog.logSize) prog input
      layout q = some t := ht
  obtain ⟨t', ht'⟩ := orElse_findSome?_isSome (fastStacks layout.stackLog R
    (leafAt (committedLeaves answers keys root height width) height width)) hmem ht'
  rw [← extract_eq_of_root haf hroot] at ht'
  exact ⟨t', ht', extract_valid ht'⟩

end Extract

/-! ## The extractor of the random-permutation model -/

/-- The paths' byte strings cover their evaluations. -/
theorem keysCover_hashesOf (P : List (Bytes × Digest)) :
    KeysCover (LeanVM.lookupEvaluation P) (P.map (·.1)) := by
  intro x d h
  simp only [LeanVM.lookupEvaluation, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, -⟩ := h
  have hpx := List.find?_some hp
  simp only [decide_eq_true_eq] at hpx
  exact List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hp, hpx⟩

/-- **The extractor of the random-permutation model is `extract` on the transcript's
evaluations**, with the keys of their support: it depends on the evaluations only. -/
theorem extractorRpm_eq_extract (prog : LeanIsaProgram) (input : PublicInput) (T : LeanVM.PermutationTranscript)
    (proof : Proof) {answers : Bytes → Option Digest} (h : LeanVM.lookupEvaluation (LeanVM.keccakEvaluationsOfTranscript T) = answers) :
    LeanVM.transcriptExtractorWithHash prog input T proof =
      extract prog input (bytecodeWords prog) answers (supportKeys answers) proof := by
  have hc : KeysCover answers ((LeanVM.keccakEvaluationsOfTranscript T).map (·.1)) := by
    rw [← h]
    exact keysCover_hashesOf _
  have e : LeanVM.transcriptExtractorWithHash prog input T proof =
      extract prog input (bytecodeWords prog) answers ((LeanVM.keccakEvaluationsOfTranscript T).map (·.1)) proof := by
    rw [← h]
    rfl
  rw [e]
  exact extract_keys_congr _ _ _ hc (keysCover_supportKeys (finite_of_keysCover hc)) _

end
end LeanVM.Extraction.ExtractProofs
