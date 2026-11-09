module

public import LeanVM.Cost.Bounds.Layout
public import LeanVM.Cost.Bounds.TranscriptReplay
public import LeanVM.Cost.Bounds.Sizes.Pruning
import all Statement.LeanIsa
import all Statement.LeanVmVerifier
import all LeanVM.Protocol.Extraction.Fast.AfterRoot
import all LeanVM.Protocol.Extraction.Fast.Extract

/-!
# Bounds: facts of the replay, for the assembly

The facts `Bounds/Top.lean` uses to assemble the compiled extractor's price (`extractorC_cost`)
from its parts' bounds (proved in the other modules of `Cost/Bounds/`):

* `bytecodeWords_length`: the bytecode has `16·2^ℓ` words;
* `commitPure_roots`, **`afterRootLite_roots`**: the replay's one root, at the ladder's first level
  (height `μ − 6 + R`, width `64`);
* **`fastStacksFast_length_le`**: at most one fast stack.
-/
namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

public section

/-! ## Facts of the run -/

theorem bytecodeWords_length (prog : Semantics.LeanIsaProgram) :
    (LeanVM.bytecodeWords prog).length = 16 * 2 ^ prog.logSize := by
  simp [LeanVM.bytecodeWords, List.length_flatMap]
  omega

theorem commitPure_roots {height width : ℕ} {s : VerifierProgramState} {t : Unit ×
    VerifierProgramState}
    (h : commitPure height width s = some t) :
    ∃ root, t.2.roots = s.roots ++ [(root, height, width)] := by
  unfold commitPure at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h.symm
      exact ⟨_, rfl⟩
    · simp at h
  · simp at h

/-- **The stack's root**: `afterRootLite`'s one root, at the ladder's first level: height
`μ - 6 + R`, width `2^6`. -/
theorem afterRootLite_roots {bytecode : List K} {π : Proof} {L : LayoutLite} {R : ℕ}
    {st : VerifierProgramState} (h : afterRootLite bytecode π = some ((L, R), st)) :
    ∃ root, st.roots = [(root, L.stackLog - 6 + R, 64)] := by
  unfold afterRootLite at h
  cases hr : readSizesLite bytecode (initialState π) with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr, Option.bind_some] at h
    obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨⟨L', R'⟩, s'⟩ := r
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    obtain ⟨-, -, hroots, -⟩ := readSizesLite_some hr
    unfold commitStackPure at ht
    split at ht
    · rename_i level rest hla
      obtain ⟨hf, hR⟩ := ladder_head hla
      obtain ⟨root, hrt⟩ := commitPure_roots ht
      refine ⟨root, ?_⟩
      rw [hrt, hroots, hf, hR]
      rfl
    · simp at ht

/-- **At most one fast stack**: every lane's pruning step keeps at most as many survivors. -/
theorem fastStacksFast_length_le (μ R : ℕ) (W : ℕ → List K) : (fastStacksFast μ R W).length ≤ 1 := by
  have key : ∀ (f : List (List (Array K) × List ℕ) → ℕ → List (List (Array K) × List ℕ)),
      (∀ st u, (f st u).length ≤ st.length) →
      ∀ (l : List ℕ) (st : List (List (Array K) × List ℕ)), st.length ≤ 1 →
        (l.foldl f st).length ≤ 1 := by
    intro f hf l
    induction l with
    | nil => intro st h; exact h
    | cons u l ih => intro st h; exact ih _ ((hf st u).trans h)
  unfold fastStacksFast
  rw [List.length_map]
  exact key _ (fun st u ↦ pruneStep_single.1) _ _ (by simp)

/-! ## The budget -/

end

end LeanVM.Cost.Bounds
