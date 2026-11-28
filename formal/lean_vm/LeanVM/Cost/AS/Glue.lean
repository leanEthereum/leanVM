/-
  LeanVM.Cost.AS.Glue

  The stack size the lite extractor's announced sizes decode to is the one the extractor's budget
  reads.
-/

module

public import Statement.CostMachine
public import LeanVM.Protocol.Extraction.AS.Lite
import LeanVM.Protocol.Compile.RunPure

/-!
# The announced stack size

* `replay_reads`: a replay of `n` reads succeeds only on a stream of at least `n` scalars, and its
  values are the stream's first `n`;
* `buildLayoutLite_stackLog`: `buildLayoutLite` succeeds with a stack size exactly where
  `buildLayout` does, with that stack size;
* **`announced_of_decSizesL`**: the stack size the replay's announced sizes decode to
  (`skelReplayP`, `decSizesL`) is the one the statement's budget reads (`announcedStackLog`).
-/

namespace LeanVM.Cost.AS

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Extraction.AS LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.Relation

public section

private theorem ret_bind {α β : Type} (a : α) (f : α → VerifierProgram β) :
    (VerifierProgram.ret a >>= f) = f a := rfl

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

theorem tables_widths_opcodes : tables.map (fun t ↦ (t.width, t.opcode)) =
    [(7, 0), (9, 1), (5, 2), (10, 3), (14, 4), (68, 5)] := by decide +kernel

theorem columnKappas_tables (logMemory : ℕ) (tableLogHeights : List ℕ) :
    columnKappas tables logMemory tableLogHeights = columnKappasL logMemory tableLogHeights := by
  unfold columnKappas columnKappasL
  have h : tables.flatMap (fun t ↦ List.replicate t.width (tableLogHeights.getD t.opcode 0)) =
      (tables.map fun t ↦ (t.width, t.opcode)).flatMap
        fun p ↦ List.replicate p.1 (tableLogHeights.getD p.2 0) := by
    rw [List.flatMap_map]
  rw [h, tables_widths_opcodes]
  rfl

/-- **`buildLayoutLite` is `buildLayout`'s sizes.** -/
theorem buildLayoutLite_lite (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) :
    buildLayoutLite bytecode logMemory tableRows =
      (buildLayout bytecode logMemory tableRows).map Layout.lite := by
  unfold buildLayoutLite buildLayout
  rcases log2Strict bytecode.length with _ | logLength
  · rfl
  · dsimp only
    split_ifs
    · rw [columnKappas_tables]
      rfl
    · rfl

/-- **The stack size the decoded announced sizes give is the one the budget reads.** -/
theorem announced_of_decSizesL (F : KeccakState → Option KeccakState) (prog : LeanIsaProgram)
    (π : Proof) (seed : KeccakState) {r₁ : List EvP × VerifierProgramState} {lay : LayoutLite} {ρ : ℕ}
    (hr : skelReplayP F skSizes (startState π seed) = some r₁)
    (hd : decSizesL (bytecodeWords prog) r₁.1 = some (lay, ρ)) :
    Cost.announcedStackLog prog π = lay.stackLog := by
  obtain ⟨hn, hm⟩ := replay_reads F _ _ r₁ hr
  change 2 + nTables ≤ π.stream.length at hn
  change _ = some (π.stream.take (2 + nTables)) at hm
  unfold decSizesL at hd
  rw [hm, Option.bind_some] at hd
  unfold sizesOfL at hd
  dsimp only at hd
  split_ifs at hd with h1 h2
  obtain ⟨lay', hb, hd⟩ := Option.bind_eq_some_iff.mp hd
  split_ifs at hd with h3
  cases hd
  rw [buildLayoutLite_lite] at hb
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨s', -, hs'⟩ := runPure_readScalars (2 + nTables)
    ⟨⟨default, [], none⟩, π.stream, [], []⟩ rfl hn
  unfold Cost.announcedStackLog announcedLayoutAndRate readAnnouncedSizes
  show ((runPure ((VerifierProgram.readScalars (2 + nTables)).bind _) _).map _ |>.map _).getD 0 = _
  rw [runPure_bind, hs', Option.bind_some]
  have h3' : Whir.minLogStack ≤ L.stackLog ∧ L.stackLog ≤ Whir.maxLogStack := h3
  simp only [VerifierProgram.require, h1, h2, h3', hL, ite_true, Verifier.liftOption, ret_bind]
  rfl

end

end LeanVM.Cost.AS
