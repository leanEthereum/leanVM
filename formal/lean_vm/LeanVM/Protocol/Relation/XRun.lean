/-
  LeanVM.Protocol.Relation.XRun

  Extracted runs of sequences and their roots, the committed word of a prefix of the log, and the
  logged experiment in two stages.
-/

module

public import LeanVM.Protocol.Compile.Rom.History
public import LeanVM.Protocol.Compile.Rom.Extract
public import LeanVM.Protocol.Compile.Rom.Bridge
public import LeanVM.Protocol.Compile.Cost
public import LeanVM.Protocol.Extraction.Defs

/-!
# Extracted runs and the log in two stages

From tag `formal-bus-archive`, `EndToEnd/Sound/Extractor.lean`, with the packed messages.

* `xrun_bind`, `xrun_rootsInv`: the extracted run of a sequence is the runs of its parts, and the
  roots of a run are its history's commitments.
* `commits_length_le_of_costs`: a run's commitments are at most half its cost.
* `committedWord_eq`: the word read from the Keccak-256 answers of a prefix of the log is the
  word extracted from the whole log, provided no entry past the prefix answers the root.
* `logged2`: the experiment in two stages, the adversary's log then the verifier's.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleComp OracleSpec

@[expose] public section

/-! ## Extracted runs -/

section XRun

variable (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)

/-- **The extracted run of a sequence** is the extracted run of its first part, then of the
second from where the first stopped. -/
theorem xrun_bind {α β : Type} (f : α → VerifierProgram β) :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev),
      xrun H F (p.bind f) s h = (xrun H F p s h).bind fun r ↦ xrun H F (f r.1) r.2.1 r.2.2
  | .ret a, s, h => rfl
  | .fail, s, h => rfl
  | .read k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rcases Compile.absorb (m := Option) F s.sponge _ _ with _ | sp
      · rfl
      · exact xrun_bind f _ _ _
    · rfl
  | .sample k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    rcases squeeze (m := Option) F s.sponge with _ | r
    · rfl
    · exact xrun_bind f _ _ _
  | .readPacked n k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rcases observePacked (m := Option) F s.sponge (s.stream.take n) with _ | sp
      · rfl
      · exact xrun_bind f _ _ _
    · rfl
  | .samplePacked n k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    rcases samplesPacked (m := Option) F s.sponge n with _ | r
    · rfl
    · exact xrun_bind f _ _ _
  | .grind bits k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rcases absorbNonce (m := Option) F s.sponge _ with _ | r
      · rfl
      · simp only [Option.bind_some]
        split
        · exact xrun_bind f _ _ _
        · rfl
    · rfl
  | .commit height width k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rcases Compile.absorb (m := Option) F s.sponge _ _ with _ | sp0
      · rfl
      · simp only [Option.bind_some]
        rcases Compile.absorb (m := Option) F sp0 _ _ with _ | sp1
        · rfl
        · exact xrun_bind f _ _ _
    · rfl
  | .query i ps k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · split
      · exact xrun_bind f _ _ _
      · rfl
    · rfl

/-- **The roots of an extracted run are its history's commitments**, the words extracted under
the roots. -/
theorem xrun_rootsInv {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev) {a : α} {s' :
        VerifierProgramState} {h' : List Ev},
      RootsInv H s h → xrun H F p s h = some (a, s', h') → RootsInv H s' h'
  | .ret a, s, h, _, _, _, hR, hr => by
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact hR
  | .fail, s, h, _, _, _, _, hr => by simp [xrun] at hr
  | .read k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · rename_i x xs hs _
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp, -, hr⟩ := hr
      exact xrun_rootsInv _ _ _ (rootsInv_append_read hR x sp xs) hr
    · simp at hr
  | .sample k, s, h, _, _, _, hR, hr => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨r, -, hr⟩ := hr
    exact xrun_rootsInv _ _ _ (rootsInv_append_sample hR _ r.2) hr
  | .readPacked n k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp, -, hr⟩ := hr
      exact xrun_rootsInv _ _ _ (rootsInv_append_readPacked hR _ sp _) hr
    · simp at hr
  | .samplePacked n k, s, h, _, _, _, hR, hr => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨r, -, hr⟩ := hr
    exact xrun_rootsInv _ _ _ (rootsInv_append_samplePacked hR _ r.2) hr
  | .grind bits k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · rename_i n xs hs _
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨r, -, hr⟩ := hr
      split at hr
      · exact xrun_rootsInv _ _ _ (rootsInv_append_grind hR bits r.2 xs) hr
      · simp at hr
    · simp at hr
  | .commit height width k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · rename_i x0 x1 xs hs _
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp0, -, sp1, -, hr⟩ := hr
      exact xrun_rootsInv _ _ _
        (rootsInv_append_commit hR (digestFromHalves (x0, x1)) height width sp1 xs) hr
    · simp at hr
  | .query i ps k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · split at hr
      · exact xrun_rootsInv _ _ _ (rootsInv_append_query hR _ _) hr
      · simp at hr
    · simp at hr

end XRun

/-- **A run's commitments are at most half its cost.** -/
theorem commits_length_le_of_costs {α : Type} {height : ℕ} :
    ∀ {p : VerifierProgram α} {n : ℕ} {Q : α → Prop} {l : List Ev} {q : VerifierProgram α},
      VerifierProgram.Costs height p n Q → p.after l = some q → 2 * (commits l).length ≤ n
  | _, _, _, [], _, _, _ => by simp [commits]
  | .ret _, _, _, _ :: _, _, _, ha => by simp [VerifierProgram.after] at ha
  | .fail, _, _, _ :: _, _, _, ha => by simp [VerifierProgram.after] at ha
  | .read k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    have := commits_length_le_of_costs (hc.2 _) ha
    simp only [commits]
    omega
  | .sample k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    have := commits_length_le_of_costs (hc.2 _) ha
    simp only [commits]
    omega
  | .readPacked m k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    split at ha
    · have := commits_length_le_of_costs (hc.2 _) ha
      simp only [commits]
      omega
    · simp at ha
  | .samplePacked m k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    split at ha
    · have := commits_length_le_of_costs (hc.2 _) ha
      simp only [commits]
      omega
    · simp at ha
  | .grind b k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    split at ha
    · have := commits_length_le_of_costs hc.2 ha
      simp only [commits]
      omega
    · simp at ha
  | .commit ht w k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    split at ha
    · have := commits_length_le_of_costs hc.2.2 ha
      have h2 := hc.2.1
      simp only [commits, List.length_cons]
      omega
    · simp at ha
  | .query i ps k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    have := commits_length_le_of_costs (hc.2 _) ha
    simp only [commits]
    omega

/-! ## The committed word -/

/-- **The word the specification reads from a prefix of the log is the word extracted from the
whole log**, without failure and when no hash entry past the prefix answers the root. -/
theorem committedWord_eq {X : Type} {σ : Seeds X} {ℓ : Log} {k : ℕ} {r : Digest}
    (hf : ¬ Fail σ ℓ) (hr : ∀ x, .inl (x, r) ∉ ℓ.drop k) (ht w : ℕ) :
    Extraction.committedWord (lookH (ℓ.take k)) r ht w = extract (lookH ℓ) r ht w := by
  have hbefore : HEntriesBefore ℓ r k := by
    intro i hi x hei
    by_contra hik
    refine hr x ?_
    rw [List.mem_iff_getElem]
    exact ⟨i - k, by simp; omega, by
      simp only [List.getElem_drop, Nat.add_sub_cancel' (by omega : k ≤ i)]; exact hei⟩
  rw [← extract_take_eq hf hbefore ht w]
  rfl

/-! ## The experiment in two stages -/

/-- The logged experiment in two stages: the adversary's run from the empty log, with the log it
leaves, then the verifier's run from that log. -/
noncomputable def logged2 {α : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) : ProbComp ((α × Log) × (Bool × Log)) :=
  (simulateQ loggedRO A).run [] >>= fun p ↦
    (fun r ↦ (p, r)) <$> (simulateQ loggedRO (V p.1)).run p.2

/-- The logged experiment forgets the adversary's log. -/
theorem logExperiment_eq_logged2 {α : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) :
    logExperiment A V = (fun w ↦ ((w.1.1, w.2.1), w.2.2)) <$> logged2 A V := by
  rw [logExperiment, Rom.run_simulateQ_bind, logged2, map_bind]
  refine bind_congr fun p ↦ ?_
  rw [simulateQ_map, StateT.run_map, Functor.map_map]

end
end LeanVM.Protocol.Relation
