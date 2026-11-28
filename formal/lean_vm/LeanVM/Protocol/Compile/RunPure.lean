/-
  LeanVM.Protocol.Compile.RunPure

  The verifier program run with every permutation answered by `default` (`Compile.runPure`), and
  the layout and rate a stream announces (`Verifier.announcedLayoutAndRate`), both in
  `Statement/Verifier/Lib.lean`, where the extractor's budget reads them.
-/

module

public import Statement.Verifier.Lib
public import CompPoly.Fields.Binary.BF64

/-!
# The pure run's algebra

* `runPure_bind`: a sequence runs as its first program, then the continuation on its value;
* `runPure_readScalars`: where no grind's challenge waits and the stream holds `n` scalars,
  `readScalars n` returns the stream's first `n`, and no challenge waits after it.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

public section

/-- **`runPure` of a sequence**: the first program's run, then the continuation's. -/
theorem runPure_bind {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β)
    (s : VerifierProgramState) :
    runPure (p.bind f) s = (runPure p s).bind fun r ↦ runPure (f r.1) r.2 := by
  induction p generalizing s with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [runPure, VerifierProgram.bind, run]
    split
    · exact ih _ _
    · rfl
  | sample k ih => exact ih _ _
  | readPacked n k ih =>
    simp only [runPure, VerifierProgram.bind, run]
    split
    · exact ih _ _
    · rfl
  | samplePacked n k ih => exact ih _ _
  | grind b k ih =>
    simp only [runPure, VerifierProgram.bind, run]
    split
    · simp only [bind, pure]
      split
      · exact ih _
      · rfl
    · rfl
  | commit h w k ih =>
    simp only [runPure, VerifierProgram.bind, run]
    split
    · exact ih _
    · rfl
  | query i ps k ih =>
    simp only [runPure, VerifierProgram.bind, run]
    split
    · simp only [bind]
      split
      · exact ih _ _
      · rfl
    · rfl

/-- Absorbing keeps the grind's challenge. -/
theorem ground_absorb_id (sp : Sponge) (x : E) (tag : ℕ) :
    (Id.run (absorb (m := Id) (fun _ ↦ default) sp x tag)).ground = sp.ground := by
  simp only [absorb, duplex, Id.run]
  split_ifs <;> rfl

/-- **`readScalars`, run**: the stream's first `n` scalars, no challenge waiting after them. -/
theorem runPure_readScalars : ∀ (n : ℕ) (s : VerifierProgramState), s.sponge.ground = none →
    n ≤ s.stream.length → ∃ s' : VerifierProgramState, s'.sponge.ground = none ∧
      runPure (VerifierProgram.readScalars n) s = some (s.stream.take n, s')
  | 0, s, hg, _ => ⟨s, hg, rfl⟩
  | n + 1, ⟨sp, [], os, rs⟩, _, hn => by simp at hn
  | n + 1, ⟨sp, x :: xs, os, rs⟩, hg, hn => by
    simp only at hg
    let sp' := Id.run (absorb (m := Id) (fun _ ↦ default) sp x dsObserve)
    have h1 : runPure VerifierProgram.readScalar ⟨sp, x :: xs, os, rs⟩ =
        some (x, ⟨sp', xs, os, rs⟩) := by
      simp only [runPure, VerifierProgram.readScalar, run, hg]
      rfl
    obtain ⟨s', hg', hs'⟩ := runPure_readScalars n ⟨sp', xs, os, rs⟩
      (by simp only [sp', ground_absorb_id, hg]) (by simp at hn ⊢; omega)
    refine ⟨s', hg', ?_⟩
    show runPure (VerifierProgram.readScalar.bind fun y ↦
      (VerifierProgram.readScalars n).bind fun ys ↦ VerifierProgram.ret (y :: ys)) _ = _
    rw [runPure_bind, h1, Option.bind_some, runPure_bind, hs', Option.bind_some]
    rfl

end

end LeanVM.Protocol.Compile
