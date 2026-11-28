module

public import NativeRustcVm.Transcript.Update

/-!
# The transcript's state after its phase changed

`TState::query_openings` advances the openings' cursor (`phase`, the word at `t + 360`) and
writes nothing else of the `TState`: `TStateAt.with_phase`, as `TStateAt.with_cursor`.
-/

namespace NativeRustcVm.Transcript

open NativeVm NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Semantics

public section

variable {d d' : Mem 64} {t : BitVec 64} {a : DecArea} {s : TState}

/-- **The phase changed.** -/
theorem TStateAt.with_phase {R : BitVec 64 → Prop} (h : TStateAt d t a s) (hk : Keeps d d')
    (hR : ∀ q, R q → ¬ InRange t tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q)
    (hs : SameOutside d d' (fun q ↦ Touch t tstateBytes (fun j ↦ 360 ≤ j ∧ j < 368) q ∨ R q))
    {p : Nat} (hpl : p ≤ s.openings.size) (hp : WordAt d' (off t 360) p.toUInt64) :
    TStateAt d' t a { s with phase := p } := by
  obtain ⟨hA, hD⟩ := h.agrees hR hs
  unfold tstateBytes at hA
  exact h.agree hk hA hD (h.sponge.agree hA (by unfold spongeBytes; omega)
      (fun j hj ⟨h1, _⟩ ↦ by unfold spongeBytes at hj; omega)) rfl rfl h.cursor_le
    (wordAt_agree hA (by omega) (fun i hi ↦ by omega) h.cursor) hpl hp h.roots_le
    (wordAt_agree hA (by omega) (fun i hi ↦ by omega) h.n_roots)
    (fun i hi ↦ by
      have hi' : i < s.roots.size := hi
      exact rootAt_agree hA (by have := h.roots_le; unfold maxRoots at this; omega)
        (fun j hj ↦ by omega) (h.roots i hi))
    (fun j hj h1 h2 ↦ by omega)

end

end NativeRustcVm.Transcript
