/-
  LeanVM.Guest.B1.Bits.AssertCanonical

  B1 for `assert_canonical`.
-/

module

public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Bits.Templates

/-!
# `assert_canonical` (G:558-565, TRIAGE #2)

Its body is `canonicalLimbsT (.n 0) 1`, then the return of `0`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_assert_canonical : coreProgram.find? "assert_canonical" = some Data.core1 :=
  Program.find?_of_indexOf? (j := 1) (by decide +kernel) rfl

theorem core1_body : Fn.body Data.core1 =
    canonicalLimbsT (.n 0) 1 ++ [.atom (.const (.n 5) (word 0 0 0)), .ret [.n 5]] := rfl

/-- **`assert_canonical`'s core IR is its meaning.** -/
theorem assert_canonical_holds : assert_canonical_Spec := by
  intro rd args rets
  rw [rel_iff_sem find_assert_canonical, core1_body, show Fn.params Data.core1 = [.n 0] from rfl]
  simp only [holdsList_append, holds_canonicalLimbsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, word_zero]
  constructor
  · rintro ⟨σ, rfl, ⟨hc, -⟩, h5, hret⟩
    exact ⟨hc, by rw [← hret, h5]⟩
  · intro hm
    obtain ⟨w, rfl⟩ : ∃ w, args = [w] := by
      match args, hm with
      | [a], _ => exact ⟨a, rfl⟩
    obtain ⟨hc, rfl⟩ := hm
    refine ⟨setl (Val.ofArgs [w]) 1 [ofK (w.limb 0), w + ofK (w.limb 0), word 1 0 1,
      ofK (w.limb 1), 0], ?_, ⟨hc, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals b1_look

end
end LeanVM.Guest.B1
