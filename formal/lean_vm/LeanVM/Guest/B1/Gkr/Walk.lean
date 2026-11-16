/-
  LeanVM.Guest.B1.Gkr.Walk

  The layers of `verify_bus_gkr` in sequence: `n` iterations of `verify_bus_gkr_loop0` from the
  root-most layer's slot are `gkrPairs n`.
-/

module

public import LeanVM.Guest.B1.Gkr.Root

/-!
# The walk by layers

`ly_chain`: when the iterations at `g^j`, `j < m`, are steps of two levels (`LyB`), then from the
slot the root-most layer writes, of `L = 2 - sh`, its point in row `1` at `pts`, `n ≤ m` of them run
`gkrPairs n` to the slot of `L = 2n + 2 - sh`, its point in row `n + 1`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **The layers in sequence.** -/
theorem ly_chain {rd : Reader} {sg og layers pts : E} {sh m : ℕ}
    (hsg : sg = gen ^ (2 - sh)) (hog : og = gen ^ sh) (hsh2 : sh < 2) (hm : m < 2 ^ 30)
    (hB : ∀ j < m, LyB rd sg og layers pts (gen ^ j))
    {s0 : Fs} {c0 : E} {st0 : GkrState} {pos0 : E}
    (h0 : GkSlot rd layers (2 - sh) s0 c0 st0 (pts * gen ^ 40) pos0) :
    ∀ n ≤ m, ∃ (xs : List E) (st : GkrState) (s : Fs) (pos : E),
      RunsTo (gkrPairs n st0) s0 xs st s ∧ TbReadsAt rd c0 xs ∧
      GkSlot rd layers (2 * n + 2 - sh) s (c0 * gen ^ xs.length) st (pts * gen ^ (40 * (n + 1)))
        pos := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨[], st0, s0, pos0, runsTo_ret _ _, tbReadsAt_nil _ _, ?_⟩
    simpa using h0
  | succ n ih =>
    obtain ⟨xs, st, s, pos, hrun, hrd, hslot⟩ := ih (by omega)
    obtain ⟨xs', st', s', pos', hrun', hrd', hslot'⟩ :=
      hB n (by omega) n sh rfl hsg hog (by omega) hsh2 s _ st pos hslot
    refine ⟨xs ++ xs', st', s', pos', ?_, ?_, ?_⟩
    · have := hrun.bind hrun'
      exact this
    · rw [tbReadsAt_append]
      exact ⟨hrd, hrd'⟩
    · rw [show 2 * (n + 1) + 2 - sh = 2 * n + 2 - sh + 2 by omega, List.length_append, pow_add,
        ← mul_assoc]
      exact hslot'

end
end LeanVM.Guest.B1.Tables
