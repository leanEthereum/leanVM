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
slot the root-most layer writes, of `L = 2 - sh` (`half = g^((1 - sh) / 4)`,
`parity = g^((1 - sh) % 4)`), `n ≤ m` of them run `gkrPairs n` to the slot of `L = 2n + 2 - sh`,
the row `40n` words on.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **The layers in sequence.** -/
theorem ly_chain {rd : Reader} {sg og layers kmn : E} {sh m : ℕ} (hk : KModNext rd kmn)
    (hsg : sg = gen ^ (2 - sh)) (hog : og = gen ^ sh) (hsh2 : sh < 2) (hm : m < 2 ^ 30)
    (hB : ∀ j < m, LyB rd sg og layers kmn (gen ^ j))
    {s0 : Fs} {c0 : E} {st0 : GkrState} {row0 pos0 : E}
    (h0 : GkSlot rd layers (2 - sh) s0 c0 st0 row0 pos0 (gen ^ ((1 - sh) / 4))
      (gen ^ ((1 - sh) % 4))) :
    ∀ n ≤ m, ∃ (xs : List E) (st : GkrState) (s : Fs) (pos : E),
      RunsTo (gkrPairs n st0) s0 xs st s ∧ TbReadsAt rd c0 xs ∧
      GkSlot rd layers (2 * n + 2 - sh) s (c0 * gen ^ xs.length) st (row0 * gen ^ (40 * n)) pos
        (gen ^ ((n + 1 - sh) / 4)) (gen ^ ((n + 1 - sh) % 4)) := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨[], st0, s0, pos0, runsTo_ret _ _, tbReadsAt_nil _ _, ?_⟩
    simpa using h0
  | succ n ih =>
    obtain ⟨xs, st, s, pos, hrun, hrd, hslot⟩ := ih (by omega)
    obtain ⟨xs', st', s', pos', hrun', hrd', hslot'⟩ :=
      hB n (by omega) hk n sh rfl hsg hog (by omega) hsh2 s _ st _ pos hslot
    refine ⟨xs ++ xs', st', s', pos', ?_, ?_, ?_⟩
    · have := hrun.bind hrun'
      exact this
    · rw [tbReadsAt_append]
      exact ⟨hrd, hrd'⟩
    · rw [show 2 * (n + 1) + 2 - sh = 2 * n + 2 - sh + 2 by omega,
        show n + 1 + 1 - sh = n + 2 - sh by omega, List.length_append, pow_add, ← mul_assoc,
        show 40 * (n + 1) = 40 * n + 40 by ring, pow_add, ← mul_assoc]
      exact hslot'

end
end LeanVM.Guest.B1.Tables
