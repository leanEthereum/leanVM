/-
  LeanVM.Guest.B1.Gkr.Walk

  The layers of `verify_bus_gkr` in sequence: `n` iterations of `__loop6` from a slot are
  `gkrPairs n`.
-/

module

public import LeanVM.Guest.B1.Gkr.Odd

/-!
# The walk by layers

`ly_chain`: when the iterations at `g^j`, `j < m`, are steps of two levels (`LyB`), then from the
slot of `L = sh` (`half = 1`, `parity = 1 = g^0`), `n ≤ m` of them run `gkrPairs n` to the slot of
`L = 2n + sh`, the row `40n` words on.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **The layers in sequence.** -/
theorem ly_chain {rd : Reader} {dsb gmu layers kmn : E} {sh m : ℕ} (hk : KModNext rd kmn)
    (hsh : LoadHolds rd (dsb * gmu) 0 (gen ^ sh)) (hsh2 : sh < 2) (hm : m < 2 ^ 30)
    (hB : ∀ j < m, LyB rd dsb gmu layers kmn (gen ^ j))
    {s0 : Fs} {c0 : E} {st0 : GkrState} {row0 pos0 : E}
    (h0 : GkSlot rd layers sh s0 c0 st0 row0 pos0 1 1) :
    ∀ n ≤ m, ∃ (xs : List E) (st : GkrState) (s : Fs) (pos : E),
      RunsTo (gkrPairs n st0) s0 xs st s ∧ TbReadsAt rd c0 xs ∧
      (s0.pend = [] ∨ 0 < n → s.pend = []) ∧
      GkSlot rd layers (2 * n + sh) s (c0 * gen ^ xs.length) st (row0 * gen ^ (40 * n)) pos
        (gen ^ (n / 4)) (gen ^ (n % 4)) := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨[], st0, s0, pos0, runsTo_ret _ _, tbReadsAt_nil _ _, fun h => h.resolve_right (by omega), ?_⟩
    simpa using h0
  | succ n ih =>
    obtain ⟨xs, st, s, pos, hrun, hrd, -, hslot⟩ := ih (by omega)
    obtain ⟨xs', st', s', pos', hrun', hrd', hp', hslot'⟩ :=
      hB n (by omega) hk n sh rfl hsh (by omega) hsh2 s _ st _ pos hslot
    refine ⟨xs ++ xs', st', s', pos', ?_, ?_, fun _ => hp', ?_⟩
    · have := hrun.bind hrun'
      exact this
    · rw [tbReadsAt_append]
      exact ⟨hrd, hrd'⟩
    · rw [show 2 * (n + 1) + sh = 2 * n + sh + 2 by ring, List.length_append, pow_add,
        ← mul_assoc, show 40 * (n + 1) = 40 * n + 40 by ring, pow_add, ← mul_assoc]
      exact hslot'

end
end LeanVM.Guest.B1.Tables
