/-
  LeanVM.Guest.B1.Place.LqTable

  The facts of `lqTable`'s entries `level_queries`' placed completeness reads, decided.
-/

module

public import LeanVM.Guest.B1.Place.Lq

/-!
# `lqTable`'s entries, checked

For each entry `(name, q, base, il, leaf, d, cd)` of `lqTable` (`LqEntry`, decided by the kernel
in `lqTable_entry`): `verify_merkle_cap__L{cd}` is in `merkleCapNames`; `opening_queries`'
specialization `oqName …` is in `openingQueriesLoops` with its loop helper `oqLoopOf …`, the shape
`lqShape base il d cd` and `odd = q % 2 · base`; `base ≤ 1`, `1 ≤ cd ≤ d`, `cd ≤ 8`; `q`'s power
digits; the two callees' names differ; and the words of a fresh instance (`lqFreshSize`) fit below
`ordG`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Whir (lqIters lqTable natStr oqName digitsVal osPowDigits)

@[expose] public section

/-- The name of `verify_merkle_cap`'s specialization at cap depth `cd`. -/
def vmcName (cd : ℕ) : String := "verify_merkle_cap__L" ++ natStr cd

/-- The words of a fresh instance of `level_queries`: the row weights, the window pointers, the
windows, the cap, the flags and `opening_queries`' chain buffer. -/
def lqFreshSize (q base il d cd : ℕ) : ℕ :=
  ((lqShape base il d cd).lo + il / (lqShape base il d cd).lo) + q + q * qwN d cd + 4 * 2 ^ cd +
    2 ^ cd + (lqIters q base + 1)

/-- An entry's facts. -/
abbrev LqEntry (q base il leaf d cd : ℕ) : Prop :=
  (vmcName cd, cd) ∈ merkleCapNames ∧
    (∃ p ∈ openingQueriesLoops, p.1 = oqName q base il leaf d cd ∧
      p.2.1 = oqLoopOf (oqName q base il leaf d cd) ∧ p.2.2.1.base = base ∧ p.2.2.1.I = il ∧
      p.2.2.1.pd = d - cd ∧ p.2.2.1.cd = cd ∧ p.2.2.2 = q % 2 * base) ∧
    base ≤ 1 ∧ 1 ≤ cd ∧ cd ≤ d ∧ cd ≤ 8 ∧ digitsVal (osPowDigits q) 1 = q ∧
    oqName q base il leaf d cd ≠ vmcName cd ∧ lqFreshSize q base il d cd < ordG

set_option maxRecDepth 100000 in
theorem lqTable_entry : ∀ e ∈ lqTable,
    LqEntry e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 := by
  decide +kernel

/-- An entry's `opening_queries` specialization, in the table. -/
theorem LqEntry.oqMem {q base il leaf d cd : ℕ} (h : LqEntry q base il leaf d cd) :
    (oqName q base il leaf d cd, oqLoopOf (oqName q base il leaf d cd), lqShape base il d cd,
      q % 2 * base) ∈ openingQueriesLoops := by
  obtain ⟨-, ⟨⟨n, l, ⟨a, b, c, d'⟩, o⟩, hp, h1, h2, h3, h4, h5, h6, h7⟩, -⟩ := h
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  exact hp

end
end LeanVM.Guest.B1
