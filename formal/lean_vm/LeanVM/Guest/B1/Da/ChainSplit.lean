/-
  LeanVM.Guest.B1.Da.ChainSplit

  A `KECCAK` chain's check in parts, for kernel evaluation in separate modules.
-/

module

public import LeanVM.Guest.B1.Da.RowShape

/-!
# Checking a long chain in parts

`ChainSpec.check` evaluates every block of a chain at once; for chains of tens of blocks the
kernel's evaluation is large. `ChainSpec.partOk s atoms lo hi` checks blocks `lo ≤ k < hi`, and
`check_of_parts` assembles the shape and the parts into `check`.
-/

namespace LeanVM.Guest.B1.Digest.ChainSpec

open LeanVM.Guest.Core

@[expose] public section

variable (s : ChainSpec)

/-- Block `k`'s checks. -/
def blockAll (atoms : List Atom) (k : ℕ) : Bool :=
  s.blockOk atoms k && (List.range 9).all (s.rateAt atoms k) &&
    (List.range 4).all fun j => s.capAt atoms k (9 + j)

/-- Blocks `lo ≤ k < hi`, checked. -/
def partOk (atoms : List Atom) (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun i => s.blockAll atoms (lo + i)

variable {s}

theorem partOk_sound {atoms : List Atom} {lo hi : ℕ} (h : s.partOk atoms lo hi = true) :
    ∀ k, lo ≤ k → k < hi → s.blockAll atoms k = true := by
  intro k h1 h2
  simp only [partOk, List.all_eq_true, List.mem_range] at h
  have := h (k - lo) (by omega)
  rwa [show lo + (k - lo) = k by omega] at this

theorem check_of_parts {atoms : List Atom} (hs : s.shapeOk = true)
    (h : ∀ k < s.nb, s.blockAll atoms k = true) : s.check atoms = true := by
  simp only [check, hs, Bool.true_and, List.all_eq_true, List.mem_range]
  intro k hk
  have := h k hk
  simpa [blockAll] using this

end
end LeanVM.Guest.B1.Digest.ChainSpec
