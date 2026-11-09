/-
  LeanVM.Guest.B1.Digest.Window

  The checks of a long chain and its loads, cut into windows of blocks and of cells, each window a
  kernel check of its own (a module of its own for the 64-block frame loops).
-/

module

public import LeanVM.Guest.B1.Digest.Steps

/-!
# Windows of the chain and load checks

`ChainSpec.check` runs over all of a chain's blocks and `loadsOk` over all of its cells in one
evaluation; the kernel's evaluation of the 64-block frame loops' checks holds over 20 GB. Here
`ChainSpec.blocksOk s atoms lo n` checks blocks `lo ≤ k < lo + n` and `loadsWin atoms p msg lo n`
cells `lo ≤ i < lo + n`; `check_of_blocks` and `loadsOk_of_wins` put windows of width `w`
covering the chain together.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

namespace ChainSpec

/-- Blocks `lo ≤ k < lo + n` of the chain pass the checker. -/
def blocksOk (s : ChainSpec) (atoms : List Atom) (lo n : ℕ) : Bool :=
  (List.range' lo n).all fun k =>
    s.blockOk atoms k && (List.range 9).all (s.rateAt atoms k) &&
      (List.range 4).all fun j => s.capAt atoms k (9 + j)

/-- **The checker from windows**: the shape, and windows of `w` blocks covering the chain. -/
theorem check_of_blocks {s : ChainSpec} {atoms : List Atom} {w W : ℕ} (hs : s.shapeOk = true)
    (hnb : s.nb ≤ w * W) (h : ∀ i < W, s.blocksOk atoms (w * i) w = true) :
    s.check atoms = true := by
  simp only [check, hs, Bool.true_and, List.all_eq_true, List.mem_range]
  intro k hk
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hi : k / w < W := by
    rw [Nat.div_lt_iff_lt_mul hw]; rw [Nat.mul_comm] at hnb; omega
  have := h (k / w) hi
  simp only [blocksOk, List.all_eq_true, List.mem_range'] at this
  exact this k ⟨k % w, Nat.mod_lt _ hw, by rw [Nat.one_mul]; exact (Nat.div_add_mod k w).symm⟩

end ChainSpec

/-- Message cells `lo ≤ i < lo + n` are loaded through `p` at offset `i`. -/
def loadsWin (atoms : List Atom) (p : V) (msg : List (Option V)) (lo n : ℕ) : Bool :=
  (List.range' lo n).all fun i => match msg.getD i none with
    | some v => atoms.any (isLoadAt v p i)
    | none => false

/-- **The loads from windows** of `w` cells covering the message. -/
theorem loadsOk_of_wins {atoms : List Atom} {p : V} {msg : List (Option V)} {w W : ℕ}
    (hl : msg.length ≤ w * W) (h : ∀ i < W, loadsWin atoms p msg (w * i) w = true) :
    loadsOk atoms p msg = true := by
  simp only [loadsOk, List.all_eq_true, List.mem_range]
  intro k hk
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hi : k / w < W := by
    rw [Nat.div_lt_iff_lt_mul hw]; rw [Nat.mul_comm] at hl; omega
  have := h (k / w) hi
  simp only [loadsWin, List.all_eq_true, List.mem_range'] at this
  exact this k ⟨k % w, Nat.mod_lt _ hw, by rw [Nat.one_mul]; exact (Nat.div_add_mod k w).symm⟩

end
end LeanVM.Guest.B1.Digest
