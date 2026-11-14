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

The checks are membership tests, so a check of a sublist is one of the list (`blocksOk_sub`,
`loadsWin_sub`). A window searches only from where its atoms start: `blocksFrom` after the
`KECCAK` before its first block (`afterKeccaks`), `loadsFrom` from its first cell's load, so its
cost does not grow with its place in the body (`blocksOk_of_from`, `loadsWin_of_from`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

open scoped VDec

@[expose] public section

/-- The atoms after the first `n` `KECCAK`s. -/
def afterKeccaks : ℕ → List Atom → List Atom
  | 0, as => as
  | _ + 1, [] => []
  | n + 1, .keccak .. :: as => afterKeccaks n as
  | n + 1, _ :: as => afterKeccaks (n + 1) as

theorem mem_of_afterKeccaks {n : ℕ} {as : List Atom} {a : Atom} (h : a ∈ afterKeccaks n as) :
    a ∈ as := by
  induction as generalizing n with
  | nil => cases n <;> simp [afterKeccaks] at h
  | cons b as ih =>
    cases n with
    | zero => exact h
    | succ n =>
      cases b <;> simp only [afterKeccaks] at h <;> exact List.mem_cons_of_mem _ (ih h)

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

theorem blocksOk_sub {s : ChainSpec} {l l' : List Atom} (hs : ∀ a ∈ l, a ∈ l') {lo n : ℕ}
    (h : s.blocksOk l lo n = true) : s.blocksOk l' lo n = true := by
  simp only [blocksOk, List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact fun k hk => ⟨⟨s.blockOk_sub hs (h k hk).1.1, fun c hc => s.rateAt_sub hs ((h k hk).1.2 c hc)⟩,
    fun j hj => s.capAt_sub hs ((h k hk).2 j hj)⟩

/-- Blocks `lo ≤ k < lo + n`, their atoms searched after the `lo`-th `KECCAK` (block `lo - 1`'s),
which every one of them follows: a window's searches start at the window. -/
def blocksFrom (s : ChainSpec) (atoms : List Atom) (lo n : ℕ) : Bool :=
  s.blocksOk (afterKeccaks lo atoms) lo n

theorem blocksOk_of_from {s : ChainSpec} {atoms : List Atom} {lo n : ℕ}
    (h : s.blocksFrom atoms lo n = true) : s.blocksOk atoms lo n = true :=
  blocksOk_sub (fun _ ha => mem_of_afterKeccaks ha) h

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

theorem loadsWin_sub {l l' : List Atom} (hs : ∀ a ∈ l, a ∈ l') {p : V} {msg : List (Option V)}
    {lo n : ℕ} (h : loadsWin l p msg lo n = true) : loadsWin l' p msg lo n = true := by
  simp only [loadsWin, List.all_eq_true] at h ⊢
  intro i hi
  have := h i hi
  split at this
  · exact any_sub hs this
  · exact absurd this (by simp)

/-- A load at offset `o`. -/
def loadOffIs (o : ℕ) : Atom → Bool
  | .load _ _ off => off == o
  | _ => false

/-- Cells `lo ≤ i < lo + n`, their loads searched from the first load at offset `lo` on. -/
def loadsFrom (atoms : List Atom) (p : V) (msg : List (Option V)) (lo n : ℕ) : Bool :=
  loadsWin (atoms.dropWhile fun a => !loadOffIs lo a) p msg lo n

theorem loadsWin_of_from {atoms : List Atom} {p : V} {msg : List (Option V)} {lo n : ℕ}
    (h : loadsFrom atoms p msg lo n = true) : loadsWin atoms p msg lo n = true :=
  loadsWin_sub (fun _ ha => (List.dropWhile_suffix _).subset ha) h

end
end LeanVM.Guest.B1.Digest
