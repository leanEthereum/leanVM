/-
  LeanVM.Guest.B1.Digest.ChildListDefs

  The checks `child_claim_list_any`'s proof evaluates (TRIAGE #89): a claim record, the records'
  layout, `child_claim_list_last__L{k}`'s body, the frame loops' bodies, and the windows of the
  64-block frame loop `__loop17`.
-/

module

public import LeanVM.Guest.B1.Digest.Window

/-!
# `child_claim_list_any`: the checks

What the kernel evaluates for `child_claim_list_any` (`ChildList`): `claimOk` (one record),
`recordsOk` (the records at their layout), `cclOk` (`child_claim_list_last__L{k}`), `anyOk` (a
frame loop of `m` claims), split for the big loop `__loop17` into `anyHead` and the windows
`anyWin i` (four blocks and nine records each, four to a module `ChildListAny{q}`), which
`anyOk_of_parts` puts back together. Only definitions and the gluing.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The bound of the first range check of `x`. -/
def rcOf (atoms : List Atom) (x : V) : Option V :=
  atoms.findSome? fun a => match a with
    | .rangeCheck x' _ _ _ k => if x' = x then some k else none
    | _ => none

/-- The pointer and offset of the first load into `x`. -/
def loadOf (atoms : List Atom) (x : V) : Option (V × ℕ) :=
  atoms.findSome? fun a => match a with
    | .load d p off => if d = x then some (p, off) else none
    | _ => none

/-- The values a claim record reads: the coverage region, the range check's bound `last`, the
table, the first mark. -/
structure ClaimVs where
  region : V
  last : V
  entries : V
  marks : V

/-- **Claim `j`'s record**: its slot `o` range-checked against `last`, its mark (`marks`, or the
previous claim's `prev · g`) loaded at `region · o`, its four cells loaded at `entries · o^4`. -/
def claimOk (atoms : List Atom) (P : ClaimVs) (j : ℕ) (o mark prev : V) (cells : List V) : Bool :=
  decide (rcOf atoms o = some P.last) &&
  (if j = 0 then decide (mark = P.marks) else
    (match mulOf atoms mark with
     | some (m, c) => decide (m = prev) && atoms.any (isConstAt c 2 0)
     | none => false)) &&
  (match loadOf atoms mark with
   | some (b, off) => off == 0 && (monoOf atoms 40 b).isPerm [P.region, o]
   | none => false) &&
  cells.length == 4 &&
  (List.range 4).all fun c => match loadOf atoms (cells.getD c default) with
    | some (p, off) => off == c && (monoOf atoms 40 p).isPerm (P.entries :: List.replicate 4 o)
    | none => false

/-- Claim `j`'s slot value, the first at `o0`. -/
def ccOV (o0 j : ℕ) : ℕ := if j = 0 then o0 else o0 + 12 + 14 * (j - 1)

/-- Claim `j`'s mark value (the first: the marks argument `mk`). -/
def ccMark (o0 : ℕ) (mk : V) (j : ℕ) : V := if j = 0 then mk else .n (ccOV o0 j + 5)

/-- Claim `j`'s cell `c`. -/
def ccCell (o0 j c : ℕ) : ℕ := if j = 0 then o0 + 8 + c else ccOV o0 j + 10 + c

/-- Claim `j`'s four cells. -/
def ccCells (o0 j : ℕ) : List V := (List.range 4).map fun c => .n (ccCell o0 j c)

/-- Claim `j`'s first atom (its hint), the first at `p0`: eleven atoms for the first claim,
thirteen for each other. -/
def ccPos (p0 j : ℕ) : ℕ := if j = 0 then p0 else p0 + 11 + 13 * (j - 1)

/-- Claim `j`'s atoms: a window of thirteen from its hint (the kernel checks a record against its
window, not the whole body). -/
def ccWin (atoms : List Atom) (p0 j : ℕ) : List Atom := (atoms.drop (ccPos p0 j)).take 13

/-- The records of `n` claims, claim `j`'s atoms from `ccPos p0 j`. -/
def recordsOk (atoms : List Atom) (P : ClaimVs) (o0 p0 n : ℕ) : Bool :=
  (List.range n).all fun j => claimOk (ccWin atoms p0 j) P j (.n (ccOV o0 j)) (ccMark o0 P.marks j)
    (ccMark o0 P.marks (j - 1)) (ccCells o0 j)

/-- The message of `n` claims: their cells, in order. -/
def ccMsg (o0 n : ℕ) : List (Option V) :=
  (List.range (4 * n)).map fun i => some (.n (ccCell o0 (i / 4) (i % 4)))

/-- The names of `child_claim_list_last`'s specializations, `k ≤ 16`. -/
def cclNames : List String :=
  ["child_claim_list_last__L0", "child_claim_list_last__L1", "child_claim_list_last__L2",
   "child_claim_list_last__L3", "child_claim_list_last__L4", "child_claim_list_last__L5",
   "child_claim_list_last__L6", "child_claim_list_last__L7", "child_claim_list_last__L8",
   "child_claim_list_last__L9", "child_claim_list_last__L10", "child_claim_list_last__L11",
   "child_claim_list_last__L12", "child_claim_list_last__L13", "child_claim_list_last__L14",
   "child_claim_list_last__L15", "child_claim_list_last__L16"]

/-- The state cells `child_claim_list_last__L{k}` loads. -/
def cclSt (k : ℕ) : List V :=
  (List.range 13).map fun c => V.n ((if k = 0 then 5 else 14 * k + 3) + c)

/-- The record values of `child_claim_list_last__L{k}`'s arguments
`[state, entries, region, marks, last]`. -/
def cclP : ClaimVs := ⟨.n 2, .n 4, .n 1, .n 3⟩

/-- The chain of `child_claim_list_last__L{k}`. -/
def cclSpec (k : ℕ) (atoms : List Atom) : ChainSpec :=
  ⟨ccMsg 5 k, 64 * k, true, some (cclSt k), keccakBlocks atoms⟩

/-- `child_claim_list_last__L{k}`'s body: `k` records, the chain over their cells from the state
at its first argument. -/
def cclOk (k : ℕ) (f : Fn) : Bool :=
  decide (f.params = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4]) &&
  match splitBody f.body with
  | some (atoms, [r0, r1]) =>
    (cclSpec k atoms).check atoms && retOk atoms (cclSpec k atoms) r0 r1 &&
      recordsOk atoms cclP 5 0 k && stLoadsOk atoms (V.n 0) (cclSt k) 0
  | _ => false

/-- The state cells a frame loop loads, from `.n st0`. -/
def anySt (st0 : ℕ) : List V := (List.range 13).map fun c => V.n (st0 + c)

/-- The record values of the frame loops `[x, N, chain, entries, region, base, last]`, the marks
at `.n mk`. -/
def anyP (mk : ℕ) : ClaimVs := ⟨.n 4, .n 6, .n 3, .n mk⟩

/-- The chain of a frame loop of `m` claims. -/
def anySpec (m o0 st0 : ℕ) (atoms : List Atom) : ChainSpec :=
  ⟨ccMsg o0 m, 0, false, some (anySt st0), keccakBlocks atoms⟩

/-- **A frame loop's body**: `m` records with the marks `base · x^m` (`.n mk`), the state at
`chain · x^13` (`.n 12`), the next at `chain · x^13 · g^13`. -/
def anyOk (fn : Fn) (f : String) (m o0 p0 mk st0 : ℕ) : Bool :=
  loopShape fn f && decide (fn.params.length = 7) &&
    (anySpec m o0 st0 (loopAtoms fn)).check (loopAtoms fn) &&
    stLoadsOk (loopAtoms fn) (V.n 12) (anySt st0) 0 &&
    recordsOk (loopAtoms fn) (anyP mk) o0 p0 m &&
    stLoadsOk (loopAtoms fn) (V.n 12)
      ((List.range 13).map ((anySpec m o0 st0 (loopAtoms fn)).outV
        ((anySpec m o0 st0 (loopAtoms fn)).nb - 1))) 13 &&
    monoIs (loopAtoms fn) (V.n 12) (V.n 2) (V.n 0) 13 &&
    monoIs (loopAtoms fn) (V.n mk) (V.n 5) (V.n 0) m

/-- Records `lo ≤ j < lo + w` of `n` (those from `n` on pass). -/
def recordsWin (atoms : List Atom) (P : ClaimVs) (o0 p0 n lo w : ℕ) : Bool :=
  (List.range' lo w).all fun j => decide (n ≤ j) ||
    claimOk (ccWin atoms p0 j) P j (.n (ccOV o0 j)) (ccMark o0 P.marks j)
      (ccMark o0 P.marks (j - 1)) (ccCells o0 j)

/-- **The records from windows** of `w` records covering the `n`. -/
theorem recordsOk_of_wins {atoms : List Atom} {P : ClaimVs} {o0 p0 n w W : ℕ} (hn : n ≤ w * W)
    (h : ∀ i < W, recordsWin atoms P o0 p0 n (w * i) w = true) :
    recordsOk atoms P o0 p0 n = true := by
  simp only [recordsOk, List.all_eq_true, List.mem_range]
  intro k hk
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hi : k / w < W := by
    rw [Nat.div_lt_iff_lt_mul hw]; rw [Nat.mul_comm] at hn; omega
  have := h (k / w) hi
  simp only [recordsWin, List.all_eq_true, List.mem_range', Bool.or_eq_true,
    decide_eq_true_eq] at this
  rcases this k ⟨k % w, Nat.mod_lt _ hw, by rw [Nat.one_mul]; exact (Nat.div_add_mod k w).symm⟩
    with h' | h'
  · omega
  · exact h'

/-- `anyOk` but the chain's blocks and the records (`anyOk_of_parts`). -/
def anyHead (fn : Fn) (f : String) (m o0 mk st0 : ℕ) : Bool :=
  loopShape fn f && decide (fn.params.length = 7) &&
    (anySpec m o0 st0 (loopAtoms fn)).shapeOk &&
    stLoadsOk (loopAtoms fn) (V.n 12) (anySt st0) 0 &&
    stLoadsOk (loopAtoms fn) (V.n 12)
      ((List.range 13).map ((anySpec m o0 st0 (loopAtoms fn)).outV
        ((anySpec m o0 st0 (loopAtoms fn)).nb - 1))) 13 &&
    monoIs (loopAtoms fn) (V.n 12) (V.n 2) (V.n 0) 13 &&
    monoIs (loopAtoms fn) (V.n mk) (V.n 5) (V.n 0) m

/-- **`anyOk` from its parts**: the head, windows of `w` blocks covering the chain, windows of
`v` records covering the `m`. -/
theorem anyOk_of_parts {fn : Fn} {f : String} {m o0 p0 mk st0 w W v U : ℕ}
    (hh : anyHead fn f m o0 mk st0 = true)
    (hnb : (anySpec m o0 st0 (loopAtoms fn)).nb ≤ w * W)
    (hb : ∀ i < W, (anySpec m o0 st0 (loopAtoms fn)).blocksOk (loopAtoms fn) (w * i) w = true)
    (hm : m ≤ v * U)
    (hr : ∀ i < U, recordsWin (loopAtoms fn) (anyP mk) o0 p0 m (v * i) v = true) :
    anyOk fn f m o0 p0 mk st0 = true := by
  simp only [anyHead, Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hh
  simp only [anyOk, h1, h2, h4, h5, h6, h7, ChainSpec.check_of_blocks h3 hnb hb,
    recordsOk_of_wins hm hr, Bool.and_self]

/-! ## The big frame loop `__loop17` (136 claims, 64 blocks), in sixteen windows -/

/-- `__loop17`'s atoms. -/
noncomputable def any136Atoms : List Atom := loopAtoms (coreProgram.getD 349 default)

/-- `__loop17`'s chain. -/
noncomputable def any136Spec : ChainSpec := anySpec 136 22 1924 any136Atoms

/-- Window `i` of `__loop17`: blocks `4i … 4i + 3`, records `9i … 9i + 8`. -/
noncomputable def anyWin (i : ℕ) : Bool :=
  any136Spec.blocksOk any136Atoms (4 * i) 4 &&
    recordsWin any136Atoms (anyP 21) 22 15 136 (9 * i) 9

end
end LeanVM.Guest.B1.Digest
