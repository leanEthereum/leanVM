/-
  LeanVM.Guest.B1.Digest.ClaimListDefs

  The checks `claim_list_digest`'s proof evaluates (TRIAGE #88): `claim_list_last__L{k}`'s chain,
  the frame loops' bodies, and the windows of the 64-block frame loop `__loop15`.
-/

module

public import LeanVM.Guest.B1.Digest.Window

/-!
# `claim_list_digest`: the checks

What the kernel evaluates for `claim_list_digest` (`ClaimList`): `clOk` (`claim_list_last__L{k}`),
`grpOk` (a frame loop of `m` claims), split for the big loop `__loop15` into `grpHead` and the
windows `bigWin i` (four blocks and 34 cells each, four to a module `ClaimListBig{q}`), which
`grpOk_of_parts` puts back together. Only definitions and the gluing: the kernel checks sit in their own modules.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## `claim_list_last__L{k}` -/

/-- The names of `claim_list_last`'s specializations, `k ≤ 16`. -/
def clNames : List String :=
  ["claim_list_last__L0", "claim_list_last__L1", "claim_list_last__L2", "claim_list_last__L3",
   "claim_list_last__L4", "claim_list_last__L5", "claim_list_last__L6", "claim_list_last__L7",
   "claim_list_last__L8", "claim_list_last__L9", "claim_list_last__L10", "claim_list_last__L11",
   "claim_list_last__L12", "claim_list_last__L13", "claim_list_last__L14", "claim_list_last__L15",
   "claim_list_last__L16"]

/-- The state cells `claim_list_last__L{k}` loads. -/
def clSt (k : ℕ) : List V := (List.range 13).map fun c => V.n (2 + 4 * k + c)

/-- The chain of `claim_list_last__L{k}`: `4k` cells loaded as `.n 2 …`, `64k` bytes, from the
state loaded as `clSt k`. -/
def clSpec (k : ℕ) (atoms : List Atom) : ChainSpec :=
  ⟨(List.range (4 * k)).map (fun i => some (V.n (i + 2))), 64 * k, true, some (clSt k),
    keccakBlocks atoms⟩

/-- `claim_list_last__L{k}`'s body is the chain over the cells at its second argument from the
state at its first. -/
def clOk (k : ℕ) (f : Fn) : Bool :=
  decide (f.params = [V.n 0, V.n 1]) &&
  match splitBody f.body with
  | some (atoms, [r0, r1]) =>
    (clSpec k atoms).check atoms && retOk atoms (clSpec k atoms) r0 r1 &&
      loadsOk atoms (V.n 1) (clSpec k atoms).msg && stLoadsOk atoms (V.n 0) (clSt k) 0
  | _ => false

/-! ## The frame loops: `m` claims a frame -/

/-- The state cells a frame loop loads, from `.n st0`. -/
def grpSt (st0 : ℕ) : List V := (List.range 13).map fun c => V.n (st0 + c)

/-- The chain of a frame loop of `m` claims: `4m` cells loaded from `.n c0`, `final=0`, from the
state `grpSt st0`. -/
def grpSpec (m c0 st0 : ℕ) (atoms : List Atom) : ChainSpec :=
  ⟨(List.range (4 * m)).map (fun i => some (V.n (i + c0))), 0, false, some (grpSt st0),
    keccakBlocks atoms⟩

/-- **A frame loop's body**: the state at `chain · x^13` (`.n 9`), the `4m` cells at
`entries · x^(4m)` (`.n ep`), the next state at `chain · x^13 · g^13`. -/
def grpOk (fn : Fn) (f : String) (m c0 st0 ep : ℕ) : Bool :=
  loopShape fn f && decide (fn.params.length = 4) &&
    (grpSpec m c0 st0 (loopAtoms fn)).check (loopAtoms fn) &&
    stLoadsOk (loopAtoms fn) (V.n 9) (grpSt st0) 0 &&
    loadsOk (loopAtoms fn) (V.n ep) (grpSpec m c0 st0 (loopAtoms fn)).msg &&
    stLoadsOk (loopAtoms fn) (V.n 9)
      ((List.range 13).map ((grpSpec m c0 st0 (loopAtoms fn)).outV
        ((grpSpec m c0 st0 (loopAtoms fn)).nb - 1))) 13 &&
    monoIs (loopAtoms fn) (V.n 9) (V.n 2) (V.n 0) 13 &&
    monoIs (loopAtoms fn) (V.n ep) (V.n 3) (V.n 0) (4 * m)

/-- `x`'s factors are `base`, `e` times `y` and `e'` times `y'`. -/
def mono2Is (atoms : List Atom) (x base y : V) (e : ℕ) (y' : V) (e' : ℕ) : Bool :=
  (monoOf atoms 40 x).isPerm (base :: List.replicate e y ++ List.replicate e' y')

/-- `grpOk` but the chain's blocks and the cells' loads (`grpOk_of_parts`). -/
def grpHead (fn : Fn) (f : String) (m c0 st0 ep : ℕ) : Bool :=
  loopShape fn f && decide (fn.params.length = 4) &&
    (grpSpec m c0 st0 (loopAtoms fn)).shapeOk &&
    stLoadsOk (loopAtoms fn) (V.n 9) (grpSt st0) 0 &&
    stLoadsOk (loopAtoms fn) (V.n 9)
      ((List.range 13).map ((grpSpec m c0 st0 (loopAtoms fn)).outV
        ((grpSpec m c0 st0 (loopAtoms fn)).nb - 1))) 13 &&
    monoIs (loopAtoms fn) (V.n 9) (V.n 2) (V.n 0) 13 &&
    monoIs (loopAtoms fn) (V.n ep) (V.n 3) (V.n 0) (4 * m)

/-- **`grpOk` from its parts**: the head, windows of `w` blocks covering the chain, windows of
`v` cells covering the message. -/
theorem grpOk_of_parts {fn : Fn} {f : String} {m c0 st0 ep w W v U : ℕ}
    (hh : grpHead fn f m c0 st0 ep = true)
    (hnb : (grpSpec m c0 st0 (loopAtoms fn)).nb ≤ w * W)
    (hb : ∀ i < W, (grpSpec m c0 st0 (loopAtoms fn)).blocksOk (loopAtoms fn) (w * i) w = true)
    (hml : 4 * m ≤ v * U)
    (hl : ∀ i < U, loadsWin (loopAtoms fn) (V.n ep) (grpSpec m c0 st0 (loopAtoms fn)).msg
      (v * i) v = true) :
    grpOk fn f m c0 st0 ep = true := by
  simp only [grpHead, Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hh
  simp only [grpOk, h1, h2, h4, h5, h6, h7, ChainSpec.check_of_blocks h3 hnb hb,
    loadsOk_of_wins (by simp [grpSpec]; exact hml) hl, Bool.and_self]

/-! ## The big frame loop `__loop15` (136 claims, 64 blocks), in sixteen windows -/

/-- `__loop15`'s atoms. -/
noncomputable def bigAtoms : List Atom := loopAtoms (coreProgram.getD 359 default)

/-- `__loop15`'s chain. -/
noncomputable def bigSpec : ChainSpec := grpSpec 136 21 565 bigAtoms

/-- Window `i` of `__loop15`: blocks `4i … 4i + 3`, cells `34i … 34i + 33`. -/
noncomputable def bigWin (i : ℕ) : Bool :=
  bigSpec.blocksOk bigAtoms (4 * i) 4 && loadsWin bigAtoms (V.n 20) bigSpec.msg (34 * i) 34

end
end LeanVM.Guest.B1.Digest
