/-
  LeanVM.Guest.CoreMode.Fam.SubDefs

  The proof stream's reads and `verify_keccak`'s reads past its layers' cursors, as `sub` residuals.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResS
public import LeanVM.Guest.CoreMode.Gen.AnyLink
public import LeanVM.Guest.CoreMode.Fam.MonoDefs
public import LeanVM.Guest.CoreMode.Fam.FamDefs
public import LeanVM.Guest.CoreMode.Fam.TermDefs
public import LeanVM.Guest.CoreMode.Fam.TileDefs
public import LeanVM.Guest.CoreMode.Fam.ExpDefs

/-!
# The stream reads' sites

The proof stream's reads (`stSites`, `stRes`, `stB`, `stResB`) and `verify_keccak`'s reads past its layers'
returned cursors (`vkStSites`, `vkStB`); `verify_tables`' are its own (`SubVt.lean`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.B2C (cellJ)

@[expose] public section

/-! ## The proof stream's reads -/

/-- **The proof stream's readers**: function, its cursor's cell, the stream's base (the layer's
parameter, the loops' through their header), the words read past the cursor. -/
def stSites : List (String × ℕ × Mode.Base × ℕ) :=
  [(name% «keccak_layer__L0», 747, .fr 17, 36), (name% «keccak_layer__L1», 773, .fr 17, 36),
    (name% «keccak_layer__L0_loop0», 20, .hp 1 17, 16), (name% «keccak_layer__L1_loop0», 20, .hp 1 17, 16),
    (name% «keccak_layer__L0_loop1», 17, .hp 1 17, 2), (name% «keccak_layer__L1_loop1», 17, .hp 1 17, 2)]

/-- The read `c` words past the cursor in cell `o`, inside the stream `st·[0, 8192)`. -/
def stRes (o : ℕ) (st : Mode.Base) (c : ℕ) : Mode.Res :=
  .sub ⟨⟨0, c, [(.fr o, 1)]⟩, .num 0, .num 1, 1, 0⟩ [⟨⟨0, 0, [(st, 1)]⟩, .num 0, .num 8192, 1, 0⟩]

/-- **A read of the proof stream** at function `j`: a site's, below its words. -/
noncomputable def stB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => stSites.any fun s ↦ (coreOf j).name == s.1 && decide (a.q.k < s.2.2.2) &&
      decide (Mode.Res.sub a bs = stRes s.2.1 s.2.2.1 a.q.k)
  | _ => false

/-! ## A read past a cursor base -/

/-- The read `c` words past the cursor base `cur`, inside the stream `st·[0, 8192)`. -/
def stResB (cur st : Mode.Base) (c : ℕ) : Mode.Res :=
  .sub ⟨⟨0, c, [(cur, 1)]⟩, .num 0, .num 1, 1, 0⟩ [⟨⟨0, 0, [(st, 1)]⟩, .num 0, .num 8192, 1, 0⟩]

/-! ## `verify_keccak`'s reads past its layers -/

/-- **`verify_keccak`'s reads past a layer's returned cursor**: the cell of the layer's frame pointer
(step `s`'s call), the words read there: the next layer's, or after the last, the outputs' and the
inputs'. -/
def vkStSites : List (ℕ × ℕ) :=
  [(379, 48), (408, 48), (436, 48), (467, 48), (498, 48), (529, 48), (556, 48), (587, 48), (617, 48),
    (650, 48), (681, 48), (711, 97)]

/-- **A read past a layer's returned cursor** (`[[q]·g^23]`) inside the stream (`[14]`), at
`verify_keccak`. -/
noncomputable def vkStB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => (coreOf j).name == name% «verify_keccak» && vkStSites.any fun s ↦ decide (a.q.k < s.2) &&
      decide (Mode.Res.sub a bs = stResB (.hp s.1 23) (.fr 14) a.q.k)
  | _ => false

end

end LeanVM.Guest.Res
