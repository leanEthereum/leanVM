/-
  LeanVM.Guest.CoreMode.Fam.SubDefs

  The proof stream's reads, as `sub` residuals.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResS
public import LeanVM.Guest.CoreMode.Gen.AnyLink
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.MonoDefs
public import LeanVM.Guest.CoreMode.Fam.FamDefs
public import LeanVM.Guest.CoreMode.Fam.TermDefs
public import LeanVM.Guest.CoreMode.Fam.ExpDefs

/-!
# The stream reads' sites

The proof stream's reads (`stSites`, `stRes`, `stB`); `verify_tables`' are its own (`SubVt.lean`).
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

end

end LeanVM.Guest.Res
