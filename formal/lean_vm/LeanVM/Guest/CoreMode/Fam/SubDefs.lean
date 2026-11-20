/-
  LeanVM.Guest.CoreMode.Fam.SubDefs

  The `sub` residuals' families, checked per certificate: a run inside a split, a read inside
  `child_claim_list_any`'s table, a read of the gap walk, the proof stream's reads, a lift's runs.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResS
public import LeanVM.Guest.CoreMode.Gen.AnyLink
public import LeanVM.Guest.CoreMode.Fam.MonoDefs
public import LeanVM.Guest.CoreMode.Fam.FamDefs
public import LeanVM.Guest.CoreMode.Fam.TermDefs
public import LeanVM.Guest.CoreMode.Fam.ExpDefs

/-!
# The stream reads' and `verify_tables`' sites

The proof stream's reads (`stSites`, `stRes`, `stB`), `verify_tables`' reads past its table sumcheck
(`vtStB`) and its groups' bases read in group order (`vtGrpRes`, `vtGrpB`).
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

/-! ## `verify_tables`' table sumcheck -/

/-- **`verify_tables`' reads past its table sumcheck's last record's cursor** (cell `2880`) inside its
stream (`[22]`), below `153` words. -/
noncomputable def vtStB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => (coreOf j).name == name% «verify_tables» && decide (a.q.k < 153) &&
      decide (Mode.Res.sub a bs = stRes 2880 (.fr 22) a.q.k)
  | _ => false

/-! ## `verify_tables`' groups -/

/-- A side's groups' bases `[57]·g^[G0, G0 + m)`, each read through a rank's group
`[57]·[[58]·g^(G0 + k)]`. -/
def vtGrpRes (G0 m : ℕ) : Mode.Res :=
  .sub ⟨⟨0, 0, [(.fr 57, 1)]⟩, .num G0, .num (G0 + m), 1, 0⟩
    ((List.range m).map fun k ↦ ⟨⟨0, 0, [(.fr 57, 1), (.hp 58 (G0 + k), 1)]⟩, .num 0, .num 1, 1, 0⟩)

/-- **`verify_tables`' groups' bases, read in group order**, at function `j`: the ranks of a side
name each of its groups, the push side's `9` and the count side's `6`. -/
noncomputable def vtGrpB (j : ℕ) (x : Mode.Res) : Bool :=
  (coreOf j).name == name% «verify_tables» && (decide (x = vtGrpRes 0 9) || decide (x = vtGrpRes 18 6))

/-! ## `verify_keccak`'s reads past its layers -/

end

end LeanVM.Guest.Res
