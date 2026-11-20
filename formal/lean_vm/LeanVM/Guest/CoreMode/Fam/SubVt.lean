/-
  LeanVM.Guest.CoreMode.Fam.SubVt

  `verify_tables`' `sub` residuals' families of the old route (`Mode.Res`): its table sumcheck's reads, its reads past
  its last record's cursor, its groups' bases.
-/

module

public import LeanVM.Guest.CoreMode.Fam.SubDefs

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-! ## `verify_tables`' table sumcheck -/

/-- **`verify_tables`' table sumcheck's reads** at function `j`: the rounds loop's reads of the stream
`[[1]·g^22]` past its record's cursor (cell `17`) and past `sumcheck_round4`'s (`[[19]·g^3]`), below
three words. -/
noncomputable def vtB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => ((coreOf j).name == name% «verify_tables_loop0» && decide (a.q.k < 3) &&
        (decide (Mode.Res.sub a bs = stResB (.fr 17) (.hp 1 22) a.q.k) ||
          decide (Mode.Res.sub a bs = stResB (.hp 19 3) (.hp 1 22) a.q.k)))
  | _ => false

/-- **`verify_tables`' reads past its table sumcheck's last record's cursor** (cell `2908`) inside its
stream (`[22]`), below `153` words. -/
noncomputable def vtStB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => (coreOf j).name == name% «verify_tables» && decide (a.q.k < 153) &&
      decide (Mode.Res.sub a bs = stRes 2908 (.fr 22) a.q.k)
  | _ => false

/-! ## `verify_tables`' groups -/

/-- A side's groups' bases `[58]·g^[G0, G0 + m)`, each read through a rank's group
`[58]·[[59]·g^(G0 + k)]`. -/
def vtGrpRes (G0 m : ℕ) : Mode.Res :=
  .sub ⟨⟨0, 0, [(.fr 58, 1)]⟩, .num G0, .num (G0 + m), 1, 0⟩
    ((List.range m).map fun k ↦ ⟨⟨0, 0, [(.fr 58, 1), (.hp 59 (G0 + k), 1)]⟩, .num 0, .num 1, 1, 0⟩)

/-- **`verify_tables`' groups' bases, read in group order**, at function `j`: the ranks of a side
name each of its groups, the push side's `9` and the count side's `6`. -/
noncomputable def vtGrpB (j : ℕ) (x : Mode.Res) : Bool :=
  (coreOf j).name == name% «verify_tables» && (decide (x = vtGrpRes 0 9) || decide (x = vtGrpRes 18 6))

end

end LeanVM.Guest.Res
