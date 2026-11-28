/-
  LeanVM.Guest.CoreMode.Fn.link_rounds.Fam

  `link_rounds`' own residual family (`CoreMode/FnReg.lean`): its returned cursor `W·count` words past `cursor`.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.link_rounds

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The returned cursor**: `link_rounds__L{t}_L{b}`'s value `73`, the word `link_rounds_last` stored at its record
`out·g^5`, is `cursor·count_g^W` (values `5`, `8`), `W = t + 1 + [b > 0]` words a round. -/
def retEq (W : ℕ) : CRes := .eq ⟨[(73, 1)], 0⟩ ⟨[(5, 1), (8, W)], 0⟩

/-- `link_rounds`' specializations with their round's words. -/
def retSpecs : List (String × ℕ) :=
  [(name% «link_rounds__L1_L0», 2), (name% «link_rounds__L6_L0», 7), (name% «link_rounds__L7_L0», 8),
    (name% «link_rounds__L8_L1», 10), (name% «link_rounds__L9_L1», 11), (name% «link_rounds__L10_L1», 12)]

/-- **Its family**: each specialization's returned cursor (`retEq`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) :=
  retSpecs.map fun p ↦ (p.1, fun _ r ↦ decide (r = retEq p.2))

end

end LeanVM.Guest.CoreMode.Own.link_rounds
