/-
  LeanVM.Guest.B1.Merkle.CapMaps

  The maps of the deployed `verify_merkle_cap` specializations' links, computed at elaboration.
-/

module

public import LeanVM.Guest.B1.Merkle.CapRef
public import LeanVM.Guest.Pack.P4.Core
public import LeanVM.Guest.Pack.P6.Core
public import LeanVM.Guest.Pack.P11.Core
public import LeanVM.Guest.Pack.P23.Core
public import LeanVM.Guest.Pack.P42.Core
public import LeanVM.Guest.Pack.P56.Core
public import LeanVM.Guest.Pack.P61.Core
meta import LeanVM.Guest.Ref.Elab
meta import LeanVM.Guest.B1.Merkle.CapRef

/-!
# `verify_merkle_cap__L2 .. L8`, their links' maps

`capMap d` is the map `cap_map%` computes at elaboration: the inference `infer`
(`LeanVM.Guest.Ref.Link`) run on `verify_merkle_cap__L{d}`'s core function read off its definition
(`LeanVM.Guest.Ref.Elab`) and on `capRef d`. Nothing here is trusted: `CapLinks.lean` checks it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Ref

meta section

deriving instance Lean.ToExpr for CapName

/-- `cap_map% d`: `infer` of `verify_merkle_cap__L{d}`'s core function and `capRef d`, as a literal
map. -/
syntax (name := capMapStx) "cap_map%" num : term

open Lean Elab Term in
def elabCapMap : TermElab := fun stx _ => do
  let d := stx[1].isNatLit?.getD 0
  let f := Name.mkStr (.mkStr `LeanVM.Guest.Fn s!"verify_merkle_cap__L{d}") "core"
  return Ref.Elab.mapE (infer (← Ref.Elab.decFn f) (capRef d))

end

attribute [local term_elab capMapStx] elabCapMap

@[expose] public section

/-- The map of the specialization at each deployed depth, computed at elaboration. -/
noncomputable def capMap : ℕ → Map CapName
  | 2 => cap_map% 2
  | 3 => cap_map% 3
  | 4 => cap_map% 4
  | 5 => cap_map% 5
  | 6 => cap_map% 6
  | 7 => cap_map% 7
  | 8 => cap_map% 8
  | _ => ⟨[]⟩

end
end LeanVM.Guest.B1
