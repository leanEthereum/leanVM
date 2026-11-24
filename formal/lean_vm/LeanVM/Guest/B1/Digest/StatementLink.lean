/-
  LeanVM.Guest.B1.Digest.StatementLink

  `statement_digest`'s compiled function is linked to its reference function.
-/

module

public import LeanVM.Guest.B1.Digest.StatementRef
-- Read by the check; it also keeps `lake-build.py --dev`'s kernel on this module (`CORE_READ`).
public import LeanVM.Guest.Pack.P27.Core
meta import LeanVM.Guest.Ref.Elab
meta import LeanVM.Guest.B1.Digest.StatementRef

/-!
# `statement_digest`, linked

`sd_linked` is one kernel evaluation of the link check (`LeanVM.Guest.Ref.Link`) of
`statement_digest` against `sdRef`, given the map `sdMap`, which this module computes when it is
elaborated (`sd_map%`, the inference `infer`'s walk). Unverified: a wrong entry can only make the
check fail.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Ref

meta section

deriving instance Lean.ToExpr for SdName

/-- `sd_map%`: the map of `statement_digest`'s core function and `sdRef`, as a literal. -/
syntax (name := sdMapStx) "sd_map%" : term

open Lean Elab Term in
def elabSdMap : TermElab := fun _ _ => do
  return Ref.Elab.mapE (infer (← Ref.Elab.decFn ``Fn.«statement_digest».core) sdRef)

end

attribute [local term_elab sdMapStx] elabSdMap

@[expose] public section

/-- `statement_digest`'s map, computed at elaboration. -/
noncomputable def sdMap : Map SdName := sd_map%

/-- **`statement_digest`'s core function is linked to `sdRef`.** -/
theorem sd_linked : sdMap.check Fn.«statement_digest».core sdRef = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
