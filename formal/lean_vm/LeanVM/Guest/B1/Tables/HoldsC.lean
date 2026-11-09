/-
  LeanVM.Guest.B1.Tables.HoldsC

  B1-c's callee statements over a generic call relation `C`, proved: `verify_bus_gkr`,
  `verify_tables` (a bytecode of `2^23` words) and `certify_placement`, on memory images of at most
  `2^32` words, for every `C` below `coreProgram.Rel`.
-/

module

public import LeanVM.Guest.B1.Tables.InterfaceC
public import LeanVM.Guest.B1.Tables.Vt.VerifyTables
public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.B1.Placement.Certify
public import LeanVM.Guest.B1.Placement.Kappas

/-!
# The callee statements over `C`, proved

`verify_bus_gkr_holdsC`, `verify_tables_holdsC`, `certify_placement_holdsC`: the `Rel` theorems,
through `CallRel.Le C (Rel rd)`; `hypKappa_holds` needs no change.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

theorem verify_bus_gkr_holdsC {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel Lm.read)) :
    verify_bus_gkr_SpecC Lm.read C :=
  verify_bus_gkr_SpecC_of hle (verify_bus_gkr_holds hμ Lm)

theorem verify_tables_holdsC (bc : List K) (hbc : bc.length = 2 ^ 23) {C : CallRel}
    (hle : CallRel.Le C (coreProgram.Rel Lm.read)) : verify_tables_SpecC bc Lm.read C :=
  verify_tables_SpecC_of hle (verify_tables_holds hμ Lm bc hbc)

theorem certify_placement_holdsC {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel Lm.read)) :
    certify_placement_SpecC Lm.read C :=
  certify_placement_SpecC_of hle (certify_placement_holds hμ Lm)

end

end
end LeanVM.Guest.B1.Tables
