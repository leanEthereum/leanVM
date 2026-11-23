/-
  LeanVM.Guest.CoreMode.Fn.level_residual.Data

  `level_residual`'s own routing data (`CoreMode/FnReg.lean`): the exponent bounds of its query counts `batches_g`, `rest_g`, which `open_stacked` binds per rate (`level_rate`), carried down from its callers (`CoreMode.carryExpB`).
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.CoreMode.Fam.ParamRef
import LeanVM.Guest.Data.Source

namespace LeanVM.Guest.CoreMode.Own.level_residual

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- Its specializations whose counts are carried. -/
def names : List String :=
  [name% «level_residual__L10_L4_L2»,
    name% «level_residual__L11_L4_L2»,
    name% «level_residual__L12_L4_L2»,
    name% «level_residual__L13_L4_L2»,
    name% «level_residual__L14_L4_L2»,
    name% «level_residual__L14_L6_L3»,
    name% «level_residual__L15_L4_L2»,
    name% «level_residual__L15_L6_L3»,
    name% «level_residual__L16_L4_L2»,
    name% «level_residual__L16_L6_L3»,
    name% «level_residual__L17_L4_L2»,
    name% «level_residual__L17_L6_L3»,
    name% «level_residual__L18_L4_L2»,
    name% «level_residual__L18_L6_L3»,
    name% «level_residual__L19_L4_L2»,
    name% «level_residual__L19_L6_L3»,
    name% «level_residual__L20_L4_L2»,
    name% «level_residual__L20_L6_L3»,
    name% «level_residual__L21_L6_L3»,
    name% «level_residual__L22_L6_L3»,
    name% «level_residual__L23_L6_L3»,
    name% «level_residual__L24_L6_L3»,
    name% «level_residual__L6_L4_L2»,
    name% «level_residual__L7_L4_L2»,
    name% «level_residual__L8_L4_L2»,
    name% «level_residual__L9_L4_L2»]

/-- **Its carried exponent bounds**: callee, parameter, lower and upper bound, every call site passing a value its
caller pins so (`open_stacked`, from its rates' constants). -/
def expCarry : List (String × ℕ × ℕ × ℕ) :=
  ((names).map fun k ↦ (k, param% level_residual "batches_g", 0, 268435456)) ++
    ((names).map fun k ↦ (k, param% level_residual "rest_g", 0, 268435456))

/-- **Its exponent facts**, the carried bounds' upper ones. -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) :=
  ((names).map fun k ↦ (k, param% level_residual "batches_g", none, 268435456)) ++
    ((names).map fun k ↦ (k, param% level_residual "rest_g", none, 268435456))

end

end LeanVM.Guest.CoreMode.Own.level_residual
