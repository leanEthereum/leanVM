/-
  LeanVM.Guest.CoreMode.Fn.level_positions.Data

  `level_positions`'s own routing data (`CoreMode/FnReg.lean`): the exponent bounds of its count of squeezes `squeezes_g`, at least `g^2`, which `open_stacked` binds per rate (`level_rate`), carried down from its callers (`CoreMode.carryExpB`).
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.CoreMode.Fam.ParamRef
import LeanVM.Guest.Data.Source

namespace LeanVM.Guest.CoreMode.Own.level_positions

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- Its specializations whose counts are carried. -/
def names : List String :=
  [name% «level_positions__L12_L6»,
    name% «level_positions__L13_L7»,
    name% «level_positions__L14_L2»,
    name% «level_positions__L15_L3»,
    name% «level_positions__L16_L4»,
    name% «level_positions__L17_L5»,
    name% «level_positions__L18_L6»,
    name% «level_positions__L19_L7»,
    name% «level_positions__L20_L2»,
    name% «level_positions__L20_L8»,
    name% «level_positions__L21_L3»,
    name% «level_positions__L22_L4»,
    name% «level_positions__L23_L5»,
    name% «level_positions__L24_L6»,
    name% «level_positions__L25_L7»,
    name% «level_positions__L26_L2»,
    name% «level_positions__L27_L3»,
    name% «level_positions__L28_L4»]

/-- **Its carried exponent bounds**: callee, parameter, lower and upper bound, every call site passing a value its
caller pins so (`open_stacked`, from its rates' constants). -/
def expCarry : List (String × ℕ × ℕ × ℕ) :=
  ((names).map fun k ↦ (k, param% level_positions "squeezes_g", 2, 268435456))

/-- **Its exponent facts**, the carried bounds' upper ones. -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) :=
  ((names).map fun k ↦ (k, param% level_positions "squeezes_g", none, 268435456))

end

end LeanVM.Guest.CoreMode.Own.level_positions
