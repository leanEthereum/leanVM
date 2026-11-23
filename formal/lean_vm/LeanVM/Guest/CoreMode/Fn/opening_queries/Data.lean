/-
  LeanVM.Guest.CoreMode.Fn.opening_queries.Data

  `opening_queries`'s own routing data (`CoreMode/FnReg.lean`): the exponent bounds of its counts of query pairs `n_iters_g` and of odd queries `odd_g` at level 0, which `level_queries` passes as constants, carried down from its callers (`CoreMode.carryExpB`).
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.CoreMode.Fam.ParamRef
import LeanVM.Guest.Data.Source

namespace LeanVM.Guest.CoreMode.Own.opening_queries

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- Its specializations whose counts are carried. -/
def names : List String :=
  [name% «opening_queries__L1_L6_L32_L12_L0_L0_L0_L0_L0»,
    name% «opening_queries__L1_L6_L32_L18_L0_L0_L0_L0_L0»,
    name% «opening_queries__L1_L6_L32_L24_L0_L0_L0_L0_L0»]

/-- **Its carried exponent bounds**: callee, parameter, lower and upper bound, every call site passing a value its
caller pins so (`level_queries`, from its constants). -/
def expCarry : List (String × ℕ × ℕ × ℕ) :=
  ((names).map fun k ↦ (k, param% opening_queries "n_iters_g", 0, 268435456)) ++
    ((names).map fun k ↦ (k, param% opening_queries "odd_g", 0, 268435456))

/-- **Its exponent facts**, the carried bounds' upper ones. -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) :=
  ((names).map fun k ↦ (k, param% opening_queries "n_iters_g", none, 268435456)) ++
    ((names).map fun k ↦ (k, param% opening_queries "odd_g", none, 268435456))

end

end LeanVM.Guest.CoreMode.Own.opening_queries
