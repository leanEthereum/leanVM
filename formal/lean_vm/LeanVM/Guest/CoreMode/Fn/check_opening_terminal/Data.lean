/-
  LeanVM.Guest.CoreMode.Fn.check_opening_terminal.Data

  `check_opening_terminal`'s own routing data (`CoreMode/FnReg.lean`): its exponent and dimension
  facts, which `verify_sub` hands it (`Res.TermFront`), and its caller.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.CoreMode.Fam.ParamRef
public import LeanVM.Guest.B1.Tables.InterfaceP
import LeanVM.Guest.Data.Source

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-- The pooled claims' `kappa_base` sources and adjustments, bus claims first. -/
def claimPairs : List (ℕ × ℕ) :=
  (List.range Tables.nPooled).map fun j ↦ (Tables.claimKappaSrc.getD j 0, Tables.claimKappaAdj j)

/-- The bus claims' pairs: their points prefixes of the bus point. -/
def busPairs : List (ℕ × ℕ) := claimPairs.take Tables.nBusClaims

/-- The tables' claims' pairs: their points prefixes of the tables' point. -/
def tabPairs : List (ℕ × ℕ) := claimPairs.drop Tables.nBusClaims

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.CoreMode.Own.check_opening_terminal

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its exponent facts**: `tau_keccak_g`, `kappa_base`'s words (`[1, g^log_mem, g^τ_0, …]`) and `gmv = g^sl`,
`sl ≤ 30` (`Res.TermFront`). -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) :=
  [(name% «check_opening_terminal», param% check_opening_terminal "tau_keccak_g", none, 31),
    (name% «check_opening_terminal», param% check_opening_terminal "kappa_base", some 0, 1)] ++
  ((List.range 7).map fun k ↦
    (name% «check_opening_terminal», param% check_opening_terminal "kappa_base", some (k + 1), 31)) ++
  [(name% «check_opening_terminal», param% check_opening_terminal "gmv", none, 31)]

/-- **Its dimension facts**: the pooled claims' `kappa_base` sources and adjustments, the bus's against `g_bus_mu`, the
tables' against `g_zc_n` (`Res.busPairs`, `Res.tabPairs`). -/
def dimFacts : List (String × ℕ × ℕ × List (ℕ × ℕ)) :=
  [(name% «check_opening_terminal», param% check_opening_terminal "kappa_base",
      param% check_opening_terminal "g_bus_mu", Res.busPairs),
    (name% «check_opening_terminal», param% check_opening_terminal "kappa_base",
      param% check_opening_terminal "g_zc_n", Res.tabPairs)]

/-- **Its caller** (`Res.callersG`): `verify_sub`. -/
def stCallers : List (String × String) := [(name% «check_opening_terminal», name% «verify_sub»)]

end

end LeanVM.Guest.CoreMode.Own.check_opening_terminal
