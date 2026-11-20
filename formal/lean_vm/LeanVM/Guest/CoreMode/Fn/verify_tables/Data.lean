/-
  LeanVM.Guest.CoreMode.Fn.verify_tables.Data

  `verify_tables`'s own routing data (`CoreMode/FnReg.lean`): its exponent facts, its rounds loop's reads of the proof stream, its nonzero divisors, its callers.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.CoreMode.Fam.ParamRef
import LeanVM.Guest.Data.Source

namespace LeanVM.Guest.CoreMode.Own.verify_tables

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its exponent facts**: `g_bus_mu = g^|point|`, `|point| < 33`, `dims_g`'s first word `g^logMem`, `logMem ≤ 32`,
which its precondition bounds (`EndExec.VtPQ`), and its other six, the tables' log-heights below `31`, which its body
bounds (`B1.Tables.vt_pads`). -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) :=
  [(name% «verify_tables», param% verify_tables "g_bus_mu", none, 33),
    (name% «verify_tables», param% verify_tables "dims_g", some 0, 33)] ++
  (List.range 6).map fun k ↦ (name% «verify_tables», param% verify_tables "dims_g", some (k + 1), 31)

/-- **Its word `g_zc_n = g^n`, `n < 34`** (`EndExec.VtQ`): its value `2545`. -/
def expVals : List (String × ℕ × ℕ) := [(name% «verify_tables», 2545, 34)]

/-- **Its rounds loop reads the proof stream past its cursor** (`CoreMode.stLoops`): the stream its caller's cell
`22`, the cursor its value `11`, `3` words an iteration. -/
def stLoops : List (String × ℕ × ℕ × ℕ) := [(name% «verify_tables_loop0», 22, 11, 3)]

/-- **Its divisors, nonzero** (`CoreMode.coreNzs`): its values `133` and `430`. -/
def nzs : List (String × V) := [(name% «verify_tables», .n 133), (name% «verify_tables», .n 430)]

/-- **Its callers and its rounds loop's** (`Res.callersG`): `verify_sub`, and itself. -/
def stCallers : List (String × String) :=
  [(name% «verify_tables», name% «verify_sub»), (name% «verify_tables_loop0», name% «verify_tables»)]

end

end LeanVM.Guest.CoreMode.Own.verify_tables
