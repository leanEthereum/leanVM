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
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»
import LeanVM.Guest.Data.ValNames.«verify_tables_loop0»

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

/-- **Its word `g_zc_n = g^n`, `n < 34`** (`EndExec.VtQ`). -/
def expVals : List (String × ℕ × ℕ) := [(name% «verify_tables», val% «verify_tables» "g_zc_n", 34)]

/-- **Its rounds loop reads the proof stream past its cursor** (`CoreMode.stLoops`): the stream its caller's cell
(`2 +` the value `stream`), the cursor its value `s1#0`, `3` words an iteration. -/
def stLoops : List (String × ℕ × ℕ × ℕ) :=
  [(name% «verify_tables_loop0», 2 + val% «verify_tables» "stream", val% «verify_tables_loop0» "s1#0", 3)]

/-- **Its divisors, nonzero** (`CoreMode.coreNzs`): its values `key@2` and `key@11`, and the tables' `kb[2 + t]`. -/
def nzs : List (String × V) := [(name% «verify_tables», .n (val% «verify_tables» "key@2")), (name% «verify_tables», .n (val% «verify_tables» "key@11")),
  (name% «verify_tables», .n (val% «verify_tables» "kb[2]")), (name% «verify_tables», .n (val% «verify_tables» "kb[3]")),
  (name% «verify_tables», .n (val% «verify_tables» "kb[4]")), (name% «verify_tables», .n (val% «verify_tables» "kb[5]")),
  (name% «verify_tables», .n (val% «verify_tables» "kb[6]")), (name% «verify_tables», .n (val% «verify_tables» "kb[7]"))]

/-- **Its callers and its rounds loop's** (`Res.callersG`): `verify_sub`, and itself. -/
def stCallers : List (String × String) :=
  [(name% «verify_tables», name% «verify_sub»), (name% «verify_tables_loop0», name% «verify_tables»)]

end

end LeanVM.Guest.CoreMode.Own.verify_tables
