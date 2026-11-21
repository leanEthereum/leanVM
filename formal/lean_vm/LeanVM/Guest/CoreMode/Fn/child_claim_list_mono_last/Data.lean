/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono_last.Data

  `child_claim_list_mono_last`'s own routing data (`CoreMode/FnReg.lean`): its nonzero divisor, its ghost family's
  specializations.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.B1.Digest.MonoDefs
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono_last__L»
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono_last__L1»

namespace LeanVM.Guest.CoreMode.Own.child_claim_list_mono_last

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its divisor, nonzero** (`CoreMode.coreNzs`): `child_claim_list_mono_last__L0`'s parameter `1`. -/
def nzs : List (String × V) := [(name% «child_claim_list_mono_last__L0», .n (valf% «child_claim_list_mono_last» "region"))]

/-- **Its ghost family's reads** (`CoreMode.mlSub`): claim `jj`'s entry `[ent]·Π_{i ≤ jj}[gap + 10i]^4`, below the
exponent of `limit_g`, each specialization's values, named in `L1`; and its links (`CoreMode.mlGl`): its caller's
cell `2` (the entries) its one ghost slot, after its four parameters, cell `5` its parameter `limit_g`. -/
def mlShape : ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ) :=
  (val% «child_claim_list_mono_last__L1» "s1.e.s2#1",
    val% «child_claim_list_mono_last__L1» "s1.e.s2.i2:child_claims_mono.s0.u0.s0#0", 10,
    valf% «child_claim_list_mono_last» "limit_g", [(2, 4, 0), (5, valf% «child_claim_list_mono_last» "limit_g", 0)])

/-- **Its ghost family's specializations** (`CoreMode.mlK`): `child_claim_list_mono_last__L{k}`, `1 ≤ k < 17`. -/
def mlLoops : List (String × ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)) :=
  (List.range 16).map fun j ↦ (B1.Digest.mlNames.getD (j + 1) "", j + 1, mlShape)

end

end LeanVM.Guest.CoreMode.Own.child_claim_list_mono_last
