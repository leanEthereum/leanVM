/-
  LeanVM.Guest.CoreMode.Fam.ResVtSt

  `verify_tables`' reads past its table sumcheck's last record's cursor (`Res.vtStB`), sound at the
  honest frames: they lie inside its stream.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResVt
public import LeanVM.Guest.CoreMode.Fam.ResStB
public import LeanVM.Guest.CoreMode.Fam.SubDefs

/-!
# `verify_tables`' index

`vt_idx`: `verify_tables`' stable name at its index.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Guest.B2C (idxOf fsN cellJ)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (vtStB stRes topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

theorem vt_idx : idxOf name% «verify_tables» = some (fn_idx% «verify_tables») := by
  decide +kernel

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

end

end

end LeanVM.Guest.EndExec
