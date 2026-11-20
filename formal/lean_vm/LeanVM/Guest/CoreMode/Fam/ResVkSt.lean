/-
  LeanVM.Guest.CoreMode.Fam.ResVkSt

  `verify_keccak`'s reads past its layers' returned cursors (`Res.vkStB`), sound at the honest frames.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResVk
public import LeanVM.Guest.CoreMode.Fam.Kid
public import LeanVM.Guest.CoreMode.Fam.ResVtL
public import LeanVM.Guest.CoreMode.Fam.ResCld
public import LeanVM.Guest.CoreMode.Fam.SubDefs
/-!
# `verify_keccak`'s body in parts

`vkT_pre`: `verify_keccak`'s template as its head, first step and steps, then its output, input and
final parts.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B2C (fsN cellJ siteOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (vkStB vkStSites stResB)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

section

variable {σ : Core.Val}

end

theorem vkT_pre : vkT = (vkHeadT ++ vkFirstT ++ vkStepsT) ++ (vkOutT ++ vkInT ++ vkFinT) := by
  rw [vkT]; simp only [List.append_assoc]

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

end

end LeanVM.Guest.EndExec
