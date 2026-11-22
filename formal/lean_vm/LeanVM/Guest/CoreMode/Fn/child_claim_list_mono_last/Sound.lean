/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono_last.Sound

  `child_claim_list_mono_last`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its divisor.
-/

module

public import LeanVM.Guest.EndExecCoreFn
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.ResM
public import LeanVM.Guest.CoreMode.Gen.MonoWalkOk
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono_last.Data

namespace LeanVM.Guest.CoreMode.Own.child_claim_list_mono_last

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its divisor, nonzero** (the gap walk, `mono_ok`). -/
theorem nzs_ok : ∀ c ∈ nzs, NzOk c := by
  simp only [nzs, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact nzVal_ml0 mono_ok

end

end LeanVM.Guest.CoreMode.Own.child_claim_list_mono_last
