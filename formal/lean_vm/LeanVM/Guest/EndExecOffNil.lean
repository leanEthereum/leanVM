/-
  LeanVM.Guest.EndExecOffNil

  `GuestLeft.off` once every function is on the core route.
-/

module

public import LeanVM.Guest.CoreMode.Gen.Certs
public import LeanVM.Guest.CoreMode.Route

/-!
# No function off the core route

`off_of_routed`: once the generated list of functions off the core route (`CoreMode.offSigs`) is empty,
`GuestLeft.off` holds at `Toff = []`: `OffOk` asks nothing of an empty list.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Guest LeanVM.Guest.EndExec

public section

/-- **`OffOk` of no function off the route.** -/
theorem offOk_nil {tab : List CoreMode.HcEnt} (ls : List (List (CertE tab))) (offK : Mode.Sig → Mode.Cert) :
    OffOk ls [] offK [] :=
  fun _ hG ↦ by simp at hG

/-- **`GuestLeft.off` once every function is routed.** -/
theorem off_of_routed (h : CoreMode.offSigs = []) :
    ∃ (offK : Mode.Sig → Mode.Cert) (Toff : List CoreMode.CFun),
      OffOk CoreMode.corePacks CoreMode.offSigs offK Toff ∧ ∀ Cf ∈ Toff, CoreMode.CfOk Cf :=
  ⟨fun _ ↦ Fn.«main».modeCert, [], h ▸ offOk_nil _ _, fun _ hc ↦ by simp at hc⟩

end

end LeanVM.Guest.Complete
