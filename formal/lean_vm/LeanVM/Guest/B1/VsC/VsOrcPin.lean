/-
  LeanVM.Guest.B1.VsC.VsOrcPin

  `verify_sub`'s honest phases composed at the pinned callee ends.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh46
public import LeanVM.Guest.B1.VsC.VsOrcPh711
public import LeanVM.Guest.B1.VsC.VsOrcPh3Spec
public import LeanVM.Guest.B1.VsC.VsOrcPh3Ctx
public import LeanVM.Guest.B1.VsC.VsOrcAllocs

/-!
# The phases at the pinned ends

Every non-leaf callee's end is pinned at `x.ec i` (`VsCtx`'s table), its call a field of `Ret1`, `Bw2` or
`Bw3`, and `Carry6`, `Carry11` carry the callees' cursor at `x.ec 6`, `x.ec 12`. So `Ph12toEndS` is
`Ph12toEndP` (`ph12toEndS_of_P`), and with `frontS`, `ph4to6S`, `ph7to11S` and `vsAllocs`:
**`vsOrcWFromCallees_of_P`**: `VsOrcWFromCallees al 17` from `Ph12toEndP al` and `VsHonEx al`;
**`vsOrcWFromCallees_of_endP`**: the same from `Ph12EndP` at every honest context, boundary state and pinned
cursor (`ph12toEndP_of`). `Carry11` carries `certify_stack`'s stack (`StkAt`), so `Ph12toEndP` holds at every
alignment (`ph12toEndP_ctx`): **`vsOrcW_of_honexA`**, **`vsWindows_of_honexA`**: `verify_sub`'s windows from the
honest contexts' existence alone.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_sub`'s windows from the callees**, given `wC`'s last phases at the pinned cursor and the honest
context's existence. -/
theorem vsOrcWFromCallees_of_P {al : String → Bool} (h3 : Ph12toEndP al) (hH : VsHonEx al) :
    VsOrcWFromCallees al 17 :=
  vsOrcWFromCallees_of_specs (frontS al) (ph4to6S al) (ph7to11S al) (ph12toEndS_of_P h3) hH vsAllocs

/-- **`verify_sub`'s windows from the callees**, given `Ph12EndP` at the pinned ends and the honest context's
existence. -/
theorem vsOrcWFromCallees_of_endP {al : String → Bool}
    (hC : CheckStackTerminalCompleteAE B2C.fs al B2C.cert 17 fun c e => e ≤ c + 2 ^ 24)
    (h : ∀ x : VsCtx, x.al = al → x.Hon → VsCalleesCompleteA B2C.fs al B2C.cert 17 →
      ∀ Own : ℕ → Prop, (∀ i, x.OwnB i → Own i) → ∀ st : St, x.Bnd st → x.Carry11 st → st.kc = x.ec 12 →
      Ph12EndP al x Own st (x.ec 13) (x.ec 14) (x.ec 15))
    (hH : VsHonEx al) : VsOrcWFromCallees al 17 :=
  vsOrcWFromCallees_of_P (ph12toEndP_of hC h) hH

/-- **`verify_sub`'s windows from the callees, given the honest contexts.** -/
theorem vsOrcW_of_honexA {al : String → Bool} (hH : VsHonEx al) : VsOrcWFromCallees al 17 :=
  vsOrcWFromCallees_of_P (ph12toEndP_ctx al) hH

/-- **`verify_sub`'s windows (`GuestLeft.vsWindows`'s form), given the honest contexts.** -/
theorem vsWindows_of_honexA {al : String → Bool} (hH : VsHonEx al) : VsWindowsFromCallees al 17 :=
  vsWindowsFromCallees_of_orcW (vsOrcW_of_honexA hH)

end
end LeanVM.Guest.B1.VsC
