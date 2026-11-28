module

public import LeanVM.Guest.EndExec
public import LeanVM.Guest.Mode.InvCert

/-!
# `ExecGaps.frame` from the core route

The core route's frame interface (`Mode.FnSpec`, from each function's kernel checks by
`fnSpecC_of`) gives `ExecGaps`' `frame` at the core route's contracts (`ctCore`, the heap contracts'
table read on the reference image) and frame predicates (`qCore`, `Mode.guestQ`), once each frame of a
function on the route has an honest valuation (`CoreHonAll`) and a step keeps the memory within the
reference's `2^κ` cells (`UsedNextAll`): `frame_core`. `main`'s contract is none when the table has
no entry at `main` (`ctMain_core`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Prover.Exec

@[expose] public section

/-- **Each frame of a function on the core route has an honest valuation**: for core data `T` at a
certificate's entry, at each state of its run on a reference run in `R`. -/
def CoreHonAll (R : Ref → Prop) (T : List CoreMode.CFun) (Ks : List Cert) (X : Ref → St → Prop) : Prop :=
  ∀ r, R r → r.Ok → ∀ K ∈ Ks, ∀ Cf ∈ T, Cf.frame.entry = K.F.entry → CoreMode.CoreHon r.img (OnRun X r) K Cf

/-- **A step keeps the memory within the reference's `2^κ` cells**, at the states on a reference
run in `R`. -/
def UsedNextAll (R : Ref → Prop) (X : Ref → St → Prop) : Prop :=
  ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → CoreMode.UsedNext C r.img (OnRun X r)

/-- The core route's contracts on a reference run: the heap contracts' table `tab` on its image. -/
noncomputable abbrev ctCore (tab : List CoreMode.HcEnt) : Ref → Cts := fun r ↦ CoreMode.ctOf r.img tab

/-- The core route's frame predicates on a reference run. -/
abbrev qCore (tab : List CoreMode.HcEnt) (T : List CoreMode.CFun) : Ref → Cert → ℕ → St → Prop :=
  fun r ↦ guestQ tab T r.img

/-- **`ExecGaps.frame` from the core route**: every certificate meets its frame interface. -/
theorem frame_core {R : Ref → Prop} {Ks : List Cert} {Km : Cert} {E0 : Env} {Y : Ref → St → Prop}
    {tab : List CoreMode.HcEnt} {T : List CoreMode.CFun} (hc : ModeCerts Ks Km E0)
    (hfn : ∀ K ∈ Ks, FnSpec tab T K) (hH : CoreHonAll R T Ks (XOf Y)) (hU : UsedNextAll R (XOf Y)) :
    ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
      FrameSpec C (refMem r.img) (OnRun (XOf Y) r) (ctCore tab r) K (qCore tab T r K) :=
  fun r hR hr C hC K hK ↦ frameSpec_guest (hfn K hK) hC rfl ((progOk_of hc hC).ok K hK) r.img _ hr.log
    (fun _ h ↦ ⟨r.n, h.2.2⟩) (fun Cf hCf he ↦ hH r hR hr K hK Cf hCf he) (hU r hR hr C hC)

/-- **`main`'s contract is none** when the table has no entry at `main`. -/
theorem ctMain_core {tab : List CoreMode.HcEnt} {Km : Cert} (h : CoreMode.hcNone tab Km.F.entry = true) :
    ∀ r, ctCore tab r Km.F.entry = none :=
  fun _ ↦ CoreMode.ctOf_none (CoreMode.hcFind_none h)

end

end LeanVM.Guest.EndExec
