/-
  LeanVM.Guest.EndExecAGaps

  `ExecGaps` from the hint bridge with the bump pointer's track, on a layout with b2c's frame sizes:
  what is left of the allocation track, by name.
-/

module

public import LeanVM.Guest.EndExecAWithin
public import LeanVM.Guest.EndExecAMain

/-!
# The hint bridge with the allocation track

`ExecGaps.ofHintsAlloc`: `ExecGaps R Ks Km E0 Ct Q (YH L D A (YAlloc L D A))` from the bridge's
premises (`HintHyps`), the references of the honest tree (`RefH`), a layout with b2c's frame sizes
(`MainA` by `mainA_of`), the guest's cursor facts (`CurHyps`), the facts by hint kind (`BufHint`,
`FrameHint`, `AddrReady`) and the core route's fields.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Prover.Exec
open LeanVM.Guest.Bridge (FnAl)

public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-- **`ExecGaps` from the hint bridge and the allocation track's named facts.** -/
theorem ExecGaps.ofHintsAlloc {R : Ref → Prop} {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env}
    {Ct : Ref → Mode.Cts} {Q : Ref → Mode.Cert → ℕ → St → Prop} (hH : HintHyps L D A)
    (hRH : ∀ r, R r → RefH L (D r) r) (hfs : L.fs = B2C.fs) (hC : CurHyps L D A) (hB : BufHint L D A)
    (hF : FrameHint L D A) (hAr : AddrReady L D A) (certs : ModeCerts Ks Km E0) (main : MainOk Km E0)
    (frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
      Mode.FrameSpec C (refMem r.img) (OnRun (XOf (YH L D A (YAlloc L D A))) r) (Ct r) K (Q r K))
    (ctMain : ∀ r, Ct r Km.F.entry = none)
    (res : ∀ r, R r → r.Ok → Mode.ResRef guestProgram r.img r.n Ks (fun s ↦ XOf (YH L D A (YAlloc L D A)) r s))
    (term : TermRef R Ks (XOf (YH L D A (YAlloc L D A)))) :
    ExecGaps R Ks Km E0 Ct Q (YH L D A (YAlloc L D A)) :=
  ExecGaps.ofHints hH (allocTrack_ofHint hH hRH main (mainA_of hfs) hC hB hF hAr) hRH certs main frame ctMain res
    term

end

end LeanVM.Guest.EndExec
