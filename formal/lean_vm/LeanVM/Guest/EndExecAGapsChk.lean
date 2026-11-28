/-
  LeanVM.Guest.EndExecAGapsChk

  `ExecGaps` from the hint bridge with the allocation track, the guest's cursor facts read off one
  check per function (`Bridge.allocFnChk`).
-/

module

public import LeanVM.Guest.EndExecAGaps
public import LeanVM.Guest.EndExecACurHyps

namespace LeanVM.Guest.EndExec

open LeanVM.Prover.Exec LeanVM.Guest
open LeanVM.Guest.Bridge (FnAl allocFnChk)

public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-- **`ExecGaps` from the hint bridge, the allocation track's per-function check and the facts by
hint kind.** -/
theorem ExecGaps.ofHintsAllocChk {R : Ref → Prop} {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env}
    {Ct : Ref → Mode.Cts} {Q : Ref → Mode.Cert → ℕ → St → Prop} (hH : HintHyps L D A)
    (hRH : ∀ r, R r → RefH L (D r) r) (hfs : L.fs = B2C.fs)
    (hchk : ∀ f fn, coreProgram.find? f = some fn → allocFnChk (A f).X fn (A f).code (A f).d = true)
    (hB : BufHint L D A) (hF : FrameHint L D A) (hAr : AddrReady L D A) (certs : ModeCerts Ks Km E0)
    (main : MainOk Km E0)
    (frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
      Mode.FrameSpec C (refMem r.img) (OnRun (XOf (YH L D A (YAlloc L D A))) r) (Ct r) K (Q r K))
    (ctMain : ∀ r, Ct r Km.F.entry = none)
    (res : ∀ r, R r → r.Ok → Mode.ResRef guestProgram r.img r.n Ks (fun s ↦ XOf (YH L D A (YAlloc L D A)) r s))
    (term : TermRef R Ks (XOf (YH L D A (YAlloc L D A)))) :
    ExecGaps R Ks Km E0 Ct Q (YH L D A (YAlloc L D A)) :=
  ExecGaps.ofHintsAlloc hH hRH hfs (curHyps_of hH.progAl hchk) hB hF hAr certs main frame ctMain res term

end

end LeanVM.Guest.EndExec
