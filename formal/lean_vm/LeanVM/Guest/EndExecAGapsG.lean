/-
  LeanVM.Guest.EndExecAGapsG

  `ExecGaps` from the hint bridge with the allocation track at the deployed alignment (`Bridge.alignA`),
  every function's allocation track and address hints' checks discharged by the kernel.
-/

module

public import LeanVM.Guest.EndExecAGapsChk
public import LeanVM.Guest.EndExecAAddr
public import LeanVM.Guest.EndExecAStat
public import LeanVM.Guest.EndExecABuf
public import LeanVM.Guest.Bridge.AllocChk.All
public import LeanVM.Guest.EndExecAFrHint
public import LeanVM.Guest.Bridge.FrAlChk.All
public import LeanVM.Guest.Bridge.JumpCells.All

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec LeanVM.Guest
open LeanVM.Guest.Bridge (alignA)

public section

variable {L : Lay} {D : Ref → RefD}

/-- **`ExecGaps` from the hint bridge at the deployed alignment**: `ExecGaps.ofHintsAllocChk` with
the per-function checks `Bridge.AllocChk.allocFnChk_guest` and, for `AddrReady` (`addrReady_of`),
`Bridge.AllocChk.addrFnChk_guest`, with `AddrFacts` from the fixed cells' words `hstat` (`addrFacts_of`). -/
theorem ExecGaps.ofHintsAllocG {R : Ref → Prop} {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env}
    {Ct : Ref → Mode.Cts} {Q : Ref → Mode.Cert → ℕ → St → Prop} (hH : HintHyps L D alignA)
    (hRH : ∀ r, R r → RefH L (D r) r) (hfs : L.fs = B2C.fs)
    (hB : BufHint L D alignA) (hF : FrameHint L D alignA)
    (hstat : ∀ r, RefH L (D r) r → r.Ok → ∀ pc fp done e st, RefTrack L D alignA r pc fp (done, e :: st) →
      ∀ q o, (alignA e.I.t.name).X.statOf q = some (.fpg o) → q < L.fs e.I.t.name →
        refMem r.img (e.I.fp + q) = ofK (g ^ (e.I.fp + o)))
    (certs : ModeCerts Ks Km E0) (main : MainOk Km E0)
    (frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
      Mode.FrameSpec C (refMem r.img) (OnRun (XOf (YH L D alignA (YAlloc L D alignA))) r) (Ct r) K (Q r K))
    (ctMain : ∀ r, Ct r Km.F.entry = none)
    (res : ∀ r, R r → r.Ok →
      Mode.ResRef guestProgram r.img r.n Ks (fun s ↦ XOf (YH L D alignA (YAlloc L D alignA)) r s))
    (term : TermRef R Ks (XOf (YH L D alignA (YAlloc L D alignA)))) :
    ExecGaps R Ks Km E0 Ct Q (YH L D alignA (YAlloc L D alignA)) :=
  ExecGaps.ofHintsAllocChk hH hRH hfs Bridge.AllocChk.allocFnChk_guest hB hF
    (addrReady_of hH hfs Bridge.AllocChk.addrFnChk_guest (addrFacts_of Bridge.AllocChk.allocFnChk_guest hstat)) certs main frame ctMain res term

/-- **Every address hint has what it needs at the deployed alignment**, on B2's layout: the address
check by the kernel, the fixed cells' words from the honest frames (`addrStat_of`). -/
theorem addrReady_alignA {L : Lay} (hH : HintHyps L D alignA) (hfs : L.fs = B2C.fs) (hHd : L.H = B2C.H)
    (hC : L.C = B2C.C) (hc : L.cert = B2C.cert) : AddrReady L D alignA :=
  addrReady_of hH hfs Bridge.AllocChk.addrFnChk_guest
    (addrFacts_of Bridge.AllocChk.allocFnChk_guest (addrStat_of hfs hHd hC hc))

/-- **`ExecGaps` from the hint bridge at the deployed alignment on B2's layout**: `ofHintsAllocG`
with the fixed cells' words proved. -/
theorem ExecGaps.ofHintsAllocB {R : Ref → Prop} {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env}
    {Ct : Ref → Mode.Cts} {Q : Ref → Mode.Cert → ℕ → St → Prop} (hH : HintHyps L D alignA)
    (hRH : ∀ r, R r → RefH L (D r) r) (hfs : L.fs = B2C.fs) (hHd : L.H = B2C.H) (hC : L.C = B2C.C)
    (hc : L.cert = B2C.cert) (hB : BufHint L D alignA) (hF : FrameHint L D alignA)
    (certs : ModeCerts Ks Km E0) (main : MainOk Km E0)
    (frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
      Mode.FrameSpec C (refMem r.img) (OnRun (XOf (YH L D alignA (YAlloc L D alignA))) r) (Ct r) K (Q r K))
    (ctMain : ∀ r, Ct r Km.F.entry = none)
    (res : ∀ r, R r → r.Ok →
      Mode.ResRef guestProgram r.img r.n Ks (fun s ↦ XOf (YH L D alignA (YAlloc L D alignA)) r s))
    (term : TermRef R Ks (XOf (YH L D alignA (YAlloc L D alignA)))) :
    ExecGaps R Ks Km E0 Ct Q (YH L D alignA (YAlloc L D alignA)) :=
  ExecGaps.ofHintsAllocChk hH hRH hfs Bridge.AllocChk.allocFnChk_guest hB hF
    (addrReady_alignA hH hfs hHd hC hc) certs main frame ctMain res term


/-- **The buffer hints at the deployed alignment**, on B2's layout: the buffer check by the kernel,
given the dynamic sizes powers of `g`. -/
theorem bufHint_alignA {L : Lay} (hH : HintHyps L D alignA) (hfs : L.fs = B2C.fs) (hHd : L.H = B2C.H)
    (hC : L.C = B2C.C) (hc : L.cert = B2C.cert) (hD : DynPowA L D) : BufHint L D alignA :=
  bufHint_of hfs hHd hC hc hH hD Bridge.AllocChk.bufFnChk_guest

/-- **`ExecGaps` from the hint bridge at the deployed alignment on B2's layout**: `ofHintsAllocB` with
the buffer hints from `DynPowA`. -/
theorem ExecGaps.ofHintsAllocD {R : Ref → Prop} {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env}
    {Ct : Ref → Mode.Cts} {Q : Ref → Mode.Cert → ℕ → St → Prop} (hH : HintHyps L D alignA)
    (hRH : ∀ r, R r → RefH L (D r) r) (hfs : L.fs = B2C.fs) (hHd : L.H = B2C.H) (hC : L.C = B2C.C)
    (hc : L.cert = B2C.cert) (hD : DynPowA L D) (hF : FrameHint L D alignA)
    (certs : ModeCerts Ks Km E0) (main : MainOk Km E0)
    (frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
      Mode.FrameSpec C (refMem r.img) (OnRun (XOf (YH L D alignA (YAlloc L D alignA))) r) (Ct r) K (Q r K))
    (ctMain : ∀ r, Ct r Km.F.entry = none)
    (res : ∀ r, R r → r.Ok →
      Mode.ResRef guestProgram r.img r.n Ks (fun s ↦ XOf (YH L D alignA (YAlloc L D alignA)) r s))
    (term : TermRef R Ks (XOf (YH L D alignA (YAlloc L D alignA)))) :
    ExecGaps R Ks Km E0 Ct Q (YH L D alignA (YAlloc L D alignA)) :=
  ExecGaps.ofHintsAllocB hH hRH hfs hHd hC hc (bufHint_alignA hH hfs hHd hC hc hD) hF certs main frame ctMain
    res term

/-- **The callee frames' hints at the deployed alignment**, on B2's layout at the budget's flags: the
frame sizes', allocation and flags' checks by the kernel, given the loops' facts. -/
theorem frameHint_alignA {L : Lay} (hH : HintHyps L D alignA) (hfs : L.fs = B2C.fs) (hHd : L.H = B2C.H)
    (hC : L.C = B2C.C) (hc : L.cert = B2C.cert) (hal : L.al = Memory.alW) (hPO : Res.ProgOk coreProgram) :
    FrameHint L D alignA :=
  frameHint_of hfs hHd hC hc hal hH hPO Bridge.AllocChk.frFnChk_guest Bridge.AllocChk.allocFnChk_guest
    Bridge.FrAlChk.frAlJ_all fun j h1 h2 ↦ Bridge.JumpCells.jcData_all j h1 (by have : nFns = fn_count% := rfl; omega)

/-- **`ExecGaps` from the hint bridge at the deployed alignment on B2's layout at the budget's flags**:
`ofHintsAllocD` with the callee frames' hints proved, given the loops' facts. -/
theorem ExecGaps.ofHintsAllocF {R : Ref → Prop} {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env}
    {Ct : Ref → Mode.Cts} {Q : Ref → Mode.Cert → ℕ → St → Prop} (hH : HintHyps L D alignA)
    (hRH : ∀ r, R r → RefH L (D r) r) (hfs : L.fs = B2C.fs) (hHd : L.H = B2C.H) (hC : L.C = B2C.C)
    (hc : L.cert = B2C.cert) (hal : L.al = Memory.alW) (hPO : Res.ProgOk coreProgram) (hD : DynPowA L D)
    (certs : ModeCerts Ks Km E0) (main : MainOk Km E0)
    (frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
      Mode.FrameSpec C (refMem r.img) (OnRun (XOf (YH L D alignA (YAlloc L D alignA))) r) (Ct r) K (Q r K))
    (ctMain : ∀ r, Ct r Km.F.entry = none)
    (res : ∀ r, R r → r.Ok →
      Mode.ResRef guestProgram r.img r.n Ks (fun s ↦ XOf (YH L D alignA (YAlloc L D alignA)) r s))
    (term : TermRef R Ks (XOf (YH L D alignA (YAlloc L D alignA)))) :
    ExecGaps R Ks Km E0 Ct Q (YH L D alignA (YAlloc L D alignA)) :=
  ExecGaps.ofHintsAllocD hH hRH hfs hHd hC hc hD (frameHint_alignA hH hfs hHd hC hc hal hPO) certs main frame
    ctMain res term

end

end LeanVM.Guest.EndExec
