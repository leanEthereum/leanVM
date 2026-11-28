/-
  LeanVM.Guest.B1.VsC.VsHonEc

  `verify_sub`'s pinned ends at the honest context, chosen: the definitions.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonParts
public import LeanVM.Guest.B1.VsC.VsNatLay
public import LeanVM.Guest.B1.VsC.VsNatHid
public import LeanVM.Guest.B1.VsC.RowSideE

/-!
# The pinned ends, chosen

The returns `ret` give `open_stacked`'s point buffers `bp`, `bp1` at `3991 …`, and those depend on its frame,
past `x.ec 15`. So each end `x.ec i` is chosen (`Classical.epsilon`) on its call at values that do not read `ret`:
the native closed forms of the link (`LinkNat.cap1`, `cap2`, `cap4`, `VsCtx.clI`, `natLI`, `natLR`, `natLC`,
`natRow`, `natLets`, `natPm`, `natBm`), `verify_keccak`'s run and `ring_switch_target`'s native buffers. The choice
reads only the context's fields other than `ec` and `ret` (through `VsCtx.skel`), so it is the same on every
context differing from `x` there.

* `VsCtx.ecRaw x N op point kw`: the ends `4, 6, 7, 9, 12, 13, 14, 15, 16` along vspin's table, `ec 12` as
  `ph11End`, `ec 16` and `open_stacked`'s point buffers from one `openCallEnd_nat` instance (`osPick`).
* **`VsCtx.ecOf`** `:= ecRaw x.skel`, **`VsCtx.bpOf`**, **`VsCtx.bp1Of`**.
* **`VsCtx.EcIn y N op point kw`**: the honest context's facts the choice needs (the guest's values against the
  native closed forms, `D3.Ok`'s native fields), each the honest choices' (vshp-asm's).
* **`VsCtx.EcFacts y N op point kw bp bp1`**: every pinned call `HonParts` and `D3.Ok` take, at `y`, with the
  steps `EcSteps 36`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link LeanVM.Guest.B1.Stack
open LeanVM.Guest.B1.Link
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VerifySub (keccakTauMin keccakTauMax qkeccakVarsCap)

@[expose] public section

/-- `link_terminal`'s valuation on the three values it reads: `.n 2846`, `.n 2891`, `.n 2890`. -/
def ltσ (a b c : E) : Val
  | .n 2846 => a
  | .n 2891 => b
  | _ => c

/-- `verify_keccak`'s oracle words: `.n 1076`'s pointer `bm`, the packed message's returns `pm` from `1287`. -/
def vkW (bm : ℕ) (pm : List E) (i : ℕ) : E := if i = 1076 then ptrAt bm else pm.getD (i - 1287) 0

namespace VsCtx

/-- The context without its ends and returns: what the choice of the ends reads. -/
def skel (x : VsCtx) : VsCtx := { x with ec := fun _ => 0, ret := fun _ _ => 0 }

variable (x : VsCtx) (N : NatOpen) (op point : List E) (kw : E)

/-- `squeeze_packed`'s frame past `certify_stack`'s end `e4` (`fpsp`'s). -/
noncomputable def fpspOf (e4 : ℕ) : ℕ :=
  allocBase (x.al "squeeze_packed")
    (leafEnd B2C.fs x.al (omName (1, 1)) (leafEnd B2C.fs x.al (spfName x.lay.stackLog) e4))

/-- `link_terminal`'s three values, natively. -/
noncomputable def ltσN : Val :=
  ltσ (natRow x N.L).coef ((natRow x N.L).certWeight * (natLets x N.L).cert)
    (prodE ((N.L.qPoint x.lay x.nF).map (1 + ·)) * (natRow x N.L).base)

/-- `certify_stack`'s end. -/
noncomputable def ec4 : ℕ := Classical.epsilon fun e =>
  CsCall B2C.fs x.al B2C.cert 17 x.lay x.qt (x.base 20) x.fpc e ∧ e ≤ x.fpc + B2C.fs "certify_stack" + 2 ^ 20

/-- `squeeze_packed`'s end, on the native capacity after `θ_0`. -/
noncomputable def ec6 : ℕ := Classical.epsilon fun e =>
  SpCall B2C.fs x.al B2C.cert 17 ((N.L.cap1 x.lay x.nF).getD 0 0) ((N.L.cap1 x.lay x.nF).getD 1 0)
    ((N.L.cap1 x.lay x.nF).getD 2 0) ((N.L.cap1 x.lay x.nF).getD 3 0) ((N.L.cap1 x.lay x.nF).getD 4 0)
    (ptrAt (x.base 4 + 1)) x.pk (x.fpspOf x.ec4) e ∧
  e ≤ x.fpspOf x.ec4 + B2C.fs "squeeze_packed" + 2 ^ 21

/-- `link_rounds__L1_L0`'s end, on the index side's native chain. -/
noncomputable def ec7 : ℕ := Classical.epsilon fun e =>
  LrCall B2C.fs x.al B2C.cert 17 ((N.L.cap2 x.lay x.nF).getD 0 0) ((N.L.cap2 x.lay x.nF).getD 1 0)
    ((N.L.cap2 x.lay x.nF).getD 2 0) ((N.L.cap2 x.lay x.nF).getD 3 0) ((N.L.cap2 x.lay x.nF).getD 4 0)
    (ptrAt x.sI) x.clI (ptrAt (x.base 6)) (ptrAt x.qt * word 365917469723852800 0) (x.natLI N.L) N.L.wsI.length
    (ph7Fp B2C.fs x.al x.wdS (x.ec6 N)) e ∧
  e ≤ ph7Fp B2C.fs x.al x.wdS (x.ec6 N) + B2C.fs "link_rounds__L1_L0" + 2 ^ 21

/-- `link_row_side__L{cc}`'s end, on the row side's native chains. -/
noncomputable def ec9 : ℕ := Classical.epsilon fun e =>
  LrsCall B2C.fs x.al B2C.cert 17 (chunkCount x.wdS) ((N.L.cap4 x.lay x.nF).getD 0 0)
    ((N.L.cap4 x.lay x.nF).getD 1 0) ((N.L.cap4 x.lay x.nF).getD 2 0) ((N.L.cap4 x.lay x.nF).getD 3 0)
    ((N.L.cap4 x.lay x.nF).getD 4 0) (ptrAt (x.natB772 N.L + 1)) (chainLast ⟨[], 0, 0⟩ (x.natLI N.L)).cl
    (ptrAt (x.base 9)) (ptrAt (x.base 10)) (ptrAt x.qt * word 365917469723852800 0) (x.natLR N.L) (x.natLC N.L)
    N.L.wsR.length N.L.wsC.length
    (allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec7 N))) e ∧
  e ≤ allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec7 N)) +
    B2C.fs (lrsNames.getD (chunkCount x.wdS - 6) "") + 2 ^ 23

/-- `Ph12`'s cursor: `Ph10`'s and `Ph11`'s leaves past the row side. -/
noncomputable def ec12 : ℕ := ph11End B2C.fs x.al x.nS x.h0S (x.ec9 N)

/-- `link_terminal__L{wd}`'s frame. -/
noncomputable def fp13 : ℕ :=
  allocBase (x.al (ltNames.getD (x.wdS - 19) "")) (tpKc B2C.fs x.al x.hgS 5 (x.ec12 N))

/-- `link_terminal__L{wd}`'s end, at the link section's native values. -/
noncomputable def ec13 : ℕ := Classical.epsilon fun e =>
  LtCall B2C.fs x.al B2C.cert 17 x.wdS (x.ltσN N) (N.L.endC x.lay x.nF).cl (x.base 6) (x.natBm N.L) (x.base 13)
    (x.base 4 + 89 + x.nS + x.wdS) ((x.bw.getD 6 []).take N.L.chunks.width) (x.sw (x.natBm N.L) 80 64)
    (natRow x N.L).shifts (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take N.L.chunks.d) (x.fp13 N) e ∧
  e ≤ x.fp13 N + B2C.fs (ltNames.getD (x.wdS - 19) "") + 2 ^ 21

/-- `verify_keccak`'s end, on the native run. -/
noncomputable def ec14 : ℕ := Classical.epsilon fun e =>
  VkCall B2C.fs x.al B2C.cert 17 (vkW (x.natBm N.L) (x.natPm N.L)) (x.base 9) (x.base 14) (x.base 15) x.qt
    (x.hgS 5) (x.bw.getD 9 []) (x.sw (x.natBm N.L) 55 25) (x.sw (x.natBm N.L) 144 N.xs.length) op point
    ((x.bw.getD 15 []).take 64) kw N.s' (allocBase (x.al "verify_keccak") (x.ec13 N)) e ∧
  e ≤ allocBase (x.al "verify_keccak") (x.ec13 N) + B2C.fs "verify_keccak" + 2 ^ 24

/-- `ring_switch_target`'s end, on the native ring buffers. -/
noncomputable def ec15 : ℕ := Classical.epsilon fun e =>
  RtCall B2C.fs x.al B2C.cert 17 x.a1 (rsW N.ks N.L.msg (ringRho N.S)) (ringF N.S ++ ringG N.S)
    (allocBase (x.al "ring_switch_target") (x.ec14 N op point kw)) e ∧
  e ≤ allocBase (x.al "ring_switch_target") (x.ec14 N op point kw) + B2C.fs "ring_switch_target" + 2 ^ 20

/-- **`open_stacked`'s native call at the cursor `kc`, with its bounds** (`openCallEnd_nat`'s conclusion). -/
def OsBody (bm nx kc bp bp1 e : ℕ) : Prop :=
  CallAtA B2C.fs x.al B2C.cert 17 (openName N.layout.stackLog)
      (rateSel N.r :: ringCap N.S ++ [N.target x.seed x.c, x.c.proof.stream.getD 8 0, x.c.proof.stream.getD 9 0,
        ptrAt (bm + 144 + nx + 1), ptrAt (x.qt + 178)])
      (osRets N.wE bp bp1 (bm + 144 + nx + 1 + N.ws.length)) (fun i => x.R i ∨ x.OwnB i)
      (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
      (fun rd => ReadsAt rd (ptrAt bp) (N.wE.point ++ List.replicate (pointCap - N.layout.stackLog) 0) ∧
        ReadsAt rd (ptrAt bp1) (N.wE.point.map (1 + ·) ++ List.replicate (pointCap - N.layout.stackLog) 1))
      (fun rd => ReadsAt rd (ptrAt (bm + 144 + nx + 1)) N.ws ∧ WinTabs rd (ptrAt (x.qt + 178)))
      (fun rd t => SameStreams (t.pops coreProgram rd)
          (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs (openName N.layout.stackLog)) (allocBase (x.al (openName N.layout.stackLog)) kc)
      (allocBase (x.al (openName N.layout.stackLog)) kc + B2C.fs (openName N.layout.stackLog)) e ∧
    bp + pointCap ≤ e ∧ bp1 + pointCap ≤ e ∧
    e ≤ allocBase (x.al (openName N.layout.stackLog)) kc + B2C.fs (openName N.layout.stackLog) + 2 ^ 36

/-- `open_stacked`'s point buffers and end, at `ring_switch_target`'s end. -/
noncomputable def osPick : ℕ × ℕ × ℕ := Classical.epsilon fun t =>
  x.OsBody N (x.natBm N.L) N.xs.length (x.ec15 N op point kw) t.1 t.2.1 t.2.2

/-- **The ends, read off the context's fields other than `ec` and `ret`.** -/
noncomputable def ecRaw (i : ℕ) : ℕ :=
  if i = 4 then x.ec4 else if i = 6 then x.ec6 N else if i = 7 then x.ec7 N else if i = 9 then x.ec9 N
  else if i = 12 then x.ec12 N else if i = 13 then x.ec13 N else if i = 14 then x.ec14 N op point kw
  else if i = 15 then x.ec15 N op point kw else if i = 16 then (x.osPick N op point kw).2.2 else 0

/-- **The honest context's ends.** -/
noncomputable def ecOf : ℕ → ℕ := x.skel.ecRaw N op point kw

/-- **`open_stacked`'s first point buffer.** -/
noncomputable def bpOf : ℕ := (x.skel.osPick N op point kw).1

/-- **`open_stacked`'s second point buffer.** -/
noncomputable def bp1Of : ℕ := (x.skel.osPick N op point kw).2.1

/-! ## What the choice needs, and what it gives -/

/-- **The honest context's facts the choice of the ends needs** (vshp-asm's, at every `ec`, `bp`, `bp1`): the guest's
values the calls read against their native closed forms, and `D3.Ok`'s native fields at `bm = natBm`,
`nx = |N.xs|`, `nxo = |N.ws|`, `ch = N.L.chunks`. -/
structure EcIn (y : VsCtx) (N : NatOpen) (op point : List E) (kw : E) : Prop where
  hbw : y.bw.map List.length = vsAllocSz y.p
  cap1 : [y.w 575, y.w 576, y.w 577, y.w 578, y.w 579] = N.L.cap1 y.lay y.nF
  g1 : [y.w 680, y.w 681, y.w 682, y.w 683, y.w 684] = N.L.cap2 y.lay y.nF
  g3 : y.w 580 = ptrAt y.sI
  gcl : lrClaim (y.w 752) (y.w 753) ((y.bw.getD 4 []).getD 6 0) ((y.bw.getD 4 []).getD 7 0) = y.clI
  g2 : [y.σ0 (.n 790), y.σ0 (.n 791), y.σ0 (.n 792), y.σ0 (.n 793), y.σ0 (.n 794)] = N.L.cap4 y.lay y.nF
  g773 : y.w 773 = (chainLast ⟨[], 0, 0⟩ (y.natLI N.L)).cl
  sec : LinkSecVals y N.L
  w1077 : y.w 1077 = (N.L.endC y.lay y.nF).cl
  hpm : ∀ j < 5, y.w (1288 + j) = (y.natPm N.L).getD (j + 1) 0
  w1076 : y.w 1076 = ptrAt (y.natBm N.L)
  hbmIn : y.base 18 ≤ y.natBm N.L ∧ y.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ y.base 18 + 256 * y.p
  hchw : N.L.chunks.width ≤ 24
  hchd : 89 + y.nS + y.wdS + N.L.chunks.d ≤ 153
  hid : LtIdentity N.L.chunks y.σ0 (y.w 1077) ((y.bw.getD 6 []).take N.L.chunks.width)
    (y.sw (y.natBm N.L) 80 64) (y.cells19.map Prod.snd)
    (((y.bw.getD 4 []).drop (89 + y.nS + y.wdS)).take N.L.chunks.d)
  hτ0 : keccakTauMin ≤ y.hgS 5
  hτ1 : y.hgS 5 ≤ keccakTauMax
  hcar : ∃ sp, (⟨[y.w 1288, y.w 1289, y.w 1290, y.w 1291, y.w 1292], []⟩ : Fs).Carries sp
  hrun : RunsTo (verifyKeccak (y.hgS 5) ((y.bw.getD 9 []).take (y.hgS 5)) (y.sw (y.natBm N.L) 55 25))
    ⟨[y.w 1288, y.w 1289, y.w 1290, y.w 1291, y.w 1292], []⟩ (y.sw (y.natBm N.L) 144 N.xs.length)
    ([⟨qkeccak, op, kw⟩], point, (y.bw.getD 15 []).take 64) N.s'
  hpend : N.s'.pend.length = rateScalars
  hopl : op.length ≤ qkeccakVarsCap
  hptl : qkeccakVarsCap + point.length ≤ (vsAllocSz y.p).getD 14 0
  hs64 : (rsW N.ks N.L.msg (ringRho N.S)).length = kBits
  hc16 : (ringF N.S ++ ringG N.S).length = 2 * ringMapWidth

/-- **The pinned calls at the honest context** (`Ret1.cs`, `Ret1.sp`, `LkCalls`, `Bw2.e12`, `D3.Ok.hlt`, `hvk`,
`ring_switch_target`'s call natively, `open_stacked`'s native call and its point buffers' bounds, `EcSteps`). -/
structure EcFacts (y : VsCtx) (N : NatOpen) (op point : List E) (kw : E) (bp bp1 : ℕ) : Prop where
  cs : CsCall B2C.fs y.al B2C.cert 17 y.lay y.qt (y.base 20) y.fpc (y.ec 4)
  sp : SpCall B2C.fs y.al B2C.cert 17 (y.w 575) (y.w 576) (y.w 577) (y.w 578) (y.w 579) (ptrAt (y.base 4 + 1)) y.pk
    y.fpsp (y.ec 6)
  lk : y.LkCalls (y.natLk2 N.L)
  e12 : y.ec 12 = ph11End B2C.fs y.al y.nS y.h0S (y.ec 9)
  hlt : LtCall B2C.fs y.al B2C.cert 17 y.wdS y.σ0 (y.w 1077) (y.base 6) (y.natBm N.L) (y.base 13)
    (y.base 4 + 89 + y.nS + y.wdS) ((y.bw.getD 6 []).take N.L.chunks.width) (y.sw (y.natBm N.L) 80 64)
    (y.cells19.map Prod.snd) (((y.bw.getD 4 []).drop (89 + y.nS + y.wdS)).take N.L.chunks.d)
    (allocBase (y.al (ltNames.getD (y.wdS - 19) "")) (tpKc B2C.fs y.al y.hgS 5 (y.ec 12))) (y.ec 13)
  hvk : VkCall B2C.fs y.al B2C.cert 17 y.w (y.base 9) (y.base 14) (y.base 15) y.qt (y.hgS 5) (y.bw.getD 9 [])
    (y.sw (y.natBm N.L) 55 25) (y.sw (y.natBm N.L) 144 N.xs.length) op point ((y.bw.getD 15 []).take 64) kw N.s'
    (allocBase (y.al "verify_keccak") (y.ec 13)) (y.ec 14)
  hrt : RtCall B2C.fs y.al B2C.cert 17 y.a1 (rsW N.ks N.L.msg (ringRho N.S)) (ringF N.S ++ ringG N.S)
    (allocBase (y.al "ring_switch_target") (y.ec 14)) (y.ec 15)
  hos : CallAtA B2C.fs y.al B2C.cert 17 (openName N.layout.stackLog)
      (rateSel N.r :: ringCap N.S ++ [N.target y.seed y.c, y.c.proof.stream.getD 8 0, y.c.proof.stream.getD 9 0,
        ptrAt (y.natBm N.L + 144 + N.xs.length + 1), ptrAt (y.qt + 178)])
      (osRets N.wE bp bp1 (y.natBm N.L + 144 + N.xs.length + 1 + N.ws.length)) (fun i => y.R i ∨ y.OwnB i)
      (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
      (fun rd => ReadsAt rd (ptrAt bp) (N.wE.point ++ List.replicate (pointCap - N.layout.stackLog) 0) ∧
        ReadsAt rd (ptrAt bp1) (N.wE.point.map (1 + ·) ++ List.replicate (pointCap - N.layout.stackLog) 1))
      (fun rd => ReadsAt rd (ptrAt (y.natBm N.L + 144 + N.xs.length + 1)) N.ws ∧ WinTabs rd (ptrAt (y.qt + 178)))
      (fun rd t => SameStreams (t.pops coreProgram rd)
          (Prover.merkleHints true (Prover.childQueries guestBytecode y.seed y.c) y.c.proof.openings) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs (openName N.layout.stackLog)) (allocBase (y.al (openName N.layout.stackLog)) (y.ec 15))
      (allocBase (y.al (openName N.layout.stackLog)) (y.ec 15) + B2C.fs (openName N.layout.stackLog)) (y.ec 16)
  hbp : bp + pointCap ≤ y.ec 16
  hbp1 : bp1 + pointCap ≤ y.ec 16
  steps : y.EcSteps 36 N.layout.stackLog

end VsCtx

end
end LeanVM.Guest.B1.VsC
