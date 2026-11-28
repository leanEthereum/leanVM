/-
  LeanVM.Guest.B1.VsC.VsOrcSpec

  The honest oracle's context and the phase helpers' statements.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcHonest
public import LeanVM.Guest.B1.VsC.VsOrcTail
public import LeanVM.Guest.B1.VsC.VsPostE
public import LeanVM.Guest.B1.VsC.VsOrcPhD
public import LeanVM.Guest.B1.VsC.VsOrcEnd
public import LeanVM.Guest.Complete.MainWords
public import LeanVM.Guest.B1.VsC.VsOrcFront2

/-!
# The honest oracle's context and the phases' statements

**The honest memory** `vsRd1 rdP cur bw ex`: the own buffers' words `bw` from `cur` (`vsAllocIdx` order, sizes
`vsAllocSz p`), then the extra cells `ex` (callees' outputs the body reads, past the buffers), then a memory `rdP`
satisfying `Pre` (so the exponent table at `qt` and the fresh claim at `qo`, wherever they lie below `fp`), `0`
where `rdP` is undefined (so `LowDef k` for every `k`). The evaluation memory `rd0` overlays `.n 19`'s twelve words with `w32`'s stored values on `rd1`
(`vsCells19`), which no fresh load of the body reads (`vsVal_congr`). The oracle is `vsW rd1 args cur p ret`.

**A context** `x : VsCtx`: the alignment flags `al`, the child, the placement, the callees' end cursors `ec`
(the helpers' `Ret*` pin them to their callees' `CallAtA` ends), the buffers' words `bw` (`.n 19`'s entry is overwritten
by the overlay in `Wo`) and the callees' return rule `ret`; every honest object is a function of it (`x.rd1`,
`x.w`, `x.rd0`, `x.σ0`, `x.Wo`, `x.Own`, `x.R`, `x.Pre`, `x.st0`). `x.Hon`: the placement's hypotheses, the
buffers' sizes, a causal `ret`, and the phase helpers' own conditions on `bw` and `ret` (`Bw1 … Ret3`, each
owned by one helper, `True` until it states them). The statements hold for every `Own` containing the
buffers' cells `x.OwnB`: their instance at `fun _ => True` gives the walk, so `verify_sub`'s allocations, so
`x.OwnB ⊆ x.Own`.

**The phases' statements**, in continuation form, each at every state with the boundary facts `Bnd`
(the `HeapBuf` cursor past the front, the callees' cursor past the buffers, `Wo` held, the posts so far a
prefix of the honest pops) and the producer's carried facts (`CarryF`, `Carry6`, `Carry11`, `True` until a
consumer needs more; the producer then proves them):
* `FrontS al` (vsph1): `FrontOk` from `x.st0B` (`x.st0` at the honest allocations), its continuation at every
  `Bnd ∧ CarryF` state;
* `Ph4to6S al` (vsph1): `Ph4Ok … Ph6Ok`, from `Bnd ∧ CarryF` to `Bnd ∧ Carry6`;
* `Ph7to11S al` (vsph2): `Ph7Ok … Ph11Ok`, from `Bnd ∧ Carry6` to `Bnd ∧ Carry11`;
* `Ph12toEndS al` (vsph3): `Ph1213Ok`, then `TailOk` to `vsKEndW`, from `Bnd ∧ Carry11`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Guest.B1.Link
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The honest memory -/

/-- The values `w32` stores into `.n 19`'s twelve words, in order. -/
def vs19Src : List ℕ := [2854, 2862, 2870, 2872, 2874, 2876, 2878, 2880, 2882, 2884, 2886, 2888]

/-- The own buffers' runs: the words `bw` one after another from `cur`. -/
def vsRuns (cur : ℕ) (bw : List (List E)) : Words := (bases cur (bw.map List.length)).zip bw

/-- The word an extra cell list gives an address, the first entry first. -/
def exAt (ex : List (ℕ × E)) (A : K) : Option E :=
  (ex.find? fun q => decide (addressOfIndex q.1 = A)).map Prod.snd

/-- **The honest memory before the overlay**: the buffers' runs, then the extra cells, then `rdP`, `0` where
`rdP` is undefined. -/
noncomputable def vsRd1 (rdP : Reader) (cur : ℕ) (bw : List (List E)) (ex : List (ℕ × E)) : Reader := fun A =>
  (rdW (vsRuns cur bw) A).or ((exAt ex A).or (some ((rdP A).getD 0)))

/-- The overlay's cells: `.n 19`'s twelve words from `b19`, `w32`'s stored values on `σ`. -/
def vsCells19 (b19 : ℕ) (σ : Val) : List (ℕ × E) :=
  (List.range 12).map fun j => (b19 + j, σ (.n (vs19Src.getD j 0)))

/-- `verify_sub`'s honest pops, as `vsPostA_final` asks them (`[]` off an announced layout). -/
noncomputable def vsPsH (seed : Digest) (c : Child) (σ : Val) : List (List Pop) :=
  match announcedLayoutAndRate guestBytecode c.proof.stream with
  | some (layout, _) => vsPs σ (vsChunks c.proof.stream) (Prover.stackHints (stackKappas layout))
      (Prover.merkleHints true (Prover.childQueries guestBytecode seed c) c.proof.openings)
  | none => []

/-! ## The non-leaf callees' calls at a frame and an end

Each is its completeness statement's `CallAtA` at the frame `fp`, ending at `e`: `certify_stack`
(`CertifyStackCompleteA`), `squeeze_packed` (`SqueezePackedCompleteA`), `link_rounds__L1_L0`
(`LinkRoundsCompleteA` at `(1, 0)`), `link_row_side__L{d}` (`LinkRowSideCompleteA`). A context pins each end
at `x.ec i` (`Ret1`, `Bw2`), so the returns `ret` fixes after it may name positions past it. -/

open LeanVM.Guest.B1.Stack LeanVM.Guest.B1.VerifySub LeanVM.Protocol.Compile in
/-- `certify_stack`'s call at the frame `fp`, ending at `e`. -/
def CsCall (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (layout : Layout)
    (qt qk fp e : ℕ) : Prop :=
  CallAtA fs al cert k "certify_stack" [ptrAtV qk, ptrAtV qt]
    [gen ^ layout.stackLog, ptrAtV (csOffsAt (fp + fs "certify_stack")),
      ptrAtV (csOffsAt (fp + fs "certify_stack") + 52)]
    (fun i => (qt ≤ i ∧ i < qt + (winTabAt + 2 ^ winTabBits)) ∨ (qk ≤ i ∧ i < qk + (2 + nTables)))
    (fun i => csOffsAt (fp + fs "certify_stack") ≤ i ∧ i < csOffsAt (fp + fs "certify_stack") + 104)
    (fun rd => StackPlaced rd layout (gen ^ layout.stackLog) (ptrAtV (csOffsAt (fp + fs "certify_stack")))
      (ptrAtV (csOffsAt (fp + fs "certify_stack") + 52)))
    (fun rd => ExpTables rd (ptrAtV qt) ∧
      ReadsAt rd (ptrAtV qk) (kappaSources layout.logMemory layout.tableLogHeights))
    (fun rd t => t.pops coreProgram rd = Prover.stackHints (stackKappas layout) ∧
      t.Every (ExactAt coreProgram rd))
    (fs "certify_stack") fp (fp + fs "certify_stack") e

/-- `squeeze_packed`'s call at the frame `fp`, ending at `e`. -/
def SpCall (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (f0 f1 f2 f3 f4 out : E)
    (p fp e : ℕ) : Prop :=
  CallAtA fs al cert k "squeeze_packed" [f0, f1, f2, f3, f4, out, gen ^ p]
    (pkSqueeze p [f0, f1, f2, f3, f4]).2
    (ptrRegion [(out, (pkSqueeze p [f0, f1, f2, f3, f4]).1.length)]) (fun _ => False) (fun _ => True)
    (fun rd ↦ ReadsAt rd out (pkSqueeze p [f0, f1, f2, f3, f4]).1)
    PostQuiet (fs "squeeze_packed") fp (fp + fs "squeeze_packed") e

/-- `link_rounds__L1_L0`'s call at the frame `fp`, ending at `e`. -/
def LrCall (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ)
    (f0 f1 f2 f3 f4 cur cl point tabs : E) (l : List (E × RSt)) (nw fp e : ℕ) : Prop :=
  CallAtA fs al cert k "link_rounds__L1_L0" [f0, f1, f2, f3, f4, cur, cl, point, gen ^ l.length, tabs]
    (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l).cells
    (ptrRegion (lrArrays cur point tabs nw l.length)) (fun _ => False) (fun _ => True)
    (fun rd ↦ ((0 : ℕ) ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd 1 0 ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l ∧
      ReadsAt rd point (l.map Prod.fst))
    PostQuiet (fs "link_rounds__L1_L0") fp (fp + fs "link_rounds__L1_L0") e

/-- `link_row_side__L{d}`'s call at the frame `fp`, ending at `e`. -/
def LrsCall (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k d : ℕ)
    (f0 f1 f2 f3 f4 cur cl chi qp tabs : E) (l1 l2 : List (E × RSt)) (nw1 nw2 fp e : ℕ) : Prop :=
  CallAtA fs al cert k (lrsNames.getD (d - 6) "") [f0, f1, f2, f3, f4, cur, cl, chi, qp, gen ^ l1.length, tabs]
    (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cells
    (ptrRegion (lrsArrays cur (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cur chi qp tabs nw1 nw2 l1.length))
    (fun _ => False) (fun _ => True)
    (fun rd ↦ WinTabs rd tabs ∧ RoundChain rd (d + 1) (lrsGrind d).1 ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1 ∧
      RoundChain rd d (lrsGrind d).2 (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2 ∧
      ReadsAt rd chi (l1.map Prod.fst) ∧ ReadsAt rd qp (l2.map Prod.fst))
    PostQuiet (fs (lrsNames.getD (d - 6) "")) fp (fp + fs (lrsNames.getD (d - 6) "")) e

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}

open LeanVM.Guest.B1.Stack LeanVM.Guest.B1.VerifySub LeanVM.Protocol.Compile in
/-- `certify_stack`'s completeness gives its call at some end. -/
theorem csCall_of (h : CertifyStackCompleteA fs al cert k) {bytecode : List K} {logMemory : ℕ} {rows : List ℕ}
    {layout : Layout} {qt qk fp : ℕ} (hb : buildLayout bytecode logMemory rows = some layout)
    (hs : layout.stackLog ≤ 30) (ht : qt + (winTabAt + 2 ^ winTabBits) ≤ fp) (hk : qk + (2 + nTables) ≤ fp) :
    ∃ e, CsCall fs al cert k layout qt qk fp e :=
  h bytecode logMemory rows layout qt qk fp hb hs ht hk

/-- `squeeze_packed`'s completeness gives its call at some end. -/
theorem spCall_of (h : SqueezePackedCompleteA fs al cert k) {f0 f1 f2 f3 f4 out : E} {p fp : ℕ} (hp : p < 64)
    (hb : PtrsBelow [(out, (pkSqueeze p [f0, f1, f2, f3, f4]).1.length)] fp) :
    ∃ e, SpCall fs al cert k f0 f1 f2 f3 f4 out p fp e :=
  h f0 f1 f2 f3 f4 out p fp hp hb

/-- `link_rounds__L1_L0`'s completeness gives its call at some end. -/
theorem lrCall_of (h : LinkRoundsCompleteA fs al cert k 1 0 "link_rounds__L1_L0") {f0 f1 f2 f3 f4 cur cl point tabs : E}
    {l : List (E × RSt)} {nw fp : ℕ} (hl : l.length < 64) (hc : cur ≠ 0)
    (hcur : (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l).cur = cur * gen ^ nw)
    (hb : PtrsBelow (lrArrays cur point tabs nw l.length) fp) :
    ∃ e, LrCall fs al cert k f0 f1 f2 f3 f4 cur cl point tabs l nw fp e :=
  h f0 f1 f2 f3 f4 cur cl point tabs l nw fp hl hc hcur hb

/-- `link_row_side__L{d}`'s completeness, from the link callees, gives its call at some end. -/
theorem lrsCall_of (h : VsLinkCalleesA fs al cert k) {d : ℕ} (h6 : 6 ≤ d) (h9 : d ≤ 9)
    {f0 f1 f2 f3 f4 cur cl chi qp tabs : E} {l1 l2 : List (E × RSt)} {nw1 nw2 fp : ℕ} (hl1 : l1.length < 64)
    (hl2 : l2.length = 6) (hc : cur ≠ 0)
    (hcur1 : (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cur = cur * gen ^ nw1)
    (hcur2 : (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cur =
      (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cur * gen ^ nw2)
    (hb : PtrsBelow (lrsArrays cur (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cur chi qp tabs nw1 nw2 l1.length)
      fp) :
    ∃ e, LrsCall fs al cert k d f0 f1 f2 f3 f4 cur cl chi qp tabs l1 l2 nw1 nw2 fp e :=
  h.row_side d h6 h9 f0 f1 f2 f3 f4 cur cl chi qp tabs l1 l2 nw1 nw2 fp hl1 hl2 hc hcur1 hcur2 hb

end

/-- `link_rounds__L1_L0`'s frame: past `state_ends__L{wd}`'s leaf at `kc`. -/
def ph7Fp (fs : String → ℕ) (al : String → Bool) (wd kc : ℕ) : ℕ :=
  allocBase (al "link_rounds__L1_L0") (leafEnd fs al (seNames.getD (wd - 19) "") kc)

/-- The callees' cursor after `Ph8`'s two leaves, `index_side__L{wd}` and `index_mle__L{wd}`, from `kc`. -/
def ph8End (fs : String → ℕ) (al : String → Bool) (wd kc : ℕ) : ℕ :=
  allocBase (al (imNames.getD (wd - 19) "")) (allocBase (al (isNames.getD (wd - 19) "")) kc +
    fs (isNames.getD (wd - 19) "")) + fs (imNames.getD (wd - 19) "")

/-- The callees' cursor after `Ph10`'s and `Ph11`'s leaves (`one_plus_suffixes__L{n}`, `packed_message__L144`,
`table_point__L{h}`), from `kc`. -/
def ph11End (fs : String → ℕ) (al : String → Bool) (n h kc : ℕ) : ℕ :=
  leafEnd fs al (tpNames.getD h "") (leafEnd fs al "packed_message__L144" (leafEnd fs al (opsNames.getD n "") kc))

/-! ## The context -/

/-- **A placement and the honest choices**: the alignment flags, the child, the placement, a memory `rdP`
satisfying `Pre`, the callees' end cursors `ec`, the own buffers' words, the extra cells, the callees' return
rule. The non-leaf callees' ends, each pinned by its call in `Ret1`, `Bw2` or `Bw3`: `ec 4` `certify_stack`,
`ec 6` `squeeze_packed` (`Carry6`'s cursor), `ec 7` `link_rounds__L1_L0`, `ec 9` `link_row_side__L{cc}`,
`ec 12` `Ph12`'s start (`Ph11`'s leaves past `ec 9`, `Carry11`'s cursor), `ec 13` `link_terminal__L{w}`,
`ec 14` `verify_keccak`, `ec 15` `ring_switch_target`, `ec 16` `open_stacked__L{s}`. -/
structure VsCtx where
  al : String → Bool
  seed : Digest
  c : Child
  qt : ℕ
  qo : ℕ
  fp : ℕ
  cur : ℕ
  rdP : Reader
  ec : ℕ → ℕ
  bw : List (List E)
  ex : List (ℕ × E)
  ret : ℕ → (ℕ → E) → E

namespace VsCtx

variable (x : VsCtx)

/-- The stream's chunk count. -/
def p : ℕ := chunksOf x.c.proof.stream.length

/-- `verify_sub`'s arguments. -/
def args : List E := vsArgs x.seed x.c (ptrAt x.qt) (ptrAt x.qo)

/-- The honest memory before the overlay. -/
noncomputable def rd1 : Reader := vsRd1 x.rdP x.cur x.bw x.ex

/-- **The honest oracle.** -/
noncomputable def w : ℕ → E := vsW x.rd1 x.args x.cur x.p x.ret

/-- Own buffer `j`'s base (`vsAllocIdx` order). -/
def base (j : ℕ) : ℕ := (bases x.cur (vsAllocSz x.p)).getD j 0

/-- The overlay's cells, on `rd1`'s values. -/
noncomputable def cells19 : List (ℕ × E) := vsCells19 (x.base 13) (vsVal x.rd1 x.w x.args)

/-- **The evaluation memory.** -/
noncomputable def rd0 : Reader := rdSet x.rd1 x.cells19

/-- `verify_sub`'s valuation. -/
noncomputable def σ0 : Val := vsσ x.rd0 x.w x.seed x.c x.qt x.qo

/-- **The node's own words**: the buffers from `cur`, `.n 19`'s the overlay's. -/
noncomputable def Wo : Words := (bases x.cur (vsAllocSz x.p)).zip (x.bw.set 13 (x.cells19.map Prod.snd))

/-- `verify_sub`'s own cells. -/
noncomputable def Own : ℕ → Prop := vsOwn x.fp x.cur x.σ0

/-- The cells the honest buffers take: `[cur, cur + Σ vsAllocSz p)`. Each statement holds for every `Own`
containing them; vsorc instantiates it at `x.Own` (`allocs σ0 (vsEs σ0) = vsAllocSz p`, from the walk an
instance at `fun _ => True` gives). -/
def OwnB (i : ℕ) : Prop := x.cur ≤ i ∧ i < x.cur + (vsAllocSz x.p).sum

/-- The caller's region. -/
def R : ℕ → Prop := vsRegion x.qt x.qo x.c.freshClaim.cells.length

/-- `verify_sub`'s `Pre`. -/
def Pre : Reader → Prop := vsPreA x.seed x.c x.qt x.qo

/-- The windows' first state. -/
noncomputable def st0 : St := vsSt0 x.σ0 x.cur x.Wo

/-- The `HeapBuf` cursor past the front's buffers. -/
def a1 : ℕ := x.cur + (824 + 256 * x.p) + 14

/-- **The placement's hypotheses** (`VsOrc`'s: `rdP` satisfies `Pre`, the cursor is below `2^60`). -/
structure Ok : Prop where
  child : VsChildOk guestBytecode x.seed x.c
  ht : x.qt + expTabLen ≤ x.fp
  ho : x.qo + x.c.freshClaim.cells.length ≤ x.fp
  hfc : x.fp + B2C.fs "verify_sub" ≤ x.cur
  pre : x.Pre x.rdP
  hcur : x.cur < 2 ^ 60

/-- The windows' first state at the honest allocations: the `HeapBuf`s from `cur`, the callees past them. It is
`x.st0` once `allocs σ0 (vsEs σ0) = vsAllocSz p` (the walk through the body), which the phases give. -/
noncomputable def st0B : St := ⟨x.cur, x.cur + (vsAllocSz x.p).sum, fun rd => HoldsWords rd x.Wo, fun _ => False, []⟩

/-! ### The announced layout and the front's numbers (vsph1's) -/

/-- The announced layout (`default` off an announced one). Irreducible: unfolding it evaluates
`announcedLayoutAndRate` on the guest's bytecode. -/
@[irreducible] noncomputable def lay : Layout := ((announcedLayoutAndRate guestBytecode x.c.proof.stream).map Prod.fst).getD default

/-- The tables' log heights. -/
noncomputable def hg (t : ℕ) : ℕ := x.lay.tableLogHeights.getD t 0

/-- The tables' rows. -/
noncomputable def rows (t : ℕ) : ℕ := x.lay.tableRows.getD t 0

/-- The link's shape's fourth word. -/
noncomputable def f4 : E := (vsLinkShape x.lay).getD 3 0

/-- The packed challenges' permutations, `squeeze_packed`'s `p`. -/
noncomputable def pk : ℕ := (packedChallenges tables (hMax x.lay) (widthOf x.lay) + 7) / 8

/-- **The front's buffers' honest words**: `0` heights, `1` table `t`'s `tsBitsW` at word `26 t`, `2` `cbL N`,
`3` `[g^hMax, g^width, flagOf, f4]`, `18` `padStream`, `19` `rowsW`, `20` `1 :: g^m :: heightsW`. -/
structure Bw1F : Prop where
  b0 : x.bw.getD 0 [] = heightsW x.hg
  b1 : ∀ t < 6, ∀ k < (tsBitsW (x.rows t) (x.hg t)).length,
    (x.bw.getD 1 [])[26 * t + k]? = (tsBitsW (x.rows t) (x.hg t))[k]?
  b2 : x.bw.getD 2 [] = cbL (x.rows 0 + x.rows 1 + x.rows 2 + x.rows 3 + x.rows 4 + x.rows 5)
  b3 : x.bw.getD 3 [] = [gen ^ hMax x.lay, gen ^ widthOf x.lay, flagOf x.lay, x.f4]
  b18 : x.bw.getD 18 [] = padStream x.c.proof.stream
  b19 : x.bw.getD 19 [] = rowsW x.rows
  b20 : x.bw.getD 20 [] = 1 :: gen ^ x.lay.logMemory :: heightsW x.hg

/-- **The front's callees' returns** as `ret`'s constant rules (`FrontRet`). -/
def Ret1F : Prop := FrontRet x.ret (announcedLayoutAndRate guestBytecode x.c.proof.stream |>.map Prod.snd |>.getD 0)
  x.lay.logMemory x.hg x.rows

/-- The callees' cursor after the front: two `assert_small_g_power` leaves with the flag set, one without. -/
noncomputable def frontEnd (fs : String → ℕ) (al : String → Bool) : ℕ :=
  if flagOf x.lay = 1 then
    leafEnd fs al "assert_small_g_power" (leafEnd fs al "assert_small_g_power"
      (frontKc fs al x.p x.hg (x.cur + (vsAllocSz x.p).sum)))
  else leafEnd fs al "assert_small_g_power" (frontKc fs al x.p x.hg (x.cur + (vsAllocSz x.p).sum))

/-- **What the front leaves**: the callees' cursor at the front's end, its posts' count (eleven when
`.n 471 = 0`, the flag set, else ten). -/
def CarryFA (fs : String → ℕ) (al : String → Bool) (st : St) : Prop :=
  st.kc = x.frontEnd fs al ∧ st.Qs.length = if x.σ0 (.n 471) = 0 then 11 else 10

/-- `certify_stack`'s frame: past `chunk_d`'s leaf at the front's end. -/
noncomputable def fpc : ℕ :=
  allocBase (x.al "certify_stack") (leafEnd B2C.fs x.al (cdNames.getD (widthOf x.lay - 19) "") (x.frontEnd B2C.fs x.al))

/-- The out-of-domain point's sponge after its squeezes (`squeeze_point_from__L{stackLog}`). -/
noncomputable def spf : List E × Fs :=
  (⟨[x.σ0 (.n 507), x.σ0 (.n 508), x.σ0 (.n 509), x.σ0 (.n 510), x.σ0 (.n 511)], []⟩ : Fs).squeezeN (x.lay.stackLog - 1)

/-- `squeeze_packed`'s frame: past `Ph5`'s two leaves at `certify_stack`'s pinned end `x.ec 4`. -/
noncomputable def fpsp : ℕ :=
  allocBase (x.al "squeeze_packed")
    (leafEnd B2C.fs x.al (omName (1, 1)) (leafEnd B2C.fs x.al (spfName x.lay.stackLog) (x.ec 4)))

/-! ### The helpers' own conditions (each owned by one helper; `True` until it states them) -/

/-- **vsph1's conditions on the buffers' words**: the front's, `.n 10`'s first word `opening_message`'s first
return, its next `8 pk` the packed challenges `squeeze_packed` draws. -/
structure Bw1 : Prop where
  front : x.Bw1F
  b4 : (x.bw.getD 4 [])[0]? = some (x.w 573)
  b4s : ∀ k < (pkSqueeze x.pk [x.w 575, x.w 576, x.w 577, x.w 578, x.w 579]).1.length,
    (x.bw.getD 4 [])[k + 1]? = (pkSqueeze x.pk [x.w 575, x.w 576, x.w 577, x.w 578, x.w 579]).1[k]?
/-! ### vsph2's conditions (`Ph7` to `Ph11`)

The front's numbers at the announced layout: `nS` the tallest table's log height (the row side's rounds),
`wdS` the pointer width (the index side's rounds), `mS` the memory's log size, `h0S` table `0`'s log height.
Buffer `j` (`vsAllocIdx` order) holds `x.bw.getD j []`: `.n (j + 6)` for `j < 18`. -/

/-- The tallest table's log height. -/
noncomputable def nS : ℕ := hMax x.lay
/-- The pointer width. -/
noncomputable def wdS : ℕ := widthOf x.lay
/-- The memory's log size. -/
noncomputable def mS : ℕ := x.lay.logMemory
/-- Table `0`'s log height. -/
noncomputable def h0S : ℕ := x.lay.tableLogHeights.getD 0 0

/-- The index side's `z` words: `.n 10`'s from `89 + nS`. -/
noncomputable def zsS : List E := (((x.bw.getD 4 []).drop (89 + x.nS)).take x.wdS)
/-- The index side's challenges: `.n 12`'s first `wdS` words. -/
noncomputable def rsS : List E := (x.bw.getD 6 []).take x.wdS
/-- The row side's challenges: `.n 15`'s first `nS` words. -/
noncomputable def as15S : List E := (x.bw.getD 9 []).take x.nS

/-- **The link's honest data** (the native link verifier's values on the accepted child): the index side's
rounds `l` from the stream at `s` (`nw` words), the row side's `l1` and the columns' `l2` from `b772 + 1`
(`nw1` and `nw2` words), the packed message at `bm`. -/
structure Lk2 where
  l : List (E × Link.RSt)
  s : ℕ
  nw : ℕ
  b772 : ℕ
  l1 : List (E × Link.RSt)
  l2 : List (E × Link.RSt)
  nw1 : ℕ
  nw2 : ℕ
  bm : ℕ

/-- **The link's data, honest** (vsnat's): the chains on every memory holding the node's words, their
cursors inside the stream's buffer (`.n 55`, buffer `18`), their challenges the buffers' words, the returns
`ret` gives the callees (`link_rounds`' `767 ..< 774`, `link_row_side`'s `1071 ..< 1078`, `packed_message`'s
`1287 ..< 1293`). -/
structure Lk2.Ok (L : Lk2) (x : VsCtx) : Prop where
  hl : L.l.length = x.wdS
  hw580 : x.w 580 = ptrAt L.s
  hsIn : x.base 18 ≤ L.s ∧ L.s + L.nw ≤ x.base 18 + 256 * x.p
  hcur : (Link.chainLast (ph7St0 x.w (x.bw.getD 4 [])) L.l).cur = x.w 580 * gen ^ L.nw
  hcells : (Link.chainLast ⟨[], 0, 0⟩ L.l).cells.length = 7
  hch : L.l.map Prod.fst = x.rsS
  hc : ∀ rd, HoldsWords rd x.Wo → x.Pre rd → Link.RoundChain rd 1 0 (ph7St0 x.w (x.bw.getD 4 [])) L.l
  r767 : ∀ j < 7, ∀ σ, x.ret (767 + j) σ = (Link.chainLast ⟨[], 0, 0⟩ L.l).cells.getD j 0
  h772 : (Link.chainLast ⟨[], 0, 0⟩ L.l).cells.getD 5 0 = ptrAt L.b772
  hbIn : x.base 18 ≤ L.b772 ∧ L.b772 + 1 + L.nw1 + L.nw2 ≤ x.base 18 + 256 * x.p
  hl1 : L.l1.length = x.nS
  hl2 : L.l2.length = 6
  hcur1 : (Link.chainLast (ph9St0 x.σ0 x.w L.b772) L.l1).cur = ptrAt (L.b772 + 1) * gen ^ L.nw1
  hcur2 : (Link.chainLast (Link.chainLast (ph9St0 x.σ0 x.w L.b772) L.l1) L.l2).cur =
    (Link.chainLast (ph9St0 x.σ0 x.w L.b772) L.l1).cur * gen ^ L.nw2
  hcells2 : (Link.chainLast ⟨[], 0, 0⟩ L.l2).cells.length = 7
  hch1 : L.l1.map Prod.fst = x.as15S
  hch2 : L.l2.map Prod.fst = x.bw.getD 10 []
  hc12 : ∀ rd, HoldsWords rd x.Wo → x.Pre rd →
    Link.RoundChain rd (chunkCount x.wdS + 1) (lrsGrind (chunkCount x.wdS)).1 (ph9St0 x.σ0 x.w L.b772) L.l1 ∧
    Link.RoundChain rd (chunkCount x.wdS) (lrsGrind (chunkCount x.wdS)).2
      (Link.chainLast (ph9St0 x.σ0 x.w L.b772) L.l1) L.l2
  r1071 : ∀ j < 7, ∀ σ, x.ret (1071 + j) σ = (Link.chainLast ⟨[], 0, 0⟩ L.l2).cells.getD j 0
  hbm : (Link.chainLast ⟨[], 0, 0⟩ L.l2).cells.getD 5 0 = ptrAt L.bm
  hbmIn : x.base 18 ≤ L.bm ∧ L.bm + 144 ≤ x.base 18 + 256 * x.p
  hpm6 : (pmRets (((x.bw.getD 18 []).drop (L.bm - x.base 18)).take 144)
    ((Link.chainLast ⟨[], 0, 0⟩ L.l2).cells.take 5)).length = 6
  rpm : ∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (pmRets (((x.bw.getD 18 []).drop (L.bm - x.base 18)).take 144)
    ((Link.chainLast ⟨[], 0, 0⟩ L.l2).cells.take 5)).getD j 0
  /-- `link_rounds__L1_L0`'s call on the index side's chain, at its frame past `x.ec 6`, pinned to end at
  `x.ec 7`. -/
  crd : LrCall B2C.fs x.al B2C.cert 17 (x.w 680) (x.w 681) (x.w 682) (x.w 683) (x.w 684) (x.w 580)
    (lrClaim (x.w 752) (x.w 753) ((x.bw.getD 4 []).getD 6 0) ((x.bw.getD 4 []).getD 7 0)) (ptrAt (x.base 6))
    (ptrAt x.qt * word 365917469723852800 0) L.l L.nw (ph7Fp B2C.fs x.al x.wdS (x.ec 6)) (x.ec 7)
  /-- `link_row_side__L{cc}`'s call on the row side's chains, at its frame past `Ph8`'s leaves from `x.ec 7`,
  pinned to end at `x.ec 9`. -/
  crs : LrsCall B2C.fs x.al B2C.cert 17 (chunkCount x.wdS) (x.σ0 (.n 790)) (x.σ0 (.n 791)) (x.σ0 (.n 792))
    (x.σ0 (.n 793)) (x.σ0 (.n 794)) (ptrAt (L.b772 + 1)) (x.w 773) (ptrAt (x.base 9)) (ptrAt (x.base 10))
    (ptrAt x.qt * word 365917469723852800 0) L.l1 L.l2 L.nw1 L.nw2
    (allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec 7))) (x.ec 9)

/-- **vsph2's conditions on the buffers' words**: the eq tensors `.n 11` (of the packed point) and `.n 17` (of
the rows' point `.n 16`), `index_side`'s outputs `.n 13` and `one_plus_suffixes`' `.n 18`, the link's
honest data (with its two non-leaf calls at `x.ec 7`, `x.ec 9`), and `Ph12`'s cursor `x.ec 12`. -/
structure Bw2 (x : VsCtx) : Prop where
  b11 : x.bw.getD 5 [] = eqLevels (ph7Rs (x.bw.getD 4 [])) 4
  b17 : x.bw.getD 11 [] = eqLevels ((x.bw.getD 10 []).take 6) 6
  b13 : (x.bw.getD 7 []).take (x.wdS + 1) = (List.range (x.wdS + 1)).map (Link.belowE x.rsS)
  b18 : (x.bw.getD 12 []).take (x.nS + 1) = (List.range (x.nS + 1)).map (Link.belowE x.as15S)
  lk : ∃ L : Lk2, L.Ok x
  /-- `Ph12`'s cursor `x.ec 12`: past `Ph10`'s and `Ph11`'s leaves from the row side's end `x.ec 9`. -/
  e12 : x.ec 12 = ph11End B2C.fs x.al x.nS x.h0S (x.ec 9)
/-- Table `t`'s log height at the announced layout. -/
noncomputable def hgS (t : ℕ) : ℕ := x.lay.tableLogHeights.getD t 0

/-- The stream's `n` words from the index `bm + o` (`.n 55`'s buffer, `18`). -/
noncomputable def sw (bm o n : ℕ) : List E := ((x.bw.getD 18 []).drop (bm - x.base 18 + o)).take n

/-- The cells of `certify_stack`'s `offs` and `kaps` buffers (`.n 486`, `.n 487`): its data at the pinned frame
`x.fpc`, `52` words each from `csOffsAt (x.fpc + fs certify_stack)`. -/
def StkCells (i : ℕ) : Prop :=
  csOffsAt (x.fpc + B2C.fs "certify_stack") ≤ i ∧ i < csOffsAt (x.fpc + B2C.fs "certify_stack") + 104

/-- **What `Ph4`'s `certify_stack` leaves at a state** (its producer's, carried to `Ph12`): its buffers claimed,
the stack placed on every memory with `Pre` and the state's `O`. -/
def StkAt (st : St) : Prop :=
  (∀ i, x.StkCells i → st.D i) ∧
    ∀ rd, x.Pre rd → st.O rd → Stack.StackPlaced rd x.lay (x.σ0 (.n 485)) (x.σ0 (.n 486)) (x.σ0 (.n 487))

/-- `StkAt` survives a phase that only adds memory conditions and claimed data. -/
theorem StkAt.mono {x : VsCtx} {st s : St} (h : x.StkAt st) (hO : ∀ rd, s.O rd → st.O rd)
    (hD : ∀ i, st.D i → s.D i) : x.StkAt s :=
  ⟨fun i hi => hD i (h.1 i hi), fun rd hp ho => h.2 rd hp (hO rd ho)⟩

/-- **`Ph12` to the end's native data** (vsnat's and `VsHonEx`'s): the packed message's cursor `bm` in the stream,
the Keccak reduction's stream words `nx` past it (from `bm + 144`), its claim (`op`, `kw`), point, sponge `s'`; the
link terminal's chunks `ch`; `open_stacked`'s log size `sl`, stream words `nxo` (from `bm + 144 + nx + 1`), WHIR end
`wE`, point buffers `bp`, `bp1`, its call's region, data, outputs, inputs and post; the stack terminal's objects. -/
structure D3 where
  bm : ℕ
  nx : ℕ
  nxo : ℕ
  ch : Chunks
  op : List E
  point : List E
  kw : E
  s' : Fs
  sl : ℕ
  wE : Whir.WhirEnd
  bp : ℕ
  bp1 : ℕ
  Ro : ℕ → Prop
  Do : ℕ → Prop
  Oo : Reader → Prop
  Po : Reader → Prop
  Qo : Reader → Tree → Prop
  layout : Layout
  link : LinkEnd
  chi : List E
  r : List E
  qPoint : List E
  kOut : List E
  kIn : List E
  f : List E
  g : List E
  xq : List E
  z : List E
  rho : E
  lam : E
  rm : E
  outputs : List ColumnClaim
  keccakSlices : List E
  oodValue : E
  v0 : E
  v1 : E
  claims : List StackClaim
  carr : List (ℕ × ℕ)

open Whir Stack VerifySub Compile in
/-- **`Ph12` to the end's data, honest**: (a) the link terminal's identity; (b) the Keccak reduction's run; the ring
switch's target and `.n 3553`'s words; (d) `open_stacked`'s call at its native returns; (e) the stack terminal's
check; the returns `ret` gives the callees; the three calls before `open_stacked` pinned at `x.ec 13`, `x.ec 14`,
`x.ec 15`, `open_stacked`'s at `x.ec 16`. -/
structure D3.Ok (D : D3) (x : VsCtx) : Prop where
  hbm : x.w 1076 = ptrAt D.bm
  hbmIn : x.base 18 ≤ D.bm ∧ D.bm + 144 + D.nx + 1 + D.nxo ≤ x.base 18 + 256 * x.p
  hch : Chunks.new x.wdS = some D.ch
  hchw : D.ch.width ≤ 24
  hchd : 89 + x.nS + x.wdS + D.ch.d ≤ 153
  hid : LtIdentity D.ch x.σ0 (x.w 1077) ((x.bw.getD 6 []).take D.ch.width) (x.sw D.bm 80 64)
    (x.cells19.map Prod.snd) (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take D.ch.d)
  hτ0 : keccakTauMin ≤ x.hgS 5
  hτ1 : x.hgS 5 ≤ keccakTauMax
  hcar : ∃ sp, (⟨[x.w 1288, x.w 1289, x.w 1290, x.w 1291, x.w 1292], []⟩ : Fs).Carries sp
  hrun : RunsTo (verifyKeccak (x.hgS 5) ((x.bw.getD 9 []).take (x.hgS 5)) (x.sw D.bm 55 25))
    ⟨[x.w 1288, x.w 1289, x.w 1290, x.w 1291, x.w 1292], []⟩ (x.sw D.bm 144 D.nx)
    ([⟨qkeccak, D.op, D.kw⟩], D.point, (x.bw.getD 15 []).take 64) D.s'
  hpend : D.s'.pend.length = rateScalars
  hop : D.op = (x.bw.getD 14 []).take D.op.length
  hopl : D.op.length ≤ qkeccakVarsCap
  hpt : D.point = ((x.bw.getD 14 []).drop qkeccakVarsCap).take D.point.length
  hptl : qkeccakVarsCap + D.point.length ≤ (vsAllocSz x.p).getD 14 0
  rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets D.s' (ptrAt (D.bm + 144)) D.nx D.kw).getD j 0
  r3810 : ∀ σ, x.ret 3810 σ = ringTarget (rsW (x.bw.getD 15 []) (x.sw D.bm 0 144) (x.σ0 (.n 3026)))
    ((mcW x.σ0).take 8) ((mcW x.σ0).drop 8)
  b23 : x.bw.getD 23 [] = rsW (x.bw.getD 15 []) (x.sw D.bm 0 144) (x.σ0 (.n 3026))
  h16 : 16 ≤ D.sl
  h30 : D.sl ≤ 30
  h489 : x.σ0 (.n 489) = gen ^ (D.sl - 16)
  hos : CallAtA B2C.fs x.al B2C.cert 17 (openName D.sl)
    (x.σ0 (.n 96) :: [x.σ0 (.n 3033), x.σ0 (.n 3034), x.σ0 (.n 3035), x.σ0 (.n 3036), x.σ0 (.n 3037)] ++
      [vsOpenTarget (x.σ0 (.n 3810)) (x.σ0 (.n 3027)) (x.σ0 (.n 779)) (x.σ0 (.n 2905)) (x.σ0 (.n 2908))
        (x.σ0 (.n 2921)) ((x.bw.getD 17 []).getD 0 0) (x.sw D.bm 0 144), x.σ0 (.n 134), x.σ0 (.n 137),
        ptrAt (D.bm + 144 + D.nx + 1), ptrAt (x.qt + 178)])
    (osRets D.wE D.bp D.bp1 (D.bm + 144 + D.nx + 1 + D.nxo)) D.Ro D.Do D.Oo D.Po D.Qo (B2C.fs (openName D.sl))
    (allocBase (x.al (openName D.sl)) (x.ec 15)) (allocBase (x.al (openName D.sl)) (x.ec 15) + B2C.fs (openName D.sl))
    (x.ec 16)
  ro : ∀ j < 6, ∀ σ, x.ret (3991 + j) σ = (osRets D.wE D.bp D.bp1 (D.bm + 144 + D.nx + 1 + D.nxo)).getD j 0
  hRo : ∀ i, D.Ro i → x.R i ∨ x.OwnB i
  hPo : ∀ rd, x.Pre rd → HoldsWords rd x.Wo → D.Po rd
  hQo : ∀ rd, LowDef 17 rd → x.Pre rd → D.Oo rd → ∀ t, D.Qo rd t →
    PopsPost (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings) rd t
  hbp : D.bp + pointCap ≤ x.ec 16
  hbp1 : D.bp1 + pointCap ≤ x.ec 16
  hlay : D.layout = x.lay
  hcl : stackedClaims D.layout D.link (publicClaimsPure D.layout D.rm D.v0 D.v1) D.outputs D.kIn D.keccakSlices D.f D.g
    D.rho (fun y ↦ eqEval D.z y, D.oodValue) = some D.claims
  hsl : D.layout.stackLog ≤ 30
  hsid : ((cstArgsOf x.σ0 x.w).getD 19 0 + stackedBasis D.claims D.lam D.xq) * (cstArgsOf x.σ0 x.w).getD 20 0 =
    (cstArgsOf x.σ0 x.w).getD 21 0
  hcarr : cstArrays (cstArgsOf x.σ0 x.w) D.chi D.r D.kOut D.kIn D.f D.g D.z = D.carr.map fun q => (ptrAt q.1, q.2)
  hfc : ∀ q ∈ D.carr, q.1 + q.2 ≤ x.ec 16
  hcc : ∀ q ∈ D.carr, ∀ t < q.2, (x.R (q.1 + t) ∨ x.OwnB (q.1 + t)) ∨ (x.StkCells (q.1 + t) ∨ D.Do (q.1 + t))
  hPc : ∀ rd, x.Pre rd → HoldsWords rd x.Wo →
    StackPlaced rd D.layout (x.σ0 (.n 485)) (x.σ0 (.n 486)) (x.σ0 (.n 487)) → D.Oo rd →
    StackCtxAt rd (cstArgsOf x.σ0 x.w) D.layout D.link D.chi D.r D.qPoint D.kOut D.kIn D.f D.g D.xq D.z D.rho
      D.lam D.rm D.outputs
  hlt : LtCall B2C.fs x.al B2C.cert 17 x.wdS x.σ0 (x.w 1077) (x.base 6) D.bm (x.base 13)
    (x.base 4 + 89 + x.nS + x.wdS) ((x.bw.getD 6 []).take D.ch.width) (x.sw D.bm 80 64) (x.cells19.map Prod.snd)
    (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take D.ch.d)
    (allocBase (x.al (Link.ltNames.getD (x.wdS - 19) "")) (tpKc B2C.fs x.al x.hgS 5 (x.ec 12))) (x.ec 13)
  hvk : VkCall B2C.fs x.al B2C.cert 17 x.w (x.base 9) (x.base 14) (x.base 15) x.qt (x.hgS 5) (x.bw.getD 9 [])
    (x.sw D.bm 55 25) (x.sw D.bm 144 D.nx) D.op D.point ((x.bw.getD 15 []).take 64) D.kw D.s'
    (allocBase (x.al "verify_keccak") (x.ec 13)) (x.ec 14)
  hrt : RtCall B2C.fs x.al B2C.cert 17 x.a1 (rsW (x.bw.getD 15 []) (x.sw D.bm 0 144) (x.σ0 (.n 3026))) (mcW x.σ0)
    (allocBase (x.al "ring_switch_target") (x.ec 14)) (x.ec 15)

/-- **vsph3's conditions on the buffers' words and the child** (vsnat's, data-free): the overlay's fresh loads, the
export's converse (the fresh claim's point and values in `r_pt`'s and `splitv`'s buffers), the end's own entries
(`.n 6`, `.n 9`, `.n 14`, `.n 8`), the ring switch's map challenges and coefficients (`.n 3039`, `.n 3040`), the
ring grind's low bits. -/
structure Bw3 (x : VsCtx) : Prop where
  fresh : VsFresh x.rd1 x.rd0 x.w x.args
  hpt : x.c.freshClaim.point = (x.bw.getD 6 []).take 19
  b8 : x.bw.getD 8 [] = x.c.freshClaim.values
  b0 : x.bw.getD 0 [] = x.lay.tableLogHeights.map Prover.count
  b3 : x.bw.getD 3 [] = vsLinkShape x.lay
  b2 : ∃ n, n < 2 ^ 24 ∧ x.σ0 (.n 240) = ofK (g ^ n) ∧
    x.bw.getD 2 [] = (List.range 24).map fun j => LeanVM.Prover.Exec.bitWord (n.testBit j)
  b21 : x.bw.getD 21 [] = mcW x.σ0
  b22 : x.bw.getD 22 [] = mcRc x.σ0
  hlow : ((x.σ0 (.n 2931)).limb 0).lane.toNat % 2 ^ 13 = 0
  /-- `Ph12` to the end's native data and the pinned calls. -/
  d3 : ∃ D : D3, D.Ok x
/-- **vsph1's conditions on the return rule**: the front's callees', `chunk_d`'s chunk count, `certify_stack`'s
three (the stack's size, its offsets and kappas at its frame), `squeeze_packed`'s five; the two non-leaf
callees' calls at their pinned ends (`certify_stack` at `x.ec 4`, `squeeze_packed` at `x.ec 6`). -/
structure Ret1 : Prop where
  front : x.Ret1F
  r484 : ∀ σ, x.ret 484 σ = gen ^ chunkCount (widthOf x.lay)
  r485 : ∀ σ, x.ret 485 σ = gen ^ x.lay.stackLog
  r486 : ∀ σ, x.ret 486 σ = ptrAt (csOffsAt (x.fpc + B2C.fs "certify_stack"))
  r487 : ∀ σ, x.ret 487 σ = ptrAt (csOffsAt (x.fpc + B2C.fs "certify_stack") + 52)
  r680 : [x.w 680, x.w 681, x.w 682, x.w 683, x.w 684] =
    (pkSqueeze x.pk [x.w 575, x.w 576, x.w 577, x.w 578, x.w 579]).2
  /-- `certify_stack`'s call at its frame `x.fpc`, pinned to end at `x.ec 4`. -/
  cs : CsCall B2C.fs x.al B2C.cert 17 x.lay x.qt (x.base 20) x.fpc (x.ec 4)
  /-- `squeeze_packed`'s call at its frame `x.fpsp`, pinned to end at `x.ec 6`. -/
  sp : SpCall B2C.fs x.al B2C.cert 17 (x.w 575) (x.w 576) (x.w 577) (x.w 578) (x.w 579) (ptrAt (x.base 4 + 1)) x.pk
    x.fpsp (x.ec 6)
/-- **vsph2's conditions on the return rule** off the link's chains: `state_ends`' (`752`, `753`),
`index_side`'s (`797 ..= 799`), the zero hint `1286`, the first `table_point`'s (`1296 ..= 1298`, table `0`
of height `h0S`: its `z` words `.n 10`'s from `89`, its challenges `.n 15`'s, its bits `.n 7`'s). -/
structure Ret2 (x : VsCtx) : Prop where
  r752 : ∀ σ, x.ret 752 σ = prodE (x.zsS.map (1 + ·))
  r753 : ∀ σ, x.ret 753 σ = Link.endsProd ((x.bw.getD 2 []).take x.wdS) x.zsS
  r797 : ∀ σ, x.ret 797 σ = indexMle x.rsS
  r798 : ∀ σ, x.ret 798 σ = (Link.sideFold x.zsS x.rsS).1
  r799 : ∀ σ, x.ret 799 σ = (Link.sideFold x.zsS x.rsS).2.1
  r1286 : ∀ σ, x.ret 1286 σ = 0
  r1296 : ∀ σ, x.ret 1296 σ = (x.bw.getD 4 []).getD 0 0 * Link.tpTotalG (((x.bw.getD 4 []).drop 89).take x.h0S)
    ((x.bw.getD 9 []).take x.h0S) ((x.bw.getD 1 []).take x.h0S) ((x.bw.getD 1 []).getD x.h0S 0) x.h0S
  r1297 : ∀ σ, x.ret 1297 σ = 1 + (1 + (x.bw.getD 1 []).getD x.h0S 0) *
    Link.tpPad ((x.bw.getD 1 []).take x.h0S) ((x.bw.getD 9 []).take x.h0S)
  r1298 : ∀ σ, x.ret 1298 σ = Link.tpFullAt (((x.bw.getD 4 []).drop 89).take x.h0S)
    ((x.bw.getD 9 []).take x.h0S) x.h0S
/-- **vsph3's conditions on the return rule** that name no native run: the five `table_point`s' (table `t` of
height `hgS t`: its `z` words `.n 10`'s from `89`, its challenges `.n 15`'s, its bits `.n 7`'s from `26 t`), and
`link_terminal`'s `2894`. -/
structure Ret3 (x : VsCtx) : Prop where
  rtp : ∀ t, 1 ≤ t → t ≤ 5 → ∀ σ,
    x.ret (tpD t + 5) σ = (x.bw.getD 4 []).getD t 0 * Link.tpTotalG (((x.bw.getD 4 []).drop 89).take (x.hgS t))
      ((x.bw.getD 9 []).take (x.hgS t)) (((x.bw.getD 1 []).drop (26 * t)).take (x.hgS t))
      ((x.bw.getD 1 []).getD (26 * t + x.hgS t) 0) (x.hgS t) ∧
    x.ret (tpD t + 6) σ = 1 + (1 + (x.bw.getD 1 []).getD (26 * t + x.hgS t) 0) *
      Link.tpPad (((x.bw.getD 1 []).drop (26 * t)).take (x.hgS t)) ((x.bw.getD 9 []).take (x.hgS t)) ∧
    x.ret (tpD t + 7) σ = Link.tpFullAt (((x.bw.getD 4 []).drop 89).take (x.hgS t))
      ((x.bw.getD 9 []).take (x.hgS t)) (x.hgS t)
  r2894 : ∀ σ, x.ret 2894 σ = 0

end VsCtx

/-- **The Fiat-Shamir facts `Ph5` and `Ph6` take** (vsnat's target): on the honest context, the guest's
transcript is the native verifier's, so the out-of-domain grind's word `.n 500` has its low `15` bits zero, the
link grind's `w 574` its low `2`; the out-of-domain point is the sponge's squeezes (`squeeze_point_from`'s
returns, the words it leaves in `.n 22`), the opening message `opening_message`'s returns on the stream's words
`11`, `12` (word `11` in `.n 23`). -/
structure VsFsChecks1 (x : VsCtx) : Prop where
  hlow5 : ((x.σ0 (.n 500)).limb 0).lane.toNat % 2 ^ 15 = 0
  hlow6 : ((x.w 574).limb 0).lane.toNat % 2 ^ 2 = 0
  hspf : [x.w 566, x.w 567, x.w 568, x.w 569, x.w 570] = x.spf.2.cap
  hP22 : ∀ k < (x.σ0 (.n 499) :: x.spf.1).length, (x.bw.getD 16 [])[k]? = (x.σ0 (.n 499) :: x.spf.1)[k]?
  hom : [x.w 573, x.w 574, x.w 575, x.w 576, x.w 577, x.w 578, x.w 579, x.w 580] =
    omRets (x.w 566) (x.w 567) (x.w 568) (x.w 569) (x.w 570) (ptrAt (x.base 18 + 11))
      [(padStream x.c.proof.stream).getD 11 0] ((padStream x.c.proof.stream).getD 12 0)
  hP23 : x.bw.getD 17 [] = [(padStream x.c.proof.stream).getD 11 0]

namespace VsCtx

variable (x : VsCtx)

/-- **The honest context**: the placement's hypotheses, the buffers' sizes, the extra cells past the buffers,
a causal return rule, the overlay's fresh loads (`rd0` reads as `rd1` at every fresh load), the Fiat-Shamir
facts, and the helpers' conditions. -/
structure Hon : Prop where
  ok : x.Ok
  hbw : x.bw.map List.length = vsAllocSz x.p
  hex : ∀ q ∈ x.ex, x.cur + (vsAllocSz x.p).sum ≤ q.1 ∧ q.1 < 2 ^ 63
  hret : CausalRule x.ret
  fresh : VsFresh x.rd1 x.rd0 x.w x.args
  fs1 : VsFsChecks1 x
  bw1 : x.Bw1
  bw2 : x.Bw2
  bw3 : x.Bw3
  ret1 : x.Ret1
  ret2 : x.Ret2
  ret3 : x.Ret3
  /-- `open_stacked`'s pinned end within `3·2^38` of the cursor (the honest callees' ends bounded), so
  `verify_sub`'s end is within `2^40`. -/
  hend : x.ec 16 ≤ x.cur + 3 * 2 ^ 38

/-! ### The boundaries -/

/-- **The facts every phase boundary keeps**: the `HeapBuf` cursor past the front's buffers, the callees'
cursor past all buffers, `Wo` held, the posts so far implying a prefix of the honest pops. -/
structure Bnd (st : St) : Prop where
  ha : st.a = x.a1
  hkc : x.cur + (vsAllocSz x.p).sum ≤ st.kc
  hO : ∀ rd, st.O rd → HoldsWords rd x.Wo
  hQ : ∀ rd, LowDef 17 rd → x.Pre rd → st.O rd →
    List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) st.Qs
      ((vsPsH x.seed x.c (rdOver x.σ0 rd)).take st.Qs.length)

/-- What the front leaves for `wC` beyond `Bnd` (vsph1's): the callees' cursor, the posts' count. -/
def CarryF (x : VsCtx) (st : St) : Prop := x.CarryFA B2C.fs x.al st
/-- **The front's numbers `Ph7 … Ph11` read** (vsph1's, carried in `Carry6`): `.n 408 = g^nS`,
`.n 409 = g^wdS`, `w 484 = g^chunkCount wdS`, `.n 694` the pointer to `.n 10`'s word `89 + nS`,
`.n 101 = g^mS`, `.n 115 = g^h0S`. -/
structure Num6 (x : VsCtx) : Prop where
  n408 : x.σ0 (.n 408) = gen ^ x.nS
  n409 : x.σ0 (.n 409) = gen ^ x.wdS
  w484 : x.w 484 = gen ^ chunkCount x.wdS
  n694 : x.σ0 (.n 694) = ptrAt (x.base 4 + 89 + x.nS)
  n101 : x.σ0 (.n 101) = gen ^ x.mS
  n115 : x.σ0 (.n 115) = gen ^ x.h0S
  /-- The table points' selectors, tables `1 ..= 5` (`Ph12`'s). -/
  sel : ∀ t, 1 ≤ t → t ≤ 5 → x.σ0 (.n (115 + t)) = gen ^ x.hgS t
  /-- The table points' bits pointers, tables `1 ..= 5`: table `t`'s bits at `.n 7`'s word `26 t` (`Ph12`'s). -/
  bv : ∀ t, 1 ≤ t → t ≤ 5 → x.σ0 (.n (tpBv t)) = ptrAt (x.base 1 + 26 * (t - 1))
/-- The posts' count after `Ph6`: the front's eleven (ten on the clear flag's branch), then five. -/
noncomputable def qs6 : ℕ := if x.σ0 (.n 471) = 0 then 16 else 15
/-- What `Ph4 … Ph6` leave beyond `Bnd` (vsph1's): the posts' count, so `Ph7 … Ph11` place theirs in the
honest pops' empty stretch, the front's numbers, the callees' cursor at `squeeze_packed`'s pinned end, and
`certify_stack`'s stack (`StkAt`). -/
def Carry6 (x : VsCtx) (st : St) : Prop := st.Qs.length = x.qs6 ∧ x.Num6 ∧ st.kc = x.ec 6 ∧ x.StkAt st
/-- What `Ph7 … Ph11` leave beyond `Bnd` (vsph2's): the posts' count, seven more, the front's numbers, the
callees' cursor at `Ph12`'s pinned start `x.ec 12`, and `certify_stack`'s stack. -/
def Carry11 (x : VsCtx) (st : St) : Prop := st.Qs.length = x.qs6 + 7 ∧ x.Num6 ∧ st.kc = x.ec 12 ∧ x.StkAt st

end VsCtx

/-- **`verify_sub`'s final condition with its end bounded**: within `2^40` of a cursor below `2^60`, and
`vsKEndW`. -/
noncomputable def VsCtx.kEndB (x : VsCtx) : St → Prop := fun s =>
  (x.cur < 2 ^ 60 → s.kc ≤ x.cur + 2 ^ 40) ∧ vsKEndW 17 guestBytecode x.seed x.c x.qt x.qo x.σ0 s

/-! ## The phases' statements -/

/-- **The front** (vsph1): `FrontHyp`'s fields at the honest values from `x.st0B`, its continuation at every
state with `Bnd` and `CarryF`. -/
def FrontS (al : String → Bool) : Prop :=
  ∀ x : VsCtx, x.al = al → x.Hon → VsCalleesCompleteA B2C.fs al B2C.cert 17 →
    ∀ Own : ℕ → Prop, (∀ i, x.OwnB i → Own i) → ∀ K : St → Prop,
    (∀ s, x.Bnd s → x.CarryF s → K s) →
    FrontOk B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre x.st0B K

/-- **`wC`'s phases 4 to 6** (vsph1). -/
def Ph4to6S (al : String → Bool) : Prop :=
  ∀ x : VsCtx, x.al = al → x.Hon → VsCalleesCompleteA B2C.fs al B2C.cert 17 →
    ∀ Own : ℕ → Prop, (∀ i, x.OwnB i → Own i) → ∀ (st : St) (K : St → Prop),
    x.Bnd st → x.CarryF st → (∀ s, x.Bnd s → x.Carry6 s → K s) →
    Ph4Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st fun s =>
    Ph5Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre s fun s =>
    Ph6Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre s K

/-- **`wC`'s phases 7 to 11** (vsph2). -/
def Ph7to11S (al : String → Bool) : Prop :=
  ∀ x : VsCtx, x.al = al → x.Hon → VsCalleesCompleteA B2C.fs al B2C.cert 17 →
    ∀ Own : ℕ → Prop, (∀ i, x.OwnB i → Own i) → ∀ (st : St) (K : St → Prop),
    x.Bnd st → x.Carry6 st → (∀ s, x.Bnd s → x.Carry11 s → K s) →
    Ph7Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st fun s =>
    Ph8Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre s fun s =>
    Ph9Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre s fun s =>
    Ph10Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre s fun s =>
    Ph11Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre s K

/-- **`wC`'s phases 12 to the end and `vsPostA`** (vsph3), ending in `x.kEndB`. -/
def Ph12toEndS (al : String → Bool) : Prop :=
  ∀ x : VsCtx, x.al = al → x.Hon → VsCalleesCompleteA B2C.fs al B2C.cert 17 →
    ∀ Own : ℕ → Prop, (∀ i, x.OwnB i → Own i) → ∀ st : St,
    x.Bnd st → x.Carry11 st →
    Ph1213Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st fun s =>
    TailOk B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre s x.kEndB

/-! ## Their composition -/

/-- **The phases compose**: the front's continuation is `wC`'s windows to `x.kEndB`. -/
theorem vsPhases_of_specs {al : String → Bool} (hF : FrontS al) (h1 : Ph4to6S al) (h2 : Ph7to11S al)
    (h3 : Ph12toEndS al) {x : VsCtx} (hal : x.al = al) (hx : x.Hon) (hc : VsCalleesCompleteA B2C.fs al B2C.cert 17)
    {Own : ℕ → Prop} (hO : ∀ i, x.OwnB i → Own i) :
    FrontOk B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre x.st0B fun s =>
      WCOk B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre s x.kEndB :=
  hF x hal hx hc Own hO _ fun _ hb hf => WCOkT.wcOk (by norm_num) rfl
    (h1 x hal hx hc Own hO _ _ hb hf fun _ hb hf => h2 x hal hx hc Own hO _ _ hb hf fun _ hb hf =>
      h3 x hal hx hc Own hO _ hb hf)

end
end LeanVM.Guest.B1.VsC
