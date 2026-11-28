/-
  LeanVM.Guest.B1.Stack.Interface

  The stack and its terminal in the circuit: what `certify_stack`, `stack_selectors` and
  `check_stack_terminal` establish, against the layout's `stack` and `verifyStackedOpening`'s basis.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.ExpTables
public import LeanVM.Guest.CoreData
import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's data.
import LeanVM.Guest.Data.Consts

/-!
# The stack and its terminal: the section's statement

`verify_sub` certifies the stack's layout (`certify_stack`), opens the stack (`open_stacked`,
`Whir/Verify.lean`) and checks the opening's terminal (`check_stack_terminal`): the weight of every
stacked claim at the opening point, batched by the powers of `λ` in the verifier's order, is the
basis `verifyStackedOpening` hands `verifyWhir` (`Statement/Verifier/Lib.lean`).

* `stackedClaims`: the claims `verifyExecution` stacks, without its program: the merged ring claim
  (`ringMerge` of the Keccak reduction's input slices on `q_keccak` and the link's pointer slices),
  the memory term (`memoryTermPure`, `memoryTermClaim`'s), the column claims with a placement (the
  link's, the public input's two, the Keccak reduction's on `q_keccak`), the out-of-domain claim;
  `stackedBasis`, their weights batched by the powers of the batching challenge.
* `MeaningCertifyStack`: on the kappa sources `[1, g^logMemory, g^(h_t)…]`, `certify_stack` returns
  `g^stackLog` and, per stack block, `g^offset` and `g^kappa`, the placement `buildLayout` gives its
  column (`StackPlaced`).
* `MeaningColumnSelector`, `MeaningStackSelectors`: a block's selector at the opening point is its
  placement's `eqAbove`.
* `StackCtxAt`: what `verify_sub` holds when it calls `check_stack_terminal`, against the verifier's
  layout, link end, Keccak reduction, ring switch and out-of-domain sample.
* `MeaningCheckStackTerminal`: under `StackCtxAt`, a call that returns gives the terminal's check
  `(inner + stackedBasis … x) · yr = target` at the opening point `x`, the form
  `open_stacked_verifyWhir` takes.
* `StackSectionSound`: the three functions' core IR give their meanings.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The verifier's stacked claims, without its program -/

/-- `memoryTermClaim`'s claim, `none` where a memory limb has no placement. -/
def memoryTermPure (layout : Layout) (link : LinkEnd) : Option StackClaim :=
  match layout.placements.getD memory0 none, layout.placements.getD memory1 none with
  | some p0, some p1 =>
    let memoryPoints := [(p0.stackPoint link.memoryPoint layout.stackLog, link.memoryScales.1),
      (p1.stackPoint link.memoryPoint layout.stackLog, link.memoryScales.2)]
    some (fun x ↦ sumE (memoryPoints.map fun (point, scale) ↦ scale * eqEval point x),
      link.memoryValue)
  | _, _ => none

/-- The public input's claims `bindPublicInput` makes at the challenge `rm`, the memory's placement
giving their point's length. -/
def publicClaimsPure (layout : Layout) (rm v0 v1 : E) : List ColumnClaim :=
  let n := ((layout.placements.getD memory0 none).map (·.variableCount)).getD 0
  let point := rm :: List.replicate (n - 1) 0
  [⟨memory0, point, v0⟩, ⟨memory1, point, v1⟩]

/-- **The claims `verifyExecution` stacks**, in its order: the merged ring claim, the memory term,
the column claims with a placement, the out-of-domain claim. -/
def stackedClaims (layout : Layout) (link : LinkEnd) (publicClaims outputs : List ColumnClaim)
    (keccakPoint keccakSlices f g : List E) (rho : E) (ood : StackClaim) : Option (List StackClaim) :=
  match layout.placements.getD qkeccak none, memoryTermPure layout link with
  | some qkeccakPlacement, some memoryTerm =>
    let ring := ringMerge [keccakRingClaim qkeccakPlacement keccakPoint keccakSlices, link.ring] f g rho
    some (ring :: memoryTerm ::
      (linkColumnClaims link ++ publicClaims ++ outputs).filterMap (·.onStack layout) ++ [ood])
  | _, _ => none

/-- **The basis `verifyStackedOpening` evaluates**: the claims' weights batched by the powers of
the batching challenge. -/
def stackedBasis (claims : List StackClaim) (batching : E) (x : List E) : E :=
  dot (powers batching claims.length) (claims.map fun c ↦ c.1 x)

/-! ## `certify_stack` -/

/-- The stack's block `b`: its global column (`stackBlocks`). -/
def blockColumn (b : ℕ) : ℕ := (stackBlocks.getD b default).column

/-- The number of stack blocks, `N_STK_BLOCKS`. -/
abbrev nStkBlocks : ℕ := stackBlocks.length

/-- **The layout's stack, placed**: `gmv` is `g^stackLog`, and per block `b` the words
`offs[b] = g^index` and `kaps[b] = g^variableCount` of its column's placement. -/
def StackPlaced (rd : Reader) (layout : Layout) (gmv offs kaps : E) : Prop :=
  gmv = gen ^ layout.stackLog ∧
    ∀ b < nStkBlocks, ∃ p : Placement, layout.placements.getD (blockColumn b) none = some p ∧
      LoadHolds rd offs b (gen ^ p.index) ∧ LoadHolds rd kaps b (gen ^ p.variableCount)

/-- The kappa sources `certify_stack` reads: `g^0`, the memory's `g^logMemory`, each table's
`g^(h_t)`. -/
def kappaSources (logMemory : ℕ) (heights : List ℕ) : List E :=
  1 :: gen ^ logMemory :: (List.range nTables).map fun t ↦ gen ^ heights.getD t 0

/-- **`certify_stack(kappa_base, g_squares)`**: on the exponent tables at `g_squares` and the kappa
sources of a layout `buildLayout` returns at `kappa_base`, it returns `[gmv, offs, kaps]` placing
that layout's stack. -/
def MeaningCertifyStack (rd : Reader) : List E → List E → Prop
  | [kb, gsq], rets => ∀ (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) (layout : Layout),
      buildLayout bytecode logMemory tableRows = some layout → ExpTables rd gsq →
      ReadsAt rd kb (kappaSources layout.logMemory layout.tableLogHeights) →
      ∃ gmv offs kaps : E, rets = [gmv, offs, kaps] ∧ StackPlaced rd layout gmv offs kaps
  | _, _ => False

/-! ## The selectors -/

/-- **`column_selector(offset, sel_eq, sel_g, n_nib, kappa)`**, through `stack_selectors`: at a block
of placement `p` (`offset = g^index`, `kappa = variableCount ≤ m`) in a stack of `2^m` words,
`4 n_nib ≥ m`, the selector is `p.eqAbove` at the opening point's first `m` coordinates. -/
def SelectorAt (p : Placement) (x : List E) (sel : E) : Prop := sel = p.eqAbove x

/-- **`stack_selectors(offs, kaps, point, point1, g_squares, n_nib)`**: on a placed stack of
`2^m` words a layout `buildLayout` returns, `m = x.length`, `n_nib = ⌈m/4⌉`, and the opening point
`x` at `point` (one plus it at `point1`), padded to `40` with zeros (ones), it returns `sel`, whose word
`b` is block `b`'s `eqAbove` at `x`. -/
def MeaningStackSelectors (nNib : ℕ) (rd : Reader) : List E → List E → Prop
  | [offs, kaps, pt, pt1, gsq], rets => ∀ (layout : Layout) (gmv : E) (x : List E),
      (∃ bytecode tableRows, buildLayout bytecode layout.logMemory tableRows = some layout) →
      StackPlaced rd layout gmv offs kaps → x.length = layout.stackLog →
      (layout.stackLog + 3) / 4 = nNib → ExpTables rd gsq →
      ReadsAt rd pt (x ++ List.replicate (40 - x.length) 0) →
      ReadsAt rd pt1 (x.map (1 + ·) ++ List.replicate (40 - x.length) 1) →
      ∃ sel : E, rets = [sel] ∧ ∀ b < nStkBlocks, ∃ p : Placement,
        layout.placements.getD (blockColumn b) none = some p ∧ LoadHolds rd sel b (p.eqAbove x)
  | _, _ => False

/-! ## `check_stack_terminal` -/

/-- The link's pointer pieces at the row point `chi` and the pointer weights `eqKernel qPoint`: per
table, per pointer column, its placement, its table's row point and its weight (`verifyLink`'s
`pieces`). -/
def pointerPieces (layout : Layout) (chi qPoint : List E) : List RingPiece :=
  let eqQ := eqKernel qPoint
  ((tables.zipIdx.foldl (fun (acc : List RingPiece × ℕ) (table, t) ↦
    table.links.pointers.foldl (fun (acc : List RingPiece × ℕ) pointer ↦
      (acc.1 ++ [{ placement := some ((layout.placements.getD (globalColumnBases.getD t 0 + pointer)
          none).getD default)
                   point := chi.take (layout.tableLogHeights.getD t 0)
                   scale := eqQ.getD acc.2 0 }], acc.2 + 1)) acc) ([], 0)).1)

/-- A table's non-pointer columns, those the link sends (`verifyLink`'s `nonPointer`). -/
def nonPointerColumns (table : Table) : List ℕ :=
  (List.range table.width).filter fun c ↦ !table.links.pointers.contains c

/-- **What `verify_sub` holds at `check_stack_terminal`'s call**, its arguments `args`, against the
verifier's objects: the layout (`buildLayout`'s) and its stack placed (`StackPlaced`); the link's end,
its row point `chi` and pointer weights `qPoint`, its memory point a prefix of `r`; the public
challenge `rm`; the Keccak reduction's output claim on `q_keccak` at `kOut` and its input point `kIn`;
the ring map's coefficients `ringCoefficients f g` and `rho`; the batching challenge `lam`; the
opening point `x` of the stack's `stackLog` coordinates; the out-of-domain point `z`. The row point
has at most `MAX_PTR_WIDTH` coordinates, the pointer weights' point `LINK_Q_VARS`, and both Keccak
points `q_keccak`'s, `h_KECCAK + slot bits`. -/
def StackCtxAt (rd : Reader) (args : List E) (layout : Layout) (link : LinkEnd)
    (chi r qPoint kOut kIn f g x z : List E) (rho lam rm : E) (outputs : List ColumnClaim) : Prop :=
  match args with
  | [gsq, kb, offs, kaps, gmv, chiP, gn, rP, glm, rmV, zv, eqq, ct, rhoV, lamV, gm1b, gm2b, pt, pt1,
      _inner, _yr, _target, oodz] =>
    (∃ bytecode tableRows, buildLayout bytecode layout.logMemory tableRows = some layout) ∧
    ExpTables rd gsq ∧ ReadsAt rd kb (kappaSources layout.logMemory layout.tableLogHeights) ∧
    StackPlaced rd layout gmv offs kaps ∧
    -- the link's row point and its pieces' points and weights
    ReadsAt rd chiP chi ∧ gn = gen ^ chi.length ∧ chi.length ≤ guest_const% MAX_PTR_WIDTH ∧
    (∀ t < nTables, layout.tableLogHeights.getD t 0 ≤ chi.length) ∧
    link.ring.pieces = pointerPieces layout chi qPoint ∧
    link.columns.map (fun c ↦ (c.1, c.2.map (·.1))) =
      tables.zipIdx.map (fun (table, t) ↦
        (chi.take (layout.tableLogHeights.getD t 0), nonPointerColumns table)) ∧
    qPoint.length = guest_const% LINK_Q_VARS ∧
    ReadsAt rd (eqq * gen ^ guest_const% EQ_Q_AT) ((eqKernel qPoint).take (guest_const% N_POINTERS)) ∧
    -- the memory term at `r`
    ReadsAt rd rP r ∧ layout.logMemory ≤ r.length ∧ glm = gen ^ layout.logMemory ∧
    link.memoryPoint = r.take layout.logMemory ∧ gm1b = link.memoryScales.1 ∧
    gm2b = link.memoryScales.2 ∧
    -- the public challenge, the Keccak reduction's points
    rmV = rm ∧ ReadsAt rd zv kOut ∧
    ReadsAt rd (zv * gen ^ guest_const% QKECCAK_VARS_CAP) kIn ∧
    (∃ word, outputs = [⟨qkeccak, kOut, word⟩]) ∧
    kOut.length = layout.tableLogHeights.getD opKeccak 0 + qkeccakSlotBits ∧ kIn.length = kOut.length ∧
    -- the ring map, the batching, the opening point, the out-of-domain point
    f.length = 8 ∧ g.length = 8 ∧ ReadsAt rd ct (ringCoefficients f g) ∧ rhoV = rho ∧ lamV = lam ∧
    x.length = layout.stackLog ∧
    ReadsAt rd pt (x ++ List.replicate (40 - x.length) 0) ∧
    ReadsAt rd pt1 (x.map (1 + ·) ++ List.replicate (40 - x.length) 1) ∧
    z.length = layout.stackLog ∧ ReadsAt rd oodz z
  | _ => False

/-- **`check_stack_terminal`'s meaning**: it returns nothing, and wherever `verify_sub`'s objects
stand as `StackCtxAt` says, the stacked claims exist and the terminal's check holds at the opening
point: `(inner + stackedBasis claims lam x) · yr = target`. -/
def MeaningCheckStackTerminal (rd : Reader) (args rets : List E) : Prop :=
  rets = [] ∧
    ∀ (layout : Layout) (link : LinkEnd) (chi r qPoint kOut kIn f g x z : List E) (rho lam rm : E)
      (outputs : List ColumnClaim) (keccakSlices : List E) (oodValue v0 v1 : E),
      StackCtxAt rd args layout link chi r qPoint kOut kIn f g x z rho lam rm outputs →
      ∃ claims, stackedClaims layout link (publicClaimsPure layout rm v0 v1) outputs kIn keccakSlices
          f g rho (fun y ↦ eqEval z y, oodValue) = some claims ∧
        (args.getD 19 0 + stackedBasis claims lam x) * args.getD 20 0 = args.getD 21 0

/-! ## The section -/

/-- `stack_selectors`' specializations: the stack's nibbles and the name. -/
def stackSelectorsNames : List (ℕ × String) :=
  [(4, "stack_selectors__L4"), (5, "stack_selectors__L5"), (6, "stack_selectors__L6"),
    (7, "stack_selectors__L7"), (8, "stack_selectors__L8")]

/-- **The stack and its terminal in the circuit**: on a memory image of `2^κ` words,
`11 ≤ κ ≤ 32` (the range checks' bounds, `STK_KEY_BOUND = 1802` the largest), `certify_stack`,
`stack_selectors` (each specialization by the stack's nibbles `n_nib`) and `check_stack_terminal`
give their meanings. -/
def StackSectionSound : Prop :=
  ∀ {κ : ℕ}, 11 ≤ κ → κ ≤ 32 → ∀ L : MemoryImage κ,
    (∀ args rets, coreProgram.Rel L.read "certify_stack" args rets →
      MeaningCertifyStack L.read args rets) ∧
    (∀ p ∈ stackSelectorsNames, ∀ args rets, coreProgram.Rel L.read p.2 args rets →
      MeaningStackSelectors p.1 L.read args rets) ∧
    (∀ args rets, coreProgram.Rel L.read "check_stack_terminal" args rets →
      MeaningCheckStackTerminal L.read args rets)

end
end LeanVM.Guest.B1.Stack
