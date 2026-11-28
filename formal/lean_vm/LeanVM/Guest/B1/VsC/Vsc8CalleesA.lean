/-
  LeanVM.Guest.B1.VsC.Vsc8CalleesA

  The placed completeness statements of `verify_sub`'s stack, terminal, ring and Keccak callees.
-/

module

public import LeanVM.Guest.Complete.CallCompleteA
public import LeanVM.Guest.ExpTables
public import LeanVM.Guest.B1.Stack.Interface
public import LeanVM.Guest.B1.KeccakGkr.Section
public import LeanVM.Guest.B1.Ring.Interface
public import LeanVM.Guest.B1.VsC.ChunkDC

/-!
# `verify_sub`'s stack, terminal, ring and Keccak callees, placed: the statements

Each is `CallAtA` at the callee's cursor right after its frame (what `KidsAtF` hands an entered
call), on the honest inputs, its caller's arrays all below its frame (`PtrsBelow`), loading from
them (`ptrRegion`) and its own data:

* `CertifyStackCompleteA`: on a layout `buildLayout` returns, its stack within `2^30` (else a
  group's `κ` can pass `33`, the guest's range check), the exponent tables at `qt` and the
  kappa sources at `qk`, `certify_stack` returns `[g^stackLog, offs, kaps]`, `offs` and `kaps` the
  two halves of its last buffer (`alloc 104`, after four `alloc 8`), placing the layout's stack
  (`StackPlaced`), popping `stackHints` of the layout's block sizes (`stackKappas`), every node exact.
* `CheckStackTerminalCompleteA`: wherever `verify_sub`'s objects stand as `StackCtxAt` says, the
  stack within `2^30` (the selectors' dispatch has `15` arms from `16`), and the native terminal check
  holds of the stacked claims, `check_stack_terminal` returns nothing, quiet.
* `RingSwitchTargetCompleteA`: on the slices and the map challenges, `ring_switch_target` returns
  `ringTarget`, quiet.
* `VerifyKeccakCompleteA`: where the native reduction `verifyKeccak` runs from the carried capacity on
  the stream words at the cursor to the output claim, the input point and the slices, `verify_keccak`
  returns the capacity after the queue's permutation, the cursor past the words, and the claim's
  word, quiet; the words it stores (the claim's point, the input point, the slices) are its caller's.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The pointer to the word of index `q` (`Complete/MainA.lean`'s `ptrAt`). -/
abbrev ptrAtV (q : ℕ) : E := ofK (addressOfIndex q)

/-- The words of the arrays `arrs` (each a pointer and a length): their indices. -/
def ptrRegion (arrs : List (E × ℕ)) (i : ℕ) : Prop :=
  ∃ q ∈ arrs, ∃ t < q.2, q.1.limb 0 * addressOfIndex t = addressOfIndex i

/-- Every word of the arrays `arrs` lies below `fp`. -/
def PtrsBelow (arrs : List (E × ℕ)) (fp : ℕ) : Prop :=
  ∀ q ∈ arrs, ∀ t < q.2, ∃ i < fp, q.1.limb 0 * addressOfIndex t = addressOfIndex i

/-- The stack blocks' log sizes, their sources' plus their adjustments (`childHints`' `kappas`). -/
def stackKappas (layout : Layout) : List ℕ :=
  stackBlocks.map fun block ↦
    (match block.source with
      | .memory => layout.logMemory
      | .table t => layout.tableLogHeights.getD t 0) + block.adj

/-- `certify_stack`'s `offs` buffer at its cursor `c`: after its four buffers of `8`. -/
abbrev csOffsAt (c : ℕ) : ℕ := c + 32

/-- **`certify_stack` completes placed.** -/
def CertifyStackCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  ∀ (bytecode : List K) (logMemory : ℕ) (rows : List ℕ) (layout : Layout) (qt qk fp : ℕ),
    buildLayout bytecode logMemory rows = some layout → layout.stackLog ≤ 30 →
    qt + (winTabAt + 2 ^ winTabBits) ≤ fp → qk + (2 + nTables) ≤ fp →
    ∃ e, CallAtA fs al cert k "certify_stack" [ptrAtV qk, ptrAtV qt]
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

/-- The arrays `check_stack_terminal` reads of `verify_sub`'s, at its arguments and the objects
`StackCtxAt` names. -/
def cstArrays (args : List E) (chi r kOut kIn f g z : List E) : List (E × ℕ) :=
  [(args.getD 0 0, (winTabAt + 2 ^ winTabBits)), (args.getD 1 0, 2 + nTables), (args.getD 2 0, nStkBlocks),
    (args.getD 3 0, nStkBlocks), (args.getD 5 0, chi.length),
    (args.getD 11 0 * gen ^ guest_const% EQ_Q_AT, guest_const% N_POINTERS), (args.getD 7 0, r.length),
    (args.getD 10 0, kOut.length), (args.getD 10 0 * gen ^ guest_const% QKECCAK_VARS_CAP, kIn.length),
    (args.getD 12 0, (ringCoefficients f g).length), (args.getD 17 0, 40), (args.getD 18 0, 40),
    (args.getD 22 0, z.length)]

/-- **`check_stack_terminal` completes placed** where the native terminal check holds. -/
def CheckStackTerminalCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  ∀ (args : List E) (layout : Layout) (link : LinkEnd) (chi r qPoint kOut kIn f g x z : List E)
    (rho lam rm : E) (outputs : List ColumnClaim) (keccakSlices : List E) (oodValue v0 v1 : E)
    (claims : List StackClaim) (fp : ℕ),
    stackedClaims layout link (publicClaimsPure layout rm v0 v1) outputs kIn keccakSlices f g rho
        (fun y ↦ eqEval z y, oodValue) = some claims → layout.stackLog ≤ 30 →
    (args.getD 19 0 + stackedBasis claims lam x) * args.getD 20 0 = args.getD 21 0 →
    PtrsBelow (cstArrays args chi r kOut kIn f g z) fp →
    ∃ e, CallAtA fs al cert k "check_stack_terminal" args []
      (ptrRegion (cstArrays args chi r kOut kIn f g z)) (fun _ => False) (fun _ => True)
      (fun rd => StackCtxAt rd args layout link chi r qPoint kOut kIn f g x z rho lam rm outputs)
      PostQuiet (fs "check_stack_terminal") fp (fp + fs "check_stack_terminal") e

/-- **`ring_switch_target` completes placed.** -/
def RingSwitchTargetCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  ∀ (sl mc : E) (s ch : List E) (fp : ℕ), s.length = kBits → ch.length = 2 * ringMapWidth →
    PtrsBelow [(sl, kBits), (mc, 2 * ringMapWidth)] fp →
    ∃ e, CallAtA fs al cert k "ring_switch_target" [sl, mc]
      [ringTarget s (ch.take ringMapWidth) (ch.drop ringMapWidth)]
      (ptrRegion [(sl, kBits), (mc, 2 * ringMapWidth)]) (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd sl s ∧ ReadsAt rd mc ch)
      PostQuiet (fs "ring_switch_target") fp (fp + fs "ring_switch_target") e

/-- The arrays `verify_keccak` reads and writes of `verify_sub`'s. -/
def vkArrays (cur chi ol zv sl tabs : E) (xs chis op point : List E) : List (E × ℕ) :=
  [(cur, xs.length), (chi, chis.length), (ol, 25), (zv, op.length),
    (zv * gen ^ qkeccakVarsCap, point.length), (sl, 64), (tabs, 2 ^ winTabBits)]

/-- **`verify_keccak` completes placed** where the native reduction runs, from a carried capacity
(a permutation's: `verify_keccak` permutes its cells). -/
def VerifyKeccakCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  ∀ (f0 f1 f2 f3 f4 cur chi ol zv sl tabs : E) (τ : ℕ) (chis outs xs op point slices : List E) (word : E)
    (s' : Fs) (fp : ℕ),
    keccakTauMin ≤ τ → τ ≤ keccakTauMax → τ ≤ chis.length → outs.length = 25 →
    (∃ sp, (⟨[f0, f1, f2, f3, f4], []⟩ : Fs).Carries sp) →
    RunsTo (verifyKeccak τ (chis.take τ) outs) ⟨[f0, f1, f2, f3, f4], []⟩ xs
      ([⟨qkeccak, op, word⟩], point, slices) s' →
    s'.pend.length = rateScalars → slices.length = 64 →
    PtrsBelow (vkArrays cur chi ol zv sl tabs xs chis op point) fp →
    ∃ e, CallAtA fs al cert k "verify_keccak" [f0, f1, f2, f3, f4, cur, gen ^ τ, chi, ol, zv, sl, tabs]
      (capOf s'.perm ++ [cur * gen ^ xs.length, word])
      (ptrRegion (vkArrays cur chi ol zv sl tabs xs chis op point)) (fun _ => False) (fun _ => True)
      (fun rd => WinTabs rd tabs ∧ ReadsAt rd chi chis ∧ ReadsAt rd ol outs ∧ ReadsAt rd cur xs ∧
        ReadsAt rd zv op ∧ ReadsAt rd (zv * gen ^ qkeccakVarsCap) point ∧ ReadsAt rd sl slices)
      PostQuiet (fs "verify_keccak") fp (fp + fs "verify_keccak") e

end
end LeanVM.Guest.B1.VsC
