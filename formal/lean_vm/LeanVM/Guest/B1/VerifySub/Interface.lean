/-
  LeanVM.Guest.B1.VerifySub.Interface

  `verify_sub`'s interface: the specification's programs its phases run, its meaning, and what
  its soundness assumes of the callees that groups 4 and 5 prove.
-/

module

public import LeanVM.Guest.B1.Tables
public import LeanVM.Spec.Node

/-!
# `verify_sub`: phases and callees (TRIAGE #44)

`verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, defer_out)` (G:2078-2281) runs
`verifyDeferredWith` (V:2235) on one child: the seed `compress(seed, pi)`, the announced sizes
(`readSizes`), the stack's root (`commitStack`), the bus challenges and GKR, the tables, Flock,
the ring switch and the stacked opening, then stores the claims on the fixed polynomials at
`defer_out` (`Node.fixedCells`). Its meaning (`MeaningVerifySub`): some fixed claims `c` and some
proof `π` that the deferring verifier accepts for the statement `pi` under `seed`, with
`fixedCells c` at `defer_out`.

The guest splits the specification's phases differently, so this file names the pieces the
callees run, each a program of the specification's language:

| callee | program | split lemma (`VerifySub.Spec`) |
|---|---|---|
| `verify_bus_gkr` (#37) | `gkrPhase depth` | `verifyBusBalance_split` |
| `verify_tables` (#39) | `tablesSeg`: `verifyBusBalance` after GKR, `tablePhase`, `publicInputPhase` | same |
| `verify_flock` (#40) | `verifyFlock ev (14 + τ)`, for every `ev` giving the matrices' value | |
| `open_stacked__L{j}` (#36) | `whirOpen μ r target`: `verifyWhir` up to its terminal | `verifyWhir_split` |
| `check_opening_terminal` (#43) | the terminal `(inner + stackWeight …) · yr = target` | |

The callees' soundness, as this proof assumes it (`Sound*`, `HypKappa`): each is "the callee's
relation, under its precondition, implies its outcome", the outcome in the specification's terms.
`TCtx` (what `verify_tables` hands `check_opening_terminal`: the claims' points and lengths) and
`PCtx` (what `certify_placement` hands it: the columns' offsets and logs) are group 5's to define;
this proof only passes them from one callee to the other.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Runs with openings and roots -/

/-- The program `p` runs from the chain state `cv` and the roots `roots`, reading exactly the
stream words `xs` and the openings `os`, to `a`, the state `cv'` and the roots `roots'`, on any
stream and openings continuing them. -/
def RunsWith {α : Type} (p : Prog α) (cv : Digest) (xs : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (a : α) (cv' : Digest) (roots' : List (Digest × ℕ × ℕ)) :
    Prop :=
  ∀ (rest : List E) (orest : List Opening),
    runId p ⟨cv, xs ++ rest, os ++ orest, roots⟩ = some (a, ⟨cv', rest, orest, roots'⟩)

/-! ## The layout -/

/-- `buildLayout`'s layout (V:1268), its checks left out: the memory's log-size `logMemory` and
the tables' row counts `tableRows`. -/
def layoutOf (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) : Layout :=
  let logBytecode := Nat.log2 bytecode.length - busBits
  let tableLogHeights := tableRows.map log2Ceil
  let (push, pull, count) := busBlocks tableLogHeights tableRows
  let (placements, stackLog) := placementsOf (columnKappas logMemory logBytecode tableLogHeights)
  ⟨logMemory, logBytecode, bytecode, push, pull, count, placements, stackLog, tableLogHeights⟩

/-- The committed columns: those that are not an embedded `BLAKE2S` limb (V:1257). -/
def blockCols (n : ℕ) : List ℕ := (List.range n).filter fun c ↦ (limbSlot c).isNone

/-- The stack's size before rounding: `Σ 2^κ` over the committed columns. -/
def stackTotal (kappas : List ℕ) : ℕ :=
  ((blockCols kappas.length).map fun c ↦ 2 ^ kappas.getD c 0).sum

/-! ## The bus (V:1468) -/

/-- The GKR walk and the count root's check (V:1476-1477). -/
def gkrPhase (depth : ℕ) : Prog (E × List E × List E) := do
  let r ← verifyGkrGrandProducts depth
  Prog.require (r.1 ≠ 0)
  return r

/-- `verifyBusBalance` after the GKR walk (V:1478-1513), from its challenges, point and values. -/
def busRest (ev : Evaluations) (layout : Layout) (alphas : List E) (beta : E)
    (point treeValues : List E) : Prog BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let weights := eqKernel alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← Prog.readN 3
  let memoryFinal ← Prog.readE
  let bytecodeFinal ← Prog.readE
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let bytecodeValue ← ev.bytecode layout.bytecode (bytecodeLow ++ alphas)
  let fp := fingerprints weights memory memoryLow bytecodeLow bytecodeValue
  let finalPc := Verifier.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (Verifier.gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp finalPc memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, point, forms3, [total0, total1, total2]⟩

/-- The push side's depth, GKR's (V:1474). -/
def pushDepth (layout : Layout) : ℕ :=
  (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth

/-- What `verify_tables` runs: the bus after GKR, the table sumcheck and the public input's
binding (V:2124-2129); the bus result and every column claim, the public ones last. -/
def tablesSeg (ev : Evaluations) (layout : Layout) (publicInput : Digest) (alphas : List E)
    (beta : E) (point treeValues : List E) : Prog (BusResult × List ColumnClaim) := do
  let bus ← busRest ev layout alphas beta point treeValues
  let claims ← tablePhase layout bus
  let publicClaims ← publicInputPhase layout publicInput
  return (bus, claims ++ publicClaims)

/-- `ev` takes `value` for the bytecode at `point`, consuming nothing. -/
def BytecodeAt (ev : Evaluations) (words : List K) (point : List E) (value : E) : Prop :=
  ∀ s, runId (ev.bytecode words point) s = some (value, s)

/-- `ev` takes `value` for the matrices at the lincheck's weights, consuming nothing. -/
def MatricesAt (ev : Evaluations) (alpha zSkip : E) (chiIn chiInPrime slices : List E)
    (value : E) : Prop :=
  ∀ s, runId (ev.matrices alpha zSkip chiIn chiInPrime slices) s = some (value, s)

/-! ## The stacked opening (V:1718-1804) -/

/-- What the stacked opening leaves for its terminal: the point in witness order, the glued
claims' weight there, the residual's value at the tail challenges, and the running claim. -/
structure WhirEnd where
  /-- The terminal point, rotated into witness order (`point.drop laneFolds ++ …`). -/
  point : List E
  /-- `Σ scalar · weightAt` over the glued claims. -/
  inner : E
  /-- `multilinearEval residual tailFolds`. -/
  residual : E
  /-- The final running claim. -/
  target : E

/-- `whirLevels` (V:1718) without the final `require`: it returns what the terminal reads. -/
def whirLevelsOpen (logN laneFolds : ℕ) : ℕ → List Whir.Level → WhirState → Prog WhirEnd
  | _, [], _ => Prog.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRounds level.fold s []
    let messageLog := logN - s.folds.length
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← Prog.readN (2 ^ messageLog)
        pure (residual, ([] : List (E × List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        Prog.commitP height width
        let oodPoint ← Prog.sampleN messageLog
        let oodValue ← Prog.readE
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])
    Prog.grindP Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← Prog.sampleE
    let queryWeights := powers lam queries.length
    let words ← Prog.queryP index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++
      [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRounds messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let inner := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds)) 0
      return ⟨point.drop laneFolds ++ point.take laneFolds, inner,
        multilinearEval residual tailFolds, target⟩
    | _ :: _ => whirLevelsOpen logN laneFolds (index + 1) rest s

/-- `verifyWhir` (V:1763) up to its terminal: what `open_stacked` runs. -/
def whirOpen (logN logInvRate : ℕ) (target : E) : Prog WhirEnd := do
  let config ← liftOption (deriveConfig logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsOpen logN ((config.head?.map (·.fold)).getD 0) 0 config ⟨target, quad, [], []⟩

/-- The terminal's check: the weight at the point times the residual's value is the claim. -/
def WhirEnd.Accepts (w : WhirEnd) (evaluateBasis : List E → E) : Prop :=
  (w.inner + evaluateBasis w.point) * w.residual = w.target

instance (w : WhirEnd) (evaluateBasis : List E → E) : Decidable (w.Accepts evaluateBasis) :=
  inferInstanceAs (Decidable (_ = _))

/-- The shape `commitStack` gives the stack's root (V:1771): `(height, width)`. -/
def stackShape (logN logInvRate : ℕ) : ℕ × ℕ :=
  match deriveConfig logN logInvRate with
  | some (level :: _) => levelShape logN level (2 ^ level.fold)
  | _ => (0, 0)

/-- The stacked opening's transparent weight at `x` (V:1781-1785): the ring-switching claim's,
then every column claim's, batched by the powers of `lam`. -/
def stackWeight (layout : Layout) (claims : List ColumnClaim) (flockPoint coeffs : List E)
    (lam : E) (x : List E) : E :=
  let all := ringSwitchClaim layout 0 (fun rPrime ↦ ringWeight flockPoint rPrime coeffs) ::
    claims.map (·.onStack layout)
  dot (powers lam all.length) (all.map fun c ↦ c.1 x)

/-! ## The guest's tables -/

/-- `BLOCK_KAPPA_SRC` (G:121): a bus block's log-height is source `s` of
`[0, log_mem, τ_0, …, τ_5]` … -/
def blockKappaSrc : List ℕ :=
  [0, 1, 0, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 0, 1, 0, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7]

/-- … plus `BLOCK_KAPPA_ADJ` (G:122). -/
def blockKappaAdj : List ℕ :=
  (List.range 102).map fun b ↦ if b = 2 ∨ b = 39 then 18 else 0

/-- `kappa_base` (G:2117-2120): `[g^0, g^log_mem, dims_g[1..7]]`. -/
def kappaBase (gLogMem : E) (dims : List E) : List E := 1 :: gLogMem :: dims

/-- `block_kappa` (G:2121-2123), over the base. -/
def blockKappas (gLogMem : E) (dims : List E) : List E :=
  (List.range 102).map fun b ↦
    (kappaBase gLogMem dims).getD (blockKappaSrc.getD b 0) 0 * gen ^ blockKappaAdj.getD b 0

/-- `N_COMMITTED_COLS`: the columns `certify_placement` places. -/
abbrev nCommittedCols : ℕ := 92

/-- `N_CLAIMS`: the column claims the pool holds. -/
abbrev nClaims : ℕ := 112

/-- The length of `open_stacked`'s point buffer, `SIZE_BITS + SLOT_STRIDE_LOG`. -/
abbrev pointCap : ℕ := 42

/-- `open_stacked`'s 28 specializations, in dispatch order. -/
def openNames : List String :=
  ["open_stacked__L0", "open_stacked__L1", "open_stacked__L2", "open_stacked__L3",
    "open_stacked__L4", "open_stacked__L5", "open_stacked__L6", "open_stacked__L7",
    "open_stacked__L8", "open_stacked__L9", "open_stacked__L10", "open_stacked__L11",
    "open_stacked__L12", "open_stacked__L13", "open_stacked__L14", "open_stacked__L15",
    "open_stacked__L16", "open_stacked__L17", "open_stacked__L18", "open_stacked__L19",
    "open_stacked__L20", "open_stacked__L21", "open_stacked__L22", "open_stacked__L23",
    "open_stacked__L24", "open_stacked__L25", "open_stacked__L26", "open_stacked__L27"]

/-- The specialization of `open_stacked` for the stack log `μ` and the rate `r`
(`config_sel = (μ - 22) + 7·(r - 1)`, G:2246-2252): `open_stacked__L{config_sel}`. -/
def openName (μ r : ℕ) : String := openNames.getD (μ - 22 + 7 * (r - 1)) ""

/-! ## The callees' soundness -/

section Callees

variable (bytecode : List K)
  (TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop)
  (PCtx : Reader → List ℕ → E → E → Prop) (rd : Reader)

/-- **`verify_bus_gkr(fs0, fs1, cursor, g_bus_mu, zeta)`** (G:1320-1438; TRIAGE #37): from the
state of `cv`, the words `xs` at the cursor run GKR of depth `depth < 33` and its count root's
check (`gkrPhase`) to `(count, point, values)`; the point is at `zeta`, and the function returns
the new state, the cursor past `xs`, and the three values. -/
def GkrOut (fs0 fs1 cur gmu zeta : E) (rets : List E) : Prop :=
  ∃ (cv : Digest) (depth : ℕ) (xs : List E) (r : E × List E × List E) (cv' : Digest),
    (fs0, fs1) = digestScalars cv ∧ gmu = gen ^ depth ∧ depth < 33 ∧
    ReadsAt rd cur xs ∧ RunsTo (gkrPhase depth) cv xs r cv' ∧ r.2.1.length = depth ∧
    r.2.2.length = 3 ∧ ReadsAt rd zeta r.2.1 ∧
    rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length] ++ r.2.2

/-- `verify_bus_gkr` is sound. -/
def SoundGkr : Prop :=
  ∀ fs0 fs1 cur gmu zeta rets,
    coreProgram.Rel rd "verify_bus_gkr" [fs0, fs1, cur, gmu, zeta] rets →
      GkrOut rd fs0 fs1 cur gmu zeta rets

/-- What `verify_sub` establishes before `verify_tables`, for the public input `pi`, the memory's
log-size `logMem`, the bus challenges `alphas`, the GKR point `point` and values `values`: the
public input's cells; the point at `zeta`, `g_bus_mu = g^|point|`; `dims_g[0] = g^log_mem` and
`block_kappa` derived from `dims_g` by the baked tables; the exponent tables; `fp_w` the equality
weights of `alphas`; the three GKR values. -/
def TablesPre (lp : E) (pi : Digest) (logMem : ℕ) (alphas point values : List E) :
    List E → Prop
  | [_, _, _, pi0, pi1, zeta, gmu, dims, _, bk, sq, fpw, _, _, _, _, cpush, cpull, ccount] =>
      (pi0, pi1) = digestScalars pi ∧ ReadsAt rd zeta point ∧ gmu = gen ^ point.length ∧
      point.length < 33 ∧ 16 ≤ logMem ∧ logMem ≤ 32 ∧
      (∃ ds : List E, ds.length = 6 ∧ ReadsAt rd dims (gen ^ logMem :: ds) ∧
        ReadsAt rd bk (blockKappas (gen ^ logMem) ds)) ∧
      ExpTables rd lp sq ∧ alphas.length = 4 ∧ ReadsAt rd fpw (eqKernel alphas) ∧
      values = [cpush, cpull, ccount]
  | _ => False

/-- **`verify_tables(…)`** (G:1475-1824; TRIAGE #38, #39): the row counts `rows` are in
`table_rows` (integer words) and their log-heights, below 29, in `dims_g`; for the layout they
give and every `ev` taking `bv` for the bytecode at `(point[..logBytecode], alphas)`, from the
state of `cv` the words `xs` at the cursor run `tablesSeg` to the bus result and the `112` column
claims, whose values are in `claim_pool`; `TCtx` holds of the claims and the buffers the terminal
reads; and the function returns the new state, the cursor past `xs`, `g^n` (the sumcheck's
rounds), `bv` and the public input's challenge `rm`. -/
def TablesOut (pi : Digest) (logMem : ℕ) (alphas point values : List E) :
    List E → List E → Prop
  | [fs0, fs1, cur, _, _, zeta, gmu, dims, rows, _, _, _, beta, pool, cplen, chi, _, _, _],
    [fs0', fs1', cur', gzcn, bv, rm] =>
      ∃ (cv : Digest) (xs : List E) (cv' : Digest) (rowsN : List ℕ) (bus : BusResult)
          (claims : List ColumnClaim), (fs0, fs1) = digestScalars cv ∧ rowsN.length = 6 ∧
        ReadsAt rd rows (rowsN.map eOfNat) ∧
        ReadsAt rd dims (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n) ∧
        (∀ n ∈ rowsN, log2Ceil n < 29) ∧ ReadsAt rd cur xs ∧
        (∀ ev, BytecodeAt ev bytecode
            (point.take (layoutOf bytecode logMem rowsN).logBytecode ++ alphas) bv →
          RunsTo (tablesSeg ev (layoutOf bytecode logMem rowsN) pi alphas beta point values) cv
            xs (bus, claims) cv') ∧
        claims.length = nClaims ∧ ReadsAt rd pool (claims.map (·.value)) ∧
        TCtx rd (layoutOf bytecode logMem rowsN) bus claims [zeta, chi, rm, gmu, gzcn, cplen] ∧
        (fs0', fs1') = digestScalars cv' ∧ cur' = cur * gen ^ xs.length
  | _, _ => False

/-- `verify_tables` is sound. -/
def SoundTables : Prop :=
  ∀ lp pi logMem alphas point values args rets,
    TablesPre rd lp pi logMem alphas point values args →
    coreProgram.Rel rd "verify_tables" args rets →
      TablesOut bytecode TCtx rd pi logMem alphas point values args rets

/-- **`verify_flock(fs0, fs1, cursor, g^τ, zerocheck_chis, lincheck_rs, z_partial)`**
(G:1827-1963; TRIAGE #40): from the state of `cv`, the words `xs` at the cursor run `verifyFlock`
on `14 + τ` variables, for every `ev` taking `mv` for the matrices at the run's weights, to its
point and slices; the zerocheck's point `chi`, the lincheck's challenges `rcs` in round order and
the slices `s` are in the three buffers; and the function returns the new state, the cursor past
`xs`, the skip challenge, the lincheck's `alpha` and `mv`. -/
def FlockOut (τ : ℕ) (fs0 fs1 cur zchis lrs zpart : E) (rets : List E) : Prop :=
  ∃ (cv : Digest) (xs : List E) (cv' : Digest) (zSkip alpha mv : E) (chi rcs s : List E),
    (fs0, fs1) = digestScalars cv ∧
    ReadsAt rd cur xs ∧ chi.length = 8 + τ ∧ rcs.length = 8 ∧ s.length = 64 ∧
    ReadsAt rd zchis chi ∧ ReadsAt rd lrs rcs ∧ ReadsAt rd zpart s ∧
    (∀ ev, MatricesAt ev alpha zSkip (chi.take 8) rcs.reverse s mv →
      RunsTo (verifyFlock ev (blake2sR1csLogSize + τ)) cv xs (rcs.reverse ++ chi.drop 8, s) cv') ∧
    rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length, zSkip, alpha, mv]

/-- `verify_flock` is sound, for a BLAKE2s table of log-height `τ < 29`. -/
def SoundFlock : Prop :=
  ∀ τ fs0 fs1 cur zchis lrs zpart rets, τ < 29 →
    coreProgram.Rel rd "verify_flock" [fs0, fs1, cur, gen ^ τ, zchis, lrs, zpart] rets →
      FlockOut rd τ fs0 fs1 cur zchis lrs zpart rets

/-- **`certify_placement(kappa_base, g_squares)`** (G:1966-1999; TRIAGE #41): over the base
`[1, g^log_mem, g^h_0, …, g^h_5]`, it returns `g^(Σ 2^κ)` over the committed columns of
`columnKappas log_mem 18 h` and two buffers of which `PCtx` holds. -/
def SoundPlace : Prop :=
  ∀ lp sq kb (logMem : ℕ) (hs : List ℕ) rets, ExpTables rd lp sq → logMem ≤ 32 →
    hs.length = 6 → (∀ h ∈ hs, h < 29) → ReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·)) →
    coreProgram.Rel rd "certify_placement" [kb, sq] rets →
      ∃ off kap, rets = [gen ^ stackTotal (columnKappas logMem 18 hs), off, kap] ∧
        PCtx rd (columnKappas logMem 18 hs) off kap

/-- Every committed column's log, in `col_kappas`, is below `N_COLUMN_LOGS = 29`: the selector
`check_opening_terminal` dispatches on is in range. -/
def KappasBelow (kap : E) : Prop := ∀ c < nCommittedCols, ∃ κ < 29, LoadHolds rd kap c (gen ^ κ)

/-- **The columns' logs are in range** once the stack is at most `2^28` (group 5's lemma). -/
def HypKappa : Prop :=
  ∀ kappas off kap, PCtx rd kappas off kap → log2Ceil (stackTotal kappas) ≤ 28 →
    KappasBelow rd kap

/-- **`open_stacked__L{j}(fs0, fs1, target, root_0, root_1, cursor)`** (G:1047-1213; TRIAGE #36)
at `j = (μ - 22) + 7·(r - 1)`: from the state of `cv`, the stack's root `root` committed with its
shape, the words `xs` at the cursor and the openings `os` run `whirOpen μ r target` to `w`; the
function returns `w`'s claim, a buffer holding its point (zero-padded to `42`), its glued weight
and its residual's value; the point has `μ` coordinates. -/
def OpenOut (μ r : ℕ) (root : Digest) (fs0 fs1 target cur : E) (rets : List E) : Prop :=
  ∃ (cv : Digest) (xs : List E) (os : List Opening) (w : WhirEnd) (cv' : Digest)
    (roots' : List (Digest × ℕ × ℕ)), (fs0, fs1) = digestScalars cv ∧ ReadsAt rd cur xs ∧
    RunsWith (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots' ∧
    ∃ pt, rets = [w.target, pt, w.inner, w.residual] ∧
      ReadsAt rd pt (w.point ++ List.replicate (pointCap - w.point.length) 0) ∧ w.point.length = μ

/-- `open_stacked` is sound at every candidate. -/
def SoundOpen : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root : Digest) fs0 fs1 target root0 root1 cur rets, (root0, root1) = digestScalars root →
      coreProgram.Rel rd (openName μ r) [fs0, fs1, target, root0, root1, cur] rets →
        OpenOut rd μ r root fs0 fs1 target cur rets

/-- What `verify_sub` establishes before `check_opening_terminal`, for the layout, the bus result,
the column claims, the batching challenge `lam`, Flock's point, the ring map's coefficients and
the opening's end `w`; the layout is `layoutOf`'s placement of its columns, and the points and
tables have the lengths the terminal reads. -/
def TermPre (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) (lam : E)
    (flockPoint coeffs : List E) (w : WhirEnd) : List E → Prop
  | [zeta, chi, rm, gmu, gzcn, glm, gtau, cplen, lampool, off, kap, zvals, ctable, pt, inner, yr,
      st] =>
      TCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn, cplen] ∧
      PCtx rd (columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights) off kap ∧
      KappasBelow rd kap ∧ glm = gen ^ layout.logMemory ∧
      gtau = gen ^ layout.tableLogHeights.getD opBlake2s 0 ∧
      ReadsAt rd lampool (powersFrom lam lam claims.length) ∧ ReadsAt rd zvals flockPoint ∧
      ReadsAt rd ctable coeffs ∧
      ReadsAt rd pt (w.point ++ List.replicate (pointCap - w.point.length) 0) ∧
      inner = w.inner ∧ yr = w.residual ∧ st = w.target ∧
      let kap := columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights
      layout.placements = (placementsOf kap).1 ∧ layout.stackLog = (placementsOf kap).2 ∧
      layout.stackLog ≤ 28 ∧ 1 ≤ layout.logMemory ∧ bus.point.length < 33 ∧
      w.point.length = layout.stackLog ∧
      flockPoint.length = layout.tableLogHeights.getD opBlake2s 0 + 8 ∧ coeffs.length = 64
  | _ => False

/-- **`check_opening_terminal(…)`** (G:2020-2075; TRIAGE #42, #43) is sound: under its
precondition, the stacked opening's terminal holds (V:1758-1760). -/
def SoundTerm : Prop :=
  ∀ layout bus claims lam flockPoint coeffs w args,
    TermPre TCtx PCtx rd layout bus claims lam flockPoint coeffs w args →
    coreProgram.Rel rd "check_opening_terminal" args [] →
      w.Accepts (stackWeight layout claims flockPoint coeffs lam)

end Callees

/-! ## The meaning -/

/-- The shape of the fixed claims a child's proof makes, as `verify_sub` exports them
(`DEFER_SIZE = 106` cells). -/
def FreshShaped (c : FixedClaims) : Prop :=
  c.bytecodePoint.length = 22 ∧ c.rowPoint.length = 8 ∧ c.columnPoint.length = 8 ∧
    c.slices.length = 64

/-- **`verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, defer_out)`**
(G:2078-2281; TRIAGE #44): the cells are a public input `pi` and a seed, and for some fixed
claims `c` of the guest's shape and some proof `π` the deferring verifier accepts `π` for `pi`
under the seed (`verifyDeferred`, V:2250), with `fixedCells c` at `defer_out`. -/
def MeaningVerifySub (bytecode : List K) (rd : Reader) : List E → List E → Prop
  | [pi0, pi1, s0, s1, _, _, out], [] =>
      ∃ (seed pi : Digest) (c : FixedClaims) (π : Proof), (s0, s1) = digestScalars seed ∧
        (pi0, pi1) = digestScalars pi ∧ verifyDeferred bytecode seed pi c π = true ∧
        FreshShaped c ∧ ReadsAt rd out (Node.fixedCells c)
  | _, _ => False

end
end LeanVM.Guest.B1.VerifySub
