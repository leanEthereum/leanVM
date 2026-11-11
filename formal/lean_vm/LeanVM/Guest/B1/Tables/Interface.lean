/-
  LeanVM.Guest.B1.Tables.Interface

  B1 of `verify_tables` and `padding_weight`: the specification's programs `verify_tables` runs
  (`busRest`, `tablesSeg`), the layout of the announced sizes (`layoutOf`), what it hands
  `check_opening_terminal` (`TCtx`), and the statements of their relations.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Gkr.Fs
public import LeanVM.Guest.B1.Placement.Interface
public import LeanVM.Guest.B1.Selectors.Interface

/-!
# `verify_tables` (TRIAGE G #51, #52): the interface

`verify_tables(fs0, …, fs4, cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, table_rows, g_squares,
fp_w, beta, claim_pool, chi, claim_push, claim_pull, claim_count)` (G:2109-2535, at 40f877dc)
settles the bus against the six tables: it certifies each side's blocks' offsets by a hinted order
of its block groups (`busLayout`, V:548), certifies every table's log-height to be
`max (log2Ceil rows) floor` (V:1294, by `padding_weight`), decomposes the three GKR leaf values
(`accumulateSide`, V:1452), reads the framework's five column claims, runs the one table sumcheck
(`tableSumcheck`, V:1552) and the public input's binding (`publicInputPhase`, V:2198). The bus's
five claim values and the public input's three are pooled (`claim_pool`, slots `0 .. 4` and
`164 .. 166`); the tables' `159` column evaluations stay where the stream holds them, and the
function returns their address (`col_eval_words`).

What it runs is `tablesSeg`: `verifyBusBalance` after the GKR walk (`busRest`), `tablePhase`,
`publicInputPhase`. The bytecode's value is the hinted `bytecode_val` (`BytecodeClaim`, exported by
`verify_sub`): for every `ev` taking that value at the bus's bytecode point, the run is the
specification's.

* `padding_weight_Spec`: `padding_weight__L{τ}(rows, zeta)` (G:2075-2107) holds exactly when
  `rows` is an integer word `n ≤ 2^τ`; it returns `paddingWeight (zeta[..τ]) n` (V:679) and the
  two words whose `lead = 1 ∧ rest ≠ 0` says `τ = log2Ceil n` (`PadLead`, `PadRest`).
* `verify_tables_Spec`: under `TablesPre` (what `verify_sub` establishes before the call), the
  relation gives `TablesOut`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `padding_weight` -/

/-- `lead` of `padding_weight` at `τ`: `1` at `τ = 0`, else bit `τ` of `n` plus bit `τ - 1`. -/
def PadLead (τ n : ℕ) : E := if τ = 0 then 1 else bitE (n.testBit τ) + bitE (n.testBit (τ - 1))

/-- `rest` of `padding_weight` at `τ`: `1` at `τ = 0`, else bit `τ` of `n` plus the word of its
bits below `τ - 1`. -/
def PadRest (τ n : ℕ) : E := if τ = 0 then 1 else bitE (n.testBit τ) + eOfNat (n % 2 ^ (τ - 1))

/-- `padding_weight__L{τ}(rows, zeta)`: `rows` is the word of `n ≤ 2^τ`, and the function returns
`pad_n` at the first `τ` words at `zeta`, `lead` and `rest`. -/
def PadWeightOut (τ : ℕ) (rd : Reader) : List E → List E → Prop
  | [rows, zeta], [pad, lead, rest] =>
      ∃ (n : ℕ) (zs : List E), n ≤ 2 ^ τ ∧ rows = eOfNat n ∧ zs.length = τ ∧
        TbReadsAt rd zeta zs ∧ pad = paddingWeight zs n ∧ lead = PadLead τ n ∧
        rest = PadRest τ n
  | _, _ => False

/-- **`padding_weight`** (G:2075-2107; TRIAGE #51) computes `paddingWeight`: soundness. -/
def padding_weight_Spec : Prop :=
  ∀ n < 33, ∀ rd args rets,
    coreProgram.Rel rd (lName "padding_weight" n) args rets → PadWeightOut n rd args rets

/-- The converse, for completeness: every outcome is a relation's. -/
def padding_weight_complete_Spec : Prop :=
  ∀ n < 33, ∀ rd args rets,
    PadWeightOut n rd args rets → coreProgram.Rel rd (lName "padding_weight" n) args rets

/-! ## The layout -/

/-- The tables' log-heights of the row counts (V:1294): `max (log2Ceil rows) floor`. -/
def tableHeightsOf (rows : List ℕ) : List ℕ :=
  List.zipWith (fun r f ↦ max (log2Ceil r) f) rows tableLogFloors

/-- `buildLayout`'s layout (V:1288), its checks left out: the memory's log-size and the tables'
row counts. -/
def layoutOf (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) : Layout :=
  let logBytecode := Nat.log2 bytecode.length - busBits
  let tableLogHeights := tableHeightsOf tableRows
  let (push, pull, count) := busBlocks tableLogHeights tableRows
  let (placements, stackLog) := placementsOf (columnKappas logMemory logBytecode tableLogHeights)
  ⟨logMemory, logBytecode, bytecode, push, pull, count, placements, stackLog, tableLogHeights⟩

/-! ## The programs -/

/-- `verifyBusBalance` after the GKR walk (V:1492-1513), from its challenges, point and values. -/
def busRest (ev : (List K → List E → VerifierProgram E)) (layout : Layout) (alphas : List E)
    (beta : E)
    (point treeValues : List E) : VerifierProgram BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let weights := eqKernel alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← VerifierProgram.readScalars 3
  let memoryFinal ← VerifierProgram.readScalar
  let bytecodeFinal ← VerifierProgram.readScalar
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let bytecodeValue ← ev layout.bytecode (bytecodeLow ++ alphas)
  let fp := fingerprints weights memory memoryLow bytecodeLow bytecodeValue
  let pcFinal := Verifier.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (Verifier.gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, point, forms3, [total0, total1, total2]⟩

/-- What `verify_tables` runs: the bus after GKR, the table sumcheck and the public input's
binding (V:2307-2311); the bus result and every column claim, the public input's last. -/
def tablesSeg (ev : (List K → List E → VerifierProgram E)) (layout : Layout) (publicInput : Digest) (alphas : List E)
    (beta : E) (point treeValues : List E) : VerifierProgram (BusResult × List ColumnClaim) := do
  let bus ← busRest ev layout alphas beta point treeValues
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase layout publicInput
  return (bus, claims ++ publicClaims)

/-! ## The claims -/

/-- `N_CLAIMS`: the column claims the pool holds. -/
abbrev nClaims : ℕ := 167

/-- The claims before the public input's: `N_CLAIMS - 3`. -/
abbrev nPooled : ℕ := nClaims - 3

/-- The claims' global columns, in `tablesSeg`'s order: the bus's, each table's columns, the
public input's. -/
def claimColumns : List ℕ :=
  [memory0, memory1, memory2, memoryFinalCounters, bytecodeFinalCounters] ++
    tables.flatMap (fun t ↦ (List.range t.width).map (globalColumnBases.getD t.opcode 0 + ·)) ++
    [memory0, memory1, memory2]

/-- `N_BUS_CLAIMS`: the bus's pooled claims, slots `0 .. 4`. -/
abbrev nBusClaims : ℕ := 5

/-- `N_COL_EVALS`: the tables' column evaluations, read where the stream holds them. -/
abbrev nColEvals : ℕ := nPooled - nBusClaims

/-- `CLAIM_KAPPA_SRC` (G:340): a claim's low dimension as a kappa source, an index into
`kappa_base = [g^0, g^log_mem, g^τ_0, …, g^τ_5]` … -/
def claimKappaSrc : List ℕ :=
  [1, 1, 1, 1, 0] ++ List.replicate 15 2 ++ List.replicate 15 3 ++ List.replicate 8 4 ++
    List.replicate 15 5 ++ List.replicate 14 6 ++ List.replicate 92 7 ++ [1, 1, 1]

/-- … plus `CLAIM_KAPPA_ADJ` (G:341): the bytecode claim's `19`. -/
def claimKappaAdj (j : ℕ) : ℕ := if j = 4 then 19 else 0

/-- Claim `j`'s low dimension, `kappa_base[CLAIM_KAPPA_SRC[j]]·g^CLAIM_KAPPA_ADJ[j]` in the exponent,
at the memory's log-size and the tables' log-heights (what `check_opening_terminal` reads,
G:3270). -/
def claimLowDim (logMem : ℕ) (taus : List ℕ) (j : ℕ) : ℕ :=
  (0 :: logMem :: taus).getD (claimKappaSrc.getD j 0) 0 + claimKappaAdj j

/-- **`TCtx`**, what `verify_tables` hands `check_opening_terminal` and `verify_keccak`, over
`[zeta, chi, rm, g_bus_mu, g_zc_n]`: the claims are `claimColumns`'s; the bus's lie on a prefix of
the bus point at `zeta`, the tables' on a prefix of the table sumcheck's point `chis` at `chi`, the
public input's at `(rm, 0, …, 0)`; and the first `164` have the low dimension `claimLowDim` of the
layout (at 40f877dc the terminal derives it from `kappa_base`, where `verify_tables` stored it in
`claim_cplen_g` before). -/
def TCtx (rd : Reader) (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) :
    List E → Prop
  | [zeta, chi, rm, gmu, gzcn] =>
      ∃ chis : List E, TbReadsAt rd zeta bus.point ∧ gmu = gen ^ bus.point.length ∧
        TbReadsAt rd chi chis ∧ gzcn = gen ^ chis.length ∧ chis.length ≤ bus.point.length ∧
        claims.length = nClaims ∧ claims.map (·.column) = claimColumns ∧
        ∀ j (p : List E), (claims.map (·.point))[j]? = some p →
          (j < nPooled → p.length = claimLowDim layout.logMemory layout.tableLogHeights j) ∧
          (j < 5 → p = bus.point.take p.length) ∧
          (5 ≤ j → j < nPooled → p = chis.take p.length) ∧
          (nPooled ≤ j → p = rm :: List.replicate ((layout.placement memory0).variableCount - 1) 0)
  | _ => False

/-! ## `verify_tables` -/

/-- `BLOCK_KAPPA_SRC` (G:126): a bus block's log-height is source `s` of
`kappa_base = [g^0, g^log_mem, g^τ_0, …, g^τ_5]` … -/
def blockKappaSrc : List ℕ :=
  [0, 1, 0, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 0, 1, 0, 2, 2, 2, 2, 2,
    3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 6, 6,
    6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]

/-- … plus `BLOCK_KAPPA_ADJ` (G:127): the bytecode blocks' `19`. -/
def blockKappaAdj (b : ℕ) : ℕ := if b = 2 ∨ b = 56 then 19 else 0

/-- `N_BLOCKS`. -/
abbrev nBlocks : ℕ := 153

/-- `N_BLOCK_GROUPS` (G:130): the runs of a side's blocks sharing one kappa source. -/
abbrev nBlockGroups : ℕ := 24

/-- `BLOCK_GROUP_START` (G:131): each block group's first block, then `N_BLOCKS`. -/
def blockGroupStart : List ℕ :=
  [0, 1, 2, 3, 8, 13, 16, 21, 26, 54, 55, 56, 57, 62, 67, 70, 75, 80, 108, 112, 116, 118, 122, 126,
    153]

/-- `SIDE_GROUP_START` (G:132): each side's first block group, then `N_BLOCK_GROUPS`. -/
def sideGroupStart : List ℕ := [0, 9, 18, 24]

/-- `RANK_KEYS_AT` (G:289): where `exponent_tables` keeps the rank keys, past the squares and the
selector shares. -/
abbrev rankKeysAt : ℕ := 34 + 16 * 9

/-- `SIDE_TAB_AT` (G:292): where `exponent_tables` keeps each block group's side. -/
abbrev sideTabAt : ℕ := rankKeysAt + 34

/-- Block group `gi`'s side (`exponent_tables`, G:732-734), a word. -/
def sideTabList : List E :=
  (List.range nBlockGroups).map fun gi ↦
    eOfNat ((List.range 3).filter (fun s ↦ sideGroupStart.getD s 0 ≤ gi)).length.pred

/-- **What `exponent_tables` leaves at `g_squares` that `verify_tables` reads**: the squares, the
rank keys and the block groups' sides. -/
def ExpTablesAt (rd : Reader) (sq : E) : Prop :=
  TbReadsAt rd sq gSquaresList ∧ TbReadsAt rd (sq * gen ^ rankKeysAt) rankKeysList ∧
    TbReadsAt rd (sq * gen ^ sideTabAt) sideTabList

/-- **What `verify_sub` establishes before `verify_tables`**, for the public input `pi`, the
memory's log-size `logMem`, the bus challenges `alphas`, the GKR point and values: the public
input's cells; the point at `zeta`, `g_bus_mu = g^|point|`; `dims_g = [g^log_mem, …]`; the
exponent tables (`ExpTablesAt`); `fp_w` the equality weights of `alphas`; the three GKR values. -/
def TablesPre (pi : Digest) (logMem : ℕ) (alphas point values : List E) (rd : Reader) :
    List E → Prop
  | [_, _, _, _, _, _, pi0, pi1, zeta, gmu, dims, _, sq, fpw, _, _, _, cpush, cpull, ccount] =>
      (pi0, pi1) = digestHalves pi ∧ TbReadsAt rd zeta point ∧ gmu = gen ^ point.length ∧
      point.length < 33 ∧ 1 ≤ logMem ∧ logMem ≤ 32 ∧
      (∃ ds : List E, ds.length = 6 ∧ TbReadsAt rd dims (gen ^ logMem :: ds)) ∧
      ExpTablesAt rd sq ∧ alphas.length = 4 ∧ TbReadsAt rd fpw (eqKernel alphas) ∧
      values = [cpush, cpull, ccount]
  | _ => False

/-- **`verify_tables`' outcome**: the row counts `rows` are integer words in `table_rows`, and
their log-heights, below `33`, in `dims_g`; for the layout they give and every `ev` taking `bv`
for the bytecode at `(point[..logBytecode], alphas)`, from the carried capacity the words `xs`
at the cursor run `tablesSeg` to the bus result and the `167` column claims, the bus's five
values and the public input's three in `claim_pool` (slots `0 .. 4`, `162 .. 164`) and the
tables' `159` at `col_eval_words`; `TCtx` holds of them; and the function returns the new
capacity, the cursor past `xs`, `g^n` (the table sumcheck's rounds), `bv`, the public input's
challenge and `col_eval_words`. -/
def TablesOut (bytecode : List K) (pi : Digest) (logMem : ℕ) (alphas point values : List E)
    (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, _, _, zeta, gmu, dims, rows, _, _, beta, pool, chi, _, _, _],
      [f0', f1', f2', f3', f4', cur', gzcn, bv, rm, cew] =>
      ∃ (xs cap' : List E) (rowsN : List ℕ) (bus : BusResult) (claims : List ColumnClaim),
        rowsN.length = 6 ∧ TbReadsAt rd rows (rowsN.map eOfNat) ∧
        TbReadsAt rd dims (gen ^ logMem :: (tableHeightsOf rowsN).map (gen ^ ·)) ∧
        (∀ h ∈ tableHeightsOf rowsN, h < 33) ∧ TbReadsAt rd cur xs ∧
        (∀ ev, BytecodeAt ev bytecode
            (point.take (layoutOf bytecode logMem rowsN).logBytecode ++ alphas) bv →
          RunsTo (tablesSeg ev (layoutOf bytecode logMem rowsN) pi alphas beta point values)
            ⟨[f0, f1, f2, f3, f4], []⟩ xs (bus, claims) ⟨cap', []⟩) ∧
        claims.length = nClaims ∧ TbReadsAt rd pool ((claims.take nBusClaims).map (·.value)) ∧
        TbReadsAt rd cew (((claims.drop nBusClaims).take nColEvals).map (·.value)) ∧
        TbReadsAt rd (pool * gen ^ nPooled) ((claims.drop nPooled).map (·.value)) ∧
        TCtx rd (layoutOf bytecode logMem rowsN) bus claims [zeta, chi, rm, gmu, gzcn] ∧
        [f0', f1', f2', f3', f4'] = cap' ∧ cur' = cur * gen ^ xs.length
  | _, _ => False

/-- **`verify_tables` is sound** (G:2109-2535; TRIAGE #52), for the guest's own bytecode words
`bytecode`. Proved for every memory of at most `2^32` words (`verify_tables_holds`). -/
def verify_tables_Spec (bytecode : List K) (rd : Reader) : Prop :=
  ∀ pi logMem alphas point values args rets,
    TablesPre pi logMem alphas point values rd args →
    coreProgram.Rel rd "verify_tables" args rets →
      TablesOut bytecode pi logMem alphas point values rd args rets

end
end LeanVM.Guest.B1.Tables
