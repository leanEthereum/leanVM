module

public import LeanVM.Cost.Decoder.Da
public import LeanVM.Guest.Fast.Search
import all LeanVM.Guest.B1.Main.Interface
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# The guest decoder's compiled chain: the children

A child's statement, read off the coverage table (`kidStmt`), and the child itself (`decKid`, its
proof by the reader `wV`); the coverage marks and counts (`markOf`, `countOf`, `slotOf`,
`segCount`) and the regions' sizes (`lxSlots`, `lsSlots`).
Each reads its logarithms by `gLogD D` (`Log.lean`), the logarithm's tables `D` given: `…D`
restates `B1.Main`'s function so, and `…D_tables` is the equation at `D = discreteLogTables`.

The searches are not compiled as written (a scan of a region per query, quadratic in the counts):
tables built once by the caller (`Staged.lean`) answer them, on every input
(`Guest/Fast/Search.lean`):

* `regionTable D rd cover lo len`: the region's marks (one logarithm per slot) sorted with their
  slots (`coverTable`); `slotIn` of it is `slotOfD` (`slotIn_regionTable`), `countIn` of it
  `segCountD` (`countIn_regionTable`), `kidSlotsIn` of it `kidSlotsD` (`kidSlotsIn_regionTable`:
  a gap-walked list's slots, all of the list's first mark, are a run of the table, in slot order);
* `kidStmtT`, `decKidT`: a child's statement and the child off the two regions' tables, `main`'s
  words the loops read (`written`, the tables' pointers) passed as values, the slots' addresses by
  powers in `K` (`xmssSlotClaim`); `kidStmtT_eq`, `decKidT_eq`: at the tables built they are `kidStmtD`,
  `decKidD`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast LeanVM.Guest.Fast

@[expose] public section

/-! ## The marks, the counts, the sizes -/

/-- The mark in coverage slot `s` (`markOf`). -/
noncomputable def markOfD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (s : ℕ) : ℕ :=
  gLogD D (cellAt rd (σ (.n 45)) s)

/-- The running count `written[c]` (`countOf`). -/
noncomputable def countOfD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (c : ℕ) : ℕ :=
  gLogD D (cellAt rd (σ (.n 399)) c)

/-- The number of children (`nKids`). -/
def nKidsD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n 6))

/-- The regions' sizes (`lxSlots`, `lsSlots`). -/
def lxSlotsD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n 22))
def lsSlotsD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n 23))

theorem markOfD_tables : markOfD discreteLogTables = markOf := by
  funext rd σ s; unfold markOfD markOf; rw [gLogD_tables]
theorem countOfD_tables : countOfD discreteLogTables = countOf := by
  funext rd σ c; unfold countOfD countOf; rw [gLogD_tables]
theorem nKidsD_tables : nKidsD discreteLogTables = nKids := by
  funext σ; unfold nKidsD nKids; rw [gLogD_tables]
theorem lxSlotsD_tables : lxSlotsD discreteLogTables = lxSlots := by
  funext σ; unfold lxSlotsD lxSlots; rw [gLogD_tables]
theorem lsSlotsD_tables : lsSlotsD discreteLogTables = lsSlots := by
  funext σ; unfold lsSlotsD lsSlots; rw [gLogD_tables]

cost_compile markOfC := markOfD
cost_compile countOfC := countOfD
cost_compile nKidsC := nKidsD
cost_compile lxSlotsC := lxSlotsD
cost_compile lsSlotsC := lsSlotsD

/-! ## A child -/

/-- The slot of the region `[lo, lo + len)` holding the mark `e` (`slotOf`). -/
noncomputable def slotOfD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len e : ℕ) : ℕ :=
  ((List.range len).find? fun s => decide (markOfD D rd σ (lo + s) = e)).getD 0

/-- The number of slots of the region `[lo, lo + len)` whose marks lie in `[a, b)` (`segCount`). -/
noncomputable def segCountD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len a b : ℕ) : ℕ :=
  ((List.range len).filter fun s =>
    decide (a ≤ markOfD D rd σ (lo + s) ∧ markOfD D rd σ (lo + s) < b)).length

/-- A child's list's slots in the region `[lo, lo + len)`, its marks in `[a, b)` (`kidSlots`). -/
noncomputable def kidSlotsD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len a b : ℕ) :
    List ℕ :=
  if segCountD D rd σ lo len a (a + 1) = segCountD D rd σ lo len a b then
    (List.range len).filter fun s => decide (a ≤ markOfD D rd σ (lo + s) ∧ markOfD D rd σ (lo + s) < b)
  else (List.range (segCountD D rd σ lo len a b)).map fun j => slotOfD D rd σ lo len (a + j)

/-- **Child `c`'s statement** (`kidStmt`). -/
noncomputable def kidStmtD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (c : ℕ) :
    NodeStatement :=
  let a := countOfD D rd σ c
  let b := countOfD D rd σ (c + 1)
  let nx := segCountD D rd σ 0 (lxSlotsD D σ) a b
  ⟨⟨(kidSlotsD D rd σ 0 (lxSlotsD D σ) a b).map (xmssAt rd (σ (.n 31))),
    (kidSlotsD D rd σ (lxSlotsD D σ) (lsSlotsD D σ) (a + nx) b).map (sphincsAt rd (σ (.n 34))),
    daDigestAt rd σ c⟩,
   deferOfCells (readCells rd (σ (.n 396) * gen ^ (24 * c)) 24)⟩

/-- **Child `c`** (`decKid`). -/
noncomputable def decKidD (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (c : ℕ) : Child :=
  ⟨kidStmtD D rd σ c, fixedOfCells (readCells rd (σ (.n 390) * gen ^ (24 * c)) 24),
    wV (subArgs rd σ c)⟩

theorem slotOfD_tables : slotOfD discreteLogTables = slotOf := by
  funext rd σ lo len e; unfold slotOfD slotOf; rw [markOfD_tables]
theorem segCountD_tables : segCountD discreteLogTables = segCount := by
  funext rd σ lo len a b; unfold segCountD segCount; rw [markOfD_tables]
theorem kidSlotsD_tables : kidSlotsD discreteLogTables = kidSlots := by
  funext rd σ lo len a b; unfold kidSlotsD kidSlots
  rw [markOfD_tables, segCountD_tables, slotOfD_tables]
theorem kidStmtD_tables : kidStmtD discreteLogTables = kidStmt := by
  funext rd σ c
  unfold kidStmtD kidStmt
  rw [countOfD_tables, segCountD_tables, lxSlotsD_tables, lsSlotsD_tables, kidSlotsD_tables]
theorem decKidD_tables : decKidD discreteLogTables = decKid := by
  funext rd σ wV c; unfold decKidD decKid; rw [kidStmtD_tables]



/-! ## The searches' compiled pieces -/

section Tables

attribute [local instance] lexOrd

cost_compile lowerBoundC measure fun _ _ lo hi ↦ hi - lo := lowerBound
cost_compile mergeNewerCoverC measure fun a b ↦ a.length + b.length := @mergeNewer (ℕ × ℕ) ℕ _
cost_compile levelMergeCoverC := @Level.merge (ℕ × ℕ) ℕ _ _ _
cost_compile carryCoverC measure fun _ ls ↦ ls.length := @carry (ℕ × ℕ) ℕ _ _ _
cost_compile insertCoverC := @SortedMap.insert (ℕ × ℕ) ℕ _ _ _
cost_compile coverInsertC := coverInsert
cost_compile mergeLevelC := mergeLevel
cost_compile flattenLevelsC := flattenLevels
cost_compile coverKeysC := coverKeys
cost_compile coverTableC := coverTable
cost_compile slotInC := slotIn
cost_compile countInC := countIn
cost_compile slotsInC := slotsIn
cost_compile kidSlotsInC := kidSlotsIn

end Tables

/-! ## The coverage tables -/

/-- A mark and its slot. -/
def markPairOf (m s : ℕ) : ℕ × ℕ := (m, s)

/-- Slot `s` of the region from `lo` of the coverage table at `cover`: its mark (a logarithm) and
`s`. -/
noncomputable def markPair (D : DiscreteLogTables) (rd : Reader) (cover : E) (lo s : ℕ) : ℕ × ℕ :=
  markPairOf (gLogD D (cellAt rd cover (lo + s))) s

/-- **The coverage table of the region `[lo, lo + len)`**: its marks sorted, with their slots
(`coverTable`), each mark read once. -/
noncomputable def regionTable (D : DiscreteLogTables) (rd : Reader) (cover : E) (lo len : ℕ) :
    Array ℕ × Array ℕ :=
  coverTable ((List.range len).map (markPair D rd cover lo))

theorem regionTable_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len : ℕ) :
    regionTable D rd (σ (.n 45)) lo len =
      coverTable (regionPairs (fun s ↦ markOfD D rd σ (lo + s)) len) := rfl

/-- **The table's first slot is `slotOf`'s.** -/
theorem slotIn_regionTable (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len e : ℕ) :
    slotIn (regionTable D rd (σ (.n 45)) lo len).1 (regionTable D rd (σ (.n 45)) lo len).2 e =
      slotOfD D rd σ lo len e := by
  rw [regionTable_eq, slotIn_coverTable]; rfl

/-- **The table's count is `segCount`'s.** -/
theorem countIn_regionTable (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len a b : ℕ) :
    countIn (regionTable D rd (σ (.n 45)) lo len).1 a b = segCountD D rd σ lo len a b := by
  rw [regionTable_eq, countIn_coverTable]; rfl

/-- **The table's child list is `kidSlots`'.** -/
theorem kidSlotsIn_regionTable (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len a b : ℕ) :
    kidSlotsIn (regionTable D rd (σ (.n 45)) lo len).1 (regionTable D rd (σ (.n 45)) lo len).2 a b =
      kidSlotsD D rd σ lo len a b := by
  rw [regionTable_eq, kidSlotsIn_coverTable]; rfl

/-- The running count `written[c]` at `w = written` (`countOf`). -/
noncomputable def countAtW (D : DiscreteLogTables) (rd : Reader) (w : E) (c : ℕ) : ℕ := gLogD D (cellAt rd w c)

cost_compile markPairOfC := markPairOf
cost_compile markPairC := markPair
cost_compile regionTableC := regionTable
cost_compile countAtWC := countAtW

/-! ## A child, off the tables -/

/-- The leanXMSS claim of slot `s` of the table at `p52` (`xmssAt`, the slot's address by a power
in `K`). -/
noncomputable def xmssSlotClaim (rd : Reader) (p52 : E) (s : ℕ) : LeanXmssClaim :=
  xmssAtK rd (p52.limb 0 * Parameters.g ^ (4 * s))

/-- The leanSPHINCS claim of slot `s` of the table at `p55` (`sphincsAt`). -/
noncomputable def sphincsSlotClaim (rd : Reader) (p55 : E) (s : ℕ) : LeanSphincsClaim :=
  sphincsAtK rd (p55.limb 0 * Parameters.g ^ (4 * s))

/-- Child `c`'s statement, its lists' slots `sx`, `ss` given. -/
noncomputable def kidStmtAt (rd : Reader) (σ : Val) (p52 p55 : E) (c : ℕ) (sx ss : List ℕ) :
    NodeStatement :=
  ⟨⟨sx.map (xmssSlotClaim rd p52), ss.map (sphincsSlotClaim rd p55), daDigestAt rd σ c⟩,
   deferOfCells (readCellsK rd ((σ (.n 396)).limb 0 * Parameters.g ^ (24 * c)) 24)⟩

/-- Child `c`'s statement, its segment `[a, b)` given: its lists' slots off the tables
(`kidSlotsIn`), the leanSPHINCS list's from the mark after the leanXMSS ones. -/
noncomputable def kidStmtSeg (rd : Reader) (σ : Val) (p52 p55 : E) (tx ts : Array ℕ × Array ℕ)
    (c a b : ℕ) : NodeStatement :=
  kidStmtAt rd σ p52 p55 c (kidSlotsIn tx.1 tx.2 a b) (kidSlotsIn ts.1 ts.2 (a + countIn tx.1 a b) b)

/-- **Child `c`'s statement** (`kidStmt`), off the regions' tables `tx`, `ts`, `written` at
`w380` and the tables at `p52`, `p55`: its segment's ends (logarithms) read here. -/
noncomputable def kidStmtT (D : DiscreteLogTables) (rd : Reader) (σ : Val) (w380 p52 p55 : E)
    (tx ts : Array ℕ × Array ℕ) (c : ℕ) : NodeStatement :=
  kidStmtSeg rd σ p52 p55 tx ts c (countAtW D rd w380 c) (countAtW D rd w380 (c + 1))

/-- The words of child `c`'s `verify_sub` call (`subArgs`), its proof's claim's address by a
power in `K`. -/
noncomputable def subArgsK (rd : Reader) (σ : Val) (c : ℕ) : List E :=
  [cellAt rd (σ (.n 384)) (2 * c), cellAt rd (σ (.n 384)) (2 * c + 1), σ (.n 26), σ (.n 27),
    σ (.n 28), mulK (σ (.n 390)) (Parameters.g ^ (24 * c))]

/-- **Child `c`** (`decKid`), off the regions' tables. -/
noncomputable def decKidT (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (w380 p52 p55 : E) (tx ts : Array ℕ × Array ℕ)
    (c : ℕ) : Child :=
  ⟨kidStmtT D rd σ w380 p52 p55 tx ts c,
    fixedOfCells (readCellsK rd ((σ (.n 390)).limb 0 * Parameters.g ^ (24 * c)) 24),
    wV (subArgsK rd σ c)⟩

/-- The two regions' tables, as `decWit`'s caller builds them. -/
noncomputable abbrev lxTable (D : DiscreteLogTables) (rd : Reader) (σ : Val) : Array ℕ × Array ℕ :=
  regionTable D rd (σ (.n 45)) 0 (lxSlotsD D σ)
noncomputable abbrev lsTable (D : DiscreteLogTables) (rd : Reader) (σ : Val) : Array ℕ × Array ℕ :=
  regionTable D rd (σ (.n 45)) (lxSlotsD D σ) (lsSlotsD D σ)

theorem xmssSlotClaim_eq (rd : Reader) (p : E) : xmssSlotClaim rd p = xmssAt rd p := by
  funext s; rw [xmssSlotClaim, xmssAt_eq_K]

theorem sphincsSlotClaim_eq (rd : Reader) (p : E) : sphincsSlotClaim rd p = sphincsAt rd p := by
  funext s; rw [sphincsSlotClaim, sphincsAt_eq_K]

/-- **Off the tables built, child `c`'s statement is `kidStmtD`'s.** -/
theorem kidStmtT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val) (c : ℕ) :
    kidStmtT D rd σ (σ (.n 399)) (σ (.n 31)) (σ (.n 34)) (lxTable D rd σ) (lsTable D rd σ) c =
      kidStmtD D rd σ c := by
  unfold kidStmtT kidStmtSeg kidStmtAt kidStmtD
  rw [countIn_regionTable, kidSlotsIn_regionTable, kidSlotsIn_regionTable, xmssSlotClaim_eq,
    sphincsSlotClaim_eq, ← readCells_mul_gen_pow]
  rfl

/-- **Off the tables built, child `c` is `decKidD`'s.** -/
theorem decKidT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (c : ℕ) :
    decKidT D rd σ wV (σ (.n 399)) (σ (.n 31)) (σ (.n 34)) (lxTable D rd σ) (lsTable D rd σ) c =
      decKidD D rd σ wV c := by
  unfold decKidT decKidD subArgsK subArgs
  rw [kidStmtT_eq, ← readCells_mul_gen_pow, mulK_gen_pow]

cost_compile xmssSlotClaimC := xmssSlotClaim
cost_compile sphincsSlotClaimC := sphincsSlotClaim
cost_compile kidStmtAtC := kidStmtAt
cost_compile kidStmtSegC := kidStmtSeg
cost_compile kidStmtC := kidStmtT
cost_compile subArgsC := subArgsK
cost_compile decKidC := decKidT

end

end LeanVM.Cost.Decoder
