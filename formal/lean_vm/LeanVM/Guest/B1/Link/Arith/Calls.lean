/-
  LeanVM.Guest.B1.Link.Arith.Calls

  The link section's reads from its callees and the transcript, and its terminal check: the
  statements the `verify_sub` assembly applies.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Section
public import LeanVM.Guest.B1.Link.Ends
public import LeanVM.Guest.B1.Link.IndexSide
public import LeanVM.Guest.B1.Link.TablePoint
public import LeanVM.Guest.B1.Link.Suffixes
public import LeanVM.Guest.B1.Link.SqueezePacked
public import LeanVM.Guest.B1.Link.Terminal

/-!
# The link section, from its callees

`LinkFacts`: what the assembly of `verify_sub` holds when it reaches the link section's end: the
shape it runs at, the values it reads from before it (`g_n`, `g_w`, `g^log_mem`, the heights, the
row and cycle bits), the callees' relations at their call sites (`squeeze_packed`, `state_ends`,
`index_side`, the six `table_point`s, `one_plus_suffixes`), and the transcript's values (`θ_0` the
grind's challenge, the drawn challenges the packed squeeze's first `linkDrawn` cells, the index
point at `r_pt`, `m1` the stream word at the rounds' cursor, the fresh coefficients the
permutation's cells, `χ` at `chi`, the pointer columns' point at `q_point`, the split values at
`splitv`, the message at the row side's cursor). `TerminalFacts`: `link_terminal`'s relation at
its dispatch, the claim, the bit-slices.

* `ReadsOfFacts`: then the section's reads are `tailIn`'s (`IRReads`), so `linkSecStatement`
  applies;
* `TerminalOfFacts`: with the terminal's facts, `linkTailR`'s terminal check holds (`TailCheck`),
  the proposition `linkTailR` requires, so `linkTail`'s (`linkTailEq`).
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Guest.B1.Link

@[expose] public section

/-- The row bits' pointers, `rows_bits·g^(ROW_BITS·t)` (`table_size`'s and `table_point`'s). -/
def bitsVn : List ℕ := [7, 159, 175, 191, 207, 223]

/-- `table_point`'s arguments at table `t`: `theta[t]`, `tau`, `bits_t`. -/
def tpThetaVn : List ℕ := [1293, 1403, 1524, 1607, 1734, 1880]

def tpTauVn : List ℕ := [1295, 1405, 1526, 1609, 1736, 1882]

def tpBitsVn : List ℕ := [7, 1407, 1528, 1611, 1738, 1884]

/-- What the assembly holds at the link section's end. -/
structure LinkFacts (rd : Reader) (σ : Val) (layout : Layout) (chunks : Chunks) (theta0 : E)
    (drawn r : List E) (m1 : E) (fresh splitv chi qPoint message : List E) (p : ℕ) : Prop where
  /-- The shape: the pointer width, the heights, the memory. -/
  widthGe : 19 ≤ chunks.width
  widthLe : chunks.width ≤ 24
  heightsLe : ∀ t < 6, layout.tableLogHeights.getD t 0 ≤ linkRows layout
  rowsLe : linkRows layout ≤ 24
  logMemoryLe : layout.logMemory ≤ chunks.width
  tableRowsLe : ∀ t < 6, layout.tableRows.getD t 0 ≤ 2 ^ layout.tableLogHeights.getD t 0
  /-- The values read from before the section: `g_n`, `g_w`, `g^log_mem`, the heights `kb[2 + t]`,
  the row bits' pointers, each table's row bits (`table_size`'s), the cycles' bits. -/
  gN : σ (.n 408) = gen ^ linkRows layout
  gW : σ (.n 409) = gen ^ chunks.width
  gMem : σ (.n 101) = gen ^ layout.logMemory
  gH : ∀ t < 6, σ (.n (115 + t)) = gen ^ layout.tableLogHeights.getD t 0
  bitsPtr : ∀ t < 5, σ (.n (bitsVn.getD (t + 1) 0)) = σ (.n (bitsVn.getD t 0)) * word 67108864 0
  rowBits : ∀ t < 6, ReadsAt rd (σ (.n (bitsVn.getD t 0)))
      (cbitsE (layout.tableRows.getD t 0) (layout.tableLogHeights.getD t 0)) ∧
    LoadHolds rd (σ (.n (bitsVn.getD t 0))) (layout.tableLogHeights.getD t 0)
      (bitE (layout.tableRows.getD t 0) (layout.tableLogHeights.getD t 0))
  cycleBits : ReadsAt rd (σ (.n 8)) (bitsE (linkCycles layout) chunks.width)
  /-- The callees, at their call sites. -/
  squeeze : coreProgram.Rel rd "squeeze_packed"
    [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579), σ (.n 679), σ (.n 645)]
    [σ (.n 680), σ (.n 681), σ (.n 682), σ (.n 683), σ (.n 684)]
  stateEnds : coreProgram.Rel rd (seNames.getD (chunks.width - 19) "") [σ (.n 694), σ (.n 8)]
    [σ (.n 752), σ (.n 753)]
  indexSide : coreProgram.Rel rd (isNames.getD (chunks.width - 19) "")
    [σ (.n 12), σ (.n 694), σ (.n 13)] [σ (.n 797), σ (.n 798), σ (.n 799)]
  tablePoint : ∀ t < 6, coreProgram.Rel rd (tpNames.getD (layout.tableLogHeights.getD t 0) "")
    [σ (.n (tpThetaVn.getD t 0)), σ (.n (tpTauVn.getD t 0)), σ (.n 15), σ (.n (tpBitsVn.getD t 0))]
    [σ (.n (omegaVn.getD t 0)), σ (.n (omegaVn.getD t 0 + 1)), σ (.n (omegaVn.getD t 0 + 2))]
  suffixes : coreProgram.Rel rd (opsNames.getD (linkRows layout) "") [σ (.n 18), σ (.n 15)]
    [σ (.n 1286)]
  /-- The transcript's values. -/
  theta : σ (.n 573) = theta0
  count : σ (.n 645) = gen ^ p
  countLt : p < 64
  drawnEq : drawn = ((pkSqueeze p [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579)]).1).take
    (linkDrawn layout chunks)
  drawnLe : linkDrawn layout chunks ≤ 8 * p
  point : ReadsAt rd (σ (.n 12)) r
  pointLen : r.length = chunks.width
  memTerm : rdw rd (σ (.n 772)) 0 = m1
  freshEq : fresh = [σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785), σ (.n 786)]
  rowPoint : ReadsAt rd (σ (.n 15)) chi
  rowPointLen : chi.length = linkRows layout
  qPointAt : ReadsAt rd (σ (.n 16)) qPoint
  splitAt : ∀ k < 36, rdw rd (σ (.n 14)) k = splitv.getD k 0
  messageAt : ∀ k < 80, rdw rd (σ (.n 1076)) k = message.getD k 0

/-- What the assembly holds of `link_terminal`'s dispatch: its relation at the pointer width, the
claim the row side's sum-check leaves, the bit-slices the message carries after its `80` values. -/
structure TerminalFacts (rd : Reader) (σ : Val) (chunks : Chunks) (message : List E) (claim : E) :
    Prop where
  chunksEq : Chunks.new chunks.width = some chunks
  terminal : coreProgram.Rel rd (ltNames.getD (chunks.width - 19) "")
    [σ (.n 12), σ (.n 1076), σ (.n 2846), σ (.n 19), σ (.n 2891), σ (.n 695), σ (.n 2890), σ (.n 1077)]
    [σ (.n 2894)]
  claimEq : σ (.n 1077) = claim
  messageLen : message.length = 144
  slices : ∀ k < 64, LoadHolds rd (σ (.n 1076)) (80 + k) (message.getD (80 + k) 0)

/-- `linkTailR`'s terminal check, the proposition it requires. -/
def TailCheck (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (chi qPoint message : List E) (claim : E) : Prop :=
  let L := tailLets layout chunks theta0 drawn r m1 fresh split qPoint
  let maxShift := layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  let nValues := tailNValues layout
  let slices := message.drop nValues
  let rowSide := tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message
  let functionals := Functionals.new chunks r maxShift
  let values := functionals.values chunks slices
  let eq0Q := prodE (qPoint.map (1 + ·))
  let certs := L.nu.map fun n ↦ L.cert * rowSide.certWeight * n
  functionals.summand rowSide.coef rowSide.shifts values certs + eq0Q * rowSide.base = claim

/-- **The section's reads are the Statement's values.** -/
def ReadsOfFacts : Prop :=
  ∀ (rd : Reader) (σ : Val) (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E)
    (m1 : E) (fresh splitv chi qPoint message : List E) (p : ℕ),
    (∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ) → TailShape layout drawn fresh splitv qPoint message →
    layout.logBytecode = guest_const% BYTECODE_LOG →
    LinkFacts rd σ layout chunks theta0 drawn r m1 fresh splitv chi qPoint message p →
    IRReads rd σ (tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message)

/-- **The terminal check holds.** -/
def TerminalOfFacts : Prop :=
  ∀ (rd : Reader) (σ : Val) (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E)
    (m1 : E) (fresh splitv chi qPoint message : List E) (p : ℕ) (claim : E),
    (∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ) → TailShape layout drawn fresh splitv qPoint message →
    layout.logBytecode = guest_const% BYTECODE_LOG →
    LinkFacts rd σ layout chunks theta0 drawn r m1 fresh splitv chi qPoint message p →
    TerminalFacts rd σ chunks message claim →
    TailCheck layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) chi qPoint message
      claim

end

end LeanVM.Guest.B1.Link.Arith
