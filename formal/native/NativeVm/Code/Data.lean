module

public import NativeVm.Transcript.Mem
public import NativeVm.Model.Verify
public import NativeVm.Field.Basic
public import NativeVm.Wire.Code

/-!
# The values the phases hand on, in the working area

Every value the model (`NativeVm.Model.verifyExecution`) passes from one phase to a later one has a
fixed place in the working area (context word `10`), after the transcript's `Transcript.workWords`
words: a **region** (`Region`, an offset and a size in words), laid end to end in the order below.
The decoder (`Wire.decode`) uses the area's first `Wire.workWords` words only while it runs and the
seed its first `bytecode length + 2`, both before any region is written, so the regions may overlap
them; the area holds `workWords n` words for a bytecode of `n` words.

| region | holds | written by |
|---|---|---|
| `layoutR` | `LayoutAt`: phase 1's layout and rate exponent | 1 |
| `oodR` | `EqClaimAt`: the stack's out-of-domain claim | 2 |
| `busR` | `BusAt`: the bus's forms, GKR point and totals | 3 |
| `evalsR` | `EvalsAt`: each table's point and evaluations | 4 |
| `claimsR` | `ClaimsAt`: the column claims, appended by phases 3 to 6 | 3, 4, 5, 6 |
| `keccakR` | `KeccakOutAt`: `q_keccak`'s point and its 64 slices | 6 |
| `ringR` | `RingAt`: the ring switch's target and coefficients | 7 |
| `basisR` | `BasisAt`: the batching scales | 7 |
| `whirR` | `WhirAt`: WHIR's running claim, its `α`s and the glued claims | 7 |
| `roundsR` | `RoundsAt`: a level's fold rounds | 7 |
| `queriesR` | `WVec`: a level's query positions | 7 |
| `rowsR` | `RowsAt`: the rows a query opens (`Transcript.query`'s output) | 7 |
| `scratchR` | any phase's scratch: sumcheck messages and challenges, GKR state, the Keccak layers' weight vectors | all |

**Encodings.** A number is one word (`NatAt`); an `E` element two, limb `0` first (`EWAt`, the
convention of `NativeVm.Field`'s `EAt`, `EWArr_iff_EArr`); an array a count word then its entries at
a fixed stride up to a capacity (`EVec`, `WVec`, `ClaimsAt`, `FormAt`). Every capacity is the
protocol's maximum (`stackCap`, `pointCap`, `claimCap`, `formCap`, ...; each says where it comes
from), so a region's size is a constant.

**Disjointness.** The regions are pairwise apart (`regions_apart`) and inside the area
(`dataEnd ≤ workWords n`); a predicate reads only its region's words, so it survives any run that
keeps them (`LayoutAt.congr`, ..., from `Same`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wd_add wd_zero)

/-! ## Words -/

/-- `mem` and `mem'` agree on the `n` words at `p`. -/
def Same (mem mem' : UInt64 → Option UInt64) (p : UInt64) (n : Nat) : Prop :=
  ∀ k < n, mem' (wd p k) = mem (wd p k)

theorem wd_wd (p : UInt64) (a k : Nat) : wd (wd p a) k = wd p (a + k) := wd_add p a k

theorem Same.sub {mem mem' : UInt64 → Option UInt64} {p : UInt64} {n : Nat} (h : Same mem mem' p n)
    {a m : Nat} (ha : a + m ≤ n) : Same mem mem' (wd p a) m := fun k hk ↦ by
  rw [wd_wd]
  exact h (a + k) (by omega)

theorem Same.word {mem mem' : UInt64 → Option UInt64} {p : UInt64} {n : Nat} (h : Same mem mem' p n)
    {k : Nat} (hk : k < n) {v : Option UInt64} (hv : mem (wd p k) = v) : mem' (wd p k) = v := by
  rw [h k hk, hv]

theorem Same.base {mem mem' : UInt64 → Option UInt64} {p : UInt64} {n : Nat} (h : Same mem mem' p n)
    (hn : 0 < n) {v : Option UInt64} (hv : mem p = v) : mem' p = v := by
  have := h 0 hn
  rw [wd_zero] at this
  rw [this, hv]

/-- The number `n` in the word at `a`. -/
def NatAt (mem : UInt64 → Option UInt64) (a : UInt64) (n : Nat) : Prop :=
  n < 2 ^ 64 ∧ mem a = some n.toUInt64

/-- The element `x` in the two words at `p`, limb `0` first. -/
def EWAt (mem : UInt64 → Option UInt64) (p : UInt64) (x : EW) : Prop :=
  mem p = some x.c0 ∧ mem (wd p 1) = some x.c1

/-- The elements `xs` from `p`, element `i` in words `2 i`, `2 i + 1`. -/
def EWArr (mem : UInt64 → Option UInt64) (p : UInt64) (xs : Array EW) : Prop :=
  ∀ i (h : i < xs.size), EWAt mem (wd p (2 * i)) xs[i]

/-- The words `xs` from `p`. -/
def WordArr (mem : UInt64 → Option UInt64) (p : UInt64) (xs : Array UInt64) : Prop :=
  ∀ i (h : i < xs.size), mem (wd p i) = some xs[i]

/-- The words of an array of at most `cap` elements of `E`: the count, then the elements. -/
def vecWords (cap : Nat) : Nat := 1 + 2 * cap

/-- At most `cap` elements of `E` at `p`: the count, then the elements from word `1`. -/
def EVec (mem : UInt64 → Option UInt64) (p : UInt64) (cap : Nat) (xs : Array EW) : Prop :=
  xs.size ≤ cap ∧ NatAt mem p xs.size ∧ EWArr mem (wd p 1) xs

/-- The words of an array of at most `cap` words: the count, then the words. -/
def wvecWords (cap : Nat) : Nat := 1 + cap

/-- At most `cap` words at `p`: the count, then the words from word `1`. -/
def WVec (mem : UInt64 → Option UInt64) (p : UInt64) (cap : Nat) (xs : Array UInt64) : Prop :=
  xs.size ≤ cap ∧ NatAt mem p xs.size ∧ WordArr mem (wd p 1) xs

theorem lane_ofLane (w : UInt64) : (K.ofLane w).lane = w := (rfl)

theorem EW.toE_limb0 (x : EW) : (x.toE.limb 0).lane = x.c0 := by
  rw [show x.toE = Field.eOf x.c0 x.c1 from rfl, Field.limb0_eOf]
  rfl

theorem EW.toE_limb1 (x : EW) : (x.toE.limb 1).lane = x.c1 := by
  rw [show x.toE = Field.eOf x.c0 x.c1 from rfl, Field.limb1_eOf]
  rfl

/-- An element in two words is `NativeVm.Field`'s `EAt` of its value. -/
theorem EWAt_iff_EAt {mem : UInt64 → Option UInt64} {p : UInt64} {x : EW} :
    EWAt mem p x ↔ Field.EAt mem p x.toE := by
  rw [EWAt, Field.EAt, EW.toE_limb0, EW.toE_limb1]
  rfl

/-- An array of elements is `NativeVm.Field`'s `EArr` of their values. -/
theorem EWArr_iff_EArr {mem : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW} :
    EWArr mem p xs ↔ Field.EArr mem p (xs.toList.map EW.toE) := by
  have e : ∀ i, wd p (2 * i) = p + (16 * i).toUInt64 := fun i ↦ by
    rw [wd, show 8 * (2 * i) = 16 * i by omega]
  constructor
  · intro h i hi
    rw [List.length_map, Array.length_toList] at hi
    have := EWAt_iff_EAt.mp (h i hi)
    rw [e] at this
    simpa using this
  · intro h i hi
    have := h i (by simpa using hi)
    rw [EWAt_iff_EAt, e]
    simpa using this

theorem NatAt.congr {mem mem' : UInt64 → Option UInt64} {a : UInt64} {n : Nat}
    (h : mem' a = mem a) (hx : NatAt mem a n) : NatAt mem' a n := ⟨hx.1, h ▸ hx.2⟩

theorem EWAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {x : EW}
    (h : Same mem mem' p 2) (hx : EWAt mem p x) : EWAt mem' p x :=
  ⟨h.base (by omega) hx.1, h.word (by omega) hx.2⟩

theorem EWArr.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW} {n : Nat}
    (h : Same mem mem' p n) (hn : 2 * xs.size ≤ n) (hx : EWArr mem p xs) : EWArr mem' p xs :=
  fun i hi ↦ (hx i hi).congr (h.sub (by omega))

theorem WordArr.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {xs : Array UInt64} {n : Nat}
    (h : Same mem mem' p n) (hn : xs.size ≤ n) (hx : WordArr mem p xs) : WordArr mem' p xs :=
  fun i hi ↦ h.word (by omega) (hx i hi)

theorem EVec.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {cap : Nat} {xs : Array EW}
    (h : Same mem mem' p (vecWords cap)) (hx : EVec mem p cap xs) : EVec mem' p cap xs :=
  ⟨hx.1, hx.2.1.congr (h.base (by unfold vecWords; omega) rfl),
    hx.2.2.congr (h.sub (a := 1) (m := 2 * cap) (by unfold vecWords; omega))
      (by have := hx.1; omega)⟩

theorem WVec.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {cap : Nat} {xs : Array UInt64}
    (h : Same mem mem' p (wvecWords cap)) (hx : WVec mem p cap xs) : WVec mem' p cap xs :=
  ⟨hx.1, hx.2.1.congr (h.base (by unfold wvecWords; omega) rfl),
    hx.2.2.congr (h.sub (a := 1) (m := cap) (by unfold wvecWords; omega)) hx.1⟩

/-! ## Capacities

Each is the protocol's maximum, from the statement's constants (`Statement/LeanVmVerifier.lean`)
or the checks a phase makes before it stores. -/

/-- Points on the stack: at most `maxLogStack` coordinates (the out-of-domain point, WHIR's `α`s
and out-of-domain points). -/
def stackCap : Nat := Whir.maxLogStack

/-- A table's point: the table sumcheck's rounds, the tallest table's log-height, at most `30`
(`buildLayout` bounds the rows by `2^30`). -/
def tablePointCap : Nat := 30

/-- A column claim's point: a table's point, or `q_keccak`'s, `KECCAK`'s point and the
`qkeccakSlotBits` slot coordinates. -/
def pointCap : Nat := tablePointCap + qkeccakSlotBits

/-- The bus's GKR point: its depth, below `64` (`verifyBusBalance`'s check). -/
def busPointCap : Nat := 63

/-- The widest table, `KECCAK`'s. -/
def widthCap : Nat := 92

/-- The terms of a bus form: the most monomials one table's tuples on one side have, `KECCAK`'s
pushes', with the constant. -/
def formCap : Nat := 148

/-- A monomial's degree in the bus forms. -/
def monoCap : Nat := 2

/-- The bus's column claims (`BusResultW.claims`). -/
def busClaimCount : Nat := 4

/-- The tables' column claims (`tableColumnClaims`): one per table column. -/
def tableClaimCount : Nat := tableWidths.sum

/-- The public input's column claims (`publicInputPhase`). -/
def publicClaimCount : Nat := 2

/-- `KECCAK`'s committed outputs' column claim (`verifyKeccak`, `keccakSegments = 2`). -/
def keccakClaimCount : Nat := 1

/-- Every column claim: the bus's, the tables', the public input's, `KECCAK`'s. -/
def claimCap : Nat := busClaimCount + tableClaimCount + publicClaimCount + keccakClaimCount

/-- The stack claims: the ring-switched one, the column claims, the out-of-domain one. -/
def stackClaimCap : Nat := claimCap + 2

/-- The ring switch's coefficients: `ringMapWidth` Frobenius powers of `ringMapWidth` challenges. -/
def ringCoeffCount : Nat := ringMapWidth * ringMapWidth

/-- A WHIR level's query positions: the largest entry of `Whir.queryTable`. -/
def queryCap : Nat := 230

/-- WHIR's levels: the longest ladder. -/
def levelCap : Nat := 6

/-- WHIR's glued claims: two per non-final level. -/
def gluedCap : Nat := 2 * (levelCap - 1)

/-- A level's fold rounds: `Whir.initialFold`, the most. -/
def roundCap : Nat := Whir.initialFold

/-- The rows one query opens: `wireMaxQueries` leaves of at most `wireMaxLeafWords` words. -/
def rowsWords : Nat := LeanVM.Protocol.Compile.wireMaxQueries * LeanVM.Protocol.Compile.wireMaxLeafWords

/-- The phases' shared scratch: room for the Keccak phase's four weight vectors over the
`keccakBits` bit positions, the equality kernel over `keccakLocalBits` variables and the slot
weights over `2^qkeccakSlotBits` slots and `64` bit positions, and every smaller scratch. -/
def scratchWords : Nat := 32768

theorem tableClaimCount_val : tableClaimCount = 153 := by decide
theorem claimCap_val : claimCap = 160 := by decide
theorem pointCap_val : pointCap = 36 := by decide
theorem widthCap_ge : ∀ w ∈ tableWidths, w ≤ widthCap := by decide

/-! ## Phase 1: the layout -/

/-- A placement: `0` for none; `1`, the variable count and the index. -/
def PlacementAt (mem : UInt64 → Option UInt64) (p : UInt64) : Option Placement → Prop
  | none => mem p = some 0
  | some pl => mem p = some 1 ∧ NatAt mem (wd p 1) pl.variableCount ∧ NatAt mem (wd p 2) pl.index

/-- The layout's words: four sizes, the heights, the rows, three per global column. -/
def layoutWords : Nat := 4 + 2 * 6 + 3 * columnCount

/-- **The layout** `layout` and the rate exponent `rate`, of the bytecode `bytecode`: the memory's,
the bytecode's and the stack's log-sizes, the rate exponent, the tables' log-heights (words
`4 ..`), their row counts (words `10 ..`), from which the bus blocks are built, and every global
column's placement (three words each from word `16`); the bounds phase 1 checks. -/
structure LayoutAt (mem : UInt64 → Option UInt64) (p : UInt64) (bc : Array UInt64)
    (layout : LayoutW) (rate : Nat) : Prop where
  bytecode : layout.bytecode = bc
  logMemory : NatAt mem p layout.logMemory
  logBytecode : NatAt mem (wd p 1) layout.logBytecode
  stackLog : NatAt mem (wd p 2) layout.stackLog
  rateWord : NatAt mem (wd p 3) rate
  heightsSize : layout.tableLogHeights.size = nTables
  heights : ∀ i < nTables, NatAt mem (wd p (4 + i)) (layout.tableLogHeights.getD i 0)
  rows : ∃ rows : Array Nat, rows.size = nTables ∧
    (∀ i < nTables, NatAt mem (wd p (10 + i)) (rows.getD i 0) ∧ rows.getD i 0 ≤ 2 ^ 30) ∧
    busBlocks layout.tableLogHeights rows = (layout.push, layout.pull, layout.count)
  placementsSize : layout.placements.size = columnCount
  placements : ∀ c < columnCount, PlacementAt mem (wd p (16 + 3 * c)) (layout.placements.getD c none)
  logMemoryBound : 1 ≤ layout.logMemory ∧ layout.logMemory ≤ 30
  logBytecodeBound : layout.logBytecode ≤ 30
  stackLogBound : Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack
  rateBound : 1 ≤ rate ∧ rate ≤ 4
  heightsBound : ∀ i < nTables, layout.tableLogHeights.getD i 0 ≤ tablePointCap
  placementsBound : ∀ c < columnCount, ∀ pl, layout.placements.getD c none = some pl →
    pl.variableCount ≤ pointCap

theorem PlacementAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {o : Option Placement}
    (h : Same mem mem' p 3) (hx : PlacementAt mem p o) : PlacementAt mem' p o := by
  cases o with
  | none => exact h.base (by omega) hx
  | some pl =>
    exact ⟨h.base (by omega) hx.1, hx.2.1.congr (h 1 (by omega)), hx.2.2.congr (h 2 (by omega))⟩

theorem columnCount_val : columnCount = 158 := by decide

theorem LayoutAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {bc : Array UInt64}
    {layout : LayoutW} {rate : Nat} (h : Same mem mem' p layoutWords)
    (hx : LayoutAt mem p bc layout rate) : LayoutAt mem' p bc layout rate := by
  have hw : layoutWords = 490 := by rw [layoutWords, columnCount_val]
  rw [hw] at h
  obtain ⟨rows, hs, hr, hb⟩ := hx.rows
  exact { hx with
    logMemory := hx.logMemory.congr (h.base (by omega) rfl)
    logBytecode := hx.logBytecode.congr (h 1 (by omega))
    stackLog := hx.stackLog.congr (h 2 (by omega))
    rateWord := hx.rateWord.congr (h 3 (by omega))
    heights := fun i hi ↦ (hx.heights i hi).congr (h _ (by unfold nTables at hi; omega))
    rows := ⟨rows, hs, fun i hi ↦
      ⟨((hr i hi).1).congr (h _ (by unfold nTables at hi; omega)), (hr i hi).2⟩, hb⟩
    placements := fun c hc ↦ (hx.placements c hc).congr
      (h.sub (by rw [columnCount_val] at hc; omega)) }

/-! ## Phase 2: the out-of-domain claim -/

/-- The words of an equality claim on the stack. -/
def eqClaimWords : Nat := vecWords stackCap + 2

/-- **A stack claim `⟨.eq z, value⟩`**, `z` at most `stackCap` coordinates, then the value. -/
def EqClaimAt (mem : UInt64 → Option UInt64) (p : UInt64) (c : StackClaimW) : Prop :=
  ∃ z, c.weight = .eq z ∧ EVec mem p stackCap z ∧ EWAt mem (wd p (vecWords stackCap)) c.value

theorem EqClaimAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {c : StackClaimW}
    (h : Same mem mem' p eqClaimWords) (hx : EqClaimAt mem p c) : EqClaimAt mem' p c := by
  obtain ⟨z, hz, hv, he⟩ := hx
  refine ⟨z, hz, hv.congr ?_, he.congr (h.sub (by unfold eqClaimWords; omega))⟩
  have := h.sub (a := 0) (m := vecWords stackCap) (by unfold eqClaimWords; omega)
  rwa [wd_zero] at this

/-! ## Column claims (phases 3 to 6) -/

/-- The words of a column claim: the column, the point, the value. -/
def claimWords : Nat := 1 + vecWords pointCap + 2

/-- **A column claim**: its global column, its point (at most `pointCap` coordinates), its value. -/
def ColumnClaimAt (mem : UInt64 → Option UInt64) (p : UInt64) (c : ColumnClaimW) : Prop :=
  NatAt mem p c.column ∧ EVec mem (wd p 1) pointCap c.point ∧
    EWAt mem (wd p (1 + vecWords pointCap)) c.value

/-- The words of the column claims' array. -/
def claimsWords : Nat := 1 + claimWords * claimCap

/-- **The column claims**: their count (at most `claimCap`), then claim `i` at word
`1 + claimWords · i`. -/
def ClaimsAt (mem : UInt64 → Option UInt64) (p : UInt64) (cs : Array ColumnClaimW) : Prop :=
  cs.size ≤ claimCap ∧ NatAt mem p cs.size ∧
    ∀ i (h : i < cs.size), ColumnClaimAt mem (wd p (1 + claimWords * i)) cs[i]

theorem ColumnClaimAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {c : ColumnClaimW}
    (h : Same mem mem' p claimWords) (hx : ColumnClaimAt mem p c) : ColumnClaimAt mem' p c :=
  ⟨hx.1.congr (h.base (by unfold claimWords; omega) rfl),
    hx.2.1.congr (h.sub (by unfold claimWords; omega)),
    hx.2.2.congr (h.sub (by unfold claimWords; omega))⟩

theorem ClaimsAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {cs : Array ColumnClaimW}
    (h : Same mem mem' p claimsWords) (hx : ClaimsAt mem p cs) : ClaimsAt mem' p cs := by
  refine ⟨hx.1, hx.2.1.congr (h.base (by unfold claimsWords; omega) rfl), fun i hi ↦
    (hx.2.2 i hi).congr (h.sub ?_)⟩
  have := hx.1
  have : claimWords * i + claimWords ≤ claimWords * claimCap := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  unfold claimsWords; omega

/-! ## Phase 3: the bus -/

/-- The words of a term: the degree, `monoCap` columns, the coefficient. -/
def termWords : Nat := 1 + monoCap + 2

/-- **A term**: its monomial's columns (at most `monoCap`, the count first), its coefficient. -/
def TermAt (mem : UInt64 → Option UInt64) (p : UInt64) (t : TermW) : Prop :=
  t.cols.size ≤ monoCap ∧ NatAt mem p t.cols.size ∧
    (∀ i (h : i < t.cols.size), NatAt mem (wd p (1 + i)) t.cols[i]) ∧
    EWAt mem (wd p (1 + monoCap)) t.coeff

/-- The words of a form. -/
def formWords : Nat := 1 + termWords * formCap

/-- **A form**: its terms' count (at most `formCap`), then term `i` at word `1 + termWords · i`. -/
def FormAt (mem : UInt64 → Option UInt64) (p : UInt64) (f : FormW) : Prop :=
  f.size ≤ formCap ∧ NatAt mem p f.size ∧
    ∀ i (h : i < f.size), TermAt mem (wd p (1 + termWords * i)) f[i]

/-- Where table `t`'s form on side `side` is in the bus's words. -/
def formOff (t side : Nat) : Nat := formWords * (3 * t + side)

/-- Where the GKR point is, after the `3 · nTables` forms. -/
def busPointOff : Nat := formWords * (3 * nTables)

/-- Where the three totals are. -/
def busTotalsOff : Nat := busPointOff + vecWords busPointCap

/-- The bus's words. -/
def busWords : Nat := busTotalsOff + 2 * nTrees

/-- **The bus's result**, what phase 4 reads of it: table `t`'s form on side `side` (`forms[t][side]`)
at `formOff t side`, the GKR point, the three totals. The column claims go to `ClaimsAt`; the
bytecode point no later phase reads. -/
def BusAt (mem : UInt64 → Option UInt64) (p : UInt64) (bus : BusResultW) : Prop :=
  bus.forms.size = nTables ∧ (∀ t < nTables, (bus.forms.getD t #[]).size = 3) ∧
    (∀ t < nTables, ∀ side < 3, FormAt mem (wd p (formOff t side)) ((bus.forms.getD t #[]).getD side #[])) ∧
    EVec mem (wd p busPointOff) busPointCap bus.point ∧
    bus.totals.size = nTrees ∧ EWArr mem (wd p busTotalsOff) bus.totals

theorem TermAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {t : TermW}
    (h : Same mem mem' p termWords) (hx : TermAt mem p t) : TermAt mem' p t := by
  unfold termWords monoCap at h
  refine ⟨hx.1, hx.2.1.congr (h.base (by omega) rfl), fun i hi ↦ ?_, hx.2.2.2.congr (h.sub (by unfold monoCap; omega))⟩
  have h1 : t.cols.size ≤ 2 := hx.1
  exact (hx.2.2.1 i hi).congr (h _ (by omega))

theorem FormAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {f : FormW}
    (h : Same mem mem' p formWords) (hx : FormAt mem p f) : FormAt mem' p f := by
  refine ⟨hx.1, hx.2.1.congr (h.base (by unfold formWords; omega) rfl), fun i hi ↦
    (hx.2.2 i hi).congr (h.sub ?_)⟩
  have := hx.1
  have : termWords * i + termWords ≤ termWords * formCap := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  unfold formWords; omega

theorem BusAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {bus : BusResultW}
    (h : Same mem mem' p busWords) (hx : BusAt mem p bus) : BusAt mem' p bus := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  refine ⟨h1, h2, fun t ht side hs ↦ (h3 t ht side hs).congr (h.sub ?_), h4.congr (h.sub ?_), h5,
    h6.congr (h.sub (a := busTotalsOff) (m := 2 * nTrees) (by unfold busWords; omega)) (by omega)⟩
  · have : formWords * (3 * t + side) + formWords ≤ formWords * (3 * nTables) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by unfold nTables at ht ⊢; omega)
    unfold formOff busWords busTotalsOff busPointOff; omega
  · unfold busWords busTotalsOff; omega

/-! ## Phase 4: the tables' evaluations -/

/-- The words of one table's point and evaluations. -/
def evalStride : Nat := vecWords tablePointCap + vecWords widthCap

/-- The words of every table's. -/
def evalsWords : Nat := evalStride * nTables

/-- **Each table's point and evaluations**, table `t` at `evalStride · t`: the point (at most
`tablePointCap` coordinates), then the evaluations (at most `widthCap`). -/
def EvalsAt (mem : UInt64 → Option UInt64) (p : UInt64) (ev : Array (Array EW × Array EW)) : Prop :=
  ev.size = nTables ∧ ∀ t < nTables,
    EVec mem (wd p (evalStride * t)) tablePointCap (ev.getD t (#[], #[])).1 ∧
    EVec mem (wd p (evalStride * t + vecWords tablePointCap)) widthCap (ev.getD t (#[], #[])).2

theorem EvalsAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64}
    {ev : Array (Array EW × Array EW)} (h : Same mem mem' p evalsWords) (hx : EvalsAt mem p ev) :
    EvalsAt mem' p ev := by
  refine ⟨hx.1, fun t ht ↦ ?_⟩
  have : evalStride * t + evalStride ≤ evalStride * nTables := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  exact ⟨(hx.2 t ht).1.congr (h.sub (by unfold evalsWords evalStride at *; omega)),
    (hx.2 t ht).2.congr (h.sub (by unfold evalsWords evalStride at *; omega))⟩

/-! ## Phase 6: `KECCAK`'s outputs -/

/-- The words of `q_keccak`'s point and slices. -/
def keccakWords : Nat := vecWords pointCap + 2 * kBits

/-- **`q_keccak`'s point and its `kBits` slices**, which ring switching takes. -/
def KeccakOutAt (mem : UInt64 → Option UInt64) (p : UInt64) (point slices : Array EW) : Prop :=
  EVec mem p pointCap point ∧ slices.size = kBits ∧ EWArr mem (wd p (vecWords pointCap)) slices

theorem KeccakOutAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {point slices : Array EW}
    (h : Same mem mem' p keccakWords) (hx : KeccakOutAt mem p point slices) :
    KeccakOutAt mem' p point slices :=
  ⟨hx.1.congr (by
      have := h.sub (a := 0) (m := vecWords pointCap) (by unfold keccakWords; omega)
      rwa [wd_zero] at this),
    hx.2.1, hx.2.2.congr (h.sub (a := vecWords pointCap) (m := 2 * kBits)
      (by unfold keccakWords; omega)) (by rw [hx.2.1])⟩

/-! ## Phase 7: ring switching and the stacked opening -/

/-- The words of the ring switch's result. -/
def ringWords : Nat := 2 + 2 * ringCoeffCount

/-- **The ring switch's result**: the target, then the `ringCoeffCount` coefficients (the point is
`KeccakOutAt`'s). -/
def RingAt (mem : UInt64 → Option UInt64) (p : UInt64) (target : EW) (coefficients : Array EW) :
    Prop :=
  EWAt mem p target ∧ coefficients.size = ringCoeffCount ∧ EWArr mem (wd p 2) coefficients

/-- The words of the batching scales. -/
def basisWords : Nat := vecWords stackClaimCap

/-- **`evaluateBasis`'s data**: the scales here, the claims the ring-switched claim, the column
claims with a placement (`ClaimsAt`) and the out-of-domain claim (`EqClaimAt`), in that order. -/
def BasisAt (mem : UInt64 → Option UInt64) (p : UInt64) (b : BasisW) (layout : LayoutW)
    (ring : StackClaimW) (claims : Array ColumnClaimW) (ood : StackClaimW) : Prop :=
  b.claims = #[ring] ++ claims.filterMap (·.onStack layout) ++ #[ood] ∧
    EVec mem p stackClaimCap b.scales

/-- Where a glued claim's query positions are. -/
def gluedQOff : Nat := 5 + vecWords stackCap

/-- Where a glued claim's query weights are. -/
def gluedWOff : Nat := gluedQOff + wvecWords queryCap

/-- The words of a glued claim. -/
def gluedWords : Nat := gluedWOff + vecWords queryCap

/-- **A glued claim**: its scalar, its first fold round, its weight's kind (`0` for `eq p`, with
`p` from word `5`; `1` for `induced μ queries weights`, `μ` at word `4`, the positions at
`gluedQOff`, the weights at `gluedWOff`). -/
def GluedAt (mem : UInt64 → Option UInt64) (p : UInt64) (g : GluedClaimW) : Prop :=
  EWAt mem p g.scalar ∧ NatAt mem (wd p 2) g.foldStart ∧
    match g.weight with
    | .eq z => mem (wd p 3) = some 0 ∧ EVec mem (wd p 5) stackCap z
    | .induced mu queries weights => mem (wd p 3) = some 1 ∧ NatAt mem (wd p 4) mu ∧
        WVec mem (wd p gluedQOff) queryCap queries ∧ EVec mem (wd p gluedWOff) queryCap weights

/-- Where the glued claims' count is in WHIR's state. -/
def whirGluedOff : Nat := 2 + vecWords stackCap

/-- The words of WHIR's state. -/
def whirWords : Nat := whirGluedOff + 1 + gluedWords * gluedCap

/-- **WHIR's state**: the running claim, the `α`s (at most `stackCap`), the glued claims' count (at
most `gluedCap`), then glued claim `i` at `whirGluedOff + 1 + gluedWords · i`. -/
def WhirAt (mem : UInt64 → Option UInt64) (p : UInt64) (s : WhirStateW) : Prop :=
  EWAt mem p s.claim ∧ EVec mem (wd p 2) stackCap s.alphas ∧ s.glued.size ≤ gluedCap ∧
    NatAt mem (wd p whirGluedOff) s.glued.size ∧
    ∀ i (h : i < s.glued.size), GluedAt mem (wd p (whirGluedOff + 1 + gluedWords * i)) s.glued[i]

/-- The words of a level's fold rounds. -/
def roundsWords : Nat := 1 + 4 * roundCap

/-- **A level's fold rounds**: their count (at most `roundCap`), then round `i`'s `α` and `β` at
words `1 + 4 i`, `3 + 4 i`. -/
def RoundsAt (mem : UInt64 → Option UInt64) (p : UInt64) (rs : Array FoldRoundW) : Prop :=
  rs.size ≤ roundCap ∧ NatAt mem p rs.size ∧
    ∀ i (h : i < rs.size), EWAt mem (wd p (1 + 4 * i)) rs[i].alpha ∧
      EWAt mem (wd p (3 + 4 * i)) rs[i].beta

/-- **The rows a query opened**, `width` words each, row `i` from word `width · i`, as
`Transcript.query` writes them. -/
def RowsAt (mem : UInt64 → Option UInt64) (p : UInt64) (width : Nat) (rows : Array (Array UInt64)) :
    Prop :=
  rows.size * width ≤ rowsWords ∧
    ∀ i (h : i < rows.size), rows[i].size = width ∧ WordArr mem (wd p (width * i)) rows[i]

/-! ## The allocation -/

/-- A region of the working area: its first word and its size in words. -/
structure Region where
  off : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- The word after the region. -/
def Region.stop (r : Region) : Nat := r.off + r.size

/-- The region after `r`, of `size` words. -/
def Region.next (r : Region) (size : Nat) : Region := ⟨r.stop, size⟩

/-- The region's first word, in the working area at `work`. -/
def Region.at (work : UInt64) (r : Region) : UInt64 := wd work r.off

/-- The address `a` is a word of the region. -/
def Region.In (work : UInt64) (r : Region) (a : UInt64) : Prop := ∃ k < r.size, a = wd work (r.off + k)

/-- Two regions do not overlap. -/
def Region.Apart (r q : Region) : Prop := r.stop ≤ q.off ∨ q.stop ≤ r.off

instance (r q : Region) : Decidable (r.Apart q) := inferInstanceAs (Decidable (_ ∨ _))

def layoutR : Region := ⟨Transcript.workWords, layoutWords⟩
def oodR : Region := layoutR.next eqClaimWords
def busR : Region := oodR.next busWords
def evalsR : Region := busR.next evalsWords
def claimsR : Region := evalsR.next claimsWords
def keccakR : Region := claimsR.next keccakWords
def ringR : Region := keccakR.next ringWords
def basisR : Region := ringR.next basisWords
def whirR : Region := basisR.next whirWords
def roundsR : Region := whirR.next roundsWords
def queriesR : Region := roundsR.next (wvecWords queryCap)
def rowsR : Region := queriesR.next rowsWords
def scratchR : Region := rowsR.next scratchWords

/-- Every region, in order. -/
def regions : List Region :=
  [layoutR, oodR, busR, evalsR, claimsR, keccakR, ringR, basisR, whirR, roundsR, queriesR, rowsR,
    scratchR]

/-- The working area's words the regions take. -/
def dataEnd : Nat := scratchR.stop

/-- **The working area's size** for a bytecode of `n` words: the decoder's, the seed's hash input,
the regions. -/
def workWords (n : Nat) : Nat := max (max Wire.workWords (n + 2)) dataEnd

theorem dataEnd_val : dataEnd = 85438 := by decide

/-- The regions are pairwise apart. -/
theorem regions_apart : regions.Pairwise Region.Apart := by decide +kernel

/-- Every region follows the transcript's words and ends by `dataEnd`. -/
theorem regions_bounds : ∀ r ∈ regions, Transcript.workWords ≤ r.off ∧ r.stop ≤ dataEnd := by
  decide +kernel

theorem dataEnd_le (n : Nat) : dataEnd ≤ workWords n := Nat.le_max_right _ _

theorem seedBuf_le (n : Nat) : n + 2 ≤ workWords n :=
  le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

theorem wireWork_le (n : Nat) : Wire.workWords ≤ workWords n :=
  le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

end NativeVm.Code
