import LeanVM.Protocol.Verifier.Claims
import LeanVM.Protocol.EndToEnd.Front.LayoutSizes
import LeanVM.Protocol.EndToEnd.Front.CommitDoom
import LeanVMTests.Runs

/-!
# Tests: the verifier's layout is the instance's

* **Two size vectors against the pinned verifier.** For the two height vectors of
  `tests/LeanVMTests/Protocol/LeanIsa.lean`, whose offsets were checked against the pinned
  verifier's `build_layout`, announced as full tables, the verifier program builds its layout, its
  stacked size is the instance's, every committed column's placement is at the instance's block
  offset with the instance's log-size, every `KECCAK` input lane and every column riding a spare
  slot (the table's columns `0 … 12` and `cnt_0`) is the column of `QKECCAK`'s block at its slot,
  and every output lane has no placement (it is derived, never opened).
* **Row counts.** Row counts that are not powers of two give the placements and the stacked size
  of the least powers of two holding them.
* **The announced sizes.** `readAnnouncedSizes` returns on the announcement of admissible sizes, and
  rejects a memory above `2^30`, a table above `2^30` rows and the rate `5`; a memory of two cells,
  the floor, is accepted, and a `KECCAK` table of two rows, at its floor height `2^9`.
* **Mutations.** Breaking ties by the higher index moves placements: the tie order is
  load-bearing.
* **The bus flushes.** Every opcode table's pushed and pulled tuples, evaluated on a row, are the
  verifier's `tables` in their order, and its count columns the verifier's `cnt` columns. This is the
  regression for `DEREF`, whose Clean table read the local cell before the store target until it
  was put in the deployed order (`tables.rs`): the tie order of equal-height bus blocks
  follows the flush order, so the leaf decomposition depends on it.
-/

namespace LeanVMTests.Protocol.EndToEnd.Front.Layout

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front

/-- Four `XOR` instructions. -/
def prog4 : LeanIsaProgram := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- The first size vector of the instance's tests, heights `16, 3, 16, 4, 16, 16`: a table as
tall as the memory. -/
def s₁ : Sizes := ⟨16, by decide, ![65536, 8, 65536, 16, 65536, 65536]⟩

/-- The second size vector, heights `2, 18, 5, 0, 7, 9` (`KECCAK` at its floor): mixed heights. -/
def s₂ : Sizes := ⟨18, by decide, ![4, 262144, 32, 1, 128, 8]⟩

/-- The second size vector's heights, from row counts that are not powers of two. -/
def s₃ : Sizes := ⟨18, by decide, ![3, 200000, 17, 0, 65, 5]⟩

/-! ## The layout -/

#guard tableLogs s₁ == [16, 3, 16, 4, 16, 16]
#guard tableLogs s₂ == [2, 18, 5, 0, 7, 9]
#guard tableLogs s₃ == tableLogs s₂
#guard (buildLayout (bytecodeWords prog4) s₁.logMem (tableRows s₁)).isSome
#guard (buildLayout (bytecodeWords prog4) s₂.logMem (tableRows s₂)).isSome
#guard (buildLayout (bytecodeWords prog4) s₃.logMem (tableRows s₃)).isSome
#guard (verifierLayout prog4 s₁).stackLog = 24
#guard (verifierLayout prog4 s₂).stackLog = 23
#guard (verifierLayout prog4 s₃).stackLog = 23
#guard decide ((verifierLayout prog4 s₃).placements = (verifierLayout prog4 s₂).placements)
#guard decide (LayoutOk s₁)

/-- The placement the instance gives a column: none for an output lane; for an input lane or a
column riding a spare slot, the column of `QKECCAK`'s block at its slot (input lane `l`: `l`;
the `KECCAK` table's columns `0 … 13`: `50 … 63`, written out here rather than read off
`qSlot`); otherwise its block's offset. -/
def instancePlacement (prog : LeanIsaProgram) (s : Sizes) (c : Col) : Option Placement :=
  if IsOut c then none
  else if h : IsVirtual c then
    let slot := if c.2.val < 14 then 50 + c.2.val else c.2.val - 15
    some
      { variableCount := s.τ 5,
        index := (blocks prog s).offset (keccakBlock prog s) + slot * 2 ^ s.τ 5 }
  else some { variableCount := kappa prog s c, index := (blocks prog s).offset (blockOf c h) }

/-- The verifier's placement of every column agrees with the instance's. -/
def placementsAgree (prog : LeanIsaProgram) (s : Sizes) : Bool :=
  columns.all fun c ↦
    (verifierLayout prog s).placements.getD (refCol c) none = instancePlacement prog s c

#guard placementsAgree prog4 s₁
#guard placementsAgree prog4 s₂
#guard placementsAgree prog4 s₃

/-- The general statements, at the test's sizes. -/
example : (verifierLayout prog4 s₁).stackLog = leanIsaμ prog4 s₁ := stackLog_verifierLayout _ _

example (c : Col) (h : ¬ IsVirtual c) :
    (verifierLayout prog4 s₂).placement (refCol c) =
      { variableCount := kappa prog4 s₂ c, index := (blocks prog4 s₂).offset (blockOf c h) } :=
  placement_committed prog4 s₂ c h

example (c : Col) (h : IsOut c) : (verifierLayout prog4 s₂).placements.getD (refCol c) none = none :=
  placements_outLane prog4 s₂ c h

example (c : Col) (hc : ¬ IsOut c) (z : Vector E (kappa prog4 s₁ c)) (v : E)
    (q : Column (leanIsaμ prog4 s₁)) :
    StackClaim.Holds (leanIsaμ prog4 s₁)
        ((⟨refCol c, z.toList, v⟩ : Verifier.ColumnClaim).stackClaim (verifierLayout prog4 s₁)) q ↔
      (⟨c, z, v⟩ : LeanVM.Protocol.ColumnClaim (leanIsaInstance prog4 s₁)).Holds q :=
  onStack_holds_iff prog4 s₁ c hc z v q

/-! ## The announced sizes -/

/-- Whether `readAnnouncedSizes` returns after the announcement, with the expected stacked size and
rate. -/
def readsTo (s : Sizes) (ρ : ℕ) (μ : ℕ) : Bool :=
  match (readAnnouncedSizes (bytecodeWords prog4)).after ((announce s ρ).map Ev.read) with
  | some (.ret a) => a.1.stackLog == μ && a.2 == ρ
  | _ => false

/-- Whether `readAnnouncedSizes` rejects after the announcement. -/
def rejects (s : Sizes) (ρ : ℕ) : Bool :=
  match (readAnnouncedSizes (bytecodeWords prog4)).after ((announce s ρ).map Ev.read) with
  | some .fail => true
  | _ => false

#guard readsTo s₁ 2 24
#guard readsTo s₂ 4 23
#guard readsTo s₃ 4 23
#guard readsTo ⟨16, by decide, ![65536, 8, 65536, 16, 65536, 2]⟩ 2 22
#guard readsTo ⟨1, by decide, ![65536, 8, 65536, 16, 65536, 65536]⟩ 2 23
#guard rejects ⟨31, by decide, ![65536, 8, 65536, 16, 65536, 65536]⟩ 2
#guard rejects ⟨16, by decide, ![65536, 8, 2 ^ 30 + 1, 16, 65536, 65536]⟩ 2
#guard rejects s₁ 5
#guard rejects s₁ 0

/-! ## Mutations -/

/-- `stack_offsets` with ties broken by the higher index. -/
def stackOffsetsHighTies (sizes : List ℕ) : List ℕ :=
  let size := fun i ↦ sizes.getD i 0
  let order := (List.range sizes.length).mergeSort fun i j ↦
    decide (size j < size i) || (decide (size i = size j) && decide (j ≤ i))
  (order.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ size i))
    (List.replicate sizes.length 0, 0)).1

#guard stackOffsetsHighTies (committedColumns.map (kappa prog4 s₁)) ≠
  (stackOffsets (committedColumns.map (kappa prog4 s₁))).1

/-! ## The bus flushes: the `DEREF` order -/

/-- A row of pseudo-random words. -/
def rowVal (i : ℕ) : K := K.ofBits ((i * 1442695040888963407 + 6364136223846793005) % 2 ^ 64)

/-- The instance's flushes of opcode table `j` on one side, evaluated on the row. -/
def instanceFlushes (j : Fin 6) (side : LeanVM.Arithmetization.Direction) : List (List E) :=
  ((opcodeTable j).flushes.filter fun f ↦ decide (f.1 = side)).map fun f ↦
    f.2.toList.map fun P ↦ ofK (P.eval fun k ↦ rowVal k.val)

/-- The verifier's flushes (`tables`) of table `j` on one side, evaluated on the row, padded to
sixteen. -/
def refFlushes (j : Fin 6) (push : Bool) : List (List E) :=
  let t := tables.getD j default
  (if push then t.flushes.push else t.flushes.pull).map fun coords ↦
    (coords.map fun f ↦ f.evaluate fun k ↦ ofK (rowVal k)) ++
      List.replicate (16 - coords.length) 0

-- Every table, `DEREF` included, flushes the verifier's tuples in the verifier's order: the
-- regression for the `DEREF` order (pointer, target, local; `tables.rs`), which the
-- instance had as pointer, local, target, moving two equal-height bus blocks. A run, compiled
-- (`lake exe test-runs`).
test_runs runs := [
  ("every table flushes the verifier's tuples in the verifier's order", fun _ ↦
    (List.finRange 6).all fun j ↦
      decide (instanceFlushes j .push = refFlushes j true) &&
        decide (instanceFlushes j .pull = refFlushes j false))]

-- The order is load-bearing: exchanging `DEREF`'s last two memory flushes breaks the agreement.
#guard decide ((instanceFlushes 3 .push).take 3 ++
    [(instanceFlushes 3 .push)[4]!, (instanceFlushes 3 .push)[3]!] ≠ refFlushes 3 true)

-- The count columns are the verifier's `cnt` columns, table by table.
#guard (List.finRange 6).all fun j ↦
  (opcodeTable j).count.map (·.val) == (tables.getD j default).countColumns

end LeanVMTests.Protocol.EndToEnd.Front.Layout
