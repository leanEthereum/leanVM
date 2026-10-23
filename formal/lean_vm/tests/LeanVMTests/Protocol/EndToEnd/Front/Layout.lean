import LeanVM.Protocol.EndToEnd.Front.LayoutSizes
import LeanVM.Protocol.EndToEnd.Front.CommitDoom

/-!
# Tests: the verifier's layout is the instance's

* **Two size vectors against the pinned Rust.** For the two height vectors of
  `tests/LeanVMTests/Protocol/LeanIsa.lean`, whose offsets were checked against the pinned Rust,
  announced as full tables, the verifier program builds its layout, its stacked size is the instance's, every committed
  column's placement is at the instance's block offset with the instance's log-size, and every
  `BLAKE2S` limb sits at the Flock region's offset plus its deployed slot, below `8` coordinates.
* **Row counts.** Row counts that are not powers of two give the placements and the stacked size
  of the least powers of two holding them.
* **The announced sizes.** `readSizes` returns on the announcement of admissible sizes, and
  rejects a memory below `2^16`, a table above `2^32` rows and the rate `5`; a `BLAKE2S` table
  of two rows is accepted.
* **Mutations.** Breaking ties by the higher index, or reading the limbs at the identity slots,
  moves placements: the tie order and the deployed slots are load-bearing.
* **The bus flushes.** Every opcode table's pushed and pulled tuples, evaluated on a row, are the
  Python's in the Python's order, and its count columns the Python's `cnt` columns. This is the
  regression for `DEREF`, whose Clean table read the local cell before the store target until it
  was put in the deployed order (`tables.rs:642-647`): the tie order of equal-height bus blocks
  follows the flush order, so the leaf decomposition depends on it.
-/

namespace LeanVMTests.Protocol.EndToEnd.Front.Layout

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front

/-- Four `XOR` instructions. -/
def prog4 : Program := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- The first size vector of the instance's tests, heights `16, 3, 16, 4, 16, 16`: a table as
tall as the memory. -/
def s₁ : Sizes := ⟨16, by decide, ![65536, 8, 65536, 16, 65536, 65536]⟩

/-- The second size vector, heights `2, 18, 5, 0, 7, 3`: mixed heights. -/
def s₂ : Sizes := ⟨18, by decide, ![4, 262144, 32, 1, 128, 8]⟩

/-- The second size vector's heights, from row counts that are not powers of two. -/
def s₃ : Sizes := ⟨18, by decide, ![3, 200000, 17, 0, 65, 5]⟩

/-! ## The layout -/

#guard tableLogs s₁ == [16, 3, 16, 4, 16, 16]
#guard tableLogs s₂ == [2, 18, 5, 0, 7, 3]
#guard tableLogs s₃ == tableLogs s₂
#guard (buildLayout (bytecodeWords prog4) s₁.logMem (tableRows s₁)).isSome
#guard (buildLayout (bytecodeWords prog4) s₂.logMem (tableRows s₂)).isSome
#guard (buildLayout (bytecodeWords prog4) s₃.logMem (tableRows s₃)).isSome
#guard (verifierLayout prog4 s₁).stackLog = 25
#guard (verifierLayout prog4 s₂).stackLog = 23
#guard (verifierLayout prog4 s₃).stackLog = 23
#guard decide ((verifierLayout prog4 s₃).placements = (verifierLayout prog4 s₂).placements)
#guard decide (LayoutOk s₁)

/-- The placement the instance gives a column: its block's offset, or the Flock region's offset
plus its deployed slot. -/
def instancePlacement (prog : Program) (s : Sizes) (c : Col) : Placement :=
  if h : IsLimb c then
    { vars := s.τ 5, low := 8,
      index := (blocks prog s).offset (flockBlock prog s) +
        (Blake2sFlock.slots ⟨c.2.val - 9, by have := h.2.2; omega⟩).val }
  else { vars := kappa prog s c, index := (blocks prog s).offset (blockOf c h) }

/-- The verifier's placement of every column agrees with the instance's. -/
def placementsAgree (prog : Program) (s : Sizes) : Bool :=
  columns.all fun c ↦
    (verifierLayout prog s).placements.getD (pyCol c) default = instancePlacement prog s c

#guard placementsAgree prog4 s₁
#guard placementsAgree prog4 s₂
#guard placementsAgree prog4 s₃

/-- The general statements, at the test's sizes. -/
example : (verifierLayout prog4 s₁).stackLog = leanIsaμ prog4 s₁ := stackLog_verifierLayout _ _

example (c : Col) (h : ¬ IsLimb c) :
    (verifierLayout prog4 s₂).placements.getD (pyCol c) default = instancePlacement prog4 s₂ c := by
  rw [placement_committed prog4 s₂ c h, instancePlacement]
  simp only [h, ↓reduceDIte]

example (F : FlockSpec) (hF : F.slot = Blake2sFlock.slots) (c : Col)
    (z : Vector E (kappa prog4 s₁ c)) (v : E) (q : Column (leanIsaμ prog4 s₁)) :
    StackClaim.Holds (leanIsaμ prog4 s₁)
        ((⟨pyCol c, z.toList, v⟩ : Verifier.ColumnClaim).onStack (verifierLayout prog4 s₁)) q ↔
      (⟨c, z, v⟩ : LeanVM.Protocol.ColumnClaim (leanIsaInstance F prog4 s₁)).Holds q :=
  onStack_holds_iff prog4 s₁ F hF c z v q

/-! ## The announced sizes -/

/-- Whether `readSizes` returns after the announcement, with the expected stacked size and rate. -/
def readsTo (s : Sizes) (ρ : ℕ) (μ : ℕ) : Bool :=
  match (readSizes (bytecodeWords prog4)).after ((announce s ρ).map Ev.read) with
  | some (.ret a) => a.1.stackLog == μ && a.2 == ρ
  | _ => false

/-- Whether `readSizes` rejects after the announcement. -/
def rejects (s : Sizes) (ρ : ℕ) : Bool :=
  match (readSizes (bytecodeWords prog4)).after ((announce s ρ).map Ev.read) with
  | some .fail => true
  | _ => false

#guard readsTo s₁ 2 25
#guard readsTo s₂ 4 23
#guard readsTo s₃ 4 23
#guard readsTo ⟨16, by decide, ![65536, 8, 65536, 16, 65536, 2]⟩ 2 22
#guard rejects ⟨15, by decide, ![65536, 8, 65536, 16, 65536, 65536]⟩ 2
#guard rejects ⟨16, by decide, ![65536, 8, 2 ^ 32 + 1, 16, 65536, 65536]⟩ 2
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

-- The limbs at the identity slots move off the deployed placement.
#guard (columns.filter fun c ↦ decide (IsLimb c)).any fun c ↦
  (verifierLayout prog4 s₁).placements.getD (pyCol c) default ≠
    { vars := s₁.τ 5, low := 8,
      index := (blocks prog4 s₁).offset (flockBlock prog4 s₁) + (c.2.val - 9) }

/-! ## The bus flushes: the `DEREF` order -/

/-- A row of pseudo-random words. -/
def rowVal (i : ℕ) : K := K.ofBits ((i * 1442695040888963407 + 6364136223846793005) % 2 ^ 64)

/-- The instance's flushes of opcode table `j` on one side, evaluated on the row. -/
def instanceFlushes (j : Fin 6) (side : LeanVM.Arithmetization.Direction) : List (List E) :=
  ((opcodeTable j).flushes.filter fun f ↦ decide (f.1 = side)).map fun f ↦
    f.2.toList.map fun P ↦ ofK (P.eval fun k ↦ rowVal k.val)

/-- The Python's flushes of table `j` on one side, evaluated on the row, padded to sixteen. -/
def pythonFlushes (j : Fin 6) (push : Bool) : List (List E) :=
  let t := tables.getD j default
  (if push then t.flushes.push else t.flushes.pull).map fun coords ↦
    (coords.map fun f ↦ f.evaluate fun k ↦ ofK (rowVal k)) ++
      List.replicate (16 - coords.length) 0

-- Every table, `DEREF` included, flushes the Python's tuples in the Python's order: the
-- regression for the `DEREF` order (pointer, target, local; `tables.rs:642-647`), which the
-- instance had as pointer, local, target, moving two equal-height bus blocks.
#guard (List.finRange 6).all fun j ↦
  decide (instanceFlushes j .push = pythonFlushes j true) &&
    decide (instanceFlushes j .pull = pythonFlushes j false)

-- The order is load-bearing: exchanging `DEREF`'s last two memory flushes breaks the agreement.
#guard decide ((instanceFlushes 3 .push).take 3 ++
    [(instanceFlushes 3 .push)[4]!, (instanceFlushes 3 .push)[3]!] ≠ pythonFlushes 3 true)

-- The count columns are the Python's `cnt` columns, table by table.
#guard (List.finRange 6).all fun j ↦
  (opcodeTable j).count.map (·.val) == (tables.getD j default).countColumns

end LeanVMTests.Protocol.EndToEnd.Front.Layout
