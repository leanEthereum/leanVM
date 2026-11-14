import LeanVM.Protocol.LeanIsa
import LeanVM.Protocol.EndToEnd.Front.LayoutInstance

/-!
# Tests: the leanISA instance

* **The stack against the pinned verifier.** For two announced size vectors, the stacked size and
  every column's offset (a `KECCAK` input lane or a column riding a spare slot: `QKECCAK`'s offset
  plus its slot times the table's height; an output lane, derived: none) equal the placement indices
  of the verifier's `build_layout` as the statement transcribes it (`placementsOf`,
  `crates/verifier/src/layout.rs:531-553`), for a program of four `XOR` instructions; the first
  offsets are pinned too. The first has a table as tall
  as the memory and three more, and a `KECCAK` table of `2^16` rows: ties go to the lower global
  index, the shared columns first. The second mixes heights and has a `KECCAK` table of eight rows,
  which takes the floor height `2^9`. Both announce full tables (`2^τ` rows); a table's height is
  the least power of two holding its rows (and at least the table's floor), so the stack is the
  same for any row count of the same height.
* **Admissible sizes.** The first vector is admissible, and so is one with row counts that are
  not powers of two, an empty table among them, and a `KECCAK` table of five rows (below its
  floor), and a memory of two cells (no floor but the public input's); a memory above `2^30`, a
  table above `2^30` rows and a stack above `2^30` are rejected, and so is the WHIR rate `5`.
* **The public lines and the bus.** Two lines, `MEMORY_0` and `MEMORY_1`, not sent; six boundary
  blocks, three per side; the Keccak region is `QKECCAK` with `2^τ_KECCAK` steps.
* **The relation is decidable, and the instance meets the bus phase's conditions.**
* **Not evaluated: a witness stacked and read back.** Even the smallest shape is too slow to
  evaluate: the stacking and the column reads are written for proofs, not for speed. The
  read-back is a theorem of the adaptor instead.
-/

namespace LeanVMTests.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front

/-- Four `XOR` instructions: a bytecode of log-size `2`. -/
def prog4 : LeanIsaProgram := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- A table as tall as the memory, and three more. -/
def s₁ : Sizes := ⟨16, by decide, ![2 ^ 16, 2 ^ 3, 2 ^ 16, 2 ^ 4, 2 ^ 16, 2 ^ 16]⟩

/-- Mixed heights, the `KECCAK` table of eight rows. -/
def s₂ : Sizes := ⟨18, by decide, ![2 ^ 2, 2 ^ 18, 2 ^ 5, 2 ^ 0, 2 ^ 7, 2 ^ 3]⟩

/-- The heights of `s₂`, from row counts that are not powers of two, an empty table among them,
and a `KECCAK` table of five rows. -/
def s₃ : Sizes := ⟨18, by decide, ![3, 2 ^ 17 + 1, 17, 0, 100, 5]⟩

-- A table's height is the least power of two holding its rows, `KECCAK`'s at least `2^9`; an
-- empty table has one row, a padding row.
#guard (List.finRange 6).map s₃.τ = (List.finRange 6).map s₂.τ
#guard (List.finRange 6).map s₂.τ = [2, 18, 5, 0, 7, 9]

/-- Every column's offset in the stack, in global order: its block's; a `KECCAK` input lane's or
spare column's, `QKECCAK`'s offset plus its slot times the table's height (the column is the
column of `QKECCAK`'s block at that slot); `none` for an output lane, which is derived. -/
def offsets (prog : LeanIsaProgram) (s : Sizes) : List (Option ℕ) :=
  columns.map fun c ↦
    if IsOut c then none
    else if h : IsVirtual c then
      some ((blocks prog s).offset (keccakBlock prog s) + (qSlot c).val * 2 ^ s.τ 5)
    else some ((blocks prog s).offset (blockOf c h))

/-- The pinned verifier's offsets (`build_layout`, `placementsOf` of the statement's
transcription): a placement's index, `none` for an output lane. -/
def verifierOffsets (s : Sizes) : List (Option ℕ) :=
  (placementsOf (refKappas prog4 s)).1.map (·.map (·.index))

#guard leanIsaμ prog4 s₁ = 24
#guard (placementsOf (refKappas prog4 s₁)).2 = 24
#guard offsets prog4 s₁ = verifierOffsets s₁
#guard (offsets prog4 s₁).take 6 =
  [some 4194304, some 4259840, some 4325376, some 8454472, some 0, some 4390912]

#guard leanIsaμ prog4 s₂ = 23
#guard (placementsOf (refKappas prog4 s₂)).2 = 23
#guard offsets prog4 s₂ = verifierOffsets s₂
#guard (offsets prog4 s₂).take 6 =
  [some 0, some 262144, some 524288, some 4243424, some 4194304, some 4243428]

/-! ## Admissible sizes -/

#guard decide (s₁.Admissible prog4)
#guard decide (s₂.Admissible prog4)
#guard decide (s₃.Admissible prog4)
#guard leanIsaμ prog4 s₃ = leanIsaμ prog4 s₂
#guard decide (Sizes.Admissible prog4 ⟨1, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨31, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨16, by decide, ![2 ^ 30 + 1, 8, 1, 1, 1, 1]⟩)
#guard decide (Sizes.Admissible prog4 ⟨28, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨29, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard leanIsaμ prog4 ⟨29, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩ = 31
#guard (List.range 6).map (fun ρ ↦ decide (validRate ρ)) = [false, true, true, true, true, false]

/-! ## The public lines, the bus, the Keccak region -/

#guard ((publicLines prog4 s₁ ⟨![1, 2, 3, 4]⟩).toList.map fun l ↦
    (l.col == memCol 0, l.col == memCol 1, l.cell0, l.cell1, l.sent)) =
  [(true, false, 1, 3, false), (false, true, 2, 4, false)]

-- In the kernel, which reads the blocks' sizes and sides alone (the compiled code would build their
-- index columns, `2^16` powers of `g`).
example : (boundary prog4 s₁).map (fun b ↦ (b.κ, b.side)) =
    [(0, .push), (16, .push), (2, .push), (0, .pull), (16, .pull), (2, .pull)] := by
  decide +kernel

#guard (keccakRegion prog4 s₂).logSteps = 9
#guard (keccakRegion prog4 s₂).col == keccakCol

-- The instance's count columns are the opcode tables' read counts.
#guard (List.finRange 9).map (fun j ↦ (counts j).length) = [0, 0, 0, 4, 4, 2, 4, 4, 27]

/-- The instance meets the bus phase's conditions and the degree bound at every size. -/
example (prog : LeanIsaProgram) (s : Sizes) :
    Bus.Conditions (leanIsaInstance prog s) ∧ (leanIsaInstance prog s).d ≤ 2 :=
  ⟨leanIsa_conditions prog s, le_rfl⟩

/-- The relation is decidable, by instance search. -/
example (prog : LeanIsaProgram) (s : Sizes) (input : PublicInput)
    (q : Column (leanIsaInstance prog s).μ) :
    Decidable (M3Holds (leanIsaInstance prog s) input q) :=
  inferInstance

end LeanVMTests.Protocol.LeanIsa
