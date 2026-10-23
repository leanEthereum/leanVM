import LeanVM.Protocol.LeanIsa

/-!
# Tests: the leanISA instance

* **The stack against the pinned Rust.** For two announced size vectors, the stacked size and
  every column's offset, or its absence for a `BLAKE2S` limb, equal what the pinned verifier
  reconstructs (`lean_vm::cpu::layout` at `a386121f84292f6fa663aaa3e570c15bc0240ea2`, for a
  program of four `XOR` instructions). The first has a table as tall as the memory and
  three more: ties go to the lower global index, the shared columns first. The second mixes
  heights and has a `BLAKE2S` table of eight rows. Both announce full tables (`2^τ` rows); a
  table's height is the least power of two holding its rows, so the stack is the same for any
  row count of the same height.
* **Admissible sizes.** The first vector is admissible, and so is one with row counts that are
  not powers of two, an empty table among them, and a `BLAKE2S` table of five rows (there is
  no floor); the memory below `2^16`, a table above `2^32` rows and a stack above `2^28` are
  rejected, and so is the WHIR rate `5`.
* **The public lines and the bus.** The third line is `MEM_TOP` with cells `0, 0`, not sent;
  six boundary blocks, three per side; the Flock region is `QFLOCK` with `2^τ_BLAKE2S` blocks.
* **The relation is decidable, and the instance meets the bus phase's conditions.**
* **Not evaluated: a witness stacked and read back.** Even the smallest shape, a stack of
  `2^15` cells with one Flock block, is too slow to evaluate: the stacking, the
  column reads and the Flock region's honest column (`F.gen`, the BLAKE2s trace) are written
  for proofs, not for speed. The read-back is a theorem of the adaptor instead.
-/

namespace LeanVMTests.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa

/-- Four `XOR` instructions: a bytecode of log-size `2`, as in the pinned Rust layout. -/
def prog4 : Program := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- A table as tall as the memory, and three more. -/
def s₁ : Sizes := ⟨16, by decide, ![2 ^ 16, 2 ^ 3, 2 ^ 16, 2 ^ 4, 2 ^ 16, 2 ^ 16]⟩

/-- Mixed heights, the `BLAKE2S` table of eight rows. -/
def s₂ : Sizes := ⟨18, by decide, ![2 ^ 2, 2 ^ 18, 2 ^ 5, 2 ^ 0, 2 ^ 7, 2 ^ 3]⟩

/-- The heights of `s₂`, from row counts that are not powers of two, an empty table among them. -/
def s₃ : Sizes := ⟨18, by decide, ![3, 2 ^ 17 + 1, 17, 0, 100, 5]⟩

-- A table's height is the least power of two holding its rows; an empty table has one row, a
-- padding row.
#guard (List.finRange 6).map s₃.τ = (List.finRange 6).map s₂.τ
#guard (List.finRange 6).map s₂.τ = [2, 18, 5, 0, 7, 3]

/-- Every column's offset in the stack, in global order; `none` for a limb. -/
def offsets (prog : Program) (s : Sizes) : List (Option ℕ) :=
  columns.map fun c ↦ if h : IsLimb c then none else some ((blocks prog s).offset (blockOf c h))

#guard leanIsaμ prog4 s₁ = 25
#guard offsets prog4 s₁ =
    [some 16777216, some 16842752, some 16908288, some 16973824, some 20709736, some 0,
     some 17039360, some 17104896, some 17170432, some 17235968, some 17301504, some 17367040,
     some 17432576, some 17498112, some 17563648, some 17629184, some 17694720, some 17760256,
     some 17825792, some 17891328, some 17956864, some 20709616, some 20709624, some 20709632,
     some 20709640, some 20709648, some 20709656, some 20709664, some 20709672, some 20709680,
     some 20709688, some 20709696, some 20709704, some 20709712, some 20709720, some 20709728,
     some 18022400, some 18087936, some 18153472, some 18219008, some 18284544, some 18350080,
     some 18415616, some 18481152, some 20709376, some 20709392, some 20709408, some 20709424,
     some 20709440, some 20709456, some 20709472, some 20709488, some 20709504, some 20709520,
     some 20709536, some 20709552, some 20709568, some 20709584, some 20709600, some 18546688,
     some 18612224, some 18677760, some 18743296, some 18808832, some 18874368, some 18939904,
     some 19005440, some 19070976, some 19136512, some 19202048, some 19267584, some 19333120,
     some 19398656, some 19464192, some 19529728, some 19595264, some 19660800, some 19726336,
     some 19791872, some 19857408, some 19922944, some 19988480, none, none, none, none, none,
     none, none, none, none, none, none, none, none, none, none, none, none, none, some 20054016,
     some 20119552, some 20185088, some 20250624, some 20316160, some 20381696, some 20447232,
     some 20512768, some 20578304, some 20643840]

#guard leanIsaμ prog4 s₂ = 23
#guard offsets prog4 s₂ =
    [some 0, some 262144, some 524288, some 786432, some 4984984, some 4980736, some 4984988,
     some 4984992, some 4984996, some 4985000, some 4985004, some 4985008, some 4985012,
     some 4985016, some 4985020, some 4985024, some 4985028, some 4985032, some 4985036,
     some 4985040, some 4985044, some 1048576, some 1310720, some 1572864, some 1835008,
     some 2097152, some 2359296, some 2621440, some 2883584, some 3145728, some 3407872,
     some 3670016, some 3932160, some 4194304, some 4456448, some 4718592, some 4984576,
     some 4984608, some 4984640, some 4984672, some 4984704, some 4984736, some 4984768,
     some 4984800, some 4985048, some 4985049, some 4985050, some 4985051, some 4985052,
     some 4985053, some 4985054, some 4985055, some 4985056, some 4985057, some 4985058,
     some 4985059, some 4985060, some 4985061, some 4985062, some 4982784, some 4982912,
     some 4983040, some 4983168, some 4983296, some 4983424, some 4983552, some 4983680,
     some 4983808, some 4983936, some 4984064, some 4984192, some 4984320, some 4984448,
     some 4984832, some 4984840, some 4984848, some 4984856, some 4984864, some 4984872,
     some 4984880, some 4984888, some 4984896, none, none, none, none, none, none, none, none,
     none, none, none, none, none, none, none, none, none, none, some 4984904, some 4984912,
     some 4984920, some 4984928, some 4984936, some 4984944, some 4984952, some 4984960,
     some 4984968, some 4984976]

/-! ## Admissible sizes -/

#guard decide (s₁.Admissible prog4)
#guard decide (s₂.Admissible prog4)
#guard decide (s₃.Admissible prog4)
#guard leanIsaμ prog4 s₃ = leanIsaμ prog4 s₂
#guard !decide (Sizes.Admissible prog4 ⟨15, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨16, by decide, ![2 ^ 32 + 1, 8, 1, 1, 1, 1]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨28, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard leanIsaμ prog4 ⟨28, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩ = 31
#guard (List.range 6).map (fun ρ ↦ decide (validRate ρ)) = [false, true, true, true, true, false]

/-! ## The public lines, the bus, the Flock region -/

#guard ((publicLines prog4 s₁ ⟨![1, 2, 3, 4]⟩).toList.map fun l ↦
    (l.col == memCol 0, l.col == memCol 1, l.col == memCol 2, l.cell0, l.cell1, l.sent)) =
  [(true, false, false, 1, 3, false), (false, true, false, 2, 4, false),
    (false, false, true, 0, 0, false)]

#guard (boundary prog4 s₁).map (fun b ↦ (b.κ, b.side)) =
  [(0, .push), (16, .push), (2, .push), (0, .pull), (16, .pull), (2, .pull)]

#guard (flockRegion prog4 s₂ Blake2sFlock.blake2sFlockSpec).kBatch = 3
#guard (flockRegion prog4 s₂ Blake2sFlock.blake2sFlockSpec).col == flockCol

-- The instance's count columns are the opcode tables' read counts.
#guard (List.finRange 9).map (fun j ↦ (counts j).length) = [0, 0, 0, 4, 4, 2, 4, 4, 10]

/-- The instance meets the bus phase's conditions and the degree bound at every size. -/
example (F : FlockSpec) (prog : Program) (s : Sizes) :
    Bus.Conditions (leanIsaInstance F prog s) ∧ (leanIsaInstance F prog s).d ≤ 2 :=
  ⟨leanIsa_conditions F prog s, le_rfl⟩

/-- The relation is decidable, by instance search. -/
example (F : FlockSpec) (prog : Program) (s : Sizes) (input : PublicInput)
    (q : Column (leanIsaInstance F prog s).μ) :
    Decidable (M3Holds (leanIsaInstance F prog s) input q) :=
  inferInstance

end LeanVMTests.Protocol.LeanIsa
