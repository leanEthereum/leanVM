import LeanVM.Protocol.LeanIsa

/-!
# Tests: the leanISA instance

* **The stack against the pinned verifier.** For two announced size vectors, the stacked size and
  every column's offset (a `KECCAK` input lane or a column riding a spare slot: `QKECCAK`'s offset
  plus its slot times the table's height; an output lane, derived: none) equal the placement indices
  of the pinned verifier's `build_layout` (`crates/verifier/src/layout.rs:492-583` at leanVM main
  `40f877dc2c858f013c5974ab71ca594b31a7aec9`, for a program of four `XOR` instructions; a driver of
  the port, checked first to give the previous values at `5e3ade21`). The first has a table as tall
  as the memory and three more, and a `KECCAK` table of `2^16` rows: ties go to the lower global
  index, the shared columns first. The second mixes heights and has a `KECCAK` table of eight rows,
  which takes the floor height `2^9`. Both announce full tables (`2^τ` rows); a table's height is
  the least power of two holding its rows (and at least the table's floor), so the stack is the
  same for any row count of the same height.
* **Admissible sizes.** The first vector is admissible, and so is one with row counts that are
  not powers of two, an empty table among them, and a `KECCAK` table of five rows (below its
  floor), and so is a memory of two cells, the floor; a memory above `2^32` cells, a table above
  `2^32` rows and a stack above `2^32` are rejected, and so is the WHIR rate `5`.
* **The public lines and the bus.** The third line is `MEM_TOP` with cells `0, 0`, not sent;
  six boundary blocks, three per side; the Keccak region is `QKECCAK` with `2^τ_KECCAK` steps.
* **The relation is decidable, and the instance meets the bus phase's conditions.**
* **Not evaluated: a witness stacked and read back.** Even the smallest shape is too slow to
  evaluate: the stacking and the column reads are written for proofs, not for speed. The
  read-back is a theorem of the adaptor instead.
-/

namespace LeanVMTests.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa

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

#guard leanIsaμ prog4 s₁ = 24
#guard offsets prog4 s₁ =
    [some 4194304, some 4259840, some 4325376, some 4390912, some 8716648, some 0, some 4456448,
     some 4521984, some 4587520, some 4653056, some 4718592, some 4784128, some 4849664,
     some 4915200, some 4980736, some 5046272, some 5111808, some 5177344, some 5242880,
     some 5308416, some 5373952, some 8716528, some 8716536, some 8716544, some 8716552,
     some 8716560, some 8716568, some 8716576, some 8716584, some 8716592, some 8716600,
     some 8716608, some 8716616, some 8716624, some 8716632, some 8716640, some 5439488,
     some 5505024, some 5570560, some 5636096, some 5701632, some 5767168, some 5832704,
     some 5898240, some 8716288, some 8716304, some 8716320, some 8716336, some 8716352,
     some 8716368, some 8716384, some 8716400, some 8716416, some 8716432, some 8716448,
     some 8716464, some 8716480, some 8716496, some 8716512, some 5963776, some 6029312,
     some 6094848, some 6160384, some 6225920, some 6291456, some 6356992, some 6422528,
     some 6488064, some 6553600, some 6619136, some 6684672, some 6750208, some 6815744,
     some 3276800, some 3342336, some 3407872, some 3473408, some 3538944, some 3604480,
     some 3670016, some 3735552, some 3801088, some 3866624, some 3932160, some 3997696,
     some 4063232, some 4128768, some 6881280, some 0, some 65536, some 131072, some 196608,
     some 262144, some 327680, some 393216, some 458752, some 524288, some 589824, some 655360,
     some 720896, some 786432, some 851968, some 917504, some 983040, some 1048576, some 1114112,
     some 1179648, some 1245184, some 1310720, some 1376256, some 1441792, some 1507328,
     some 1572864, none, none, none, none, none, none, none, none, none, none, none, none, none,
     none, none, none, none, none, none, none, none, none, none, none, none, some 6946816,
     some 7012352, some 7077888, some 7143424, some 7208960, some 7274496, some 7340032,
     some 7405568, some 7471104, some 7536640, some 7602176, some 7667712, some 7733248,
     some 7798784, some 7864320, some 7929856, some 7995392, some 8060928, some 8126464,
     some 8192000, some 8257536, some 8323072, some 8388608, some 8454144, some 8519680,
     some 8585216, some 8650752]

#guard leanIsaμ prog4 s₂ = 23
#guard offsets prog4 s₂ =
    [some 0, some 262144, some 524288, some 786432, some 5029888, some 4980736, some 5029892,
     some 5029896, some 5029900, some 5029904, some 5029908, some 5029912, some 5029916,
     some 5029920, some 5029924, some 5029928, some 5029932, some 5029936, some 5029940,
     some 5029944, some 5029948, some 1048576, some 1310720, some 1572864, some 1835008,
     some 2097152, some 2359296, some 2621440, some 2883584, some 3145728, some 3407872,
     some 3670016, some 3932160, some 4194304, some 4456448, some 4718592, some 5029632,
     some 5029664, some 5029696, some 5029728, some 5029760, some 5029792, some 5029824,
     some 5029856, some 5029952, some 5029953, some 5029954, some 5029955, some 5029956,
     some 5029957, some 5029958, some 5029959, some 5029960, some 5029961, some 5029962,
     some 5029963, some 5029964, some 5029965, some 5029966, some 5027840, some 5027968,
     some 5028096, some 5028224, some 5028352, some 5028480, some 5028608, some 5028736,
     some 5028864, some 5028992, some 5029120, some 5029248, some 5029376, some 5029504,
     some 5006336, some 5006848, some 5007360, some 5007872, some 5008384, some 5008896,
     some 5009408, some 5009920, some 5010432, some 5010944, some 5011456, some 5011968,
     some 5012480, some 5012992, some 5013504, some 4980736, some 4981248, some 4981760,
     some 4982272, some 4982784, some 4983296, some 4983808, some 4984320, some 4984832,
     some 4985344, some 4985856, some 4986368, some 4986880, some 4987392, some 4987904,
     some 4988416, some 4988928, some 4989440, some 4989952, some 4990464, some 4990976,
     some 4991488, some 4992000, some 4992512, some 4993024, none, none, none, none, none, none,
     none, none, none, none, none, none, none, none, none, none, none, none, none, none, none,
     none, none, none, none, some 5014016, some 5014528, some 5015040, some 5015552, some 5016064,
     some 5016576, some 5017088, some 5017600, some 5018112, some 5018624, some 5019136,
     some 5019648, some 5020160, some 5020672, some 5021184, some 5021696, some 5022208,
     some 5022720, some 5023232, some 5023744, some 5024256, some 5024768, some 5025280,
     some 5025792, some 5026304, some 5026816, some 5027328]

/-! ## Admissible sizes -/

#guard decide (s₁.Admissible prog4)
#guard decide (s₂.Admissible prog4)
#guard decide (s₃.Admissible prog4)
#guard leanIsaμ prog4 s₃ = leanIsaμ prog4 s₂
#guard decide (Sizes.Admissible prog4 ⟨1, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨33, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨16, by decide, ![2 ^ 32 + 1, 8, 1, 1, 1, 1]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨31, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard leanIsaμ prog4 ⟨31, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩ = 34
#guard (List.range 6).map (fun ρ ↦ decide (validRate ρ)) = [false, true, true, true, true, false]

/-! ## The public lines, the bus, the Keccak region -/

#guard ((publicLines prog4 s₁ ⟨![1, 2, 3, 4]⟩).toList.map fun l ↦
    (l.col == memCol 0, l.col == memCol 1, l.col == memCol 2, l.cell0, l.cell1, l.sent)) =
  [(true, false, false, 1, 3, false), (false, true, false, 2, 4, false),
    (false, false, true, 0, 0, false)]

#guard (boundary prog4 s₁).map (fun b ↦ (b.κ, b.side)) =
  [(0, .push), (16, .push), (2, .push), (0, .pull), (16, .pull), (2, .pull)]

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
