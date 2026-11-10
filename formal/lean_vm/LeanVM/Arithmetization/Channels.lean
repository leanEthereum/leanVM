/-
  LeanVM.Arithmetization.Channels

  The three bus interactions of leanISA as six Clean channels, the image a channel guarantee is
  stated against, the two read gadgets, and the bus data of every channel.
-/

module

public import LeanVM.Parameters.CleanField
public import LeanVM.Semantics.Lemmas
public import LeanVM.Arithmetization.Bytecode
public import Clean.Circuit.Basic
public import Clean.Utils.Tactics.ProvableStructDeriving
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# The bus channels

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `b41c196b`.

**The tuples.** Every bus tuple is sixteen `K` slots: a domain separator, then the
interaction's coordinates, then zeros (specification §5.1,
`doc/leanvm/body/05-arithmetization.tex:12` and `:16`; `crates/leanvm_core/src/tables.rs:94-96`,
`SEP_STATE`, `SEP_MEM`, `SEP_BYTECODE`). The three interactions and their coordinate orders:

* state, separator `g^0`: `(pc, fp)` (§6.1, `06-bus-interactions.tex:8`; `tables.rs:131-145`);
* memory, separator `g^1`: `(addr, count, v₀, v₁)`, a read of the word `v` at `addr` with
  count `count` (§6.2 "Tuple and columns" and "Flush rules", `:40-47`, and §6.3, `:86`;
  `tables.rs:124-148` at `leanvm-rev`, two limbs);
* bytecode, separator `g^2`: `(pc, count, opcode, op₁, …, op₁₂)`, the bytecode `entry` after the
  address and the count, fifteen coordinates, the widest message, filling the sixteen slots (§6.4;
  `tables.rs:113-122` at leanVM main `40f877dc`).

A typed message is one such coordinate list: the state message is the register pair `Regs` of
the semantics itself, over `K` when evaluated and over `Expression K` in a row (one structure, one
meaning), and `MemMsg` and `BytecodeMsg` are the two lookup tuples. The three `toElements`
lemmas pin the order Clean flattens a message in to the specification's; `busTuple` is the
sixteen-slot form, and `channelSep` and `channelDir` name each channel's separator and
direction as data, so that the proof system (issue #12) reads the M3 bus off these
channels rather than transcribing the tuples again (issue #13).

**The channels** (specification §6, Theorem 6.4 and Corollary 6.5). A read is
`pull (addr, count, v)` and `push (addr, g·count, v)` (§6.2 "Flush rules"). A *gated* read
(`memReadIf`, the Rust's `memory_coords_if`, `tables.rs:132-147` at `40f877dc`, for a `KECCAK`
output cell past the first) pushes the counter `count + flag·count·g + flag·count` instead: in
characteristic two that is `g·count` at `flag = 1`, a read, and `count` at `flag = 0`, where the
push is the pull's own tuple and the pair cancels; its pull is a `Channel.pullIf flag`, so a
soundness proof may assume its guarantee only at `flag = 1`. The lookup theorem
says that when the bus balances, every count is nonzero, and there are fewer than `2^64 - 1`
reads, every pulled memory tuple is a correct read of the committed image and every pulled
bytecode tuple is an entry of the public program. What a pull may assume locally is the
channel's `Guarantees`: `MemPull` states the whole lookup fact, `MemoryImage.read` of the image
named by the prover data, since the image is committed and lives nowhere else; `BytecodePull`
states only that the pulled entry decodes, through `decode`, to an instruction, a static fact
about the tuple that names no program (the paragraph on the program below), which is all a table
needs (`DEREF`'s flag pair must be a store mode's) and which `Soundness.BytecodeChannel` derives
from the lookup theorem together with the strong fact, that the entry is the program's at the
pulled counter. The state pull carries no guarantee: a pulled state need not be reachable, since a
balanced witness may hold closed walks disjoint from the run, and what the state channel yields is
the walk decomposition of `Soundness.Walk` (issue #10). Pushes carry no
guarantee; what a push must satisfy is the emitting component's `Spec`.

**Direction as data.** Clean tags every interaction with a direction: a pull of multiplicity `1`
is granted its channel's guarantee and a pull's multiplicity must be `0` or `1`, and an active push
owes the guarantee (`Channel.toRaw`). Each interaction of leanISA is a *pair* of channels,
`*.pull` and `*.push`, every interaction on a `*.pull` channel a pull and every one on a `*.push`
channel a push, so the direction of an interaction is also the channel it is on (`channelDir`):
`memRead` and `bytecodeRead` emit through `Channel.pull` on the pull channel, the one emitter whose
interaction a soundness proof may assume the guarantee of, and through `Channel.push` on the push
channel, whose guarantee is `True`, so a push owes nothing and what it must satisfy is the
emitting component's `Spec`. Every interaction of the tables and the boundary blocks has
multiplicity `1`, but for the pull of a gated read, of multiplicity `flag`, which no balance reads;
balance is the multiset equality of the two channels of a pair (`BalancedPair`), never a field
sum, which counts nothing over `K`. Merging each pair into one directed channel (issue #16) would
delete `Direction` and `channelDir` and make every push owe its pull's guarantee; the statement's
strength does not depend on it.

**The image** is read off Clean's `ProverData`, the string-keyed store a component's `Spec`
sees: `memRows` is its `"mem"` table, one row of two limbs per word. `imageOf` is total, since
a channel guarantee is a total proposition on arbitrary data, and so it normalises: it takes
the *floor* logarithm of the table's row count, capped at the verifier's bound (`maxLogMem`),
as its log-size, which drops the rows at indices from that power of two on whenever the count
is not exactly it. The cap also keeps `κ < 64`, the hypothesis under which `MemoryImage.read`
reads an address as an index (`gLog?_spec`), so `MemPull.Guarantees` means what it says on
every data. `WellShapedData` is the shape under which the reading drops nothing (the row count
is exactly a power of two within the cap, `wellShapedData_iff`), and `imageOf_apply` is its
specification. Clean derives the prover data from the witness's rows by component name, and the
memory block is named `"mem"` (`Arithmetization.Boundary`), so the image is the block's rows, cut at
their two limbs, and the derived data is well shaped (`Caps.well_shaped`,
`SatisfiedBy.seed_rows`).

**The program is public and the channels are program-free.** leanVM's bytecode is "public,
i.e. not committed, the verifier can evaluate it directly" (§6.4, `06-bus-interactions.tex:96`):
the eight entry columns ride the bytecode seed and finalize blocks as `Coord::Public`
(`cpu/layout.rs:8-11`, `:287-289`, `:382-394`; `leaf.rs:36-39`), and every opcode table's read
is its own constant opcode and its own operand columns, `[Const(BC), Col(pc), Col(count),
Const(opcode), operands…]` (`tables.rs:147-156`): no table knows the program, and what binds a
row's operands to the program is the bus, Theorem 6.4 applied to the bytecode pair. The Lean
follows that division of labour. The program is not prover data: Clean's `ProverData` is a
field of the witness, so a guarantee stated over a program read off it would be about a program
the prover chose. Nor is it a parameter of the channels
or of the tables: that would make the AIR itself a function of the program, where leanVM's is
fixed for all programs. It enters through the verifier only, as leanVM's does: the bytecode
block's fixed columns `bytecodeComponent prog`, whose rows are `bytecodeRowOf prog` with only the
finalize counts free, and the verifier's sentinel counter `leanIsaVerifier prog`
(`Arithmetization.Boundary`), as the verifier forms "the program's whole share of the two bytecode
blocks" itself (§8.6, Bus 4).

## Wrong readings excluded

* A push on a pull channel is not a push: `memRead` never emits on `MemPull` with `push`, and a
  `pull` on a push channel is granted `True`. The direction is `channelDir`, read from the channel.
* `-1 = 1` in `K`: a multiplicity carries no direction; the direction is the interaction's tag
  and its channel's (tests).
* `Channel.emit`, Clean's plain emitter, pushes, so a soundness proof of a component using it
  could never assume the guarantee of its own pull; `memRead` and `bytecodeRead` use
  `Channel.pull` instead.
* The element order of a typed message is its field order, a vector field contributing its
  elements in place: `(addr, count, v₀, v₁)`, never `(v, addr, count)` or the separator
  inside the message (`memMsg_toElements`).
* A table whose row count is not a power of two within its cap is silently truncated by
  `imageOf` (a three-row store yields a one-bit image, tests) and is not `WellShapedData`; the
  empty store is not either, since its image still has one word.
* The bytecode guarantee is not `True`: `DEREF`'s constraints are defined at the flag pair
  `(1, 1)`, which is no store mode's (`tables.rs:621-628`), so its soundness needs the pulled
  entry to decode; that every entry on the bus does is a fact about the public program
  (`decode_entry` on the block's rows), and `Soundness.BytecodeChannel` derives it (tests: the
  pair `(1, 1)` is rejected at every counter).
* The bytecode guarantee names no program: neither one read off the prover data, which the
  prover chooses, nor a parameter, which would put the program into every
  table's type. `BytecodePull.Guarantees` is the same proposition on every data
  (tests, `Iff.rfl`).
-/

namespace LeanVM.Semantics

/-! ## The state message -/

-- The state message is the semantics' register pair: `Regs K` evaluated, `Regs (Expression K)`
-- in a row (specification §6.1). Derived in the structure's own namespace, where Clean's handler
-- names its helpers after the structure.
deriving instance ProvableStruct for Registers

end LeanVM.Semantics

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## Messages -/

/-- The memory tuple after its separator: `(addr, count, v₀, v₁)`, a read of the word
`v = v₀ + v₁·y` at address `addr` with count `count` (specification §6.2, §6.3). -/
structure MemMsg (F : Type) where
  /-- The address, `fp · o` for an operand `o`. -/
  addr : F
  /-- The read count, a power of `g`. -/
  count : F
  /-- The two limbs of the word. -/
  v : Vector F 2
  deriving ProvableStruct

/-- The bytecode tuple after its separator: `(pc, count, opcode, op₁, …, op₁₂)`, a read of the
entry `(opcode, op₁, …, op₁₂)` (`entry`) at counter `pc` (specification §6.4). -/
structure BytecodeMsg (F : Type) where
  /-- The program counter, the entry's address. -/
  pc : F
  /-- The read count. -/
  count : F
  /-- The opcode, coordinate 3 of the tuple. -/
  opcode : F
  /-- The twelve operand slots. -/
  op : Vector F 12
  deriving ProvableStruct

/-! ## The image in the prover data -/

/-- The prover-data table holding the memory image: one row of two limbs per word. The
program has no table: it is public (the module docstring). -/
def memDataName : String := "mem"

/-- The rows of the `"mem"` table. -/
def memRows (data : ProverData K) : Array (Vector K 2) := data memDataName 2

/-- The memory image named by the prover data: `κ` is the floor logarithm of the `"mem"` row
count, capped at `maxLogMem`, word `i` is row `i` as limbs `(c₀, c₁)`, and a missing row
reads as `0`. Rows at indices from `2^κ` on are dropped; `WellShapedData` is the shape under
which there are none. -/
def imageOf (data : ProverData K) : (κ : ℕ) × MemoryImage κ :=
  ⟨min (Nat.log 2 (memRows data).size) maxLogMem,
    fun i ↦ (((memRows data)[(i : ℕ)]?).map fun v ↦ E.ofLimbs v[0] v[1]).getD 0⟩

/-- The prover data is well shaped: the `"mem"` table has exactly the `2^κ` rows of its image,
that is, its row count is a power of two within the cap `2^maxLogMem` (`wellShapedData_iff`),
so that `imageOf` drops nothing. A conjunct of the statement's `Caps`. -/
structure WellShapedData (data : ProverData K) : Prop where
  /-- The `"mem"` table has `2^κ` rows. -/
  memRows_size : (memRows data).size = 2 ^ (imageOf data).1

/-! ## The six channels -/

/-- The state pull, separator `g^0`. No guarantee: a pulled state need not be reachable. -/
def StatePull : Channel K Registers where
  name := "st.pull"
  Guarantees _ _ := True

/-- The state push, separator `g^0`. -/
def StatePush : Channel K Registers where
  name := "st.push"
  Guarantees _ _ := True

/-- The memory pull, separator `g^1`: a pulled tuple is a correct read of the image named by
the prover data (specification Theorem 6.4 and Corollary 6.5). -/
def MemPull : Channel K MemMsg where
  name := "mem.pull"
  Guarantees m data := (imageOf data).2.read m.addr = some (E.ofLimbs m.v[0] m.v[1])

/-- The memory push, separator `g^1`. -/
def MemPush : Channel K MemMsg where
  name := "mem.push"
  Guarantees _ _ := True

/-- The bytecode pull, separator `g^2`: the pulled entry decodes to an instruction (`decode`). A
static fact about the tuple alone, naming no program and reading no data: it is what the `DEREF`
table needs (a flag pair that is no store mode decodes to nothing) and what every entry of the
public program satisfies (`decode_entry`). That the entry is the program's at the pulled counter
is `Soundness.BytecodeChannel`'s, specification Theorem 6.4 on the bytecode pair from the
block's rows (`BytecodeRowsAreTheProgram`); the module docstring says why neither a program
read off the data nor a program parameter belongs here. -/
def BytecodePull : Channel K BytecodeMsg where
  name := "bc.pull"
  Guarantees b _ := ∃ ins, decode (#v[b.opcode] ++ b.op) = some ins

/-- The bytecode push, separator `g^2`. -/
def BytecodePush : Channel K BytecodeMsg where
  name := "bc.push"
  Guarantees _ _ := True

/-! ## The read gadgets -/

/-- A memory read of the word `v` at `addr` with count `count`: pull `(addr, count, v)`, push
`(addr, g·count, v)` (specification §6.2 "Flush rules"; `tables.rs:124-148` at `leanvm-rev`). The pull is a
`Channel.pull`, so that a soundness proof may assume `MemPull.Guarantees` of it. -/
def memRead (addr count : Expression K) (v : Vector (Expression K) 2) : Circuit K Unit := do
  MemPull.pull ⟨addr, count, v⟩
  MemPush.push ⟨addr, Expression.const g * count, v⟩

/-- A memory read of the word `v` at `addr` with count `count` when `flag` is `1`
(`memory_coords_if`, `tables.rs:133-137`, and `memory_if`, `crates/verifier/src/layout.rs:171-176`,
at `leanvm-rev`): pull `(addr, count, v)` and push `(addr, count + flag·count·g +
flag·count, v)`, `g·count` at `flag = 1` and the pull's own tuple at `flag = 0`, where the pair
cancels. The pull is a `Channel.pullIf flag`: its guarantee is assumed at `flag = 1` only. -/
def memReadIf (flag addr count : Expression K) (v : Vector (Expression K) 2) : Circuit K Unit := do
  MemPull.pullIf flag ⟨addr, count, v⟩
  MemPush.push ⟨addr, count + Expression.const g * (flag * count) + flag * count, v⟩

/-- The push counter of a gated read (`memReadIf`; `memory_coords_if`, `tables.rs:132-147` at
leanVM main `40f877dc`): `count + g·(flag·count) + flag·count`, the value of `memReadIf`'s push counter, which is `g·count` at
`flag = 1` (`gatedCount_one`) and `count` at `flag = 0` (`gatedCount_zero`). -/
def gatedCount (flag c : K) : K := c + g * (flag * c) + flag * c

/-- At flag `1` a gated read pushes `g·count`: it is a read. -/
theorem gatedCount_one (c : K) : gatedCount 1 c = g * c := by
  unfold gatedCount
  rw [one_mul, add_comm c, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- At flag `0` a gated read pushes the pull's own count: the pair cancels. -/
theorem gatedCount_zero (c : K) : gatedCount 0 c = c := by
  simp [gatedCount]

/-- A bytecode read of the entry `(opcode, op)` at counter `pc` with count `count`: pull
`(pc, count, opcode, op)`, push `(pc, g·count, opcode, op)` (specification §6.2, §6.4;
`tables.rs:113-122`). -/
def bytecodeRead (pc count opcode : Expression K) (op : Vector (Expression K) 12) :
    Circuit K Unit := do
  BytecodePull.pull ⟨pc, count, opcode, op⟩
  BytecodePush.push ⟨pc, Expression.const g * count, opcode, op⟩

/-! ## Bus data -/

/-- The direction of a bus flush (specification §5.1 "The bus"), as a channel of a pair carries it.
It agrees with Clean's `Channel.Direction` tag on every interaction of the ensemble; this one and
`channelDir` are deleted once the pairs are merged into directed channels (issue #16). -/
inductive Direction
  | pull
  | push
  deriving DecidableEq, Repr

/-- The direction of a channel, read from its name: the three `*.pull` channels pull, every other
channel pushes. Never the sign of a multiplicity. Deleted with `Direction` (issue #16). -/
def channelDir (c : RawChannel K) : Direction :=
  if c.name = StatePull.name ∨ c.name = MemPull.name ∨ c.name = BytecodePull.name then .pull
  else .push

/-- The domain separator of a channel (specification §5.1 "Domain separation";
`tables.rs:94-96`): `g^0` for the state pair, `g^1` for memory, `g^2` for bytecode, and `0`,
which is no separator, for any other channel. -/
def channelSep (c : RawChannel K) : K :=
  if c.name = StatePull.name ∨ c.name = StatePush.name then addressOfIndex 0
  else if c.name = MemPull.name ∨ c.name = MemPush.name then addressOfIndex 1
  else if c.name = BytecodePull.name ∨ c.name = BytecodePush.name then addressOfIndex 2
  else 0

/-- The sixteen-slot bus tuple of a message on a channel: the channel's separator, then the
message's elements in order, then zeros (specification §5.1, `05-arithmetization.tex:12`). -/
def busTuple (c : RawChannel K) (msg : List K) : Vector K 16 :=
  let m := fun j : ℕ ↦ msg.getD j 0
  #v[channelSep c, m 0, m 1, m 2, m 3, m 4, m 5, m 6, m 7, m 8, m 9, m 10, m 11, m 12, m 13,
    m 14]

/-! ## Load-bearing lemmas -/

/-- A state message flattens to `[pc, fp]` (specification §6.1). -/
theorem regs_toElements (s : Registers K) : (toElements s).toList = [s.pc, s.fp] := by
  obtain ⟨pc, fp⟩ := s
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]

/-- A memory message flattens to `[addr, count, v₀, v₁]` (specification §6.2). -/
theorem memMsg_toElements (m : MemMsg K) :
    (toElements m).toList = [m.addr, m.count] ++ m.v.toList := by
  obtain ⟨addr, count, v⟩ := m
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]

/-- A bytecode message flattens to `[pc, count, opcode, op₁, …, op₁₂]` (specification §6.4). -/
theorem bytecodeMsg_toElements (b : BytecodeMsg K) :
    (toElements b).toList = [b.pc, b.count, b.opcode] ++ b.op.toList := by
  obtain ⟨pc, count, opcode, op⟩ := b
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]

/-- Slot `0` of a bus tuple is the separator and slot `j + 1` is element `j` of the message,
`0` past its end. -/
theorem busTuple_getElem (c : RawChannel K) (msg : List K) (j : ℕ) (hj : j < 16) :
    (busTuple c msg)[j] = if j = 0 then channelSep c else msg.getD (j - 1) 0 := by
  interval_cases j <;> simp [busTuple]

/-- Well shaped means: the `"mem"` table's row count is a power of two within its cap,
`2^maxLogMem`. -/
theorem wellShapedData_iff (data : ProverData K) :
    WellShapedData data ↔ ∃ κ ≤ maxLogMem, (memRows data).size = 2 ^ κ := by
  constructor
  · rintro ⟨hm⟩
    exact ⟨_, Nat.min_le_right _ _, hm⟩
  · rintro ⟨κ, hκ, hκm⟩
    refine ⟨?_⟩
    show (memRows data).size = 2 ^ min (Nat.log 2 (memRows data).size) maxLogMem
    rw [hκm, Nat.log_pow (by norm_num), Nat.min_eq_left hκ]

/-- Under the shape, every index of the image is a row of the `"mem"` table. -/
theorem WellShapedData.memIndex_lt {data : ProverData K} (h : WellShapedData data)
    (i : Fin (2 ^ (imageOf data).1)) : (i : ℕ) < (memRows data).size := by
  rw [h.memRows_size]; exact i.isLt

/-- Under the shape, word `i` of the image is row `i` of the `"mem"` table, as limbs. -/
theorem imageOf_apply {data : ProverData K} (h : WellShapedData data)
    (i : Fin (2 ^ (imageOf data).1)) {v : Vector K 2}
    (hv : (memRows data)[(i : ℕ)]'(h.memIndex_lt i) = v) :
    (imageOf data).2 i = E.ofLimbs v[0] v[1] := by
  simp [imageOf, Array.getElem?_eq_getElem (h.memIndex_lt i), hv]

end LeanVM.Arithmetization
